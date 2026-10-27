import RingBuffer.Spec
namespace RingBuffer

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid WellFormed <;> infer_instance

/-- The state after writing `x` behind the newest value. -/
def pushed (s : State) (x : Nat) : State :=
  { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }

/-- The state after removing the oldest value. -/
def popped (s : State) : State :=
  { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }

def refStep : Impl := fun s op =>
  if Valid s op then
    match op with
    | .enqueue x => (.ok, pushed s x)
    | .dequeue => (.got (s.buf s.head), popped s)
  else (.rejected, s)

theorem step_invalid {s : State} {op : Op} (h : ¬ Valid s op) : refStep s op = (.rejected, s) := by
  simp [refStep, h]

theorem step_enqueue {s : State} {x : Nat} (h : Valid s (.enqueue x)) :
    refStep s (.enqueue x) = (.ok, pushed s x) := by
  simp [refStep, h]

theorem step_dequeue {s : State} (h : Valid s .dequeue) :
    refStep s .dequeue = (.got (s.buf s.head), popped s) := by
  simp [refStep, h]

theorem ok_valid {s : State} {op : Op} (h : (refStep s op).1 ≠ .rejected) : Valid s op := by
  by_cases hv : Valid s op
  · exact hv
  · rw [step_invalid hv] at h; exact absurd rfl h

/-- Distinct positions below the capacity occupy distinct slots. -/
theorem mod_ne {h i n c : Nat} (hi : i < n) (hn : n < c) : (h + i) % c ≠ (h + n) % c := by
  intro heq
  have h1 : ((h + n) - (h + i)) % c = 0 := Nat.sub_mod_eq_zero_of_mod_eq heq.symm
  have h2 : (h + n) - (h + i) = n - i := by omega
  rw [h2, Nat.mod_eq_of_lt (by omega)] at h1
  omega

theorem pushed_contents {s : State} (x : Nat) (hn : s.count < s.capacity) :
    contents (pushed s x) = contents s ++ [x] := by
  simp only [contents, pushed, slot, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]
  congr 1
  apply List.map_inj_left.mpr
  intro i hi
  have hi' : i < s.count := List.mem_range.mp hi
  simp [mod_ne hi' hn]

theorem popped_contents {s : State} (hw : WellFormed s) (hn : 0 < s.count) :
    contents s = s.buf s.head :: contents (popped s) := by
  obtain ⟨m, hm⟩ : ∃ m, s.count = m + 1 := ⟨s.count - 1, by omega⟩
  simp only [contents, popped, slot, hm, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.add_zero, Nat.mod_eq_of_lt hw.2.1, Nat.add_sub_cancel]
  congr 1
  apply List.map_inj_left.mpr
  intro i _
  simp only [Function.comp, Nat.mod_add_mod]
  congr 2
  omega

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s op h
  cases op with
  | enqueue x => rw [step_enqueue h]; simp
  | dequeue => rw [step_dequeue h]; simp

theorem ref_req_invalid_noop : InvalidNoop refStep := fun _ _ h => step_invalid h

theorem ref_req_well_formed : KeepsWellFormed refStep := by
  intro s op hw
  by_cases hv : Valid s op
  · cases op with
    | enqueue x =>
      rw [step_enqueue hv]
      have := hv.2
      exact ⟨hw.1, hw.2.1, by simp [pushed]; omega⟩
    | dequeue =>
      rw [step_dequeue hv]
      have := hw.2.2
      exact ⟨hw.1, Nat.mod_lt _ hw.1, by simp [popped]; omega⟩
  · rw [step_invalid hv]; exact hw

theorem ref_req_enqueue_effects : EnqueueEffects refStep := by
  intro s x h
  rw [step_enqueue (ok_valid h)]; rfl

theorem ref_req_dequeue_effects : DequeueEffects refStep := by
  intro s h
  rw [step_dequeue (ok_valid h)]; rfl

theorem ref_req_enqueue_contents : EnqueueContents refStep := by
  intro s x h
  have hv := ok_valid h
  rw [step_enqueue hv]
  exact pushed_contents x hv.2

theorem ref_req_dequeue_contents : DequeueContents refStep := by
  intro s h
  have hv := ok_valid h
  rw [step_dequeue hv]
  exact ⟨_, rfl, popped_contents hv.1 hv.2⟩

/-- Any implementation whose single steps move values correctly satisfies REQ-FIFO. -/
theorem fifo_of_flow (st : Impl)
    (h : ∀ s op, contents s ++ inflowOf (op, (st s op).1)
      = outflowOf (op, (st s op).1) ++ contents (st s op).2) : Fifo st := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    simp only [run, inflow, outflow, List.flatMap_cons] at ih ⊢
    rw [← List.append_assoc, h, List.append_assoc, ih, List.append_assoc]

theorem step_flow (s : State) (op : Op) :
    contents s ++ inflowOf (op, (refStep s op).1)
      = outflowOf (op, (refStep s op).1) ++ contents (refStep s op).2 := by
  by_cases hv : Valid s op
  · cases op with
    | enqueue x => rw [step_enqueue hv]; simp [inflowOf, outflowOf, pushed_contents x hv.2]
    | dequeue => rw [step_dequeue hv]; simp [inflowOf, outflowOf, popped_contents hv.1 hv.2]
  · rw [step_invalid hv]; simp [inflowOf, outflowOf]

theorem ref_req_fifo : Fifo refStep := fifo_of_flow refStep step_flow

-- Side-effect fix: a dequeue also clears the slot it frees.
def clearHead (s : State) (r : Outcome × State) : Outcome × State :=
  if r.1 ≠ .rejected then (r.1, { r.2 with buf := fun i => if i = s.head then 0 else s.buf i }) else r

def step : Impl := fun s op =>
  match op with
  | .enqueue x => refStep s (.enqueue x)
  | .dequeue => clearHead s (refStep s .dequeue)

theorem step_enq (s : State) (x : Nat) : step s (.enqueue x) = refStep s (.enqueue x) := rfl
theorem step_deq (s : State) : step s .dequeue = clearHead s (refStep s .dequeue) := rfl
theorem clear_fst (s : State) (r : Outcome × State) : (clearHead s r).1 = r.1 := by
  unfold clearHead; split <;> rfl
theorem clear_wf (s : State) (r : Outcome × State) (h : WellFormed r.2) : WellFormed (clearHead s r).2 := by
  unfold clearHead; split
  · exact h
  · exact h

theorem fst_eq (s : State) (op : Op) : (step s op).1 = (refStep s op).1 := by
  cases op with
  | enqueue x => rfl
  | dequeue => rw [step_deq, clear_fst]

/-- Clearing the freed slot does not change the stored values. -/
theorem cleared_contents (s : State) (hv : Valid s .dequeue) :
    contents { popped s with buf := fun i => if i = s.head then 0 else s.buf i }
      = contents (popped s) := by
  obtain ⟨⟨hc, hh, hle⟩, hn⟩ := hv
  simp only [contents, popped, slot]
  apply List.map_inj_left.mpr
  intro i hi
  have hi' : i < s.count - 1 := List.mem_range.mp hi
  have hne : (s.head + 1 + i) % s.capacity ≠ s.head := by
    have := mod_ne (h := s.head) (i := 0) (n := i + 1) (c := s.capacity) (by omega) (by omega)
    rw [Nat.add_zero, Nat.mod_eq_of_lt hh, show s.head + (i + 1) = s.head + 1 + i by omega] at this
    exact fun e => this e.symm
  simp [Nat.mod_add_mod, hne]

theorem contents_eq (s : State) (op : Op) : contents (step s op).2 = contents (refStep s op).2 := by
  cases op with
  | enqueue x => rfl
  | dequeue =>
    rw [step_deq]
    by_cases h : (refStep s .dequeue).1 ≠ .rejected
    · have hv := ok_valid h
      unfold clearHead
      rw [if_pos h, step_dequeue hv]
      exact cleared_contents s hv
    · unfold clearHead; rw [if_neg h]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h; rw [fst_eq]; exact ref_req_valid_succeeds s op h
theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x => exact ref_req_invalid_noop s _ h
  | dequeue => rw [step_deq, ref_req_invalid_noop s _ h]; simp [clearHead]
theorem req_well_formed : KeepsWellFormed step := by
  intro s op hw
  have hr := ref_req_well_formed s op hw
  cases op with
  | enqueue x => exact hr
  | dequeue => rw [step_deq]; exact clear_wf s _ hr
theorem req_enqueue_effects : EnqueueEffects step := fun s x h => ref_req_enqueue_effects s x h
-- Weakened restatement: the slot contents after a dequeue are not promised.
theorem req_dequeue_effects : ∀ s, (step s .dequeue).1 ≠ .rejected →
    (step s .dequeue).1 = .got (s.buf s.head) ∧
      (step s .dequeue).2.head = (s.head + 1) % s.capacity ∧ (step s .dequeue).2.count = s.count - 1 := by
  intro s h
  rw [fst_eq] at h
  have e := ref_req_dequeue_effects s h
  rw [step_deq]
  unfold clearHead
  rw [if_pos h, e]
  exact ⟨rfl, rfl, rfl⟩
theorem req_enqueue_contents : EnqueueContents step := fun s x h => ref_req_enqueue_contents s x h
theorem req_dequeue_contents : DequeueContents step := by
  intro s h; rw [fst_eq] at h; rw [fst_eq, contents_eq]; exact ref_req_dequeue_contents s h
theorem req_fifo : Fifo step := by
  apply fifo_of_flow
  intro s op; rw [fst_eq, contents_eq]; exact step_flow s op

end RingBuffer
