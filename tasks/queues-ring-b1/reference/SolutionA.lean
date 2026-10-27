import RingBuffer.Spec
/-!
# Reference solution A (hidden from agents)

Decide validity first; enqueue writes slot `(head + count) % capacity`, dequeue advances
`head` modulo `capacity`.
-/

namespace RingBuffer

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid WellFormed <;> infer_instance

/-- The state after writing `x` behind the newest value. -/
def pushed (s : State) (x : Nat) : State :=
  { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }

/-- The state after removing the oldest value. -/
def popped (s : State) : State :=
  { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }

def step : Impl := fun s op =>
  if Valid s op then
    match op with
    | .enqueue x => (.ok, pushed s x)
    | .dequeue => (.got (s.buf s.head), popped s)
  else (.rejected, s)

theorem step_invalid {s : State} {op : Op} (h : ¬ Valid s op) : step s op = (.rejected, s) := by
  simp [step, h]

theorem step_enqueue {s : State} {x : Nat} (h : Valid s (.enqueue x)) :
    step s (.enqueue x) = (.ok, pushed s x) := by
  simp [step, h]

theorem step_dequeue {s : State} (h : Valid s .dequeue) :
    step s .dequeue = (.got (s.buf s.head), popped s) := by
  simp [step, h]

theorem ok_valid {s : State} {op : Op} (h : (step s op).1 ≠ .rejected) : Valid s op := by
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

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x => rw [step_enqueue h]; simp
  | dequeue => rw [step_dequeue h]; simp

theorem req_invalid_noop : InvalidNoop step := fun _ _ h => step_invalid h

theorem req_well_formed : KeepsWellFormed step := by
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

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  rw [step_enqueue (ok_valid h)]; rfl

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  rw [step_dequeue (ok_valid h)]; rfl

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x h
  have hv := ok_valid h
  rw [step_enqueue hv]
  exact pushed_contents x hv.2

theorem req_dequeue_contents : DequeueContents step := by
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
    contents s ++ inflowOf (op, (step s op).1)
      = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
  by_cases hv : Valid s op
  · cases op with
    | enqueue x => rw [step_enqueue hv]; simp [inflowOf, outflowOf, pushed_contents x hv.2]
    | dequeue => rw [step_dequeue hv]; simp [inflowOf, outflowOf, popped_contents hv.1 hv.2]
  · rw [step_invalid hv]; simp [inflowOf, outflowOf]

theorem req_fifo : Fifo step := fifo_of_flow step step_flow

end RingBuffer
