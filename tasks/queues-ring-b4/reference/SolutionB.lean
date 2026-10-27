import RingBuffer.Spec
/-!
# Reference solution B (hidden from agents)

Index arithmetic without `%`: the write slot wraps by one conditional subtraction and the
head wraps back to zero at the end of the array.
-/

namespace RingBuffer

/-- Reduce an index below `2 * c` into `[0, c)`. -/
def wrap (c i : Nat) : Nat := if i < c then i else i - c

def step : Impl
  | s, .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { capacity := s.capacity, head := s.head, count := s.count + 1,
              buf := fun i => if i = wrap s.capacity (s.head + s.count) then x else s.buf i })
    else (.rejected, s)
  | s, .dequeue =>
    if s.capacity ≠ 0 ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count ≠ 0 then
      (.got (s.buf s.head), { s with
        head := if s.head + 1 = s.capacity then 0 else s.head + 1, count := s.count - 1 })
    else (.rejected, s)

theorem wrap_eq {c h n : Nat} (hh : h < c) (hn : n < c) : wrap c (h + n) = (h + n) % c := by
  unfold wrap
  by_cases hlt : h + n < c
  · rw [if_pos hlt, Nat.mod_eq_of_lt hlt]
  · rw [if_neg hlt, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem next_eq {c h : Nat} (hh : h < c) : (if h + 1 = c then 0 else h + 1) = (h + 1) % c := by
  by_cases he : h + 1 = c
  · rw [if_pos he, he, Nat.mod_self]
  · rw [if_neg he, Nat.mod_eq_of_lt (by omega)]

/-- The specified state after a successful enqueue. -/
def enqState (s : State) (x : Nat) : State :=
  { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }

/-- The specified state after a successful dequeue. -/
def deqState (s : State) : State :=
  { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }

theorem enq_valid {s : State} {x : Nat} (h : Valid s (.enqueue x)) :
    step s (.enqueue x) = (.ok, enqState s x) := by
  obtain ⟨⟨hc, hh, _⟩, hn⟩ := h
  have hw : wrap s.capacity (s.head + s.count) = slot s s.count := wrap_eq hh hn
  simp only [step, hc, hh, hn, and_self, if_true, hw]
  rfl

theorem enq_invalid {s : State} {x : Nat} (h : ¬ Valid s (.enqueue x)) :
    step s (.enqueue x) = (.rejected, s) := by
  have : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
    intro ⟨a, b, c⟩; exact h ⟨⟨a, b, by omega⟩, c⟩
  simp only [step, this, if_false]

theorem deq_valid {s : State} (h : Valid s .dequeue) :
    step s .dequeue = (.got (s.buf s.head), deqState s) := by
  obtain ⟨⟨hc, hh, hle⟩, hn⟩ := h
  have hcond : s.capacity ≠ 0 ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count ≠ 0 :=
    ⟨by omega, hh, hle, by omega⟩
  simp only [step, if_pos hcond, next_eq hh]
  rfl

theorem deq_invalid {s : State} (h : ¬ Valid s .dequeue) : step s .dequeue = (.rejected, s) := by
  have : ¬ (s.capacity ≠ 0 ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count ≠ 0) := by
    intro ⟨a, b, c, d⟩; exact h ⟨⟨by omega, b, c⟩, by omega⟩
  simp only [step, this, if_false]

theorem step_invalid {s : State} {op : Op} (h : ¬ Valid s op) : step s op = (.rejected, s) := by
  cases op with
  | enqueue x => exact enq_invalid h
  | dequeue => exact deq_invalid h

theorem ok_valid {s : State} {op : Op} (h : (step s op).1 ≠ .rejected) : Valid s op := by
  by_cases hv : Valid s op
  · exact hv
  · rw [step_invalid hv] at h; exact absurd rfl h

theorem slots_differ {h i n c : Nat} (hi : i < n) (hn : n < c) : (h + i) % c ≠ (h + n) % c := by
  intro heq
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq heq.symm
  rw [show (h + n) - (h + i) = n - i by omega, Nat.mod_eq_of_lt (by omega)] at h1
  omega

theorem enqState_contents (s : State) (x : Nat) (hn : s.count < s.capacity) :
    contents (enqState s x) = contents s ++ [x] := by
  unfold contents enqState
  rw [List.range_succ, List.map_append]
  simp only [slot, List.map_cons, List.map_nil]
  congr 1
  apply List.map_inj_left.mpr
  intro i hi
  simp [slots_differ (List.mem_range.mp hi) hn]

theorem deqState_contents (s : State) (hh : s.head < s.capacity) (hn : 0 < s.count) :
    contents s = s.buf s.head :: contents (deqState s) := by
  unfold contents deqState
  obtain ⟨m, hm⟩ : ∃ m, s.count = m + 1 := ⟨s.count - 1, by omega⟩
  simp only [hm, Nat.add_sub_cancel]
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [slot, Nat.add_zero, Nat.mod_eq_of_lt hh]
  congr 1
  apply List.map_inj_left.mpr
  intro i _
  simp only [Function.comp_apply, Nat.mod_add_mod, Nat.add_succ, Nat.succ_add]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x => rw [enq_valid h]; simp
  | dequeue => rw [deq_valid h]; simp

theorem req_invalid_noop : InvalidNoop step := fun _ _ h => step_invalid h

theorem req_enqueue_effects : EnqueueEffects step := fun s x h => enq_valid (ok_valid h)

theorem req_dequeue_effects : DequeueEffects step := fun s h => deq_valid (ok_valid h)

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hw
  obtain ⟨hc, hh, hle⟩ := hw
  by_cases hv : Valid s op
  · cases op with
    | enqueue x =>
      rw [enq_valid hv]
      have := hv.2
      exact ⟨hc, hh, by simp [enqState]; omega⟩
    | dequeue =>
      rw [deq_valid hv]
      exact ⟨hc, Nat.mod_lt _ hc, by simp [deqState]; omega⟩
  · rw [step_invalid hv]; exact ⟨hc, hh, hle⟩

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x h
  have hv := ok_valid h
  rw [enq_valid hv]; exact enqState_contents s x hv.2

theorem req_dequeue_contents : DequeueContents step := by
  intro s h
  have hv := ok_valid h
  rw [deq_valid hv]; exact ⟨_, rfl, deqState_contents s hv.1.2.1 hv.2⟩

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    simp only [run, inflow, outflow, List.flatMap_cons] at ih ⊢
    have hstep : contents s ++ inflowOf (op, (step s op).1)
        = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
      by_cases hv : Valid s op
      · cases op with
        | enqueue x => rw [enq_valid hv, enqState_contents s x hv.2]; simp [inflowOf, outflowOf]
        | dequeue =>
          rw [deq_valid hv, deqState_contents s hv.1.2.1 hv.2]; simp [inflowOf, outflowOf]
      · rw [step_invalid hv]; cases op <;> simp [inflowOf, outflowOf]
    rw [← List.append_assoc, hstep, List.append_assoc, ih, List.append_assoc]

end RingBuffer
