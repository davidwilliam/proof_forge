import RingBuffer.Spec
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { s with
        buf := fun i => if i = slot s s.count then x else s.buf i,
        count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity then
      (.got (s.buf s.head), { s with
        head := (s.head + 1) % s.capacity,
        count := s.count - 1 })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | enqueue x =>
    have h1 : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
      simp [Valid, WellFormed] at hV
      exact ⟨hV.1.1, hV.1.2.1, hV.2⟩
    simp [step, h1]
  | dequeue =>
    have h1 : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity := by
      simp [Valid, WellFormed] at hV
      exact ⟨hV.1.1, hV.1.2.1, hV.2, hV.1.2.2⟩
    simp [step, h1]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv
  cases op with
  | enqueue x =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro h; apply hInv; simp [Valid, WellFormed]; exact ⟨⟨h.1, h.2.1, Nat.le_of_lt h.2.2⟩, h.2.2⟩
    simp [step, hcond]
  | dequeue =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity) := by
      intro h; apply hInv; simp [Valid, WellFormed]; exact ⟨⟨h.1, h.2.1, h.2.2.2⟩, h.2.2.1⟩
    simp [step, hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hW
  cases op with
  | enqueue x =>
    by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · have h : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by simp [step, hcond]
      rw [h]; simp [WellFormed] at hW ⊢; omega
    · have h : step s (.enqueue x) = (.rejected, s) := by simp [step, hcond]
      rw [h]; exact hW
  | dequeue =>
    by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity
    · have h : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by simp [step, hcond]
      rw [h]; simp [WellFormed]; exact ⟨hW.1, Nat.mod_lt _ hW.1, by omega⟩
    · have h : step s .dequeue = (.rejected, s) := by simp [step, hcond]
      rw [h]; exact hW

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hOk
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · simp [step, hcond]
  · have heq : step s (.enqueue x) = (.rejected, s) := by simp [step, hcond]
    rw [heq] at hOk; simp at hOk

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hOk
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity
  · simp [step, hcond]
  · have heq : step s .dequeue = (.rejected, s) := by simp [step, hcond]
    rw [heq] at hOk; simp at hOk

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hOk
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact h
    · have heq : step s (.enqueue x) = (.rejected, s) := by simp [step, h]
      rw [heq] at hOk; simp at hOk
  have hEq : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by simp [step, hcond]
  rw [hEq]
  have hcap : 0 < s.capacity := hcond.1
  have hslot_eq : ∀ i, slot { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } i = slot s i := by intro i; simp [slot]
  have h_contents : contents { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } = (List.range (s.count + 1)).map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)) := by simp [contents, hslot_eq]
  rw [h_contents]
  have hne : ∀ i, i < s.count → slot s i ≠ slot s s.count := by
    intro i hi heq; simp [slot] at heq
    have hAi : s.head + i < s.capacity * 2 := by omega
    have hAc : s.head + s.count < s.capacity * 2 := by omega
    have mod_sub : ∀ n c, 0 < c → c ≤ n → n < c * 2 → n % c = n - c := by
      intro n c hc hle hlt
      have h1 : n = c + (n - c) := by omega
      have h2 : n - c < c := by omega
      have h3 : (n - c) % c = n - c := Nat.mod_eq_of_lt h2
      calc n % c = (c + (n - c)) % c := by rw [← h1]
        _ = (n - c) % c := by rw [Nat.add_mod_left]
        _ = n - c := h3
    by_cases h1 : s.head + i < s.capacity <;> by_cases h2 : s.head + s.count < s.capacity
    · have e1 : (s.head + i) % s.capacity = s.head + i := Nat.mod_eq_of_lt h1
      have e2 : (s.head + s.count) % s.capacity = s.head + s.count := Nat.mod_eq_of_lt h2
      rw [e1, e2] at heq; omega
    · have e1 : (s.head + i) % s.capacity = s.head + i := Nat.mod_eq_of_lt h1
      have e2 : (s.head + s.count) % s.capacity = s.head + s.count - s.capacity := mod_sub _ _ hcap (by omega) hAc
      rw [e1, e2] at heq; omega
    · have e1 : (s.head + i) % s.capacity = s.head + i - s.capacity := mod_sub _ _ hcap (by omega) hAi
      have e2 : (s.head + s.count) % s.capacity = s.head + s.count := Nat.mod_eq_of_lt h2
      rw [e1, e2] at heq; omega
    · have e1 : (s.head + i) % s.capacity = s.head + i - s.capacity := mod_sub _ _ hcap (by omega) hAi
      have e2 : (s.head + s.count) % s.capacity = s.head + s.count - s.capacity := mod_sub _ _ hcap (by omega) hAc
      rw [e1, e2] at heq; omega
  have hrange : List.range (s.count + 1) = List.range s.count ++ [s.count] := by simp [List.range_succ]
  rw [hrange, List.map_append]
  have h1 : List.map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)) (List.range s.count) = List.map (fun i => s.buf (slot s i)) (List.range s.count) := by
    apply List.map_congr_left; intro i hi; have hi' : i < s.count := List.mem_range.mp hi; simp [hne i hi']
  rw [h1]; simp [contents]

private theorem range_cons_map_succ (n : Nat) : List.range (n + 1) = 0 :: List.map (· + 1) (List.range n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    calc List.range (k + 1 + 1) = List.range (k + 1) ++ [k + 1] := by simp [List.range_succ]
      _ = (0 :: List.map (· + 1) (List.range k)) ++ [k + 1] := by rw [ih]
      _ = 0 :: (List.map (· + 1) (List.range k) ++ [k + 1]) := by simp
      _ = 0 :: List.map (· + 1) (List.range (k + 1)) := by simp [List.range_succ, List.map_append]

theorem req_dequeue_contents : DequeueContents step := by
  intro s hOk
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity := by
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity
    · exact h
    · have heq : step s .dequeue = (.rejected, s) := by simp [step, h]
      rw [heq] at hOk; simp at hOk
  have hEq : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by simp [step, hcond]
  have h0 : slot s 0 = s.head := by simp [slot, Nat.mod_eq_of_lt hcond.2.1]
  refine ⟨s.buf s.head, by rw [hEq], ?_⟩
  have hStepSnd : (step s Op.dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by rw [hEq]
  rw [hStepSnd]
  cases hcnt : s.count with
  | zero => omega
  | succ n =>
    have hcs : contents s = List.map (fun i => s.buf (slot s i)) (List.range (n + 1)) := by simp [contents, hcnt]
    have hr := range_cons_map_succ n
    have h_head_val : s.buf (slot s 0) = s.buf s.head := by rw [h0]
    have h_tail : List.map (fun i => s.buf (slot s (i + 1))) (List.range n) =
                 List.map (fun j => s.buf (slot { s with head := (s.head + 1) % s.capacity, count := n } j)) (List.range n) := by
      apply List.map_congr_left
      intro j hj
      have hj_lt_cap : j < s.capacity := by have : j < n := List.mem_range.mp hj; omega
      have h_eq_slot : slot s (j+1) = slot { s with head := (s.head + 1) % s.capacity, count := n } j := by
        simp only [slot]
        have h2 : s.head + (j + 1) = s.head + 1 + j := by omega
        rw [h2, Nat.add_mod, Nat.mod_eq_of_lt hj_lt_cap]
      rw [h_eq_slot]
    have h_state_eq : ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) = { s with head := (s.head + 1) % s.capacity, count := n } := by simp [hcnt]
    have h_target_n : contents { s with head := (s.head + 1) % s.capacity, count := n } =
               List.map (fun j => s.buf (slot { s with head := (s.head + 1) % s.capacity, count := n } j)) (List.range n) := by simp [contents]
    have h_target : contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } =
               List.map (fun j => s.buf (slot { s with head := (s.head + 1) % s.capacity, count := n } j)) (List.range n) := by rw [h_state_eq]; exact h_target_n
    calc contents s = List.map (fun i => s.buf (slot s i)) (List.range (n + 1)) := hcs
      _ = List.map (fun i => s.buf (slot s i)) (0 :: List.map (· + 1) (List.range n)) := by rw [hr]
      _ = s.buf (slot s 0) :: List.map (fun i => s.buf (slot s (i + 1))) (List.range n) := by simp
      _ = s.buf s.head :: List.map (fun j => s.buf (slot { s with head := (s.head + 1) % s.capacity, count := n } j)) (List.range n) := by rw [h_head_val, h_tail]
      _ = s.buf s.head :: contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by rw [h_target]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    simp only [run]
    by_cases hV : Valid s op
    · have hNotRej : (step s op).1 ≠ .rejected := req_valid_succeeds s op hV
      cases op with
      | enqueue x =>
        have hEnq : contents (step s (Op.enqueue x)).2 = contents s ++ [x] := req_enqueue_contents s x hNotRej
        have hOk : (step s (Op.enqueue x)).1 = .ok := by
          have hE := req_enqueue_effects s x hNotRej; rw [hE]; rfl
        have ih' := ih (step s (Op.enqueue x)).2
        have hIn : inflowOf (Op.enqueue x, Outcome.ok) = [x] := by simp [inflowOf]
        have hOut : outflowOf (Op.enqueue x, Outcome.ok) = ([] : List Nat) := by simp [outflowOf]
        have h1 : inflow (((Op.enqueue x, (step s (Op.enqueue x)).1) :: (run step (step s (Op.enqueue x)).2 ops).1)) = [x] ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by
          simp [inflow, hIn, hOk]
        have h2 : outflow (((Op.enqueue x, (step s (Op.enqueue x)).1) :: (run step (step s (Op.enqueue x)).2 ops).1)) = outflow (run step (step s (Op.enqueue x)).2 ops).1 := by
          simp [outflow, hOut, hOk]
        rw [h1, h2]
        calc contents s ++ ([x] ++ inflow (run step (step s (Op.enqueue x)).2 ops).1)
            = (contents s ++ [x]) ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by rw [List.append_assoc]
          _ = contents (step s (Op.enqueue x)).2 ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by rw [hEnq]
          _ = outflow (run step (step s (Op.enqueue x)).2 ops).1 ++ contents (run step (step s (Op.enqueue x)).2 ops).2 := ih'
      | dequeue =>
        obtain ⟨x, hGot, hCont⟩ := req_dequeue_contents s hNotRej
        have ih' := ih (step s Op.dequeue).2
        have hIn : inflowOf (Op.dequeue, Outcome.got x) = ([] : List Nat) := by simp [inflowOf]
        have hOut : outflowOf (Op.dequeue, Outcome.got x) = [x] := by simp [outflowOf]
        have h1 : inflow (((Op.dequeue, (step s Op.dequeue).1) :: (run step (step s Op.dequeue).2 ops).1)) = inflow (run step (step s Op.dequeue).2 ops).1 := by
          simp [inflow, hIn, hGot]
        have h2 : outflow (((Op.dequeue, (step s Op.dequeue).1) :: (run step (step s Op.dequeue).2 ops).1)) = [x] ++ outflow (run step (step s Op.dequeue).2 ops).1 := by
          simp [outflow, hOut, hGot]
        rw [h1, h2]
        calc contents s ++ inflow (run step (step s Op.dequeue).2 ops).1
            = (x :: contents (step s Op.dequeue).2) ++ inflow (run step (step s Op.dequeue).2 ops).1 := by rw [hCont]
          _ = [x] ++ (contents (step s Op.dequeue).2 ++ inflow (run step (step s Op.dequeue).2 ops).1) := by simp
          _ = [x] ++ (outflow (run step (step s Op.dequeue).2 ops).1 ++ contents (run step (step s Op.dequeue).2 ops).2) := by rw [ih']
          _ = ([x] ++ outflow (run step (step s Op.dequeue).2 ops).1) ++ contents (run step (step s Op.dequeue).2 ops).2 := by rw [List.append_assoc]
    · have hNoop := req_invalid_noop s op hV
      have hRej : (step s op).1 = Outcome.rejected := by rw [hNoop]
      have hSt : (step s op).2 = s := by rw [hNoop]
      have hIn : inflowOf (op, Outcome.rejected) = ([] : List Nat) := by cases op <;> simp [inflowOf]
      have hOut : outflowOf (op, Outcome.rejected) = ([] : List Nat) := by cases op <;> simp [outflowOf]
      have h1 : inflow (((op, (step s op).1) :: (run step (step s op).2 ops).1)) = inflow (run step s ops).1 := by
        rw [hRej, hSt]; simp [inflow, hIn]
      have h2 : outflow (((op, (step s op).1) :: (run step (step s op).2 ops).1)) ++ contents (run step (step s op).2 ops).2 = outflow (run step s ops).1 ++ contents (run step s ops).2 := by
        rw [hRej, hSt]; simp [outflow, hOut]
      have h3 : contents s ++ inflow (((op, (step s op).1) :: (run step (step s op).2 ops).1)) = contents s ++ inflow (run step s ops).1 := by
        rw [h1]
      rw [h3, h2]
      exact ih s

end RingBuffer
