import RingBuffer.Spec
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | enqueue x =>
    simp only [step]
    have h1 : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      obtain ⟨⟨hcap, hhead, hle⟩, hlt⟩ := hV; exact ⟨hcap, hhead, hlt⟩
    simp [h1]
  | dequeue =>
    simp only [step]
    have h1 : (0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity) := by
      obtain ⟨⟨hcap, hhead, hle⟩, hpos⟩ := hV; exact ⟨hcap, hhead, hpos, hle⟩
    simp [h1]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv
  cases op with
  | enqueue x =>
    simp only [step]
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro h; apply hInv; obtain ⟨hcap, hhead, hlt⟩ := h; exact ⟨⟨hcap, hhead, Nat.le_of_lt hlt⟩, hlt⟩
    simp [hcond]
  | dequeue =>
    simp only [step]
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity) := by
      intro h; apply hInv; obtain ⟨hcap, hhead, hpos, hle⟩ := h; exact ⟨⟨hcap, hhead, hle⟩, hpos⟩
    simp [hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hW; obtain ⟨hcap, hhead, hle⟩ := hW
  cases op with
  | enqueue x =>
    simp only [step]
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · simp only [h, ite_true]; refine ⟨hcap, hhead, ?_⟩; simp; omega
    · simp [h]; exact ⟨hcap, hhead, hle⟩
  | dequeue =>
    simp only [step]
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity
    · simp only [h, ite_true]; refine ⟨hcap, Nat.mod_lt _ hcap, ?_⟩; simp; omega
    · simp [h]; exact ⟨hcap, hhead, hle⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hOk
  have hGuard : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact hc
    · have hRej : (step s (Op.enqueue x)).1 = Outcome.rejected := by simp [step, hc]
      exact absurd hRej hOk
  simp [step, hGuard]

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hOk
  have hGuard : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity
    · exact hc
    · have hRej : (step s Op.dequeue).1 = Outcome.rejected := by simp [step, hc]
      exact absurd hRej hOk
  simp [step, hGuard]

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hOk
  have hGuard : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact hc
    · have hRej : (step s (Op.enqueue x)).1 = Outcome.rejected := by simp [step, hc]
      exact absurd hRej hOk
  have hStep : (step s (Op.enqueue x)).2 = { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } := by simp [step, hGuard]
  rw [hStep]
  obtain ⟨hcap, hhead, hlt⟩ := hGuard
  have hSlotNe : ∀ i, i < s.count → slot s i ≠ slot s s.count := by
    intro i hi; unfold slot; intro heq
    have hsub_lt : s.count - i < s.capacity := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hlt
    have hadd : s.head + s.count = s.head + i + (s.count - i) := by omega
    have h1 : (s.head + i + (s.count - i)) % s.capacity = ((s.head + i) % s.capacity + (s.count - i)) % s.capacity := by
      rw [Nat.add_mod]; rw [Nat.mod_eq_of_lt hsub_lt]
    have h_tail_eq : (s.head + s.count) % s.capacity = ((s.head + i) % s.capacity + (s.count - i)) % s.capacity := by
      calc (s.head + s.count) % s.capacity = (s.head + i + (s.count - i)) % s.capacity := by rw [← hadd]
        _ = ((s.head + i) % s.capacity + (s.count - i)) % s.capacity := h1
    have hc_eq : ((s.head + i) % s.capacity + (s.count - i)) % s.capacity = (s.head + i) % s.capacity := by rw [← h_tail_eq, heq]
    by_cases hsum : (s.head + i) % s.capacity + (s.count - i) < s.capacity
    · rw [Nat.mod_eq_of_lt hsum] at hc_eq; omega
    · have hdiff_lt : (s.head + i) % s.capacity + (s.count - i) - s.capacity < s.capacity := by omega
      have h_eq : (s.head + i) % s.capacity + (s.count - i) = ((s.head + i) % s.capacity + (s.count - i) - s.capacity) + s.capacity := by omega
      have hmod : ((s.head + i) % s.capacity + (s.count - i)) % s.capacity = ((s.head + i) % s.capacity + (s.count - i) - s.capacity) % s.capacity := by
        conv_lhs => rw [h_eq]; rw [Nat.add_mod, Nat.mod_self]
      have hmod2 : ((s.head + i) % s.capacity + (s.count - i) - s.capacity) % s.capacity = (s.head + i) % s.capacity + (s.count - i) - s.capacity := Nat.mod_eq_of_lt hdiff_lt
      rw [hmod, hmod2] at hc_eq; omega
  have hSlotEq : ∀ i, slot { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } i = slot s i := by intro i; simp [slot]
  unfold contents; simp only [hSlotEq]
  have hrange : List.range (s.count + 1) = List.range s.count ++ [s.count] := by simp
  rw [hrange, List.map_append]
  have hmap_eq : List.map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)) (List.range s.count) = List.map (fun i => s.buf (slot s i)) (List.range s.count) := by
    apply List.map_congr_left; intro i hi
    have hi_lt : i < s.count := List.mem_range.mp hi
    have hne := hSlotNe i hi_lt; simp [hne]
  have htail : List.map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)) [s.count] = [x] := by simp
  rw [hmap_eq, htail]

theorem req_dequeue_contents : DequeueContents step := by
  intro s hOk
  have hGuard : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity
    · exact hc
    · have hRej : (step s Op.dequeue).1 = Outcome.rejected := by simp [step, hc]
      exact absurd hRej hOk
  obtain ⟨hcap, hhead, hpos, _⟩ := hGuard
  have hEff := req_dequeue_effects (s := s) hOk
  refine ⟨s.buf s.head, by rw [hEff], ?_⟩
  have hEq : contents s = s.buf s.head :: contents { capacity := s.capacity, buf := s.buf, head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
    simp only [contents, slot]
    cases hcount : s.count with
    | zero => omega
    | succ n =>
      have hhead0 : (s.head + 0) % s.capacity = s.head := by simp [Nat.mod_eq_of_lt hhead]
      have hLHS : (List.range (n + 1)).map (fun i => s.buf ((s.head + i) % s.capacity)) = s.buf ((s.head + 0) % s.capacity) :: (List.range n).map (fun i => s.buf ((s.head + (i+1)) % s.capacity)) := by
        have h : List.range (n + 1) = 0 :: (List.range n).map (· + 1) := by
          have : List.range (n + 1) = List.range n ++ [n] := by simp
          rw [this]; simp [List.range_succ]
        rw [h]; simp
      rw [hLHS, hhead0]
      congr 1
      apply List.ext_getElem
      · simp
      · intro m h1 h2; simp at h1 h2
        have hm_cap : m < s.capacity := by omega
        have hmod : (s.head + (m + 1)) % s.capacity = ((s.head + 1) % s.capacity + m) % s.capacity := by
          have h1 : s.head + (m + 1) = s.head + 1 + m := by omega
          rw [h1, Nat.add_mod]
          have : (m % s.capacity) = m := Nat.mod_eq_of_lt hm_cap
          simp [this, Nat.add_mod]
        simp [hmod]
  rw [hEq, hEff]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons o ops ih =>
    cases o with
    | enqueue x =>
      by_cases hOk : (step s (.enqueue x)).1 ≠ .rejected
      · have hEnq := req_enqueue_contents s x hOk
        have hOkEq : (step s (.enqueue x)).1 = .ok := by have hEff := req_enqueue_effects s x hOk; rw [hEff]
        have hRun : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, (step s (.enqueue x)).1) :: (run step (step s (.enqueue x)).2 ops).1, (run step (step s (.enqueue x)).2 ops).2) := by simp [run]
        have hin : inflowOf (Op.enqueue x, (step s (.enqueue x)).1) = [x] := by simp [inflowOf, hOkEq]
        have hout : outflowOf (Op.enqueue x, (step s (.enqueue x)).1) = [] := by simp [outflowOf, hOkEq]
        have ih' := ih (step s (Op.enqueue x)).2
        rw [hRun]
        have hIn : inflow ((Op.enqueue x, (step s (.enqueue x)).1) :: (run step (step s (.enqueue x)).2 ops).1) = [x] ++ inflow (run step (step s (.enqueue x)).2 ops).1 := by simp [inflow, hin]
        have hOut : outflow ((Op.enqueue x, (step s (.enqueue x)).1) :: (run step (step s (.enqueue x)).2 ops).1) = outflow (run step (step s (.enqueue x)).2 ops).1 := by simp [outflow, hout]
        rw [hIn, hOut]
        calc contents s ++ ([x] ++ inflow (run step (step s (.enqueue x)).2 ops).1)
            = (contents s ++ [x]) ++ inflow (run step (step s (.enqueue x)).2 ops).1 := by rw [List.append_assoc]
          _ = contents (step s (.enqueue x)).2 ++ inflow (run step (step s (.enqueue x)).2 ops).1 := by rw [← hEnq]
          _ = outflow (run step (step s (.enqueue x)).2 ops).1 ++ contents (run step (step s (.enqueue x)).2 ops).2 := ih'
      · have hNotOk : (step s (.enqueue x)).1 = .rejected := by
          have h : (step s (.enqueue x)).1 = .rejected ∨ (step s (.enqueue x)).1 = .ok ∨ ∃ y, (step s (.enqueue x)).1 = .got y := by cases hc : (step s (.enqueue x)).1 <;> simp [hc]
          rcases h with h | h | h
          · exact h
          · exfalso; exact hOk (by rw [h]; simp)
          · obtain ⟨y, hy⟩ := h; exfalso; exact hOk (by rw [hy]; simp)
        have hInv : ¬ Valid s (.enqueue x) := by intro hV; have := req_valid_succeeds s (.enqueue x) hV; rw [hNotOk] at this; simp at this
        have hNoop : step s (.enqueue x) = (.rejected, s) := req_invalid_noop s (.enqueue x) hInv
        have hRun : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, .rejected) :: (run step s ops).1, (run step s ops).2) := by simp [run, hNoop, hNotOk]
        rw [hRun]
        simp only [inflow, inflowOf, outflow, outflowOf, List.flatMap_cons]
        simp; exact ih s
    | dequeue =>
      by_cases hOk : (step s .dequeue).1 ≠ .rejected
      · obtain ⟨x, hxOut, hxCont⟩ := req_dequeue_contents s hOk
        have hRun : run step s (Op.dequeue :: ops) = ((Op.dequeue, (step s .dequeue).1) :: (run step (step s .dequeue).2 ops).1, (run step (step s .dequeue).2 ops).2) := by simp [run]
        have hin : inflowOf (Op.dequeue, (step s .dequeue).1) = [] := by simp [inflowOf, hxOut]
        have hout : outflowOf (Op.dequeue, (step s .dequeue).1) = [x] := by simp [outflowOf, hxOut]
        have ih' := ih (step s .dequeue).2
        rw [hRun]
        have hIn : inflow ((Op.dequeue, (step s .dequeue).1) :: (run step (step s .dequeue).2 ops).1) = inflow (run step (step s .dequeue).2 ops).1 := by simp [inflow, hin]
        have hOut : outflow ((Op.dequeue, (step s .dequeue).1) :: (run step (step s .dequeue).2 ops).1) = [x] ++ outflow (run step (step s .dequeue).2 ops).1 := by simp [outflow, hout]
        rw [hIn, hOut]
        calc contents s ++ inflow (run step (step s .dequeue).2 ops).1
            = (x :: contents (step s .dequeue).2) ++ inflow (run step (step s .dequeue).2 ops).1 := by rw [hxCont]
          _ = [x] ++ (contents (step s .dequeue).2 ++ inflow (run step (step s .dequeue).2 ops).1) := by simp
          _ = [x] ++ (outflow (run step (step s .dequeue).2 ops).1 ++ contents (run step (step s .dequeue).2 ops).2) := by rw [ih']
          _ = ([x] ++ outflow (run step (step s .dequeue).2 ops).1) ++ contents (run step (step s .dequeue).2 ops).2 := by rw [List.append_assoc]
      · have hNotOk : (step s .dequeue).1 = .rejected := by
          have h : (step s .dequeue).1 = .rejected ∨ (step s .dequeue).1 = .ok ∨ ∃ y, (step s .dequeue).1 = .got y := by cases hc : (step s .dequeue).1 <;> simp [hc]
          rcases h with h | h | h
          · exact h
          · exfalso; exact hOk (by rw [h]; simp)
          · obtain ⟨y, hy⟩ := h; exfalso; exact hOk (by rw [hy]; simp)
        have hInv : ¬ Valid s .dequeue := by intro hV; have := req_valid_succeeds s .dequeue hV; rw [hNotOk] at this; simp at this
        have hNoop : step s .dequeue = (.rejected, s) := req_invalid_noop s .dequeue hInv
        have hRun : run step s (Op.dequeue :: ops) = ((Op.dequeue, .rejected) :: (run step s ops).1, (run step s ops).2) := by simp [run, hNoop, hNotOk]
        rw [hRun]
        simp only [inflow, inflowOf, outflow, outflowOf, List.flatMap_cons]
        simp; exact ih s

end RingBuffer
