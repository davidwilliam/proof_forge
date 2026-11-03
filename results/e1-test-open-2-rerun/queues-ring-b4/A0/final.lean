import RingBuffer.Spec

namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hv
  cases op with
  | enqueue x =>
    obtain ⟨⟨hcp, hhp, _⟩, hlt⟩ := hv
    unfold step
    have hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := ⟨hcp, hhp, hlt⟩
    simp [hc]
  | dequeue =>
    obtain ⟨⟨hcp, hhp, hle⟩, hpos⟩ := hv
    unfold step
    have hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := ⟨hcp, hhp, hle, hpos⟩
    simp [hc]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hn
  cases op with
  | enqueue x =>
    unfold step
    have hc_false : ¬(0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro hc; exact hn ⟨⟨hc.1, hc.2.1, Nat.le_of_lt hc.2.2⟩, hc.2.2⟩
    simp [hc_false]
  | dequeue =>
    unfold step
    have hc_false : ¬(0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hc; exact hn ⟨⟨hc.1, hc.2.1, hc.2.2.1⟩, hc.2.2.2⟩
    simp [hc_false]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hwf
  obtain ⟨hcp, hhp, hle⟩ := hwf
  cases op with
  | enqueue x =>
    unfold step
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · simp [hc]
      obtain ⟨_, _, hlt⟩ := hc
      exact ⟨hcp, hhp, by omega⟩
    · simp [hc]
      exact ⟨hcp, hhp, hle⟩
  | dequeue =>
    unfold step
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · simp [hc]
      exact ⟨hcp, Nat.mod_lt _ hcp, by omega⟩
    · simp [hc]
      exact ⟨hcp, hhp, hle⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · unfold step; simp [hc]
  · have hstep : step s (Op.enqueue x) = (.rejected, s) := by unfold step; simp [hc]
    rw [hstep] at h; contradiction

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · unfold step; simp [hc]
  · have hstep : step s Op.dequeue = (.rejected, s) := by unfold step; simp [hc]
    rw [hstep] at h; contradiction

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x h
  have hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases hc' : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact hc'
    · have hstep : step s (Op.enqueue x) = (.rejected, s) := by unfold step; simp [hc']
      rw [hstep] at h; contradiction
  have heff := req_enqueue_effects (s:=s) (x:=x) h
  obtain ⟨hcp, _hhp, _hlt⟩ := hc
  rw [heff]
  unfold contents slot; simp only
  have hrange : List.range (s.count + 1) = List.range s.count ++ [s.count] := by
    simp [List.range_succ]
  rw [hrange, List.map_append]
  have hprefix : List.map (fun i => if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)) (List.range s.count)
      = List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count) := by
    apply List.map_congr_left; intro i hi
    have hneq : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := by
      intro heq
      have hi_lt : i < s.count := List.mem_range.mp hi
      have hk_lt : s.count - i < s.capacity := by omega
      have h_add : s.head + s.count = s.head + i + (s.count - i) := by omega
      have hmod_eq2 : (s.head + i + (s.count - i)) % s.capacity = (s.head + i) % s.capacity := by
        rw [← h_add, heq]
      have hmod_add : (s.head + i + (s.count - i)) % s.capacity = ((s.head + i) % s.capacity + (s.count - i)) % s.capacity := by
        have h1 : (s.head + i + (s.count - i)) % s.capacity = ((s.head + i) % s.capacity + (s.count - i) % s.capacity) % s.capacity := by
          rw [Nat.add_mod]
        rw [h1, Nat.mod_eq_of_lt hk_lt]
      have h1 : ((s.head + i) % s.capacity + (s.count - i)) % s.capacity = (s.head + i) % s.capacity := by
        rw [← hmod_add]; exact hmod_eq2
      by_cases hlt2 : (s.head + i) % s.capacity + (s.count - i) < s.capacity
      · have hmod2 : ((s.head + i) % s.capacity + (s.count - i)) % s.capacity = (s.head + i) % s.capacity + (s.count - i) := Nat.mod_eq_of_lt hlt2
        rw [hmod2] at h1; omega
      · have hsub_lt : (s.head + i) % s.capacity + (s.count - i) - s.capacity < s.capacity := by omega
        have hmod3 : ((s.head + i) % s.capacity + (s.count - i)) % s.capacity = (s.head + i) % s.capacity + (s.count - i) - s.capacity := by
          have h_eq : (s.head + i) % s.capacity + (s.count - i) = s.capacity + ((s.head + i) % s.capacity + (s.count - i) - s.capacity) := by omega
          calc ((s.head + i) % s.capacity + (s.count - i)) % s.capacity
              = (s.capacity + ((s.head + i) % s.capacity + (s.count - i) - s.capacity)) % s.capacity := by rw [← h_eq]
            _ = ((s.head + i) % s.capacity + (s.count - i) - s.capacity) % s.capacity := by rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
            _ = (s.head + i) % s.capacity + (s.count - i) - s.capacity := Nat.mod_eq_of_lt hsub_lt
        rw [hmod3] at h1; omega
    simp [hneq]
  have hlast : List.map (fun i => if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)) [s.count] = [x] := by simp
  rw [hprefix, hlast]

theorem req_dequeue_contents : DequeueContents step := by
  intro s h
  have hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
    by_cases hc' : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · exact hc'
    · have hstep : step s Op.dequeue = (.rejected, s) := by unfold step; simp [hc']
      rw [hstep] at h; contradiction
  have heff := req_dequeue_effects (s:=s) h
  obtain ⟨hcp, hhp, _hle, _hpos⟩ := hc
  rw [heff]
  refine ⟨s.buf s.head, rfl, ?_⟩
  unfold contents slot; simp only
  have hcount_eq : s.count = s.count - 1 + 1 := by omega
  have h0 : (s.head + 0) % s.capacity = s.head := Nat.mod_eq_of_lt hhp
  have hcount_rw : List.range s.count = List.range (s.count - 1 + 1) := by rw [← hcount_eq]
  have h_succ_eq : s.count - 1 + 1 = Nat.succ (s.count - 1) := by omega
  have lhs_eq : List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range (s.count - 1 + 1))
      = s.buf s.head :: List.map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) (List.range (s.count - 1)) := by
    conv => lhs; rw [h_succ_eq]
    have h_range : List.range (Nat.succ (s.count - 1)) = 0 :: List.map (fun x => x + 1) (List.range (s.count - 1)) := by simp
    rw [h_range, List.map_cons]
    -- normalize head modulo
    have hhead_mod : s.head % s.capacity = s.head := Nat.mod_eq_of_lt hhp
    simp [h0, hhead_mod]
  rw [hcount_rw, lhs_eq]
  congr 1
  apply List.map_congr_left; intro i hi
  have hic : i < s.capacity := by omega
  show s.buf ((s.head + (i + 1)) % s.capacity) = s.buf (((s.head + 1) % s.capacity + i) % s.capacity)
  have h1 : ((s.head + 1) % s.capacity + i) % s.capacity = (s.head + 1 + i) % s.capacity := by
    calc ((s.head + 1) % s.capacity + i) % s.capacity
        = ((s.head + 1) % s.capacity + i % s.capacity) % s.capacity := by rw [Nat.mod_eq_of_lt hic]
      _ = ((s.head + 1) + i) % s.capacity := by rw [← Nat.add_mod]
  rw [h1]
  have : s.head + 1 + i = s.head + (i + 1) := by omega
  rw [this]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | enqueue x =>
      by_cases h : (step s (.enqueue x)).1 ≠ .rejected
      · have heff := req_enqueue_effects (s:=s) (x:=x) h
        have hcont := req_enqueue_contents (s:=s) (x:=x) h
        have ih_succ := ih (step s (.enqueue x)).2
        have hrun : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, .ok) :: (run step (step s (.enqueue x)).2 ops).1, (run step (step s (.enqueue x)).2 ops).2) := by simp [run, heff]
        rw [hrun]
        simp only [inflow, outflow, List.flatMap_cons, inflowOf, outflowOf]
        calc contents s ++ ([x] ++ inflow (run step (step s (.enqueue x)).2 ops).1)
            = (contents s ++ [x]) ++ inflow (run step (step s (.enqueue x)).2 ops).1 := by rw [List.append_assoc]
          _ = contents (step s (.enqueue x)).2 ++ inflow (run step (step s (.enqueue x)).2 ops).1 := by rw [hcont]
          _ = outflow (run step (step s (.enqueue x)).2 ops).1 ++ contents (run step (step s (.enqueue x)).2 ops).2 := ih_succ
      · have h_not_valid : ¬ Valid s (.enqueue x) := by intro hv; exact h (req_valid_succeeds _ _ hv)
        have hnoop := req_invalid_noop (s:=s) (op:=.enqueue x) h_not_valid
        have hrun : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, .rejected) :: (run step s ops).1, (run step s ops).2) := by simp [run, hnoop]
        rw [hrun]
        simp only [inflow, outflow, List.flatMap_cons, inflowOf, outflowOf]
        exact ih s
    | dequeue =>
      by_cases h : (step s .dequeue).1 ≠ .rejected
      · have heff := req_dequeue_effects (s:=s) h
        have hpair := req_dequeue_contents (s:=s) h
        obtain ⟨y, hy_out, hy_cont⟩ := hpair
        have hy_eq : y = s.buf s.head := by rw [heff] at hy_out; simpa using hy_out.symm
        subst hy_eq
        have ih_succ := ih (step s .dequeue).2
        have hrun : run step s (Op.dequeue :: ops) = ((Op.dequeue, .got (s.buf s.head)) :: (run step (step s .dequeue).2 ops).1, (run step (step s .dequeue).2 ops).2) := by simp [run, heff]
        rw [hrun]
        simp only [inflow, outflow, List.flatMap_cons, inflowOf, outflowOf]
        calc contents s ++ inflow (run step (step s .dequeue).2 ops).1
            = (s.buf s.head :: contents (step s .dequeue).2) ++ inflow (run step (step s .dequeue).2 ops).1 := by rw [hy_cont]
          _ = s.buf s.head :: (contents (step s .dequeue).2 ++ inflow (run step (step s .dequeue).2 ops).1) := by simp
          _ = s.buf s.head :: (outflow (run step (step s .dequeue).2 ops).1 ++ contents (run step (step s .dequeue).2 ops).2) := by rw [ih_succ]
          _ = (s.buf s.head :: outflow (run step (step s .dequeue).2 ops).1) ++ contents (run step (step s .dequeue).2 ops).2 := by simp
      · have h_not_valid : ¬ Valid s .dequeue := by intro hv; exact h (req_valid_succeeds _ _ hv)
        have hnoop := req_invalid_noop (s:=s) (op:=.dequeue) h_not_valid
        have hrun : run step s (Op.dequeue :: ops) = ((Op.dequeue, .rejected) :: (run step s ops).1, (run step s ops).2) := by simp [run, hnoop]
        rw [hrun]
        simp only [inflow, outflow, List.flatMap_cons, inflowOf, outflowOf]
        exact ih s

end RingBuffer
