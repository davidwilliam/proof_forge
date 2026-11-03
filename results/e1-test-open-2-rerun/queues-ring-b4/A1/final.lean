import RingBuffer.Spec
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      let tail := (s.head + s.count) % s.capacity
      (.ok, { s with buf := fun i => if i = tail then x else s.buf i, count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem inflow_cons2 (p : Op × Outcome) (t : List (Op × Outcome)) :
  inflow (p :: t) = inflowOf p ++ inflow t := by
  unfold inflow
  simp

theorem outflow_cons2 (p : Op × Outcome) (t : List (Op × Outcome)) :
  outflow (p :: t) = outflowOf p ++ outflow t := by
  unfold outflow
  simp

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hValid
  cases op with
  | enqueue x =>
    have h : Valid s (Op.enqueue x) := hValid
    unfold Valid at h
    obtain ⟨⟨hcap, hhead, hcount_le⟩, hcount_lt⟩ := h
    unfold step
    simp [hcap, hhead, hcount_lt]
  | dequeue =>
    have h : Valid s Op.dequeue := hValid
    unfold Valid at h
    obtain ⟨⟨hcap, hhead, hcount_le⟩, hpos⟩ := h
    unfold step
    simp [hcap, hhead, hcount_le, hpos]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInvalid
  cases op with
  | enqueue x =>
    have hGuard : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro ⟨hcap, hhead, hlt⟩
      apply hInvalid
      show Valid s (Op.enqueue x)
      unfold Valid
      constructor
      · exact ⟨hcap, hhead, Nat.le_of_lt hlt⟩
      · exact hlt
    unfold step
    simp [hGuard]
  | dequeue =>
    have hGuard : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro ⟨hcap, hhead, hle, hpos⟩
      apply hInvalid
      show Valid s Op.dequeue
      unfold Valid
      exact ⟨⟨hcap, hhead, hle⟩, hpos⟩
    unfold step
    simp [hGuard]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hWf
  obtain ⟨hcap, hhead, hcount_le⟩ := hWf
  cases op with
  | enqueue x =>
    unfold step
    by_cases hGuard : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · simp only [if_pos hGuard]
      refine ⟨?_, ?_, ?_⟩
      · simp; exact hcap
      · simp; exact hhead
      · simp; omega
    · simp only [if_neg hGuard]
      exact ⟨hcap, hhead, hcount_le⟩
  | dequeue =>
    unfold step
    by_cases hGuard : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · simp only [if_pos hGuard]
      refine ⟨?_, ?_, ?_⟩
      · simp; exact hcap
      · simp; exact Nat.mod_lt _ hcap
      · simp; omega
    · simp only [if_neg hGuard]
      exact ⟨hcap, hhead, hcount_le⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  -- split on guard
  by_cases hGuard : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · simp [hGuard]
    -- need to show slot equality: already definitionally same
    rfl
  · simp [hGuard] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  unfold step at h ⊢
  by_cases hGuard : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · simp [hGuard]
  · simp [hGuard] at h

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x h
  unfold step at h ⊢
  by_cases hGuard : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · simp only [if_pos hGuard] at h ⊢
    have hcap : 0 < s.capacity := hGuard.1
    have hhead : s.head < s.capacity := hGuard.2.1
    have hcount_lt : s.count < s.capacity := hGuard.2.2
    unfold contents slot
    simp only
    have h_range : List.range (s.count + 1) = List.range s.count ++ [s.count] := by
      rw [List.range_succ]
    have h1 : List.map (fun i => if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)) (List.range s.count) = List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count) := by
      apply List.map_congr_left
      intro i hi
      have hi_mem : i < s.count := List.mem_range.mp hi
      have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := by
        intro heq
        have h1_lt : s.head + i < 2 * s.capacity := by omega
        have h2_lt : s.head + s.count < 2 * s.capacity := by omega
        by_cases h1c : s.head + i < s.capacity
        · by_cases h2c : s.head + s.count < s.capacity
          · rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_of_lt h2c] at heq; omega
          · have hle : s.capacity ≤ s.head + s.count := by omega
            have hlt2 : s.head + s.count - s.capacity < s.capacity := by omega
            have heq2 : s.head + s.count = s.head + s.count - s.capacity + s.capacity := by omega
            have h2mod : (s.head + s.count) % s.capacity = s.head + s.count - s.capacity := by
              have htmp : (s.head + s.count - s.capacity + s.capacity) % s.capacity = (s.head + s.count - s.capacity) % s.capacity := Nat.add_mod_right (s.head + s.count - s.capacity) s.capacity
              rw [← heq2] at htmp; exact htmp.trans (Nat.mod_eq_of_lt hlt2)
            rw [Nat.mod_eq_of_lt h1c, h2mod] at heq; omega
        · by_cases h2c : s.head + s.count < s.capacity
          · have hle : s.capacity ≤ s.head + i := by omega
            have hlt2 : s.head + i - s.capacity < s.capacity := by omega
            have heq2 : s.head + i = s.head + i - s.capacity + s.capacity := by omega
            have h1mod : (s.head + i) % s.capacity = s.head + i - s.capacity := by
              have htmp : (s.head + i - s.capacity + s.capacity) % s.capacity = (s.head + i - s.capacity) % s.capacity := Nat.add_mod_right (s.head + i - s.capacity) s.capacity
              rw [← heq2] at htmp; exact htmp.trans (Nat.mod_eq_of_lt hlt2)
            rw [h1mod, Nat.mod_eq_of_lt h2c] at heq; omega
          · have hle1 : s.capacity ≤ s.head + i := by omega
            have hlt21 : s.head + i - s.capacity < s.capacity := by omega
            have heq21 : s.head + i = s.head + i - s.capacity + s.capacity := by omega
            have h1mod : (s.head + i) % s.capacity = s.head + i - s.capacity := by
              have htmp : (s.head + i - s.capacity + s.capacity) % s.capacity = (s.head + i - s.capacity) % s.capacity := Nat.add_mod_right (s.head + i - s.capacity) s.capacity
              rw [← heq21] at htmp; exact htmp.trans (Nat.mod_eq_of_lt hlt21)
            have hle2 : s.capacity ≤ s.head + s.count := by omega
            have hlt22 : s.head + s.count - s.capacity < s.capacity := by omega
            have heq22 : s.head + s.count = s.head + s.count - s.capacity + s.capacity := by omega
            have h2mod : (s.head + s.count) % s.capacity = s.head + s.count - s.capacity := by
              have htmp : (s.head + s.count - s.capacity + s.capacity) % s.capacity = (s.head + s.count - s.capacity) % s.capacity := Nat.add_mod_right (s.head + s.count - s.capacity) s.capacity
              rw [← heq22] at htmp; exact htmp.trans (Nat.mod_eq_of_lt hlt22)
            rw [h1mod, h2mod] at heq; omega
      simp [hne]
    rw [h_range, List.map_append]
    rw [h1]
    simp
  · simp only [if_neg hGuard] at h
    exact absurd rfl h

theorem req_dequeue_contents : DequeueContents step := by
  intro s h
  unfold step at h ⊢
  by_cases hGuard : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · simp only [if_pos hGuard] at h ⊢
    refine ⟨s.buf s.head, rfl, ?_⟩
    unfold contents slot
    simp only
    have hhead : s.head < s.capacity := hGuard.2.1
    have h_step : ∀ i, ((s.head + 1) % s.capacity + i) % s.capacity = (s.head + (i + 1)) % s.capacity := by
      intro i
      rw [show s.head + (i+1) = s.head + 1 + i from by omega]
      rw [Nat.mod_add_mod]
    have h_range_gen : ∀ n, List.range (n + 1) = 0 :: List.map (· + 1) (List.range n) := by
      intro n
      induction n with
      | zero => rfl
      | succ k ih =>
        calc List.range (k + 1 + 1) = List.range (k+1) ++ [k+1] := by rw [List.range_succ]
          _ = (0 :: List.map (· + 1) (List.range k)) ++ [k+1] := by rw [ih]
          _ = 0 :: (List.map (· + 1) (List.range k) ++ [k+1]) := rfl
          _ = 0 :: List.map (· + 1) (List.range (k+1)) := by simp [List.range_succ]
    have h_range_eq : List.range s.count = 0 :: List.map (· + 1) (List.range (s.count - 1)) := by
      cases hc : s.count with
      | zero => omega
      | succ n =>
        show List.range (n+1) = 0 :: List.map (·+1) (List.range ((n+1)-1))
        simp only [Nat.add_sub_cancel]
        exact h_range_gen n
    have h_contents_s : (List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity)) =
        s.buf ((s.head + 0) % s.capacity) :: (List.range (s.count - 1)).map (fun i => s.buf ((s.head + (i+1)) % s.capacity)) := by
      rw [h_range_eq]
      simp only [List.map_cons, List.map_map]
      rfl
    simp only [Nat.add_zero, Nat.mod_eq_of_lt hhead] at h_contents_s
    have h_contents_next_eq : (List.range (s.count - 1)).map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) =
        (List.range (s.count - 1)).map (fun i => s.buf ((s.head + (i+1)) % s.capacity)) := by
      apply List.map_congr_left
      intro i _
      rw [h_step]
    show (List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity)) =
        s.buf s.head :: (List.range (s.count - 1)).map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity))
    rw [h_contents_s, h_contents_next_eq]
  · simp only [if_neg hGuard] at h
    simp at h

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    have hSingle : contents s ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
      cases op with
      | enqueue x =>
        by_cases hGuard : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
        · have hNotRej : (step s (Op.enqueue x)).1 ≠ .rejected := by unfold step; simp [hGuard]
          have hCont := req_enqueue_contents s x hNotRej
          have hOk : (step s (Op.enqueue x)).1 = .ok := by have hE := req_enqueue_effects s x hNotRej; rw [hE]
          have hIn : inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [x] := by simp [inflowOf, hOk]
          have hOut : outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [] := by simp [outflowOf, hOk]
          rw [hIn, hOut, hCont]; simp
        · have hRej : step s (Op.enqueue x) = (.rejected, s) := by unfold step; simp [hGuard]
          have hIn : inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [] := by rw [hRej]; rfl
          have hOut : outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [] := by rw [hRej]; rfl
          rw [hIn, hOut, hRej]; simp
      | dequeue =>
        by_cases hGuard : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
        · have hNotRej : (step s Op.dequeue).1 ≠ .rejected := by unfold step; simp [hGuard]
          obtain ⟨y, hy1, hy2⟩ := req_dequeue_contents s hNotRej
          have hGot : (step s Op.dequeue).1 = .got (s.buf s.head) := by have hE := req_dequeue_effects s hNotRej; rw [hE]
          -- hy1: .got y = .got (buf head) or vice versa? Let's handle both
          have hy1eq : y = s.buf s.head := by rw [hGot] at hy1; cases hy1; rfl
          rw [hy1eq] at hy2
          have hIn : inflowOf (Op.dequeue, (step s Op.dequeue).1) = [] := by simp [inflowOf, hGot]
          have hOut : outflowOf (Op.dequeue, (step s Op.dequeue).1) = [s.buf s.head] := by simp [outflowOf, hGot]
          rw [hIn, hOut, hy2]; simp
        · have hRej : step s Op.dequeue = (.rejected, s) := by unfold step; simp [hGuard]
          have hIn : inflowOf (Op.dequeue, (step s Op.dequeue).1) = [] := by rw [hRej]; rfl
          have hOut : outflowOf (Op.dequeue, (step s Op.dequeue).1) = [] := by rw [hRej]; rfl
          rw [hIn, hOut, hRej]; simp
    have ih' := ih (step s op).2
    have hRun1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by simp [run]
    have hRun2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by simp [run]
    rw [hRun1, hRun2]
    have hInflowCons : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := inflow_cons2 _ _
    have hOutflowCons : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := outflow_cons2 _ _
    rw [hInflowCons, hOutflowCons]
    calc contents s ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (contents s ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ contents (step s op).2) ++ inflow (run step (step s op).2 ops).1 := by rw [hSingle]
      _ = outflowOf (op, (step s op).1) ++ (contents (step s op).2 ++ inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ contents (run step (step s op).2 ops).2) := by rw [ih']
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ contents (run step (step s op).2 ops).2 := by rw [List.append_assoc]

end RingBuffer
