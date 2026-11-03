import RingBuffer.Spec
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem mod_two_aux (a n : Nat) (_h1 : 0 < n) (h2 : a < 2 * n) : a % n = if a < n then a else a - n := by
  by_cases ha : a < n
  · simp [ha, Nat.mod_eq_of_lt ha]
  · have hsub : a - n < n := by omega
    have : a % n = (a - n + n) % n := by
      have : (a - n) + n = a := by omega
      rw [this]
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hsub]
    simp [ha]

theorem slot_ne_aux (s : State) (i : Nat) (hi : i < s.count) (hv : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := by
  have hpos := hv.1
  have hAi : s.head + i < 2 * s.capacity := by omega
  have hAc : s.head + s.count < 2 * s.capacity := by omega
  rw [mod_two_aux _ _ hpos hAi, mod_two_aux _ _ hpos hAc]
  intro heq
  by_cases hi_lt : s.head + i < s.capacity <;> by_cases hc_lt : s.head + s.count < s.capacity <;> simp [hi_lt, hc_lt] at heq <;> omega

theorem slot_shift_aux (s : State) (i : Nat) : ((s.head + 1) % s.capacity + i) % s.capacity = (s.head + 1 + i) % s.capacity := by
  have h1 : ((s.head + 1) % s.capacity + i) % s.capacity = (((s.head + 1) % s.capacity % s.capacity + i % s.capacity) % s.capacity) := by rw [← Nat.add_mod]
  have h2 : (((s.head + 1) % s.capacity % s.capacity + i % s.capacity) % s.capacity) = (((s.head + 1) % s.capacity + i % s.capacity) % s.capacity) := by rw [Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
  have h3 : (((s.head + 1) % s.capacity + i % s.capacity) % s.capacity) = (s.head + 1 + i) % s.capacity := by rw [← Nat.add_mod]
  rw [h1, h2, h3]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hv
  cases op with
  | enqueue x =>
    simp [Valid] at hv
    obtain ⟨hw, hlt⟩ := hv
    show (step s (Op.enqueue x)).1 ≠ .rejected
    simp [step, hw.1, hw.2.1, hlt]
  | dequeue =>
    simp [Valid] at hv
    obtain ⟨hw, hlt⟩ := hv
    show (step s Op.dequeue).1 ≠ .rejected
    simp [step, hw.1, hw.2.1, hw.2.2, hlt]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hv
  cases op with
  | enqueue x =>
    have hc : ¬(0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro h; apply hv; exact ⟨⟨h.1, h.2.1, Nat.le_of_lt h.2.2⟩, h.2.2⟩
    show step s (Op.enqueue x) = (.rejected, s)
    simp [step, hc]
  | dequeue =>
    have hc : ¬(0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro h; apply hv; exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩
    show step s Op.dequeue = (.rejected, s)
    simp [step, hc]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hw
  cases op with
  | enqueue x =>
    show WellFormed (step s (Op.enqueue x)).2
    simp only [step]
    split
    · simp [WellFormed] at hw ⊢; omega
    · exact hw
  | dequeue =>
    show WellFormed (step s Op.dequeue).2
    simp only [step]
    split
    · simp [WellFormed] at hw ⊢; constructor; exact hw.1; constructor; exact Nat.mod_lt _ hw.1; omega
    · exact hw

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  have hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases hc' : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact hc'
    · exfalso; apply h; simp [step, hc']
  -- step reduces to ok-branch and slot definition matches
  have hstep : step s (Op.enqueue x) = (Outcome.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by simp [step, hc]
  have hslot : (s.head + s.count) % s.capacity = slot s s.count := rfl
  rw [hslot] at hstep
  exact hstep

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  have hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
    by_cases hc' : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · exact hc'
    · exfalso; apply h; simp [step, hc']
  simp [step, hc]

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x h
  have hv : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases hc' : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact hc'
    · exfalso; apply h; simp [step, hc']
  have he := req_enqueue_effects (s:=s) (x:=x) h
  rw [he]
  unfold contents slot; simp only
  have key : ∀ n (s' : State), s'.count = n → 0 < s'.capacity ∧ s'.head < s'.capacity ∧ n < s'.capacity →
    List.map (fun i => if (s'.head + i) % s'.capacity = (s'.head + n) % s'.capacity then x else s'.buf ((s'.head + i) % s'.capacity)) (List.range (n+1))
    = List.map (fun i => s'.buf ((s'.head + i) % s'.capacity)) (List.range n) ++ [x] := by
    intro n s' hn1 hv'
    have hr : List.range (n+1) = List.range n ++ [n] := by simp [List.range_succ]
    rw [hr, List.map_append]
    have h1m : List.map (fun i => if (s'.head + i) % s'.capacity = (s'.head + n) % s'.capacity then x else s'.buf ((s'.head + i) % s'.capacity)) [n] = [x] := by simp
    rw [h1m]
    have hmap : List.map (fun i => if (s'.head + i) % s'.capacity = (s'.head + n) % s'.capacity then x else s'.buf ((s'.head + i) % s'.capacity)) (List.range n)
      = List.map (fun i => s'.buf ((s'.head + i) % s'.capacity)) (List.range n) := by
      apply List.map_congr_left; intro i hi; have hi2 : i < n := by simp at hi; omega
      have hne : (s'.head + i) % s'.capacity ≠ (s'.head + n) % s'.capacity := by have := slot_ne_aux (s:={s' with count := n}) i hi2 (by simpa using hv'); simpa using this
      simp [hne]
    rw [hmap]
  exact key s.count s rfl hv

theorem req_dequeue_contents : DequeueContents step := by
  intro s h
  have hv : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
    by_cases hc' : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · exact hc'
    · exfalso; apply h; simp [step, hc']
  have he := req_dequeue_effects (s:=s) h
  rw [he]
  refine ⟨s.buf s.head, rfl, ?_⟩
  unfold contents slot; simp only
  have hhead := hv.2.1
  obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
  rw [hn]
  have hshift_all : ∀ i, s.buf (((s.head + 1) % s.capacity + i) % s.capacity) = s.buf ((s.head + (i + 1)) % s.capacity) := by
    intro i
    have h1 := slot_shift_aux s i
    have h3 : s.head + 1 + i = s.head + (i + 1) := by omega
    rw [h3] at h1
    rw [h1]
  have lhs_eq : List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range (n + 1))
      = s.buf ((s.head + 0) % s.capacity) :: List.map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) (List.range n) := by
    rw [List.range_succ_eq_map]; simp
  have h0eq : s.buf ((s.head + 0) % s.capacity) = s.buf s.head := by simp [Nat.mod_eq_of_lt hhead]
  rw [lhs_eq, h0eq]
  have rhs_eq : List.map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) (List.range n)
      = List.map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) (List.range n) := by
    apply List.map_congr_left; intro i _; exact hshift_all i
  have hcount_eq : n + 1 - 1 = n := by omega
  change s.buf s.head :: List.map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) (List.range n) =
    s.buf s.head :: List.map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) (List.range (n + 1 - 1))
  rw [hcount_eq, rhs_eq]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    have hrun1 : run step s (op :: ops) = ((op, (step s op).1) :: (run step (step s op).2 ops).1, (run step (step s op).2 ops).2) := by simp [run]
    simp only [hrun1, inflow, outflow, List.flatMap_cons]
    by_cases hv : Valid s op
    · cases op with
      | enqueue x =>
        have hnr : (step s (Op.enqueue x)).1 ≠ .rejected := by intro hrej; have := req_valid_succeeds (s:=s) (op:=Op.enqueue x) hv; contradiction
        have hec := req_enqueue_contents (s:=s) (x:=x) hnr
        have ih' := ih (step s (Op.enqueue x)).2
        have hin : inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [x] := by have he := req_enqueue_effects (s:=s) (x:=x) hnr; rw [he]; simp [inflowOf]
        have hout : outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [] := by have he := req_enqueue_effects (s:=s) (x:=x) hnr; rw [he]; simp [outflowOf]
        simp only [hin, hout, List.nil_append]
        calc contents s ++ ([x] ++ inflow (run step (step s (Op.enqueue x)).2 ops).1)
            = (contents s ++ [x]) ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by rw [List.append_assoc]
          _ = contents (step s (Op.enqueue x)).2 ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by rw [hec]
          _ = outflow (run step (step s (Op.enqueue x)).2 ops).1 ++ contents (run step (step s (Op.enqueue x)).2 ops).2 := ih'
      | dequeue =>
        have hnr : (step s Op.dequeue).1 ≠ .rejected := by intro hrej; have := req_valid_succeeds (s:=s) (op:=Op.dequeue) hv; contradiction
        obtain ⟨y, hy1, hy2⟩ := req_dequeue_contents (s:=s) hnr
        have hout : outflowOf (Op.dequeue, (step s Op.dequeue).1) = [y] := by simp [outflowOf, hy1]
        have hin : inflowOf (Op.dequeue, (step s Op.dequeue).1) = [] := by simp [inflowOf]
        simp only [hin, hout, List.nil_append]
        have ih' := ih (step s Op.dequeue).2
        calc contents s ++ inflow (run step (step s Op.dequeue).2 ops).1
            = (y :: contents (step s Op.dequeue).2) ++ inflow (run step (step s Op.dequeue).2 ops).1 := by rw [hy2]
          _ = y :: (contents (step s Op.dequeue).2 ++ inflow (run step (step s Op.dequeue).2 ops).1) := rfl
          _ = y :: (outflow (run step (step s Op.dequeue).2 ops).1 ++ contents (run step (step s Op.dequeue).2 ops).2) := by rw [ih']
          _ = ([y] ++ outflow (run step (step s Op.dequeue).2 ops).1) ++ contents (run step (step s Op.dequeue).2 ops).2 := rfl
    · have hnoop := req_invalid_noop (s:=s) (op:=op) hv
      have h1 : (step s op).1 = .rejected := by rw [hnoop]
      have h2 : (step s op).2 = s := by rw [hnoop]
      have hin : inflowOf (op, (step s op).1) = [] := by rw [h1]; cases op <;> simp [inflowOf]
      have hout : outflowOf (op, (step s op).1) = [] := by rw [h1]; simp [outflowOf]
      simp only [hin, hout, h2, List.nil_append]; exact ih s

end RingBuffer
