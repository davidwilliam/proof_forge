import RingBuffer.Spec
import ProofForgeFin
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

private theorem mod_add_eq_imp_mod_zero {a d cap : Nat} (hcap : 0 < cap) (h : (a + d) % cap = a % cap) : d % cap = 0 := by
  have h1 : (a + d) % cap = (a % cap + d % cap) % cap := by
    rw [Nat.add_mod]
  rw [h1] at h
  have ha_lt : a % cap < cap := Nat.mod_lt _ hcap
  have hd_lt : d % cap < cap := Nat.mod_lt _ hcap
  by_cases hd0 : d % cap = 0
  · exact hd0
  · exfalso
    have hsum_lt_or_ge : a % cap + d % cap < cap ∨ cap ≤ a % cap + d % cap := by omega
    cases hsum_lt_or_ge with
    | inl hlt =>
      have hmod : (a % cap + d % cap) % cap = a % cap + d % cap := Nat.mod_eq_of_lt hlt
      rw [hmod] at h
      omega
    | inr hge =>
      have hmod : (a % cap + d % cap) % cap = a % cap + d % cap - cap := by
        have h_lt : a % cap + d % cap - cap < cap := by omega
        have h_eq : a % cap + d % cap = (a % cap + d % cap - cap) + cap := by omega
        calc (a % cap + d % cap) % cap = ((a % cap + d % cap - cap) + cap) % cap := by rw [← h_eq]
          _ = (a % cap + d % cap - cap) % cap := by rw [Nat.add_mod_right]
          _ = a % cap + d % cap - cap := Nat.mod_eq_of_lt h_lt
      rw [hmod] at h
      omega

private theorem enqueue_neq {head cap i cnt : Nat} (hcap : 0 < cap) (hi : i < cnt) (hcnt : cnt < cap)
  : (head + i) % cap ≠ (head + cnt) % cap := by
  intro heq
  have hd_lt : cnt - i < cap := by omega
  have hsum : head + cnt = (head + i) + (cnt - i) := by omega
  have heq' : ((head + i) + (cnt - i)) % cap = (head + i) % cap := by rw [← hsum, heq]
  have hzero := mod_add_eq_imp_mod_zero hcap heq'
  have hmod_zero : (cnt - i) % cap = 0 := hzero
  have hmod_eq : (cnt - i) % cap = cnt - i := Nat.mod_eq_of_lt hd_lt
  rw [hmod_eq] at hmod_zero
  omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  unfold Valid at hV
  unfold step
  cases op with
  | enqueue x =>
    simp only
    have h1 : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      exact ⟨hV.1.1, hV.1.2.1, hV.2⟩
    simp [h1]
  | dequeue =>
    simp only
    have h1 : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      exact ⟨hV.1.1, hV.1.2.1, hV.1.2.2, hV.2⟩
    simp [h1]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv
  unfold Valid at hInv
  unfold step
  cases op with
  | enqueue x =>
    simp only
    -- Condition for enqueue in Valid is equivalent to implementation condition
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro h
      apply hInv
      refine ⟨⟨h.1, h.2.1, Nat.le_of_lt h.2.2⟩, h.2.2⟩
    simp [hcond]
  | dequeue =>
    simp only
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro h
      apply hInv
      exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩
    simp [hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hWF
  unfold step
  cases op with
  | enqueue x =>
    simp only
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · simp only [h, ↓reduceIte]
      simp [WellFormed] at hWF ⊢
      omega
    · simp [h]
      exact hWF
  | dequeue =>
    simp only
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · simp only [h, ↓reduceIte]
      simp [WellFormed] at hWF ⊢
      have hm : (s.head + 1) % s.capacity < s.capacity := Nat.mod_lt _ (by omega)
      omega
    · simp [h]
      exact hWF

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  simp only at h ⊢
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · simp only [if_pos hc] at h ⊢
    rfl
  · simp [if_neg hc] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  unfold step at h ⊢
  simp only at h ⊢
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · simp [hc] at h ⊢
  · simp [hc] at h

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x h
  unfold step at h ⊢
  simp only at h ⊢
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · simp only [if_pos hc] at h ⊢
    unfold contents slot
    have hrange : List.range (s.count + 1) = List.range s.count ++ [s.count] := by simp [List.range_succ]
    have hmap : (List.range (s.count + 1)).map (fun i => (fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + i) % s.capacity))
        = ((List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity))) ++ [x] := by
      rw [hrange, List.map_append]
      congr 1
      · apply List.map_congr_left
        intro i hi
        have hi_lt : i < s.count := by simp [List.mem_range] at hi; omega
        have hneq : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := enqueue_neq hc.1 hi_lt hc.2.2
        simp [hneq]
      · simp
    exact hmap
  · simp [if_neg hc] at h

theorem req_dequeue_contents : DequeueContents step := by
  intro s h
  unfold step at h ⊢
  simp only at h ⊢
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · have hpos : (if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then (Outcome.got (s.buf s.head), ({ capacity := s.capacity, buf := s.buf, head := (s.head + 1) % s.capacity, count := s.count - 1 } : State)) else (Outcome.rejected, s)) = (Outcome.got (s.buf s.head), ({ capacity := s.capacity, buf := s.buf, head := (s.head + 1) % s.capacity, count := s.count - 1 } : State)) := by simp [if_pos hc]
    rw [hpos] at h ⊢
    simp only at h
    have hhead : s.head < s.capacity := hc.2.1
    refine ⟨s.buf s.head, rfl, ?_⟩
    unfold contents slot
    simp only [hpos]
    have h_range0 : ∀ n, List.range (n+1) = 0 :: (List.range n).map (· + 1) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        calc List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by simp [List.range_succ]
          _ = (0 :: (List.range n).map (· + 1)) ++ [n + 1] := by rw [ih]
          _ = 0 :: ((List.range n).map (· + 1) ++ [n+1]) := by rfl
          _ = 0 :: ((List.range n ++ [n]).map (· + 1)) := by simp [List.map_append]
          _ = 0 :: (List.range (n+1)).map (· + 1) := by rw [← List.range_succ]
    have hcnt : s.count = (s.count - 1) + 1 := by omega
    conv => lhs; rw [hcnt]
    rw [show (List.range ((s.count - 1) + 1)).map (fun i => s.buf ((s.head + i) % s.capacity)) = s.buf ((s.head + 0) % s.capacity) :: (List.range (s.count - 1)).map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) from by
      have hr := h_range0 (s.count - 1)
      have h1 : (List.range ((s.count - 1) + 1)).map (fun i => s.buf ((s.head + i) % s.capacity)) = ((0 :: (List.range (s.count - 1)).map (· + 1)).map (fun i => s.buf ((s.head + i) % s.capacity))) := by rw [hr]
      rw [h1]
      simp]
    simp only [Nat.add_zero, Nat.mod_eq_of_lt hhead]
    have h_eq : ((List.range (s.count - 1)).map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)))
        = (List.range (s.count - 1)).map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) := by
      apply List.map_congr_left
      intro i hi
      have h1 : s.head + (i + 1) = (s.head + 1) + i := by omega
      have h2 : (s.head + (i + 1)) % s.capacity = ((s.head + 1 + i) % s.capacity) := by rw [h1]
      have h3 : ((s.head + 1 + i) % s.capacity) = (((s.head + 1) % s.capacity + i) % s.capacity) := by
        rw [Nat.mod_add_mod]
      rw [h2, h3]
    rw [h_eq]
  · have hneg : (if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then (Outcome.got (s.buf s.head), ({ capacity := s.capacity, buf := s.buf, head := (s.head + 1) % s.capacity, count := s.count - 1 } : State)) else (Outcome.rejected, s)) = (Outcome.rejected, s) := by simp [if_neg hc]
    rw [hneg] at h
    simp at h

theorem req_fifo : Fifo step := by
  unfold Fifo
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hrun : run step s (op :: ops) = ((op, (step s op).1) :: (run step (step s op).2 ops).1, (run step (step s op).2 ops).2) := by
      simp [run]
    have hinflow : inflow (run step s (op :: ops)).1 = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      rw [hrun]; simp [inflow]
    have houtflow : outflow (run step s (op :: ops)).1 = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      rw [hrun]; simp [outflow]
    have hfinal : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by rw [hrun]
    rw [hinflow, houtflow, hfinal]
    cases op with
    | enqueue x =>
      by_cases hrejected : (step s (Op.enqueue x)).1 = .rejected
      · have hstep : step s (Op.enqueue x) = (.rejected, s) := by
          unfold step at hrejected ⊢
          simp only at hrejected ⊢
          by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
          · simp [hc] at hrejected
          · simp [hc]
        rw [hstep]
        simp [inflowOf, outflowOf]
        exact ih s
      · have h_ok : (step s (Op.enqueue x)).1 = .ok := by
          cases hoc : (step s (Op.enqueue x)).1 with
          | rejected => exact absurd hoc hrejected
          | ok => rfl
          | got v => unfold step at hoc; simp only at hoc; split at hoc <;> simp_all
        rw [h_ok]
        simp [inflowOf, outflowOf]
        have hcont : contents (step s (Op.enqueue x)).2 = contents s ++ [x] := by
          apply req_enqueue_contents; intro h; exact hrejected h
        have h_eq : contents s ++ [x] = contents (step s (Op.enqueue x)).2 := by rw [hcont]
        calc contents s ++ ([x] ++ inflow (run step (step s (Op.enqueue x)).2 ops).1)
            = (contents s ++ [x]) ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by rw [List.append_assoc]
          _ = contents (step s (Op.enqueue x)).2 ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by rw [h_eq]
          _ = outflow (run step (step s (Op.enqueue x)).2 ops).1 ++ contents (run step (step s (Op.enqueue x)).2 ops).2 := ih _
          _ = ([] ++ outflow (run step (step s (Op.enqueue x)).2 ops).1) ++ contents (run step (step s (Op.enqueue x)).2 ops).2 := by simp
    | dequeue =>
      by_cases hrejected : (step s Op.dequeue).1 = .rejected
      · have hstep : step s Op.dequeue = (.rejected, s) := by
          unfold step at hrejected ⊢
          simp only at hrejected ⊢
          by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
          · simp [hc] at hrejected
          · simp [hc]
        rw [hstep]
        simp [inflowOf, outflowOf]
        exact ih s
      · have h_not_rej : (step s Op.dequeue).1 ≠ .rejected := hrejected
        obtain ⟨x, hgot, hcont⟩ := req_dequeue_contents (s:=s) h_not_rej
        rw [hgot]
        simp [inflowOf, outflowOf]
        have hcont' : contents s = x :: contents (step s Op.dequeue).2 := hcont
        calc contents s ++ inflow (run step (step s Op.dequeue).2 ops).1
            = (x :: contents (step s Op.dequeue).2) ++ inflow (run step (step s Op.dequeue).2 ops).1 := by rw [hcont']
          _ = [x] ++ (contents (step s Op.dequeue).2 ++ inflow (run step (step s Op.dequeue).2 ops).1) := by simp [List.cons_append, List.append_assoc]
          _ = [x] ++ (outflow (run step (step s Op.dequeue).2 ops).1 ++ contents (run step (step s Op.dequeue).2 ops).2) := by rw [ih _]
          _ = ([x] ++ outflow (run step (step s Op.dequeue).2 ops).1) ++ contents (run step (step s Op.dequeue).2 ops).2 := by rw [List.append_assoc]

end RingBuffer
