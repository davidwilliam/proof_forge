import RingBuffer.Spec

namespace RingBuffer

def step : Impl
  | s, .enqueue x =>
    if _ : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { s with
        buf := fun i => if i = slot s s.count then x else s.buf i,
        count := s.count + 1 })
    else
      (.rejected, s)
  | s, .dequeue =>
    if _ : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with
        head := (s.head + 1) % s.capacity,
        count := s.count - 1 })
    else
      (.rejected, s)

theorem aux_mod_sub (n cap : Nat) (_h : 0 < cap) (hlo : cap ≤ n) (hhi : n < cap + cap) : n % cap = n - cap := by
  have hsub : n - cap < cap := by omega
  have hrewrite : (n - cap) + cap = n := by omega
  have h_eq : n % cap = ((n - cap) + cap) % cap := by rw [hrewrite]
  have h_mod : ((n - cap) + cap) % cap = (n - cap) % cap := Nat.add_mod_right _ _
  have h_small : (n - cap) % cap = n - cap := Nat.mod_eq_of_lt hsub
  exact h_eq.trans (h_mod.trans h_small)

theorem aux_enq_slot_ne (head cap count i : Nat) (hc0 : 0 < cap) (hh : head < cap) (hlt : count < cap) (hi : i < count) : (head + i) % cap ≠ (head + count) % cap := by
  intro heq
  have hi_le : head + i < cap + cap := by omega
  have hc_lt : head + count < cap + cap := by omega
  by_cases h1 : cap ≤ head + i
  · have h2 : cap ≤ head + count := by omega
    have r1 : (head + i) % cap = (head + i) - cap := aux_mod_sub _ _ hc0 h1 hi_le
    have r2 : (head + count) % cap = (head + count) - cap := aux_mod_sub _ _ hc0 h2 hc_lt
    rw [r1, r2] at heq
    omega
  · have lt1 : head + i < cap := by omega
    have r1 : (head + i) % cap = head + i := Nat.mod_eq_of_lt lt1
    by_cases h2 : cap ≤ head + count
    · have r2 : (head + count) % cap = (head + count) - cap := aux_mod_sub _ _ hc0 h2 hc_lt
      rw [r1, r2] at heq
      omega
    · have lt2 : head + count < cap := by omega
      have r2 : (head + count) % cap = head + count := Nat.mod_eq_of_lt lt2
      rw [r1, r2] at heq
      omega

theorem aux_map_range_eq (n : Nat) (f g : Nat → Nat) (h : ∀ i, i < n → f i = g i) : (List.range n).map f = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have ih' : (List.range k).map f = (List.range k).map g := ih (fun i hi => h i (by omega))
    have hk : f k = g k := h k (Nat.lt_succ_self k)
    simp [List.range_succ, List.map_append, ih', hk]

theorem aux_slot_shift (head cap i : Nat) : (((head + 1) % cap + i) % cap) = ((head + (i + 1)) % cap) := by
  have h1 : (((head + 1) % cap + i) % cap) = ((head + 1 + i) % cap) := Nat.mod_add_mod _ _ _
  rw [h1]
  congr 1
  omega

theorem aux_enq_core (s : State) (x : Nat) (hc0 : 0 < s.capacity) (hh : s.head < s.capacity) (hlt : s.count < s.capacity) : contents ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) = contents s ++ [x] := by
  show (List.range (s.count + 1)).map (fun i => (fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + i) % s.capacity)) = (List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity)) ++ [x]
  rw [List.range_succ]
  rw [List.map_append]
  have hmap : (List.range s.count).map (fun i => (fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + i) % s.capacity)) = (List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity)) := by
    apply aux_map_range_eq
    intro i hi
    have hne2 : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := aux_enq_slot_ne s.head s.capacity s.count i hc0 hh hlt hi
    show (if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf _) = _
    exact if_neg hne2
  rw [hmap]
  have hsing : ([s.count].map (fun i => (fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + i) % s.capacity))) = [x] := by
    show [if (s.head + s.count) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf _] = [x]
    rw [if_pos rfl]
  rw [hsing]

theorem aux_deq_core (s : State) (hc0 : 0 < s.capacity) (hh : s.head < s.capacity) (hle : s.count ≤ s.capacity) (hlt : 0 < s.count) : contents s = s.buf s.head :: contents ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) := by
  obtain ⟨k, hk⟩ : ∃ k, s.count = k + 1 := ⟨s.count - 1, by omega⟩
  have hcount : s.count - 1 = k := by omega
  have hhead : (s.head + 0) % s.capacity = s.head := by
    calc (s.head + 0) % s.capacity = s.head % s.capacity := by rw [Nat.add_zero]
      _ = s.head := Nat.mod_eq_of_lt hh
  have htail_eq : (List.range k).map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) = (List.range k).map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) := by
    apply aux_map_range_eq
    intro i _
    rw [aux_slot_shift]
  have hcs : contents s = (List.range (k + 1)).map (fun i => s.buf ((s.head + i) % s.capacity)) := by
    simp only [contents, slot]
    rw [hk]
  have hrange : List.range (k + 1) = 0 :: ((List.range k).map Nat.succ) := List.range_succ_eq_map
  have hLHS : contents s = s.buf s.head :: (List.range k).map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) := by
    rw [hcs, hrange, List.map_cons]
    have hhd : s.buf ((s.head + 0) % s.capacity) = s.buf s.head := by rw [hhead]
    rw [hhd]
    congr 1
    rw [List.map_map]
    apply aux_map_range_eq
    intro i _
    rfl
  have hRHS : contents ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) = (List.range k).map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) := by
    show (List.range (s.count - 1)).map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) = _
    rw [hcount]
  rw [hLHS, hRHS, htail_eq]

theorem aux_single_step (s : State) (op : Op) : contents s ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
  cases op with
  | enqueue x =>
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · obtain ⟨hc0, hh, hlt⟩ := hc
      have heq : step s (Op.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
        unfold step
        exact dif_pos ⟨hc0, hh, hlt⟩
      have h1 : (step s (Op.enqueue x)).1 = .ok := by rw [heq]
      have h4 : (step s (Op.enqueue x)).2 = ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) := by rw [heq]
      have hcont := aux_enq_core s x hc0 hh hlt
      have h2 : inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [x] := by rw [h1]; rfl
      have h3 : outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [] := by rw [h1]; rfl
      rw [h2, h3, h4]
      rw [List.nil_append]
      rw [hcont]
    · have heq : step s (Op.enqueue x) = (.rejected, s) := by
        unfold step
        exact dif_neg hc
      have h1 : (step s (Op.enqueue x)).1 = .rejected := by rw [heq]
      have h2 : (step s (Op.enqueue x)).2 = s := by rw [heq]
      have hi : inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [] := by rw [h1]; rfl
      have ho : outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [] := by rw [h1]; rfl
      rw [hi, ho, h2, List.append_nil, List.nil_append]
  | dequeue =>
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · obtain ⟨hc0, hh, hle, hlt⟩ := hc
      have heq : step s Op.dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
        unfold step
        exact dif_pos ⟨hc0, hh, hle, hlt⟩
      have hcore := aux_deq_core s hc0 hh hle hlt
      have h2 : (step s Op.dequeue).2 = ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) := by rw [heq]
      have h1 : (step s Op.dequeue).1 = .got (s.buf s.head) := by rw [heq]
      have hi : inflowOf (Op.dequeue, (step s Op.dequeue).1) = [] := by rw [h1]; rfl
      have ho : outflowOf (Op.dequeue, (step s Op.dequeue).1) = [s.buf s.head] := by rw [h1]; rfl
      rw [hi, ho, h2, List.append_nil]
      exact hcore
    · have heq : step s Op.dequeue = (.rejected, s) := by
        unfold step
        exact dif_neg hc
      have h1 : (step s Op.dequeue).1 = .rejected := by rw [heq]
      have h2 : (step s Op.dequeue).2 = s := by rw [heq]
      have hi : inflowOf (Op.dequeue, (step s Op.dequeue).1) = [] := by rw [h1]; rfl
      have ho : outflowOf (Op.dequeue, (step s Op.dequeue).1) = [] := by rw [h1]; rfl
      rw [hi, ho, h2, List.append_nil, List.nil_append]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    obtain ⟨⟨hc0, hh, hle⟩, hlt⟩ := h
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := ⟨hc0, hh, hlt⟩
    have heq : step s (Op.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
      unfold step
      exact dif_pos hcond
    rw [heq]
    simp
  | dequeue =>
    simp only [Valid, WellFormed] at h
    obtain ⟨⟨hc0, hh, hle⟩, hlt⟩ := h
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := ⟨hc0, hh, hle, hlt⟩
    have heq : step s Op.dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
      unfold step
      exact dif_pos hcond
    rw [heq]
    simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    have hneg : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro hc
      obtain ⟨hc0, hh, hlt⟩ := hc
      apply h
      exact ⟨⟨hc0, hh, Nat.le_of_lt hlt⟩, hlt⟩
    unfold step
    simp [hneg]
  | dequeue =>
    simp only [Valid, WellFormed] at h
    have hneg : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hc
      obtain ⟨hc0, hh, hle, hlt⟩ := hc
      apply h
      exact ⟨⟨hc0, hh, hle⟩, hlt⟩
    unfold step
    simp [hneg]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hwf
  simp only [WellFormed] at hwf
  obtain ⟨hc0, hh, hle⟩ := hwf
  cases op with
  | enqueue x =>
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · have heq : step s (Op.enqueue x) =
        (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
          unfold step
          exact dif_pos hc
      have h2 : (step s (Op.enqueue x)).2 = ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) := by rw [heq]
      rw [h2]
      obtain ⟨_, _, hlt⟩ := hc
      simp only [WellFormed]
      exact ⟨hc0, hh, Nat.succ_le_of_lt hlt⟩
    · have heq2 : step s (Op.enqueue x) = (.rejected, s) := by
          unfold step
          exact dif_neg hc
      have h2 : (step s (Op.enqueue x)).2 = s := by rw [heq2]
      rw [h2]
      simp only [WellFormed]
      exact ⟨hc0, hh, hle⟩
  | dequeue =>
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · have heq : step s Op.dequeue =
        (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
          unfold step
          exact dif_pos hc
      have h2 : (step s Op.dequeue).2 = ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) := by rw [heq]
      rw [h2]
      simp only [WellFormed]
      refine ⟨hc0, Nat.mod_lt _ hc0, ?_⟩
      omega
    · have heq2 : step s Op.dequeue = (.rejected, s) := by
          unfold step
          exact dif_neg hc
      have h2 : (step s Op.dequeue).2 = s := by rw [heq2]
      rw [h2]
      simp only [WellFormed]
      exact ⟨hc0, hh, hle⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hne
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · have heq : step s (Op.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
      unfold step
      exact dif_pos hc
    exact heq
  · have heq2 : step s (Op.enqueue x) = (.rejected, s) := by
      unfold step
      exact dif_neg hc
    have hcontra : (step s (Op.enqueue x)).1 = .rejected := by rw [heq2]
    exact absurd hcontra hne

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · have heq : step s Op.dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
      unfold step
      exact dif_pos hc
    exact heq
  · have heq2 : step s Op.dequeue = (.rejected, s) := by
      unfold step
      exact dif_neg hc
    have hcontra : (step s Op.dequeue).1 = .rejected := by rw [heq2]
    exact absurd hcontra hne

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · obtain ⟨hc0, hh, hlt⟩ := hc
    have heq : step s (Op.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
      unfold step
      exact dif_pos ⟨hc0, hh, hlt⟩
    have hstep2 : (step s (Op.enqueue x)).2 = ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) := by rw [heq]
    rw [hstep2]
    exact aux_enq_core s x hc0 hh hlt
  · have heq2 : step s (Op.enqueue x) = (.rejected, s) := by
      unfold step
      exact dif_neg hc
    have hcontra : (step s (Op.enqueue x)).1 = .rejected := by rw [heq2]
    exact absurd hcontra hne

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · obtain ⟨hc0, hh, hle, hlt⟩ := hc
    have heq : step s Op.dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
      unfold step
      exact dif_pos ⟨hc0, hh, hle, hlt⟩
    refine ⟨s.buf s.head, by rw [heq], ?_⟩
    have hstep2 : (step s Op.dequeue).2 = ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) := by rw [heq]
    rw [hstep2]
    have hcore := aux_deq_core s hc0 hh hle hlt
    rw [hcore]
  · have heq2 : step s Op.dequeue = (.rejected, s) := by
      unfold step
      exact dif_neg hc
    have hcontra : (step s Op.dequeue).1 = .rejected := by rw [heq2]
    exact absurd hcontra hne

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    have h1 : (run step s []).1 = ([] : List (Op × Outcome)) := rfl
    have h2 : (run step s []).2 = s := rfl
    rw [h1, h2]
    simp [inflow, outflow]
  | cons op rest ih =>
    have hsingle := aux_single_step s op
    have hrun1 : (run step s (op :: rest)).1 = (op, (step s op).1) :: (run step (step s op).2 rest).1 := rfl
    have hrun2 : (run step s (op :: rest)).2 = (run step (step s op).2 rest).2 := rfl
    have hih := ih (s := (step s op).2)
    have hinf : inflow ((op, (step s op).1) :: (run step (step s op).2 rest).1) = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1 := rfl
    have hout : outflow ((op, (step s op).1) :: (run step (step s op).2 rest).1) = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1 := rfl
    rw [hrun1, hrun2, hinf, hout]
    rw [← List.append_assoc, hsingle, List.append_assoc, hih, ← List.append_assoc]

end RingBuffer
