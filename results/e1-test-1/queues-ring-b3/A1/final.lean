import RingBuffer.Spec
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (Outcome.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 })
    else (Outcome.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (Outcome.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (Outcome.rejected, s)

theorem my_wf_aux1 : KeepsWellFormed step := by
  intro s op hwf
  cases op with
  | enqueue x =>
    unfold step
    by_cases h : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · simp [h]
      obtain ⟨hc0, hh, hcc⟩ := hwf
      obtain ⟨_, _, hlt⟩ := h
      exact ⟨hc0, hh, Nat.succ_le_of_lt hlt⟩
    · simp [h]
      exact hwf
  | dequeue =>
    unfold step
    by_cases h : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · simp [h]
      obtain ⟨hc0, hh, hcc⟩ := hwf
      refine ⟨hc0, Nat.mod_lt _ hc0, Nat.le_trans (Nat.sub_le _ _) hcc⟩
    · simp [h]
      exact hwf

theorem add_cap_mod (k cap : Nat) : (k + cap) % cap = k % cap := by
  have hself : cap % cap = 0 := Nat.mod_self cap
  have h1 : (cap % cap + k) % cap = (cap + k) % cap := Nat.mod_add_mod cap cap k
  rw [hself] at h1
  simp only [Nat.zero_add] at h1
  have hcomm : cap + k = k + cap := Nat.add_comm cap k
  rw [hcomm] at h1
  exact h1.symm

theorem mod_sub_cap (t d cap : Nat) (_ht : t < cap) (hge : cap ≤ t + d) (hlt : t + d < cap + cap) : (t + d) % cap = t + d - cap := by
  have hcancel : t + d - cap + cap = t + d := Nat.sub_add_cancel hge
  have hlt2 : t + d - cap < cap := by omega
  have hmod : (t + d - cap + cap) % cap = (t + d - cap) % cap := add_cap_mod (t + d - cap) cap
  rw [hcancel] at hmod
  rw [Nat.mod_eq_of_lt hlt2] at hmod
  exact hmod

theorem slot_ne_of_lt (s : State) (i : Nat) (hi : i < s.count)
    (hhead : s.head < s.capacity) (_hcap : 0 < s.capacity)
    (hcount : s.count < s.capacity) :
    slot s i ≠ slot s s.count := by
  intro heq
  simp only [slot] at heq
  by_cases hle : s.head + s.count < s.capacity
  · have hm1 : (s.head + s.count) % s.capacity = s.head + s.count :=
      Nat.mod_eq_of_lt hle
    have hlt1 : s.head + i < s.capacity := by omega
    have hm2 : (s.head + i) % s.capacity = s.head + i :=
      Nat.mod_eq_of_lt hlt1
    rw [hm1, hm2] at heq
    omega
  · have hge : s.capacity ≤ s.head + s.count := by omega
    have hlt_ub : s.head + s.count < s.capacity + s.capacity := by omega
    have hm1 : (s.head + s.count) % s.capacity = s.head + s.count - s.capacity :=
      mod_sub_cap s.head s.count s.capacity hhead hge hlt_ub
    by_cases hle2 : s.head + i < s.capacity
    · have hm2 : (s.head + i) % s.capacity = s.head + i :=
        Nat.mod_eq_of_lt hle2
      rw [hm1, hm2] at heq
      omega
    · have hge2 : s.capacity ≤ s.head + i := by omega
      have hlt_ub2 : s.head + i < s.capacity + s.capacity := by omega
      have hm2 : (s.head + i) % s.capacity = s.head + i - s.capacity :=
        mod_sub_cap s.head i s.capacity hhead hge2 hlt_ub2
      rw [hm1, hm2] at heq
      omega

theorem map_range_succ (f : Nat → Nat) (n : Nat) :
    ((List.range (n + 1)).map f) = ((List.range n).map f) ++ [f n] := by
  simp [List.range_succ]

theorem deq_slot_shift_aux (head cap i : Nat) :
    (((head + 1) % cap + i) % cap) = ((head + (i + 1)) % cap) := by
  have h1 : (((head + 1) % cap + i) % cap) = ((head + 1 + i) % cap) :=
    Nat.mod_add_mod (head + 1) cap i
  have h2 : (head + 1 + i) = (head + (i + 1)) := by omega
  rw [h1, h2]

theorem deq_range_map_aux6 (f : Nat → Nat) (n : Nat) :
    ((List.range (n + 1)).map f) = f 0 :: ((List.range n).map (fun i => f (i + 1))) := by
  rw [@List.range_succ_eq_map n]
  simp only [List.map_cons, List.map_map, Function.comp_def, Nat.succ_eq_add_one]

theorem fifo_inflow_cons (a : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (a :: t) = inflowOf a ++ inflow t := by
  simp [inflow]

theorem fifo_outflow_cons (a : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (a :: t) = outflowOf a ++ outflow t := by
  simp [outflow]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    obtain ⟨⟨hcap, hhead, _hle⟩, hlt⟩ := h
    have hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) :=
      ⟨hcap, hhead, hlt⟩
    simp [step, hcond]
  | dequeue =>
    obtain ⟨⟨hcap, hhead, hle⟩, hpos⟩ := h
    have hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) :=
      ⟨hcap, hhead, hle, hpos⟩
    simp [step, hcond]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    have hC : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro hcon
      obtain ⟨hcap, hhead, hlt⟩ := hcon
      apply h
      refine ⟨⟨hcap, hhead, Nat.le_of_lt hlt⟩, hlt⟩
    simp [step, hC]
  | dequeue =>
    have hC : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hcon
      obtain ⟨hcap, hhead, hle, hpos⟩ := hcon
      apply h
      exact ⟨⟨hcap, hhead, hle⟩, hpos⟩
    simp [step, hC]

theorem req_well_formed : KeepsWellFormed step := my_wf_aux1

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hne
  by_cases hC : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · simp [step, hC]
  · have hrej : step s (.enqueue x) = (.rejected, s) := by simp [step, hC]
    rw [hrej] at hne
    exact absurd rfl hne

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  by_cases hC : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · simp [step, hC]
  · have hrej : step s .dequeue = (.rejected, s) := by simp [step, hC]
    rw [hrej] at hne
    exact absurd rfl hne

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  by_cases hC : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · have hcap : 0 < s.capacity := hC.1
    have hhead : s.head < s.capacity := hC.2.1
    have hcount : s.count < s.capacity := hC.2.2
    have hst2 : (step s (.enqueue x)).2 =
        ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) := by
      simp [step, hC]
    rw [hst2]
    have hcont_s : contents s =
        ((List.range s.count).map (fun i => s.buf (slot s i))) := rfl
    have hcont_t : contents ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) =
        ((List.range (s.count + 1)).map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i))) := rfl
    rw [hcont_s, hcont_t]
    have hprefix : ∀ n, n ≤ s.count →
        ((List.range n).map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i))) =
        ((List.range n).map (fun i => s.buf (slot s i))) := by
      intro n hn
      induction n with
      | zero => rfl
      | succ n ih =>
        have hn_le : n ≤ s.count := by omega
        have hn_lt : n < s.count := by omega
        have ih' := ih hn_le
        have hne2 : slot s n ≠ slot s s.count :=
          slot_ne_of_lt s n hn_lt hhead hcap hcount
        have hif : (if slot s n = slot s s.count then x else s.buf (slot s n)) =
            s.buf (slot s n) := by simp [hne2]
        have h1 := map_range_succ (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)) n
        have h2 := map_range_succ (fun i => s.buf (slot s i)) n
        rw [h1, h2, ih', hif]
    have h1 := map_range_succ (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)) s.count
    rw [h1, hprefix s.count (Nat.le_refl _)]
    simp
  · have hrej : step s (.enqueue x) = (.rejected, s) := by simp [step, hC]
    rw [hrej] at hne
    exact absurd rfl hne

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  by_cases hC : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · have hhead : s.head < s.capacity := hC.2.1
    have h1eq : (step s .dequeue).1 = Outcome.got (s.buf s.head) := by
      simp [step, hC]
    have h2eq : (step s .dequeue).2 =
        ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) := by
      simp [step, hC]
    refine ⟨s.buf s.head, h1eq, ?_⟩
    rw [h2eq]
    have hex : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
    obtain ⟨n, hn⟩ := hex
    have hcount_sub : s.count - 1 = n := by omega
    have hslot_s0 : s.buf (slot s 0) = s.buf s.head := by
      have h : slot s 0 = s.head := by
        unfold slot
        simp only [Nat.add_zero]
        exact Nat.mod_eq_of_lt hhead
      rw [h]
    have hslot_main : ∀ i, slot s (i + 1) =
        slot ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) i := by
      intro i
      unfold slot
      simp only
      exact (deq_slot_shift_aux s.head s.capacity i).symm
    have htail : ∀ m, ((List.range m).map (fun i => s.buf (slot s (i + 1)))) =
        ((List.range m).map (fun i => s.buf (slot ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) i))) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ihm =>
        have ha := map_range_succ (fun i => s.buf (slot s (i + 1))) m
        have hb := map_range_succ (fun i => s.buf (slot ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) i)) m
        rw [ha, hb, ihm]
        have heq : s.buf (slot s (m + 1)) =
            s.buf (slot ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) m) := by
          rw [← hslot_main m]
        rw [heq]
    have hcont_s : contents s = ((List.range (n + 1)).map (fun i => s.buf (slot s i))) := by
      simp [contents, hn]
    have hcont_t : contents ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) =
        ((List.range n).map (fun i => s.buf (slot ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) i))) := by
      simp [contents, hcount_sub]
    rw [hcont_s, hcont_t]
    have hf := deq_range_map_aux6 (fun i => s.buf (slot s i)) n
    rw [hf, hslot_s0, htail n]
  · have hrej : step s .dequeue = (.rejected, s) := by simp [step, hC]
    rw [hrej] at hne
    exact absurd rfl hne

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    have hsingle : contents s ++ inflowOf (op, (step s op).1)
        = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
      cases op with
      | enqueue x =>
        by_cases hrej : (step s (.enqueue x)).1 = Outcome.rejected
        · have hNotValid : ¬ Valid s (.enqueue x) := fun hv => req_valid_succeeds s (.enqueue x) hv hrej
          have hstep := req_invalid_noop s (.enqueue x) hNotValid
          have h1 : (step s (.enqueue x)).1 = Outcome.rejected := hrej
          have h2 : (step s (.enqueue x)).2 = s := by rw [hstep]
          simp [h1, h2, inflowOf, outflowOf]
        · have hOk : (step s (.enqueue x)).1 = Outcome.ok := by
            have hEff := req_enqueue_effects s x hrej
            rw [hEff]
          have hcont := req_enqueue_contents s x hrej
          simp [hOk, inflowOf, outflowOf, hcont]
      | dequeue =>
        by_cases hrej : (step s .dequeue).1 = Outcome.rejected
        · have hNotValid : ¬ Valid s .dequeue := fun hv => req_valid_succeeds s .dequeue hv hrej
          have hstep := req_invalid_noop s .dequeue hNotValid
          have h1 : (step s .dequeue).1 = Outcome.rejected := hrej
          have h2 : (step s .dequeue).2 = s := by rw [hstep]
          simp [h1, h2, inflowOf, outflowOf]
        · obtain ⟨x, hx1, hx2⟩ := req_dequeue_contents s hrej
          simp [hx1, inflowOf, outflowOf, hx2]
    have htail := ih (step s op).2
    have hfst : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by simp only [run]
    have hsnd : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by simp only [run]
    rw [hfst, hsnd]
    rw [fifo_inflow_cons, fifo_outflow_cons]
    have h1 : contents s ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
      = (contents s ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by rw [List.append_assoc]
    have h2 : (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ contents (run step (step s op).2 ops).2
      = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ contents (run step (step s op).2 ops).2) := by rw [List.append_assoc]
    rw [h1, h2, hsingle, ← htail]
    rw [← List.append_assoc]

end RingBuffer
