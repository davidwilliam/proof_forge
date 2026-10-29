import RingBuffer.Spec

namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if _ : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity then
      (Outcome.ok, { s with
        buf := fun i => if i = slot s s.count then x else s.buf i,
        count := s.count + 1 })
    else
      (Outcome.rejected, s)
  | .dequeue =>
    if _ : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (Outcome.got (s.buf s.head), { s with
        head := (s.head + 1) % s.capacity,
        count := s.count - 1 })
    else
      (Outcome.rejected, s)

theorem distinct_core (cap r d : Nat) (_hc0 : 0 < cap) (hd0 : 0 < d) (hdlt : d < cap)
    (_hrlt : r < cap) (heq : (r + d) % cap = r) : False := by
  have hmod1 : (r + d) % cap + cap * ((r + d) / cap) = r + d := Nat.mod_add_div (r + d) cap
  rw [heq] at hmod1
  have hd_eq : d = cap * ((r + d) / cap) := by omega
  cases hq : ((r + d) / cap) with
  | zero =>
    rw [hq] at hd_eq
    simp [Nat.mul_zero] at hd_eq
    omega
  | succ n =>
    rw [hq] at hd_eq
    have hmul : cap * (n + 1) = cap * n + cap := by simp [Nat.mul_add, Nat.mul_one]
    rw [hmul] at hd_eq
    omega

theorem slot_ne_of_lt (s : State) (i : Nat) (hi : i < s.count)
    (hc0 : 0 < s.capacity) (_hh : s.head < s.capacity) (hlt : s.count < s.capacity) :
    (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := by
  intro heq
  have hd0 : 0 < s.count - i := by omega
  have hdlt : s.count - i < s.capacity := by omega
  have ha_eq : s.head + s.count = (s.head + i) + (s.count - i) := by omega
  rw [ha_eq] at heq
  have hd_mod : (s.count - i) % s.capacity = s.count - i :=
    Nat.mod_eq_of_lt hdlt
  have h_add : ((s.head + i) + (s.count - i)) % s.capacity
      = (((s.head + i) % s.capacity) + ((s.count - i) % s.capacity)) % s.capacity :=
    Nat.add_mod (s.head + i) (s.count - i) s.capacity
  rw [hd_mod] at h_add
  rw [h_add] at heq
  have hrlt : (s.head + i) % s.capacity < s.capacity := Nat.mod_lt _ hc0
  exact distinct_core s.capacity ((s.head + i) % s.capacity) (s.count - i)
    hc0 hd0 hdlt hrlt heq.symm

theorem map_range_eq_of_mem (s : State) (x : Nat) (n : Nat) (hn : n ≤ s.count)
    (hc0 : 0 < s.capacity) (hh : s.head < s.capacity) (hlt : s.count < s.capacity) :
    ((List.range n).map (fun i => (if (s.head + i) % s.capacity = slot s s.count then x else s.buf ((s.head + i) % s.capacity)))) =
    ((List.range n).map (fun i => s.buf ((s.head + i) % s.capacity))) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hk_le : k ≤ s.count := by omega
    have hk_lt : k < s.count := by omega
    have hne : (s.head + k) % s.capacity ≠ slot s s.count := by
      simp only [slot]
      exact slot_ne_of_lt s k hk_lt hc0 hh hlt
    have hih := ih hk_le
    have hsing : (if (s.head + k) % s.capacity = slot s s.count then x else s.buf ((s.head + k) % s.capacity)) = s.buf ((s.head + k) % s.capacity) :=
      if_neg hne
    have hsing_list : List.map (fun i => (if (s.head + i) % s.capacity = slot s s.count then x else s.buf ((s.head + i) % s.capacity))) [k] =
        List.map (fun i => s.buf ((s.head + i) % s.capacity)) [k] := by
      simp [hsing]
    have e_range : List.range (k + 1) = List.range k ++ [k] := by simp [List.range_succ]
    rw [e_range, List.map_append, List.map_append, hih, hsing_list]

theorem dequeue_contents_helper_map_range_succ {α : Type} (f : Nat → α) : ∀ n : Nat,
    ((List.range (n + 1)).map f) = f 0 :: ((List.range n).map (fun i => f (i + 1))) := by
  intro n
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by simp [List.range_succ]
    have h2 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    rw [h1, List.map_append]
    rw [ih (f := f)]
    rw [h2, List.map_append]
    simp

theorem dequeue_contents_helper_slot_succ (head cap : Nat) (i : Nat) :
    (head + (i + 1)) % cap = (((head + 1) % cap) + i) % cap := by
  have h1 : head + (i + 1) = (head + 1) + i := by omega
  rw [h1]
  rw [Nat.mod_add_mod]

theorem enq_cond_of_not_rejected (s : State) (x : Nat)
    (hne : (step s (.enqueue x)).1 ≠ .rejected) :
    0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity := by
  by_cases hC' : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity)
  · exact hC'
  · exfalso
    have hstep_rej : step s (.enqueue x) = (Outcome.rejected, s) := by
      simp [step, dif_neg hC']
    have heq : (step s (.enqueue x)).1 = Outcome.rejected := by rw [hstep_rej]
    exact hne heq

theorem enq_state_eq (s : State) (x : Nat)
    (hC : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity) :
    (step s (.enqueue x)).2 = { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } := by
  simp [step, dif_pos hC]

theorem enq_contents_eq (s : State) (x : Nat)
    (hc0 : 0 < s.capacity) (hh : s.head < s.capacity) (hlt : s.count < s.capacity)
    (hstep2 : (step s (.enqueue x)).2 = { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) :
    contents (step s (.enqueue x)).2 = contents s ++ [x] := by
  rw [hstep2]
  show contents { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } = contents s ++ [x]
  have hshow : contents { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }
      = ((List.range (s.count + 1)).map (fun i : Nat => (if (s.head + i) % s.capacity = slot s s.count then x else s.buf ((s.head + i) % s.capacity)))) := rfl
  have hshow2 : contents s = ((List.range s.count).map (fun i : Nat => s.buf ((s.head + i) % s.capacity))) := rfl
  rw [hshow, hshow2]
  have hrange : List.range (s.count + 1) = List.range s.count ++ [s.count] := by simp [List.range_succ]
  simp only [hrange, List.map_append]
  have hlast : (if (s.head + s.count) % s.capacity = slot s s.count then x else s.buf ((s.head + s.count) % s.capacity)) = x := by
    simp [slot]
  have hmapsing : List.map (fun i : Nat => (if (s.head + i) % s.capacity = slot s s.count then x else s.buf ((s.head + i) % s.capacity))) [s.count] = [x] := by
    simp [hlast]
  rw [hmapsing]
  have hprefix : ((List.range s.count).map (fun i : Nat => (if (s.head + i) % s.capacity = slot s s.count then x else s.buf ((s.head + i) % s.capacity)))) =
      ((List.range s.count).map (fun i : Nat => s.buf ((s.head + i) % s.capacity))) :=
    map_range_eq_of_mem s x s.count (Nat.le_refl _) hc0 hh hlt
  rw [hprefix]

theorem deq_contents_eq (s : State)
    (hh : s.head < s.capacity) (hpos : 0 < s.count)
    (hstep1 : (step s .dequeue).1 = Outcome.got (s.buf s.head))
    (hstep2 : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) :
    ∃ y, (step s .dequeue).1 = Outcome.got y ∧ contents s = y :: contents (step s .dequeue).2 := by
  refine ⟨s.buf s.head, hstep1, ?_⟩
  rw [hstep2]
  show contents s = s.buf s.head :: contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }
  obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
  have hmod : s.head % s.capacity = s.head := Nat.mod_eq_of_lt hh
  have h0 : (s.head + 0) % s.capacity = s.head := by
    have he : s.head + 0 = s.head := by omega
    rw [he]
    exact hmod
  have hfg : ∀ i : Nat, s.buf ((s.head + (i + 1)) % s.capacity) = s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity) := by
    intro i
    rw [dequeue_contents_helper_slot_succ]
  have hmap := dequeue_contents_helper_map_range_succ (fun i => s.buf ((s.head + i) % s.capacity)) n
  have e1 : contents s = ((List.range s.count).map (fun i : Nat => s.buf ((s.head + i) % s.capacity))) := rfl
  have e2 : contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }
      = ((List.range (s.count - 1)).map (fun i : Nat => s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity))) := rfl
  rw [e1, e2, hn]
  rw [hmap, h0]
  congr 1
  have hnn : n + 1 - 1 = n := by omega
  rw [hnn]
  have heq : (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) = (fun i => s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity)) := funext hfg
  rw [heq]

theorem single_step_eq (s : State) (op : Op) :
    contents s ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
  cases op with
  | enqueue x =>
    by_cases hC : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity)
    · have h1 : (step s (.enqueue x)).1 = Outcome.ok := by simp [step, dif_pos hC]
      have hstep2 := enq_state_eq s x hC
      have hcont := enq_contents_eq s x hC.1 hC.2.1 hC.2.2.2 hstep2
      have hin : inflowOf (.enqueue x, (step s (.enqueue x)).1) = [x] := by rw [h1]; rfl
      have hout : outflowOf (.enqueue x, (step s (.enqueue x)).1) = ([] : List Nat) := by rw [h1]; rfl
      rw [hin, hout, hcont]
      simp
    · have h1 : (step s (.enqueue x)).1 = Outcome.rejected := by simp [step, dif_neg hC]
      have h2 : (step s (.enqueue x)).2 = s := by simp [step, dif_neg hC]
      have hin : inflowOf (.enqueue x, (step s (.enqueue x)).1) = ([] : List Nat) := by rw [h1]; rfl
      have hout : outflowOf (.enqueue x, (step s (.enqueue x)).1) = ([] : List Nat) := by
        rw [h1]
        rfl
      rw [hin, hout, h2]
      simp
  | dequeue =>
    by_cases hC : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · have h1 : (step s .dequeue).1 = Outcome.got (s.buf s.head) := by simp [step, dif_pos hC]
      have hstep2 : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by simp [step, dif_pos hC]
      obtain ⟨y, hy1, hy2⟩ := deq_contents_eq s hC.2.1 hC.2.2.2 h1 hstep2
      rw [h1] at hy1
      have hy_eq : y = s.buf s.head := by simp at hy1; exact hy1.symm
      rw [hy_eq] at hy2
      have hin : inflowOf (.dequeue, (step s .dequeue).1) = ([] : List Nat) := by rw [h1]; rfl
      have hout : outflowOf (.dequeue, (step s .dequeue).1) = [s.buf s.head] := by rw [h1]; rfl
      rw [hin, hout]
      simp [hy2]
    · have h1 : (step s .dequeue).1 = Outcome.rejected := by simp [step, dif_neg hC]
      have h2 : (step s .dequeue).2 = s := by simp [step, dif_neg hC]
      have hin : inflowOf (.dequeue, (step s .dequeue).1) = ([] : List Nat) := by rw [h1]; rfl
      have hout : outflowOf (.dequeue, (step s .dequeue).1) = ([] : List Nat) := by rw [h1]; rfl
      rw [hin, hout, h2]
      simp

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    obtain ⟨⟨hc0, hh, hle⟩, hlt⟩ := h
    simp only [step]
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity :=
      ⟨hc0, hh, hle, hlt⟩
    have hpos : (dite (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity)
      (fun _ => (Outcome.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }))
      (fun _ => (Outcome.rejected, s))).1 ≠ .rejected := by
      rw [dite_eq_ite]
      simp [hcond]
    simpa using hpos
  | dequeue =>
    simp only [Valid, WellFormed] at h
    obtain ⟨⟨hc0, hh, hle⟩, hlt⟩ := h
    simp only [step]
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count :=
      ⟨hc0, hh, hle, hlt⟩
    have hpos : (dite (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
      (fun _ => (Outcome.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }))
      (fun _ => (Outcome.rejected, s))).1 ≠ .rejected := by
      rw [dite_eq_ite]
      simp [hcond]
    simpa using hpos

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    have hC : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity) := by
      intro hc
      apply h
      obtain ⟨hc0, hh, hle, hlt⟩ := hc
      exact ⟨⟨hc0, hh, hle⟩, hlt⟩
    unfold step
    simp only []
    rw [dif_neg hC]
  | dequeue =>
    have hC : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hc
      apply h
      obtain ⟨hc0, hh, hle, hlt⟩ := hc
      exact ⟨⟨hc0, hh, hle⟩, hlt⟩
    unfold step
    simp only []
    rw [dif_neg hC]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hW
  obtain ⟨hc0, hh, hle⟩ := hW
  cases op with
  | enqueue x =>
    show WellFormed (step s (.enqueue x)).2
    unfold step
    simp only []
    split
    · next hC =>
      obtain ⟨hc0', hh', hle', hlt'⟩ := hC
      exact ⟨hc0, hh, Nat.succ_le_of_lt hlt'⟩
    · exact ⟨hc0, hh, hle⟩
  | dequeue =>
    show WellFormed (step s .dequeue).2
    unfold step
    simp only []
    split
    · next hC =>
      obtain ⟨hc0', hh', hle', hlt'⟩ := hC
      refine ⟨hc0, Nat.mod_lt _ hc0, ?_⟩
      exact Nat.le_trans (Nat.pred_le _) hle
    · exact ⟨hc0, hh, hle⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hne
  simp only [step] at hne ⊢
  by_cases hC : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity)
  · simp [dif_pos hC]
  · simp [dif_neg hC] at hne

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  simp only [step] at hne ⊢
  by_cases hC : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · simp [dif_pos hC]
  · simp [dif_neg hC] at hne

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  have hC := enq_cond_of_not_rejected s x hne
  have hc0 : 0 < s.capacity := hC.1
  have hh : s.head < s.capacity := hC.2.1
  have hlt : s.count < s.capacity := hC.2.2.2
  have hstep2 := enq_state_eq s x hC
  exact enq_contents_eq s x hc0 hh hlt hstep2

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  simp only [step] at hne ⊢
  by_cases hC : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · have hh : s.head < s.capacity := hC.2.1
    have hpos : 0 < s.count := hC.2.2.2
    have hstep1 : (step s .dequeue).1 = Outcome.got (s.buf s.head) := by simp [step, dif_pos hC]
    have hstep2 : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by simp [step, dif_pos hC]
    exact deq_contents_eq s hh hpos hstep1 hstep2
  · simp [dif_neg hC] at hne

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op rest ih =>
    have h_single : contents s ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ contents (step s op).2 :=
      single_step_eq s op
    have h_tail : contents (step s op).2 ++ inflow (run step (step s op).2 rest).1
        = outflow (run step (step s op).2 rest).1 ++ contents (run step (step s op).2 rest).2 :=
      ih (step s op).2
    have h_run1 : (run step s (op :: rest)).1 = (op, (step s op).1) :: (run step (step s op).2 rest).1 := by
      simp [run]
    have h_run2 : (run step s (op :: rest)).2 = (run step (step s op).2 rest).2 := by
      simp [run]
    rw [h_run1, h_run2]
    have hin' : inflow ((op, (step s op).1) :: (run step (step s op).2 rest).1)
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1 := by
      simp [inflow]
    have hout' : outflow ((op, (step s op).1) :: (run step (step s op).2 rest).1)
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1 := by
      simp [outflow]
    rw [hin', hout']
    rw [← List.append_assoc (contents s) _ _]
    rw [h_single]
    rw [List.append_assoc]
    rw [h_tail]
    rw [← List.append_assoc]

end RingBuffer
