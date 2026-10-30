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

theorem aux_slot_ne2 (s : State) (i : Nat) (hi : i < s.count) (hc : s.count < s.capacity) (hhead : s.head < s.capacity) (_hcap : 0 < s.capacity) :
    slot s i ≠ slot s s.count := by
  unfold slot
  intro heq
  have h1 : s.head + i < s.capacity ∨ s.capacity ≤ s.head + i := Nat.lt_or_ge _ _
  have h2 : s.head + s.count < s.capacity ∨ s.capacity ≤ s.head + s.count := Nat.lt_or_ge _ _
  rcases h1 with hlt1 | hge1
  · rcases h2 with hlt2 | hge2
    · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at heq; omega
    · rw [Nat.mod_eq_of_lt hlt1] at heq
      have hmod2 : (s.head + s.count) % s.capacity = (s.head + s.count - s.capacity) % s.capacity := Nat.mod_eq_sub_mod hge2
      have hlt_sub : s.head + s.count - s.capacity < s.capacity := by omega
      rw [hmod2, Nat.mod_eq_of_lt hlt_sub] at heq; omega
  · rcases h2 with hlt2 | hge2
    · have hmod1 : (s.head + i) % s.capacity = (s.head + i - s.capacity) % s.capacity := Nat.mod_eq_sub_mod hge1
      have hlt_sub1 : s.head + i - s.capacity < s.capacity := by omega
      rw [hmod1, Nat.mod_eq_of_lt hlt_sub1, Nat.mod_eq_of_lt hlt2] at heq; omega
    · have hmod1 : (s.head + i) % s.capacity = (s.head + i - s.capacity) % s.capacity := Nat.mod_eq_sub_mod hge1
      have hmod2 : (s.head + s.count) % s.capacity = (s.head + s.count - s.capacity) % s.capacity := Nat.mod_eq_sub_mod hge2
      have hlt_sub1 : s.head + i - s.capacity < s.capacity := by omega
      have hlt_sub2 : s.head + s.count - s.capacity < s.capacity := by omega
      rw [hmod1, Nat.mod_eq_of_lt hlt_sub1, hmod2, Nat.mod_eq_of_lt hlt_sub2] at heq; omega

theorem slot_succ_eq (s : State) (_hcap : 0 < s.capacity) (i : Nat) :
    (s.head + (i + 1)) % s.capacity = ((s.head + 1) % s.capacity + i) % s.capacity := by
  have h1 : s.head + (i + 1) = s.head + 1 + i := by omega
  rw [h1, ← Nat.mod_add_mod]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hValid
  cases op with
  | enqueue x =>
    have hWF := hValid.1
    have hLt := hValid.2
    unfold WellFormed at hWF
    have hcap : 0 < s.capacity := hWF.1
    have hhead : s.head < s.capacity := hWF.2.1
    unfold step
    simp only [hcap, hhead, hLt, and_self]
    intro hcontra
    injection hcontra
  | dequeue =>
    have hWF := hValid.1
    have hpos := hValid.2
    unfold WellFormed at hWF
    have hcap : 0 < s.capacity := hWF.1
    have hhead : s.head < s.capacity := hWF.2.1
    have hcount_le : s.count ≤ s.capacity := hWF.2.2
    unfold step
    simp only [hcap, hhead, hcount_le, hpos, and_self]
    intro hcontra
    injection hcontra

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv
  unfold Valid WellFormed at hInv
  unfold step
  cases op with
  | enqueue x =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro h
      apply hInv
      constructor
      · exact ⟨h.1, h.2.1, Nat.le_of_lt h.2.2⟩
      · exact h.2.2
    simp only [hcond, ite_false]
  | dequeue =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro h
      apply hInv
      constructor
      · exact ⟨h.1, h.2.1, h.2.2.1⟩
      · exact h.2.2.2
    simp only [hcond, ite_false]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hWF
  have hcap : 0 < s.capacity := hWF.1
  have hhead : s.head < s.capacity := hWF.2.1
  have hcnt : s.count ≤ s.capacity := hWF.2.2
  unfold WellFormed at hWF ⊢
  unfold step
  cases op with
  | enqueue x =>
    simp only
    split
    · next hcond =>
      have hcond1 : s.count < s.capacity := hcond.2.2
      simp only
      refine ⟨hcap, hhead, ?_⟩
      omega
    · simp only
      exact ⟨hcap, hhead, hcnt⟩
  | dequeue =>
    simp only
    split
    · next hcond =>
      simp only
      refine ⟨?_, ?_, ?_⟩
      · exact hcap
      · exact Nat.mod_lt _ hcap
      · omega
    · simp only
      exact ⟨hcap, hhead, hcnt⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact hc
    · have hrej : (step s (Op.enqueue x)).1 = .rejected := by
        unfold step
        simp [hc]
      exact absurd hrej h
  have hstep : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
    unfold step slot
    simp [hcond]
  exact hstep

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · exact hc
    · have hrej : (step s Op.dequeue).1 = .rejected := by unfold step; simp [hc]
      exact absurd hrej h
  have hstep : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
    unfold step; simp [hcond]
  exact hstep

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x h
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact hc
    · have hrej : (step s (Op.enqueue x)).1 = .rejected := by unfold step; simp [hc]
      exact absurd hrej h
  have _hcap : 0 < s.capacity := hcond.1
  have hhead : s.head < s.capacity := hcond.2.1
  have hcnt_lt : s.count < s.capacity := hcond.2.2
  have hstep_eq : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
    unfold step slot; simp [hcond]
  have h_snd : (step s (.enqueue x)).2 = { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } := by rw [hstep_eq]
  rw [h_snd]
  unfold contents slot
  simp only
  have hrw : List.range (s.count + 1) = List.range s.count ++ [s.count] := by simp [List.range_succ]
  rw [hrw, List.map_append]
  have hmap_eq : List.map (fun i => (if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity))) (List.range s.count)
      = List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count) := by
    apply List.map_congr_left
    intro i hi
    have hi_lt : i < s.count := List.mem_range.mp hi
    have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := aux_slot_ne2 s i hi_lt hcnt_lt hhead _hcap
    simp [hne]
  rw [hmap_eq]
  simp

theorem req_dequeue_contents : DequeueContents step := by
  intro s h
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · exact hc
    · have hrej : (step s Op.dequeue).1 = .rejected := by unfold step; simp [hc]
      exact absurd hrej h
  have hcap : 0 < s.capacity := hcond.1
  have hhead : s.head < s.capacity := hcond.2.1
  have hstep_eq : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
    unfold step; simp [hcond]
  refine ⟨s.buf s.head, ?_, ?_⟩
  · rw [hstep_eq]
  · have h_snd : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by rw [hstep_eq]
    rw [h_snd]
    unfold contents slot
    simp only
    have hmap_eq : List.map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) (List.range (s.count - 1))
        = List.map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) (List.range (s.count - 1)) := by
      apply List.map_congr_left
      intro i hi
      congr 1
      have := slot_succ_eq s hcap i
      rw [this]
    have h_range_succ : List.range s.count = 0 :: List.map (· + 1) (List.range (s.count - 1)) := by
      cases hcnt : s.count with
      | zero => omega
      | succ n =>
        simp only [Nat.succ_sub_succ, Nat.sub_zero]
        rw [List.range_succ_eq_map]
    have h_contents_s : List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count)
        = s.buf ((s.head + 0) % s.capacity) :: List.map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) (List.range (s.count - 1)) := by
      rw [h_range_succ, List.map_cons, List.map_map]
      simp
    have h0 : s.buf ((s.head + 0) % s.capacity) = s.buf s.head := by
      have : (s.head + 0) % s.capacity = s.head := Nat.mod_eq_of_lt hhead
      rw [this]
    rw [h_contents_s, h0, hmap_eq]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | enqueue x =>
      by_cases hrej : (step s (Op.enqueue x)).1 = .rejected
      · have h_state : step s (Op.enqueue x) = (.rejected, s) := by
          unfold step
          have hc : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
            intro hc
            have : (step s (Op.enqueue x)).1 = .ok := by unfold step; simp [hc]
            rw [this] at hrej; contradiction
          simp [hc]
        have h_run : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, .rejected) :: (run step s ops).1, (run step s ops).2) := by
          simp [run, h_state]
        have h_in : inflow (run step s (Op.enqueue x :: ops)).1 = inflow (run step s ops).1 := by
          rw [h_run]; simp [inflow, inflowOf]
        have h_out : outflow (run step s (Op.enqueue x :: ops)).1 = outflow (run step s ops).1 := by
          rw [h_run]; simp [outflow, outflowOf]
        rw [h_in, h_out, h_run]
        simp
        exact ih s
      · have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
          by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
          · exact hc
          · have hrej2 : (step s (Op.enqueue x)).1 = .rejected := by unfold step; simp [hc]
            exact absurd hrej2 hrej
        have hstep_eq : step s (Op.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
          unfold step slot; simp [hcond]
        have h_ok : (step s (Op.enqueue x)).1 = .ok := by rw [hstep_eq]
        have h_enqueue_contents : contents (step s (Op.enqueue x)).2 = contents s ++ [x] :=
          req_enqueue_contents (s:=s) (x:=x) (by simp [h_ok])
        have h_run : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, .ok) :: (run step (step s (Op.enqueue x)).2 ops).1, (run step (step s (Op.enqueue x)).2 ops).2) := by
          simp [run, hstep_eq]
        have h_in : inflow (run step s (Op.enqueue x :: ops)).1 = [x] ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by
          rw [h_run]; simp [inflow, inflowOf]
        have h_out : outflow (run step s (Op.enqueue x :: ops)).1 = outflow (run step (step s (Op.enqueue x)).2 ops).1 := by
          rw [h_run]; simp [outflow, outflowOf]
        have ih_eq := ih (step s (Op.enqueue x)).2
        rw [h_in, h_out, h_run]
        simp only
        have h1 : contents s ++ ([x] ++ inflow (run step (step s (Op.enqueue x)).2 ops).1) = (contents s ++ [x]) ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by simp [List.append_assoc]
        rw [h1, ← h_enqueue_contents]
        exact ih_eq
    | dequeue =>
      by_cases hrej : (step s Op.dequeue).1 = .rejected
      · have h_state : step s Op.dequeue = (.rejected, s) := by
          unfold step
          have hc : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
            intro hc
            have : (step s Op.dequeue).1 = .got (s.buf s.head) := by unfold step; simp [hc]
            rw [this] at hrej; contradiction
          simp [hc]
        have h_run : run step s (Op.dequeue :: ops) = ((Op.dequeue, .rejected) :: (run step s ops).1, (run step s ops).2) := by
          simp [run, h_state]
        have h_in : inflow (run step s (Op.dequeue :: ops)).1 = inflow (run step s ops).1 := by
          rw [h_run]; simp [inflow, inflowOf]
        have h_out : outflow (run step s (Op.dequeue :: ops)).1 = outflow (run step s ops).1 := by
          rw [h_run]; simp [outflow, outflowOf]
        rw [h_in, h_out, h_run]
        simp
        exact ih s
      · have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
          by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
          · exact hc
          · have hrej2 : (step s Op.dequeue).1 = .rejected := by unfold step; simp [hc]
            exact absurd hrej2 hrej
        have hstep_eq : step s Op.dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
          unfold step; simp [hcond]
        have h_got : (step s Op.dequeue).1 = .got (s.buf s.head) := by rw [hstep_eq]
        have h_deq_contents : contents s = s.buf s.head :: contents (step s Op.dequeue).2 := by
          have h := req_dequeue_contents (s:=s) (by simp [h_got])
          obtain ⟨y, hy1, hy2⟩ := h
          have hy_eq : y = s.buf s.head := by
            have h' : Outcome.got y = Outcome.got (s.buf s.head) := by rw [← hy1, h_got]
            injection h'
          rw [hy_eq] at hy2
          exact hy2
        have h_run : run step s (Op.dequeue :: ops) = ((Op.dequeue, .got (s.buf s.head)) :: (run step (step s Op.dequeue).2 ops).1, (run step (step s Op.dequeue).2 ops).2) := by
          simp [run, hstep_eq]
        have h_in : inflow (run step s (Op.dequeue :: ops)).1 = inflow (run step (step s Op.dequeue).2 ops).1 := by
          rw [h_run]; simp [inflow, inflowOf]
        have h_out : outflow (run step s (Op.dequeue :: ops)).1 = [s.buf s.head] ++ outflow (run step (step s Op.dequeue).2 ops).1 := by
          rw [h_run]; simp [outflow, outflowOf]
        have ih_eq := ih (step s Op.dequeue).2
        rw [h_in, h_out, h_run, h_deq_contents]
        have h_assoc : (s.buf s.head :: contents (step s Op.dequeue).2) ++ inflow (run step (step s Op.dequeue).2 ops).1 = [s.buf s.head] ++ (contents (step s Op.dequeue).2 ++ inflow (run step (step s Op.dequeue).2 ops).1) := by simp
        rw [h_assoc, ih_eq, List.append_assoc]

end RingBuffer
