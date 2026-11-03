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

private theorem enqueue_cond_of_ok {s : State} {x : Nat} (h : (step s (.enqueue x)).1 ≠ .rejected) :
    0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
  unfold step at h
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · exact hc
  · simp [hc] at h

private theorem dequeue_cond_of_ok {s : State} (h : (step s .dequeue).1 ≠ .rejected) :
    0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
  unfold step at h
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · exact hc
  · simp [hc] at h

private theorem tail_ne_slot {cap head count i : Nat} (hcap : 0 < cap) (hi : i < count) (hcnt : count < cap) :
    (head + i) % cap ≠ (head + count) % cap := by
  intro heq
  have hb_pos : 0 < count - i := Nat.sub_pos_of_lt hi
  have hb_lt : count - i < cap := Nat.lt_of_le_of_lt (Nat.sub_le count i) hcnt
  have hi_le : i ≤ count := Nat.le_of_lt hi
  have h_add : i + (count - i) = count := Nat.add_sub_cancel' hi_le
  have ha_eq : head + count = head + i + (count - i) := by
    calc head + count = head + (i + (count - i)) := by rw [h_add]
      _ = head + i + (count - i) := by rw [Nat.add_assoc]
  rw [ha_eq] at heq
  have h_add_mod : (head + i + (count - i)) % cap = ((head + i) % cap + (count - i) % cap) % cap :=
    Nat.add_mod (head + i) (count - i) cap
  rw [h_add_mod] at heq
  have hb_mod : (count - i) % cap = count - i := Nat.mod_eq_of_lt hb_lt
  rw [hb_mod] at heq
  have hk_lt : (head + i) % cap < cap := Nat.mod_lt _ hcap
  have hlt_or_ge : (head + i) % cap + (count - i) < cap ∨ cap ≤ (head + i) % cap + (count - i) := Nat.lt_or_ge _ _
  rcases hlt_or_ge with hlt | hge
  · have hmod : ((head + i) % cap + (count - i)) % cap = (head + i) % cap + (count - i) := Nat.mod_eq_of_lt hlt
    rw [hmod] at heq
    have hd0 : count - i = 0 := by
      have h_eq : (head + i) % cap + (count - i) = (head + i) % cap + 0 := by
        rw [Nat.add_zero]
        exact heq.symm
      exact Nat.add_left_cancel h_eq
    rw [hd0] at hb_pos
    exact Nat.lt_irrefl 0 hb_pos
  · have h_lt2 : (head + i) % cap + (count - i) < cap + cap := Nat.add_lt_add hk_lt hb_lt
    have hsub_lt : (head + i) % cap + (count - i) - cap < cap := by
      rw [Nat.sub_lt_iff_lt_add hge]
      exact h_lt2
    have h1 : (head + i) % cap + (count - i) = cap + ((head + i) % cap + (count - i) - cap) := by
      rw [Nat.add_comm cap ((head + i) % cap + (count - i) - cap)]
      exact (Nat.sub_add_cancel hge).symm
    have hmod : ((head + i) % cap + (count - i)) % cap = (head + i) % cap + (count - i) - cap := by
      have h2 : (cap + ((head + i) % cap + (count - i) - cap)) % cap = ((head + i) % cap + (count - i) - cap) % cap := by
        simp [Nat.add_mod_left]
      rw [← h1] at h2
      rw [Nat.mod_eq_of_lt hsub_lt] at h2
      exact h2
    rw [hmod] at heq
    have h_eq_cap : cap = count - i := by
      have h_sub : ((head + i) % cap + (count - i) - cap) + cap = (head + i) % cap + (count - i) := Nat.sub_add_cancel hge
      have h_rw : (head + i) % cap + cap = (head + i) % cap + (count - i) := by
        have htemp : (head + i) % cap + cap = ((head + i) % cap + (count - i) - cap) + cap := by rw [← heq]
        rw [htemp, h_sub]
      exact Nat.add_left_cancel h_rw
    have hlt_eq : cap < cap := by rw [← h_eq_cap] at hb_lt; exact hb_lt
    exact Nat.lt_irrefl cap hlt_eq

private theorem contents_enqueue_aux (s : State) (x : Nat) (h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) :
    contents { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 } = contents s ++ [x] := by
  unfold contents slot
  have hr : List.range (s.count + 1) = List.range s.count ++ [s.count] := by
    rw [List.range_succ]
  rw [hr, List.map_append]
  have h1 : ∀ i, i ∈ List.range s.count → (if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)) = s.buf ((s.head + i) % s.capacity) := by
    intro i hi
    have hi_lt : i < s.count := List.mem_range.mp hi
    have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity :=
      tail_ne_slot h.1 hi_lt h.2.2
    simp [hne]
  have hmap_eq : List.map (fun i => if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)) (List.range s.count)
      = List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count) := by
    apply List.map_congr_left
    intro i hi
    exact h1 i hi
  rw [hmap_eq]
  simp [List.map_append]

private theorem range_succ_eq_map_aux (n : Nat) : List.range (n + 1) = 0 :: List.map Nat.succ (List.range n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by rw [List.range_succ]
      _ = (0 :: List.map Nat.succ (List.range n)) ++ [n + 1] := by rw [ih]
      _ = 0 :: (List.map Nat.succ (List.range n) ++ [Nat.succ n]) := rfl
      _ = 0 :: List.map Nat.succ (List.range n ++ [n]) := by simp [List.map_append]
      _ = 0 :: List.map Nat.succ (List.range (n + 1)) := by rw [← List.range_succ]

private theorem contents_dequeue_aux (s : State) (h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) :
    contents s = s.buf s.head :: contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
  unfold contents slot
  simp only
  have hpos : 0 < s.count := h.2.2.2
  have hle1 : 1 ≤ s.count := Nat.succ_le_of_lt hpos
  have hcnt_eq : s.count = (s.count - 1) + 1 := (Nat.sub_add_cancel hle1).symm
  have h0 : (s.head + 0) % s.capacity = s.head := Nat.mod_eq_of_lt h.2.1
  have hrw0 : List.range ((s.count - 1) + 1) = 0 :: List.map Nat.succ (List.range (s.count - 1)) :=
    range_succ_eq_map_aux (s.count - 1)
  have hrw : List.range s.count = 0 :: List.map Nat.succ (List.range (s.count - 1)) := by
    calc List.range s.count = List.range ((s.count - 1) + 1) := by rw [← hcnt_eq]
      _ = 0 :: List.map Nat.succ (List.range (s.count - 1)) := hrw0
  rw [hrw]
  simp only [List.map_cons]
  rw [h0]
  congr 1
  have hmap : List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.map Nat.succ (List.range (s.count - 1))) =
      List.map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) (List.range (s.count - 1)) := by
    simp
  rw [hmap]
  apply List.map_congr_left
  intro i hi
  have hi_lt_cap : i < s.capacity := by
    have him : i < s.count - 1 := List.mem_range.mp hi
    omega
  have hi_mod : i % s.capacity = i := Nat.mod_eq_of_lt hi_lt_cap
  show s.buf ((s.head + (i + 1)) % s.capacity) = s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity)
  congr 1
  have h1' : s.head + (i + 1) = s.head + 1 + i := by omega
  rw [h1']
  have h_add_mod : (s.head + 1 + i) % s.capacity = ((s.head + 1) % s.capacity + i % s.capacity) % s.capacity := by
    exact Nat.add_mod (s.head + 1) i s.capacity
  rw [h_add_mod, hi_mod]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  unfold Valid at hV
  unfold step
  cases op with
  | enqueue x =>
    have h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := ⟨hV.1.1, hV.1.2.1, hV.2⟩
    simp [h]
  | dequeue =>
    have h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := ⟨hV.1.1, hV.1.2.1, hV.1.2.2, hV.2⟩
    simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv
  unfold step
  cases op with
  | enqueue x =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro h
      apply hInv
      constructor
      · exact ⟨h.1, h.2.1, Nat.le_of_lt h.2.2⟩
      · exact h.2.2
    simp [hcond]
  | dequeue =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro h
      apply hInv
      exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩
    simp [hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hW
  unfold WellFormed at hW ⊢
  unfold step
  cases op with
  | enqueue x =>
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · simp only [h]
      exact ⟨h.1, h.2.1, Nat.succ_le_of_lt h.2.2⟩
    · simp only [h]; exact hW
  | dequeue =>
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · simp only [h]
      exact ⟨h.1, Nat.mod_lt _ h.1, Nat.le_trans (Nat.sub_le _ _) h.2.2.1⟩
    · simp only [h]; exact hW

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hOk
  have h := enqueue_cond_of_ok (s:=s) (x:=x) hOk
  unfold step slot
  simp [h]

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hOk
  have h := dequeue_cond_of_ok (s:=s) hOk
  unfold step
  simp [h]

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hOk
  have h := enqueue_cond_of_ok (s:=s) (x:=x) hOk
  have hstep : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
    unfold step; simp [h]
  have hcont := contents_enqueue_aux s x h
  rw [hstep]
  exact hcont

theorem req_dequeue_contents : DequeueContents step := by
  intro s hOk
  have h := dequeue_cond_of_ok (s:=s) hOk
  have hstep : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
    unfold step; simp [h]
  refine ⟨s.buf s.head, ?_, ?_⟩
  · rw [hstep]
  · have hc := contents_dequeue_aux s h
    rw [hstep]
    exact hc

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons hd tl ih =>
    have hRun : run step s (hd :: tl) = ((hd, (step s hd).1) :: (run step (step s hd).2 tl).1, (run step (step s hd).2 tl).2) := rfl
    cases hd with
    | enqueue x =>
      by_cases hV : Valid s (.enqueue x)
      · have hSucceeds : (step s (.enqueue x)).1 ≠ .rejected := req_valid_succeeds s (.enqueue x) hV
        have hCont := req_enqueue_contents (s:=s) (x:=x) hSucceeds
        have hOk : (step s (.enqueue x)).1 = .ok := by
          have := req_enqueue_effects (s:=s) (x:=x) hSucceeds
          rw [this]
        have ih' := ih (step s (.enqueue x)).2
        have h1 : run step s (Op.enqueue x :: tl) = ((Op.enqueue x, .ok) :: (run step (step s (.enqueue x)).2 tl).1, (run step (step s (.enqueue x)).2 tl).2) := by rw [hRun, hOk]
        rw [h1]
        simp only [inflow, outflow, List.flatMap_cons, inflowOf, outflowOf, hOk]
        calc contents s ++ ([x] ++ inflow (run step (step s (Op.enqueue x)).2 tl).1)
            = (contents s ++ [x]) ++ inflow (run step (step s (Op.enqueue x)).2 tl).1 := by simp
          _ = contents (step s (Op.enqueue x)).2 ++ inflow (run step (step s (Op.enqueue x)).2 tl).1 := by rw [hCont]
          _ = outflow (run step (step s (Op.enqueue x)).2 tl).1 ++ contents (run step (step s (Op.enqueue x)).2 tl).2 := ih'
      · have hStep : step s (.enqueue x) = (.rejected, s) := req_invalid_noop s (.enqueue x) hV
        have h1 : run step s (Op.enqueue x :: tl) = ((Op.enqueue x, .rejected) :: (run step s tl).1, (run step s tl).2) := by rw [hRun, hStep]
        rw [h1]
        simp [inflow, outflow, inflowOf, outflowOf]
        exact ih s
    | dequeue =>
      by_cases hV : Valid s .dequeue
      · have hSucceeds : (step s .dequeue).1 ≠ .rejected := req_valid_succeeds s .dequeue hV
        obtain ⟨x, hxGot, hxCont⟩ := req_dequeue_contents (s:=s) hSucceeds
        have ih' := ih (step s .dequeue).2
        have h1 : run step s (Op.dequeue :: tl) = ((Op.dequeue, .got x) :: (run step (step s .dequeue).2 tl).1, (run step (step s .dequeue).2 tl).2) := by rw [hRun, hxGot]
        rw [h1]
        simp [inflow, outflow, inflowOf, outflowOf, hxGot]
        calc contents s ++ inflow (run step (step s .dequeue).2 tl).1
            = (x :: contents (step s .dequeue).2) ++ inflow (run step (step s .dequeue).2 tl).1 := by rw [hxCont]
          _ = [x] ++ (contents (step s .dequeue).2 ++ inflow (run step (step s .dequeue).2 tl).1) := by simp
          _ = [x] ++ (outflow (run step (step s .dequeue).2 tl).1 ++ contents (run step (step s .dequeue).2 tl).2) := by rw [ih']
      · have hStep : step s .dequeue = (.rejected, s) := req_invalid_noop s .dequeue hV
        have h1 : run step s (Op.dequeue :: tl) = ((Op.dequeue, .rejected) :: (run step s tl).1, (run step s tl).2) := by rw [hRun, hStep]
        rw [h1]
        simp [inflow, outflow, inflowOf, outflowOf]
        exact ih s

end RingBuffer
