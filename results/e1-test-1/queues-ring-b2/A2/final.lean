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

theorem probe3 (s : State) (x : Nat) (h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) : (step s (Op.enqueue x)).1 ≠ .rejected := by
  simp [step, h]

theorem mytest_invalid : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro hc
      apply h
      obtain ⟨hc0, hh, hlt⟩ := hc
      exact ⟨⟨hc0, hh, Nat.le_of_lt hlt⟩, hlt⟩
    simp [step, hcond]
  | dequeue =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hc
      apply h
      obtain ⟨hc0, hh, hle, hpos⟩ := hc
      exact ⟨⟨hc0, hh, hle⟩, hpos⟩
    simp [step, hcond]

theorem tmp_check_range : True := by
  have h1 : List.range 3 = [0,1,2] := rfl
  trivial
#check @List.range_succ
#check @List.map_append

theorem tmp_probe_lemmas : True := by
  trivial
#check @Nat.div_add_mod
#check @Nat.mod_add_div
#check @Nat.div_le_div_right
#check @Nat.mod_eq_of_lt
#check @Nat.add_mod
#check @Nat.mul_comm

theorem tmp_probe2 : True := by
  have h1 : ∀ (a b : Nat), (a + b) % b = a % b := by intro a b; exact Nat.add_mod_right a b
  have h2 : ∀ (a n : Nat), a % n % n = a % n := by intro a n; exact Nat.mod_mod a n
  trivial

theorem tmp_mod_sub3 (a cap : Nat) (h1 : a < 2 * cap) (h2 : cap ≤ a) : a % cap = a - cap := by
  obtain ⟨k, rfl⟩ : ∃ k, a = cap + k := ⟨a - cap, by omega⟩
  have hk : k < cap := by omega
  have hkm : k % cap = k := Nat.mod_eq_of_lt hk
  have h1 : (cap + k) % cap = k % cap := by
    rw [Nat.add_comm cap k, Nat.add_mod_right]
  rw [h1, hkm]
  omega

theorem tmp_list_map_range_succ (f : Nat → Nat) (n : Nat) :
    ((List.range (n + 1)).map f) = f 0 :: ((List.range n).map (fun i => f (i + 1))) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hr1 : List.range (k + 1 + 1) = List.range (k + 1) ++ [k + 1] := List.range_succ
    have hr2 : List.range (k + 1) = List.range k ++ [k] := List.range_succ
    rw [hr1, List.map_append]
    rw [ih]
    rw [hr2, List.map_append]
    simp

theorem tmp_slot_shift2 (h i cap : Nat) :
    ((h + 1) % cap + i) % cap = (h + (i + 1)) % cap := by
  have e1 : ((h + 1) % cap + i) % cap = (h + 1 + i) % cap := Nat.mod_add_mod _ _ _
  rw [e1]
  congr 1
  omega

theorem hb_slot_ne_aux (h i cnt cap : Nat) (_hc0 : 0 < cap) (hh : h < cap) (hlt : cnt < cap) (hi : i < cnt) : (h + i) % cap ≠ (h + cnt) % cap := by
  have ha_lt : h + i < 2 * cap := by omega
  have hb_lt : h + cnt < 2 * cap := by omega
  have hab : h + i < h + cnt := by omega
  intro heq
  by_cases ha : h + i < cap
  · have ha_mod : (h + i) % cap = h + i := Nat.mod_eq_of_lt ha
    by_cases hb : h + cnt < cap
    · have hb_mod : (h + cnt) % cap = h + cnt := Nat.mod_eq_of_lt hb
      rw [ha_mod, hb_mod] at heq
      omega
    · have hb_ge : cap ≤ h + cnt := by omega
      have hb_mod : (h + cnt) % cap = h + cnt - cap := tmp_mod_sub3 _ _ hb_lt hb_ge
      rw [ha_mod, hb_mod] at heq
      omega
  · have ha_ge : cap ≤ h + i := by omega
    have ha_mod : (h + i) % cap = h + i - cap := tmp_mod_sub3 _ _ ha_lt ha_ge
    have hb_ge : cap ≤ h + cnt := by omega
    have hb_mod : (h + cnt) % cap = h + cnt - cap := tmp_mod_sub3 _ _ hb_lt hb_ge
    rw [ha_mod, hb_mod] at heq
    omega

theorem hb_enq_contents_aux (s : State) (x : Nat)
    (hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) :
    contents { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 } = contents s ++ [x] := by
  obtain ⟨hc0, hh, hlt⟩ := hcond
  have hrw : List.range (s.count + 1) = List.range s.count ++ [s.count] := List.range_succ
  unfold contents slot
  simp only
  rw [hrw, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi_lt : i < s.count := (List.mem_range.mp hi)
    have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity :=
      hb_slot_ne_aux s.head i s.count s.capacity hc0 hh hlt hi_lt
    simp only [hne, ↓reduceIte]
  · simp only [List.map_cons, List.map_nil]
    simp only [↓reduceIte]

theorem hb_deq_contents_aux (s : State)
    (hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) :
    contents s = s.buf s.head :: contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
  obtain ⟨hc0, hh, hle, hpos⟩ := hcond
  obtain ⟨k, hk⟩ : ∃ k, s.count = k + 1 := ⟨s.count - 1, by omega⟩
  have hhead : (s.head + 0) % s.capacity = s.head := by
    have h1 : s.head + 0 = s.head := Nat.add_zero _
    rw [h1]
    exact Nat.mod_eq_of_lt hh
  have hfun : (fun i => s.buf ((s.head + (i + 1)) % s.capacity))
      = (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) := by
    funext i
    congr 1
    exact (tmp_slot_shift2 s.head i s.capacity).symm
  have hsplit := tmp_list_map_range_succ (fun i => s.buf ((s.head + i) % s.capacity)) k
  have hc1 : contents s = ((List.range (k + 1)).map (fun i => s.buf ((s.head + i) % s.capacity))) := by
    simp [contents, slot, hk]
  have hc2 : contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }
      = ((List.range k).map (fun i => s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity))) := by
    have hcount : s.count - 1 = k := by omega
    simp [contents, slot, hcount]
  rw [hc1, hc2]
  rw [hsplit]
  simp only [hhead]
  rw [hfun]

theorem hb_single_aux (s : State) (op : Op) :
    contents s ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
  cases op with
  | enqueue x =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · have hs : step s (Op.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
        simp [step, hcond]
      have hcc := hb_enq_contents_aux s x hcond
      rw [hs]
      simp only [inflowOf, outflowOf]
      simp [hcc]
    · have hs : step s (Op.enqueue x) = (.rejected, s) := by simp [step, hcond]
      rw [hs]
      simp [inflowOf, outflowOf]
  | dequeue =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · have hs : step s Op.dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
        simp [step, hcond]
      have hcc := hb_deq_contents_aux s hcond
      rw [hs]
      simp only [inflowOf, outflowOf]
      simp [hcc]
    · have hs : step s Op.dequeue = (.rejected, s) := by simp [step, hcond]
      rw [hs]
      simp [inflowOf, outflowOf]

theorem hb_inflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (p :: t) = inflowOf p ++ inflow t := by
  simp [inflow]

theorem hb_outflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (p :: t) = outflowOf p ++ outflow t := by
  simp [outflow]
#check @List.flatMap_cons
#check inflow
#check outflow
#check run

theorem hb_run_nil (s : State) : run step s [] = ([], s) := rfl

theorem hb_run_cons_fst (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
  simp only [run]

theorem hb_run_cons_snd (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
  simp only [run]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    obtain ⟨⟨hc0, hh, hle⟩, hlt⟩ := h
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := ⟨hc0, hh, hlt⟩
    simp [step, hcond]
  | dequeue =>
    simp only [Valid, WellFormed] at h
    obtain ⟨⟨hc0, hh, hle⟩, hpos⟩ := h
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := ⟨hc0, hh, hle, hpos⟩
    simp [step, hcond]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro hc
      apply h
      obtain ⟨hc0, hh, hlt⟩ := hc
      exact ⟨⟨hc0, hh, Nat.le_of_lt hlt⟩, hlt⟩
    simp [step, hcond]
  | dequeue =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hc
      apply h
      obtain ⟨hc0, hh, hle, hpos⟩ := hc
      exact ⟨⟨hc0, hh, hle⟩, hpos⟩
    simp [step, hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op h
  obtain ⟨hc0, hh, hle⟩ := h
  cases op with
  | enqueue x =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · have hs : step s (Op.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
        simp [step, hcond]
      rw [hs]
      simp only [WellFormed]
      exact ⟨hc0, hh, by omega⟩
    · have hs : step s (Op.enqueue x) = (.rejected, s) := by simp [step, hcond]
      rw [hs]
      simp only [WellFormed]
      exact ⟨hc0, hh, hle⟩
  | dequeue =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · have hs : step s Op.dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
        simp [step, hcond]
      rw [hs]
      simp only [WellFormed]
      refine ⟨hc0, Nat.mod_lt _ hc0, by omega⟩
    · have hs : step s Op.dequeue = (.rejected, s) := by simp [step, hcond]
      rw [hs]
      simp only [WellFormed]
      exact ⟨hc0, hh, hle⟩

theorem req_enqueue_effects  : EnqueueEffects step := by
  intro s x hne
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · have hs : step s (Op.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
      simp [step, hcond]
    have hslot : slot s s.count = (s.head + s.count) % s.capacity := rfl
    rw [← hslot] at hs
    exact hs
  · simp [step, hcond] at hne

theorem req_dequeue_effects  : DequeueEffects step := by
  intro s hne
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · simp [step, hcond]
  · simp [step, hcond] at hne

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · have hs : step s (Op.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
      simp [step, hcond]
    have hcc := hb_enq_contents_aux s x hcond
    have hstep : (step s (Op.enqueue x)).2 = { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 } := by rw [hs]
    rw [hstep]
    exact hcc
  · simp [step, hcond] at hne

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · have hs : step s Op.dequeue =
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
      simp [step, hcond]
    obtain ⟨hc0, hh, hle, hpos⟩ := hcond
    obtain ⟨k, hk⟩ : ∃ k, s.count = k + 1 := ⟨s.count - 1, by omega⟩
    refine ⟨s.buf s.head, by rw [hs], ?_⟩
    rw [hs]
    simp only
    have hhead : (s.head + 0) % s.capacity = s.head := by
      have h1 : s.head + 0 = s.head := Nat.add_zero _
      rw [h1]
      exact Nat.mod_eq_of_lt hh
    have hfun : (fun i => s.buf ((s.head + (i + 1)) % s.capacity))
        = (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) := by
      funext i
      congr 1
      exact (tmp_slot_shift2 s.head i s.capacity).symm
    have hsplit := tmp_list_map_range_succ (fun i => s.buf ((s.head + i) % s.capacity)) k
    have hstep : (fun i => s.buf ((s.head + (i + 1)) % s.capacity))
        = (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) := hfun
    have hc1 : contents s = ((List.range (k + 1)).map (fun i => s.buf ((s.head + i) % s.capacity))) := by
      simp [contents, slot, hk]
    have hc2 : contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }
        = ((List.range k).map (fun i => s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity))) := by
      have hcount : s.count - 1 = k := by omega
      simp [contents, slot, hcount]
    rw [hc1, hc2]
    rw [hsplit]
    simp only [hhead]
    rw [hfun]
  · simp [step, hcond] at hne

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hsingle := hb_single_aux s op
    have hih := ih (step s op).2
    have hfst : (run step s (op :: ops)).1
        = (op, (step s op).1) :: (run step (step s op).2 ops).1 := hb_run_cons_fst s op ops
    have hsnd : (run step s (op :: ops)).2
        = (run step (step s op).2 ops).2 := hb_run_cons_snd s op ops
    rw [hfst, hsnd]
    rw [hb_inflow_cons, hb_outflow_cons]
    calc contents s ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (contents s ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ contents (step s op).2) ++ inflow (run step (step s op).2 ops).1 := by rw [hsingle]
      _ = outflowOf (op, (step s op).1) ++ (contents (step s op).2 ++ inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ contents (run step (step s op).2 ops).2) := by rw [hih]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ contents (run step (step s op).2 ops).2 := by rw [List.append_assoc]

end RingBuffer
