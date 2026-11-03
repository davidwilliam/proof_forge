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

theorem req_invalid_noop_aux : InvalidNoop step := by
  intro s op hInv
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at hInv
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro ⟨hcap, hhead, hlt⟩
      apply hInv
      constructor
      · exact ⟨hcap, hhead, Nat.le_of_lt hlt⟩
      · exact hlt
    unfold step
    simp [hcond]
  | dequeue =>
    simp only [Valid, WellFormed] at hInv
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro ⟨hcap, hhead, hle, hpos⟩
      apply hInv
      exact ⟨⟨hcap, hhead, hle⟩, hpos⟩
    unfold step
    simp [hcond]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | enqueue x =>
    simp only [Valid] at hV
    obtain ⟨⟨hcap, hhead, hle⟩, hlt⟩ := hV
    show (step s (Op.enqueue x)).1 ≠ .rejected
    unfold step
    simp [hcap, hhead, hlt]
  | dequeue =>
    simp only [Valid] at hV
    obtain ⟨⟨hcap, hhead, hle⟩, hpos⟩ := hV
    show (step s Op.dequeue).1 ≠ .rejected
    unfold step
    simp [hcap, hhead, hle, hpos]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at hInv
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro ⟨hcap, hhead, hlt⟩
      apply hInv
      constructor
      · exact ⟨hcap, hhead, Nat.le_of_lt hlt⟩
      · exact hlt
    unfold step
    simp [hcond]
  | dequeue =>
    simp only [Valid, WellFormed] at hInv
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro ⟨hcap, hhead, hle, hpos⟩
      apply hInv
      exact ⟨⟨hcap, hhead, hle⟩, hpos⟩
    unfold step
    simp [hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hWF
  obtain ⟨hcap, hhead, hcnt⟩ := hWF
  cases op with
  | enqueue x =>
    unfold step
    by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · simp only [if_pos hcond]
      simp only [WellFormed]
      exact ⟨hcap, hhead, by omega⟩
    · simp only [if_neg hcond]
      exact ⟨hcap, hhead, hcnt⟩
  | dequeue =>
    unfold step
    by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · simp only [if_pos hcond]
      simp only [WellFormed]
      exact ⟨hcap, Nat.mod_lt _ hcap, by omega⟩
    · simp only [if_neg hcond]
      exact ⟨hcap, hhead, hcnt⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  -- step for enqueue is if cond then ...
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · simp [hcond] at h ⊢
    -- slot = tail
    rfl
  · simp [hcond] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  unfold step at h ⊢
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · simp [hcond] at h ⊢
  · simp [hcond] at h

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x h
  have hEff := req_enqueue_effects s x h
  have hCond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact hc
    · have hStep : step s (Op.enqueue x) = (Outcome.rejected, s) := by
        unfold step
        simp [hc]
      rw [hStep] at h
      simp at h
  obtain ⟨hcap, hhead, hlt⟩ := hCond
  rw [hEff]
  simp only
  unfold contents slot
  have hRange : List.range (s.count + 1) = List.range s.count ++ [s.count] := by
    simp [List.range_succ]
  rw [hRange]
  rw [List.map_append]
  have hMapSingleton : List.map (fun i => if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)) [s.count] = [x] := by
    simp
  rw [hMapSingleton]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := by
    intro heq
    have hmA : (s.head + i) % s.capacity = if s.head + i < s.capacity then s.head + i else s.head + i - s.capacity := by
      by_cases hh : s.head + i < s.capacity
      · simp [hh, Nat.mod_eq_of_lt hh]
      · have h2 : s.head + i - s.capacity < s.capacity := by omega
        have heq2 : s.head + i = (s.head + i - s.capacity) + s.capacity := by omega
        have : (s.head + i - s.capacity + s.capacity) % s.capacity = (s.head + i - s.capacity) % s.capacity := Nat.add_mod_right _ _
        rw [← heq2] at this
        rw [Nat.mod_eq_of_lt h2] at this
        simp [hh, this]
    have hmB : (s.head + s.count) % s.capacity = if s.head + s.count < s.capacity then s.head + s.count else s.head + s.count - s.capacity := by
      by_cases hh : s.head + s.count < s.capacity
      · simp [hh, Nat.mod_eq_of_lt hh]
      · have h2 : s.head + s.count - s.capacity < s.capacity := by omega
        have heq2 : s.head + s.count = (s.head + s.count - s.capacity) + s.capacity := by omega
        have : (s.head + s.count - s.capacity + s.capacity) % s.capacity = (s.head + s.count - s.capacity) % s.capacity := Nat.add_mod_right _ _
        rw [← heq2] at this
        rw [Nat.mod_eq_of_lt h2] at this
        simp [hh, this]
    rw [hmA, hmB] at heq
    by_cases ha : s.head + i < s.capacity <;> by_cases hb : s.head + s.count < s.capacity <;> simp [ha, hb] at heq <;> omega
  simp [hne]

theorem req_dequeue_contents : DequeueContents step := by
  intro s h
  have hEff := req_dequeue_effects s h
  have hCond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · exact hc
    · have hStep : step s Op.dequeue = (Outcome.rejected, s) := by
        unfold step
        simp [hc]
      rw [hStep] at h
      simp at h
  obtain ⟨hcap, hhead, hle, hpos⟩ := hCond
  rw [hEff]
  refine ⟨s.buf s.head, rfl, ?_⟩
  unfold contents slot
  have hsucc : s.count = (s.count - 1) + 1 := by omega
  show List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count) =
    s.buf s.head :: List.map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) (List.range (s.count - 1))
  rw [hsucc]
  have hmap : ∀ k (f : Nat → Nat), List.map f (List.range (k+1)) = f 0 :: List.map (fun i => f (i+1)) (List.range k) := by
    intro k f
    have : List.range (k+1) = 0 :: List.map (fun x => x+1) (List.range k) := by
      simp [List.range_succ_eq_map]
    rw [this]
    simp
  rw [hmap (s.count - 1) (fun i => s.buf ((s.head + i) % s.capacity))]
  simp only [Nat.add_zero, Nat.mod_eq_of_lt hhead]
  congr 1
  apply List.map_congr_left
  intro i hi
  have h1 : s.head + (i + 1) = s.head + 1 + i := by omega
  have h2 : (s.head + (i+1)) % s.capacity = (s.head + 1 + i) % s.capacity := by rw [h1]
  have h3 : ((s.head + 1) % s.capacity + i) % s.capacity = (s.head + 1 + i) % s.capacity := Nat.mod_add_mod _ _ _
  rw [h2, h3]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | enqueue x =>
      by_cases hRej : (step s (.enqueue x)).1 = .rejected
      · have hNoop : step s (.enqueue x) = (.rejected, s) := by
          have hInv : ¬ Valid s (.enqueue x) := by
            intro hV; have hsuc := req_valid_succeeds s (.enqueue x) hV; simp [hRej] at hsuc
          exact req_invalid_noop s (.enqueue x) hInv
        have h1 : inflow ((Op.enqueue x, .rejected) :: (run step s ops).1) = inflow (run step s ops).1 := by simp [inflow, inflowOf]
        have h2 : outflow ((Op.enqueue x, .rejected) :: (run step s ops).1) = outflow (run step s ops).1 := by simp [outflow, outflowOf]
        simp [run, hNoop, h1, h2, ih]
      · have hNotRej : (step s (.enqueue x)).1 ≠ .rejected := hRej
        have hCont := req_enqueue_contents s x hNotRej
        have hEff := req_enqueue_effects s x hNotRej
        have hOk : (step s (.enqueue x)).1 = .ok := by rw [hEff]
        have h1 : inflow ((Op.enqueue x, .ok) :: (run step (step s (.enqueue x)).2 ops).1) = [x] ++ inflow (run step (step s (.enqueue x)).2 ops).1 := by simp [inflow, inflowOf]
        have h2 : outflow ((Op.enqueue x, .ok) :: (run step (step s (.enqueue x)).2 ops).1) = outflow (run step (step s (.enqueue x)).2 ops).1 := by simp [outflow, outflowOf]
        simp [run, hOk, h1, h2]
        have ih' := ih (s := (step s (.enqueue x)).2)
        calc contents s ++ ([x] ++ inflow (run step (step s (.enqueue x)).2 ops).1)
            = (contents s ++ [x]) ++ inflow (run step (step s (.enqueue x)).2 ops).1 := by simp [List.append_assoc]
          _ = contents (step s (.enqueue x)).2 ++ inflow (run step (step s (.enqueue x)).2 ops).1 := by rw [hCont]
          _ = outflow (run step (step s (.enqueue x)).2 ops).1 ++ contents (run step (step s (.enqueue x)).2 ops).2 := ih'
    | dequeue =>
      by_cases hRej : (step s .dequeue).1 = .rejected
      · have hNoop : step s .dequeue = (.rejected, s) := by
          have hInv : ¬ Valid s .dequeue := by intro hV; have hsuc := req_valid_succeeds s .dequeue hV; simp [hRej] at hsuc
          exact req_invalid_noop s .dequeue hInv
        have h1 : inflow ((Op.dequeue, .rejected) :: (run step s ops).1) = inflow (run step s ops).1 := by simp [inflow, inflowOf]
        have h2 : outflow ((Op.dequeue, .rejected) :: (run step s ops).1) = outflow (run step s ops).1 := by simp [outflow, outflowOf]
        simp [run, hNoop, h1, h2, ih]
      · have hNotRej : (step s .dequeue).1 ≠ .rejected := hRej
        obtain ⟨y, hGot, hContEq⟩ := req_dequeue_contents s hNotRej
        have h1 : inflow ((Op.dequeue, .got y) :: (run step (step s .dequeue).2 ops).1) = inflow (run step (step s .dequeue).2 ops).1 := by simp [inflow, inflowOf, hGot]
        have h2 : outflow ((Op.dequeue, .got y) :: (run step (step s .dequeue).2 ops).1) = [y] ++ outflow (run step (step s .dequeue).2 ops).1 := by simp [outflow, outflowOf, hGot]
        simp [run, hGot, h1, h2]
        have ih' := ih (s := (step s .dequeue).2)
        calc contents s ++ inflow (run step (step s .dequeue).2 ops).1
            = (y :: contents (step s .dequeue).2) ++ inflow (run step (step s .dequeue).2 ops).1 := by rw [hContEq]
          _ = [y] ++ (contents (step s .dequeue).2 ++ inflow (run step (step s .dequeue).2 ops).1) := by simp
          _ = [y] ++ (outflow (run step (step s .dequeue).2 ops).1 ++ contents (run step (step s .dequeue).2 ops).2) := by rw [ih']
          _ = ([y] ++ outflow (run step (step s .dequeue).2 ops).1) ++ contents (run step (step s .dequeue).2 ops).2 := by simp [List.append_assoc]

end RingBuffer
