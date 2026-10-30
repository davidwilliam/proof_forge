import RingBuffer.Spec
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      let tail := (s.head + s.count) % s.capacity
      (.ok, { s with buf := fun i => if i = tail then x else s.buf i, count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if h : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem aux_mod_two (cap a : Nat) (_hcap : 0 < cap) (h1 : a < 2 * cap) (hge : cap ≤ a) : (a % cap) = a - cap := by
  have h_eq : a = cap + (a - cap) := by omega
  calc a % cap = (cap + (a - cap)) % cap := by rw [← h_eq]
    _ = (a - cap) % cap := by rw [Nat.add_mod_left]
    _ = a - cap := Nat.mod_eq_of_lt (by omega)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | enqueue x =>
    simp [Valid] at hV
    obtain ⟨⟨hcap, hhead, hle⟩, hlt⟩ := hV
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := ⟨hcap, hhead, hlt⟩
    have hstep : step s (Op.enqueue x) = (if h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then (let tail := (s.head + s.count) % s.capacity; (Outcome.ok, { s with buf := fun i => if i = tail then x else s.buf i, count := s.count + 1 }) ) else (Outcome.rejected, s)) := rfl
    rw [hstep]
    simp [hcond]
  | dequeue =>
    simp [Valid] at hV
    obtain ⟨⟨hcap, hhead, hle⟩, hpos⟩ := hV
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity := ⟨hcap, hhead, hpos, hle⟩
    have hstep : step s Op.dequeue = (if h : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity then (Outcome.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) else (Outcome.rejected, s)) := rfl
    rw [hstep]
    simp [hcond]

theorem req_invalid_noop     : InvalidNoop step := by
  intro s op hInv
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at hInv
    -- hInv : ¬ ( (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity) ∧ s.count < s.capacity )
    -- Need to show step rejects
    unfold step
    simp only
    -- need to show condition false
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro h
      apply hInv
      obtain ⟨hcap, hhead, hlt⟩ := h
      exact ⟨⟨hcap, hhead, Nat.le_of_lt hlt⟩, hlt⟩
    simp [hcond]
  | dequeue =>
    simp only [Valid, WellFormed] at hInv
    unfold step
    simp only
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity) := by
      intro h
      apply hInv
      obtain ⟨hcap, hhead, hpos, hle⟩ := h
      exact ⟨⟨hcap, hhead, hle⟩, hpos⟩
    simp [hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hWF
  obtain ⟨hcap, hhead, hle⟩ := hWF
  cases op with
  | enqueue x =>
    unfold step
    simp only
    by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · have h1 : (if h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then (let tail := (s.head + s.count) % s.capacity; (Outcome.ok, { s with buf := fun i => if i = tail then x else s.buf i, count := s.count + 1 }) ) else (Outcome.rejected, s)) = (Outcome.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by simp [hcond]
      rw [h1]
      simp only [WellFormed]
      obtain ⟨_, _, hlt⟩ := hcond
      exact ⟨hcap, hhead, Nat.succ_le_of_lt hlt⟩
    · have h1 : (if h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then (let tail := (s.head + s.count) % s.capacity; (Outcome.ok, { s with buf := fun i => if i = tail then x else s.buf i, count := s.count + 1 }) ) else (Outcome.rejected, s)) = (Outcome.rejected, s) := by simp [hcond]
      rw [h1]
      exact ⟨hcap, hhead, hle⟩
  | dequeue =>
    unfold step
    simp only
    by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity
    · have h1 : (if h : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity then (Outcome.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) else (Outcome.rejected, s)) = (Outcome.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by simp [hcond]
      rw [h1]
      simp only [WellFormed]
      obtain ⟨_, _, _, _⟩ := hcond
      refine ⟨hcap, Nat.mod_lt _ hcap, by omega⟩
    · have h1 : (if h : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity then (Outcome.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) else (Outcome.rejected, s)) = (Outcome.rejected, s) := by simp [hcond]
      rw [h1]
      exact ⟨hcap, hhead, hle⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hNotRej
  unfold step at hNotRej ⊢
  simp only at hNotRej ⊢
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · simp [hcond]
    rfl
  · simp [hcond] at hNotRej

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hNotRej
  unfold step at hNotRej ⊢
  simp only at hNotRej ⊢
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity
  · simp [hcond]
  · simp [hcond] at hNotRej

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hNotRej
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    have hdec := Classical.em (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    cases hdec with
    | inl h => exact h
    | inr h =>
      have hstep : step s (Op.enqueue x) = (Outcome.rejected, s) := by unfold step; simp [h]
      have hfalse : False := by rw [hstep] at hNotRej; simp at hNotRej
      exact False.elim hfalse
  have hcap : 0 < s.capacity := hcond.1
  have _hhead : s.head < s.capacity := hcond.2.1
  have hlt : s.count < s.capacity := hcond.2.2
  have hstep : step s (Op.enqueue x) = (Outcome.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
    unfold step; simp [hcond]
  have hgoal : contents (step s (Op.enqueue x)).2 = contents s ++ [x] := by
    rw [hstep]
    simp only
    unfold contents slot
    simp only
    rw [List.range_succ]
    simp only [List.map_append, List.map_cons, List.map_nil]
    have h_eq : (List.range s.count).map (fun i => if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)) = (List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity)) := by
      apply List.map_congr_left
      intro i hi
      have hi_lt : i < s.count := List.mem_range.mp hi
      have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := by
        intro heq
        have h1_lt : s.head + i < 2 * s.capacity := by omega
        have h2_lt : s.head + s.count < 2 * s.capacity := by omega
        have h1m : (s.head + i) % s.capacity = if s.head + i < s.capacity then s.head + i else s.head + i - s.capacity := by
          by_cases h1c : s.head + i < s.capacity
          · simp [h1c, Nat.mod_eq_of_lt h1c]
          · have hge : s.capacity ≤ s.head + i := by omega
            simp [h1c, aux_mod_two s.capacity (s.head + i) hcap h1_lt hge]
        have h2m : (s.head + s.count) % s.capacity = if s.head + s.count < s.capacity then s.head + s.count else s.head + s.count - s.capacity := by
          by_cases h2c : s.head + s.count < s.capacity
          · simp [h2c, Nat.mod_eq_of_lt h2c]
          · have hge : s.capacity ≤ s.head + s.count := by omega
            simp [h2c, aux_mod_two s.capacity (s.head + s.count) hcap h2_lt hge]
        by_cases h1c : s.head + i < s.capacity <;> by_cases h2c : s.head + s.count < s.capacity
        <;> simp [h1m, h2m, h1c, h2c] at heq <;> omega
      simp [hne]
    rw [h_eq]
    simp
  exact hgoal

theorem req_dequeue_contents : DequeueContents step := by
  intro s hNotRej
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity := by
    have hdec := Classical.em (0 < s.capacity ∧ s.head < s.capacity ∧ 0 < s.count ∧ s.count ≤ s.capacity)
    cases hdec with
    | inl h => exact h
    | inr h =>
      have hstep : step s Op.dequeue = (Outcome.rejected, s) := by unfold step; simp [h]
      have hfalse : False := by rw [hstep] at hNotRej; simp at hNotRej
      exact False.elim hfalse
  have hhead : s.head < s.capacity := hcond.2.1
  have hstep_eq : step s Op.dequeue = (Outcome.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
    unfold step; simp [hcond]
  have hfst : (step s Op.dequeue).1 = Outcome.got (s.buf s.head) := by rw [hstep_eq]
  refine ⟨s.buf s.head, hfst, ?_⟩
  rw [hstep_eq]
  simp only
  unfold contents slot
  simp only
  obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
  rw [hn]
  have hcons : ∀ k (f : Nat → Nat), (List.range (k+1)).map f = f 0 :: (List.range k).map (fun i => f (i+1)) := by
    intro k f
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [List.range_succ, List.map_append] at ih ⊢
      rw [ih]
      simp
  rw [hcons n (fun i => s.buf ((s.head + i) % s.capacity))]
  simp only [Nat.add_zero, Nat.mod_eq_of_lt hhead]
  congr 1
  apply List.map_congr_left
  intro i hi
  have h1 : s.head + (i + 1) = s.head + 1 + i := by omega
  rw [h1]
  rw [Nat.mod_add_mod]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hSingle : contents s ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
      by_cases hRej : (step s op).1 = .rejected
      · have hInvalid : ¬ Valid s op := by
          intro hV
          have hNotRej := req_valid_succeeds s op hV
          exact hNotRej hRej
        have hStep : step s op = (.rejected, s) := req_invalid_noop s op hInvalid
        have h2 : (step s op).2 = s := by rw [hStep]
        cases op with
        | enqueue x =>
          simp [inflowOf, outflowOf, hRej, h2]
        | dequeue =>
          simp [inflowOf, outflowOf, hRej, h2]
      · cases op with
        | enqueue x =>
          have hEnq : contents (step s (Op.enqueue x)).2 = contents s ++ [x] :=
            req_enqueue_contents s x hRej
          have hOk : (step s (Op.enqueue x)).1 = .ok := by
              cases hO : (step s (Op.enqueue x)).1 with
              | ok => rfl
              | rejected => exact absurd hO hRej
              | got y =>
                have heff := req_enqueue_effects s x hRej
                rw [heff] at hO
                simp at hO
          have h1 : inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [x] := by simp [inflowOf, hOk]
          have h2 : outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = ([] : List Nat) := by simp [outflowOf, hOk]
          simp [h1, h2, hEnq]
        | dequeue =>
          have hDeq := req_dequeue_contents s hRej
          obtain ⟨x, hxOk, hxCont⟩ := hDeq
          have hOut : outflowOf (Op.dequeue, (step s Op.dequeue).1) = [x] := by simp [outflowOf, hxOk]
          have hIn : inflowOf (Op.dequeue, (step s Op.dequeue).1) = ([] : List Nat) := by simp [inflowOf, hxOk]
          rw [hIn, hOut]
          simp
          rw [hxCont]
    have hInflow : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      simp [inflow]
    have hOutflow : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      simp [outflow]
    have ih' := ih (step s op).2
    have hrw1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
      simp [run]
    have hrw2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
      simp [run]
    rw [hrw1, hrw2]
    rw [hInflow, hOutflow]
    calc contents s ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (contents s ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ contents (step s op).2) ++ inflow (run step (step s op).2 ops).1 := by rw [hSingle]
      _ = outflowOf (op, (step s op).1) ++ (contents (step s op).2 ++ inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ contents (run step (step s op).2 ops).2) := by rw [ih']
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ contents (run step (step s op).2 ops).2 := by rw [List.append_assoc]

end RingBuffer
