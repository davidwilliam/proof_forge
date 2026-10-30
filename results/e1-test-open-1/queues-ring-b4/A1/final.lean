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

theorem range_succ_map_aux2 : ∀ n : Nat, List.range (n + 1) = 0 :: (List.range n).map (· + 1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    calc List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by simp [List.range_succ]
      _ = (0 :: (List.range n).map (· + 1)) ++ [n + 1] := by rw [ih]
      _ = 0 :: ((List.range n).map (· + 1) ++ [n + 1]) := rfl
      _ = 0 :: ((List.range n ++ [n]).map (· + 1)) := by simp [List.map_append]
      _ = 0 :: (List.range (n + 1)).map (· + 1) := by rw [← List.range_succ]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | enqueue x =>
    have h : Valid s (Op.enqueue x) := hV
    unfold Valid at h
    obtain ⟨⟨hcap, hhead, hle⟩, hlt⟩ := h
    unfold step
    simp only [hcap, hhead, hlt, and_self]
    intro hEq
    simp at hEq
  | dequeue =>
    have h : Valid s Op.dequeue := hV
    unfold Valid at h
    obtain ⟨⟨hcap, hhead, hle⟩, hpos⟩ := h
    unfold step
    have h1 : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count :=
      ⟨hcap, hhead, hle, hpos⟩
    simp only [h1]
    intro hEq
    simp at hEq

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv
  cases op with
  | enqueue x =>
    have h : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro ⟨hcap, hhead, hlt⟩
      apply hInv
      show WellFormed s ∧ s.count < s.capacity
      exact ⟨⟨hcap, hhead, Nat.le_of_lt hlt⟩, hlt⟩
    show step s (Op.enqueue x) = (Outcome.rejected, s)
    unfold step
    simp only [if_neg h]
  | dequeue =>
    have h : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro ⟨hcap, hhead, hle, hpos⟩
      apply hInv
      show WellFormed s ∧ 0 < s.count
      exact ⟨⟨hcap, hhead, hle⟩, hpos⟩
    show step s Op.dequeue = (Outcome.rejected, s)
    unfold step
    simp only [if_neg h]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hWF
  obtain ⟨hcap, hhead, hle⟩ := hWF
  cases op with
  | enqueue x =>
    show WellFormed (step s (Op.enqueue x)).2
    unfold step
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · simp [h]
      exact ⟨h.1, h.2.1, Nat.succ_le_of_lt h.2.2⟩
    · simp [h]
      exact ⟨hcap, hhead, hle⟩
  | dequeue =>
    show WellFormed (step s Op.dequeue).2
    unfold step
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · simp [h]
      refine ⟨h.1, Nat.mod_lt _ h.1, ?_⟩
      exact Nat.le_trans (Nat.sub_le _ _) h.2.2.1
    · simp [h]
      exact ⟨hcap, hhead, hle⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hNotRej
  unfold step at hNotRej ⊢
  by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · simp only [if_pos h] at hNotRej ⊢
    rfl
  · simp only [if_neg h] at hNotRej
    simp at hNotRej

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hNotRej
  unfold step at hNotRej ⊢
  by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · simp only [if_pos h] at hNotRej ⊢
  · simp only [if_neg h] at hNotRej
    simp at hNotRej

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hNotRej
  have hCond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    unfold step at hNotRej
    simp only at hNotRej
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact h
    · simp [h] at hNotRej
  obtain ⟨hCap, hHead, hCnt⟩ := hCond
  have hEq := req_enqueue_effects s x hNotRej
  have hS2 : (step s (Op.enqueue x)).2 = { capacity := s.capacity, buf := fun i => if i = slot s s.count then x else s.buf i, head := s.head, count := s.count + 1 } := by
    have h := congrArg Prod.snd hEq; simpa using h
  have mod_eq_ite : ∀ n, n < 2 * s.capacity → n % s.capacity = if n < s.capacity then n else n - s.capacity := by
    intro n hn
    by_cases hlt : n < s.capacity
    · simp [hlt, Nat.mod_eq_of_lt hlt]
    · have hsub_lt : n - s.capacity < s.capacity := by omega
      have h_eq : n = s.capacity + (n - s.capacity) := by omega
      have h1 : n % s.capacity = (s.capacity + (n - s.capacity)) % s.capacity := by rw [← h_eq]
      -- rewrite add mod right
      have hAdd : (s.capacity + (n - s.capacity)) % s.capacity = (n - s.capacity) % s.capacity := by
        have h' : (s.capacity + (n - s.capacity)) % s.capacity = ((n - s.capacity) + s.capacity) % s.capacity := by rw [Nat.add_comm]
        rw [h', Nat.add_mod_right]
      rw [h1, hAdd, Nat.mod_eq_of_lt hsub_lt]
      simp [hlt]
  have inj_aux : ∀ a b, a < s.capacity → b < s.capacity → (s.head + a) % s.capacity = (s.head + b) % s.capacity → a = b := by
    intro a b ha hb heq
    have ha2 : s.head + a < 2 * s.capacity := by omega
    have hb2 : s.head + b < 2 * s.capacity := by omega
    rw [mod_eq_ite _ ha2] at heq
    rw [mod_eq_ite _ hb2] at heq
    by_cases ha_lt : s.head + a < s.capacity
    · by_cases hb_lt : s.head + b < s.capacity
      · simp [ha_lt, hb_lt] at heq; omega
      · simp [ha_lt, hb_lt] at heq; omega
    · by_cases hb_lt : s.head + b < s.capacity
      · simp [ha_lt, hb_lt] at heq; omega
      · simp [ha_lt, hb_lt] at heq; omega
  have hS2' : (step s (Op.enqueue x)).2 = { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 } := by
    have hh := hS2; simp [slot] at hh ⊢; exact hh
  rw [hS2']
  show contents { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 } = contents s ++ [x]
  unfold contents slot
  simp only
  rw [List.range_succ]
  simp only [List.map_append, List.map_cons, List.map_nil]
  have hmap : (List.range s.count).map (fun i => (if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity))) = (List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity)) := by
    apply List.map_congr_left
    intro i hi
    have hi_lt : i < s.count := List.mem_range.mp hi
    have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := by
      intro heq
      have : i = s.count := inj_aux i s.count (by omega) hCnt heq
      omega
    simp [hne]
  rw [hmap]
  simp

theorem req_dequeue_contents : DequeueContents step := by
  intro s hNotRej
  have hEq := req_dequeue_effects s hNotRej
  have hOut : (step s Op.dequeue).1 = Outcome.got (s.buf s.head) := by
    have h := congrArg Prod.fst hEq; simpa using h
  have hSt : (step s Op.dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
    have h := congrArg Prod.snd hEq; simpa using h
  refine ⟨s.buf s.head, hOut, ?_⟩
  have hCond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
    unfold step at hNotRej
    simp only at hNotRej
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · exact h
    · simp [h] at hNotRej
  obtain ⟨hCap, hHead, hLe, hPos⟩ := hCond
  rw [hSt]
  show contents s = s.buf s.head :: contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }
  unfold contents slot
  simp only
  have hCountEq : s.count = (s.count - 1) + 1 := by omega
  conv => lhs; rw [hCountEq]
  rw [range_succ_map_aux2 (s.count - 1)]
  simp only [List.map_cons]
  have h0 : (s.head + 0) % s.capacity = s.head := by
    simp [Nat.mod_eq_of_lt hHead]
  rw [h0]
  congr 1
  have hmap : List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.map (fun x => x + 1) (List.range (s.count - 1)))
      = List.map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) (List.range (s.count - 1)) := by
    rw [List.map_map]
    simp
  rw [hmap]
  apply List.map_congr_left
  intro i hi
  have hi_lt_cap : i < s.capacity := by
    have : i < s.count - 1 := List.mem_range.mp hi
    omega
  have hi_mod : i % s.capacity = i := Nat.mod_eq_of_lt hi_lt_cap
  have hmod : ((s.head + 1) % s.capacity + i) % s.capacity = (s.head + (i + 1)) % s.capacity := by
    have h1 : (s.head + 1 + i) % s.capacity = ((s.head + 1) % s.capacity + i % s.capacity) % s.capacity := Nat.add_mod (s.head + 1) i s.capacity
    rw [hi_mod] at h1
    have h2 : s.head + (i + 1) = s.head + 1 + i := by omega
    rw [h2, ← h1]
  show s.buf ((s.head + (i + 1)) % s.capacity) = s.buf (((s.head + 1) % s.capacity + i) % s.capacity)
  rw [← hmod]

theorem req_fifo : Fifo step := by
  have step_fifo_aux : ∀ s op, contents s ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
    intro s op
    cases op with
    | enqueue x =>
      by_cases h : (step s (Op.enqueue x)).1 ≠ .rejected
      · have hEnq := req_enqueue_contents s x h
        have hEq : (step s (Op.enqueue x)).1 = .ok := by
          have hE := req_enqueue_effects s x h
          have hh := congrArg Prod.fst hE
          simpa using hh
        simp only [hEq, inflowOf, outflowOf, hEnq]
        simp
      · have hRej : (step s (Op.enqueue x)).1 = .rejected := by
          cases hc : (step s (Op.enqueue x)).1 with
          | rejected => rfl
          | ok => exfalso; apply h; simp [hc]
          | got _ => exfalso; apply h; simp [hc]
        have hInv : ¬ Valid s (Op.enqueue x) := by
          intro hV
          have hn := req_valid_succeeds s (Op.enqueue x) hV
          rw [hRej] at hn
          simp at hn
        have hNoop := req_invalid_noop s (Op.enqueue x) hInv
        have hSnd : (step s (Op.enqueue x)).2 = s := by
          have hh := congrArg Prod.snd hNoop
          simpa [hRej] using hh
        simp [hRej, inflowOf, outflowOf, hSnd]
    | dequeue =>
      by_cases h : (step s Op.dequeue).1 ≠ .rejected
      · obtain ⟨x, hGot, hCont⟩ := req_dequeue_contents s h
        have hSndEq : contents s = x :: contents (step s Op.dequeue).2 := hCont
        simp [hGot, inflowOf, outflowOf, hSndEq]
      · have hRej : (step s Op.dequeue).1 = .rejected := by
          cases hc : (step s Op.dequeue).1 with
          | rejected => rfl
          | ok => exfalso; apply h; simp [hc]
          | got _ => exfalso; apply h; simp [hc]
        have hInv : ¬ Valid s Op.dequeue := by
          intro hV
          have hn := req_valid_succeeds s Op.dequeue hV
          rw [hRej] at hn
          simp at hn
        have hNoop := req_invalid_noop s Op.dequeue hInv
        have hSnd : (step s Op.dequeue).2 = s := by
          have hh := congrArg Prod.snd hNoop
          simpa [hRej] using hh
        simp [hRej, inflowOf, outflowOf, hSnd]
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hStep := step_fifo_aux s op
    have ih2 := ih (s := (step s op).2)
    have hinflow : inflow (((op, (step s op).1) :: (run step (step s op).2 ops).1)) = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      unfold inflow
      simp
    have houtflow : outflow (((op, (step s op).1) :: (run step (step s op).2 ops).1)) = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      unfold outflow
      simp
    simp only [run]
    rw [hinflow, houtflow]
    calc contents s ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (contents s ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ contents (step s op).2) ++ inflow (run step (step s op).2 ops).1 := by rw [hStep]
      _ = outflowOf (op, (step s op).1) ++ (contents (step s op).2 ++ inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ contents (run step (step s op).2 ops).2) := by rw [ih2]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ contents (run step (step s op).2 ops).2 := by rw [List.append_assoc]

end RingBuffer
