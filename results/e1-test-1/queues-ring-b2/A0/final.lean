import RingBuffer.Spec
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { capacity := s.capacity, buf := fun i => (if i = slot s s.count then x else s.buf i), head := s.head, count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { capacity := s.capacity, buf := s.buf, head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem add_cap_mod (cap k : Nat) (h : k < cap) : (cap + k) % cap = k := by
  have h1 : k % cap = k := Nat.mod_eq_of_lt h
  have h2 : cap % cap = 0 := Nat.mod_self cap
  have h3 : (cap + k) % cap = ((cap % cap) + (k % cap)) % cap := Nat.add_mod cap k cap
  rw [h3, h2, h1, Nat.zero_add]
  exact Nat.mod_eq_of_lt h

theorem sub_cap_mod (a cap : Nat) (hle : cap ≤ a) (hlt : a < cap + cap) : a % cap = a - cap := by
  have hlt2 : a - cap < cap := by omega
  have hEq : a = cap + (a - cap) := by omega
  have hStep : a % cap = (cap + (a - cap)) % cap := congrArg (fun n => n % cap) hEq
  rw [hStep]
  exact add_cap_mod cap (a - cap) hlt2

theorem tail_ne_aux (head count cap i : Nat) (_hcap : 0 < cap) (hhead : head < cap)
    (hcount : count < cap) (hi : i < count) :
    (head + i) % cap ≠ (head + count) % cap := by
  intro heq
  cases Decidable.em (head + count < cap) with
  | inl hB =>
    have eB : (head + count) % cap = head + count := Nat.mod_eq_of_lt hB
    have hA : head + i < cap := by omega
    have eA : (head + i) % cap = head + i := Nat.mod_eq_of_lt hA
    rw [eA, eB] at heq
    omega
  | inr hB =>
    have hleB : cap ≤ head + count := by omega
    have hltB : head + count < cap + cap := by omega
    have eB : (head + count) % cap = head + count - cap :=
      sub_cap_mod (head + count) cap hleB hltB
    cases Decidable.em (head + i < cap) with
    | inl hA =>
      have eA : (head + i) % cap = head + i := Nat.mod_eq_of_lt hA
      rw [eA, eB] at heq
      omega
    | inr hA =>
      have hleA : cap ≤ head + i := by omega
      have hltA : head + i < cap + cap := by omega
      have eA : (head + i) % cap = head + i - cap :=
        sub_cap_mod (head + i) cap hleA hltA
      rw [eA, eB] at heq
      omega

theorem shift_mod_aux (head cap i : Nat) (_hcap : 0 < cap) (hhead : head < cap) (hi : i < cap) :
    (((head + 1) % cap) + i) % cap = (head + (i + 1)) % cap := by
  cases Decidable.em (head + 1 < cap) with
  | inl hlt =>
    have e : (head + 1) % cap = head + 1 := Nat.mod_eq_of_lt hlt
    rw [e]
    have hEq : head + 1 + i = head + (i + 1) := by omega
    rw [hEq]
  | inr hlt =>
    have heqcap : head + 1 = cap := by omega
    have e : (head + 1) % cap = 0 := by rw [heqcap]; exact Nat.mod_self cap
    rw [e]
    have hZero : (0 + i) % cap = i := by
      have h1 : (0 : Nat) + i = i := Nat.zero_add i
      rw [h1]
      exact Nat.mod_eq_of_lt hi
    rw [hZero]
    have hRhs : head + (i + 1) = cap + i := by omega
    rw [hRhs]
    exact (add_cap_mod cap i hi).symm

theorem range_map_succ_aux (F : Nat → Nat) (n : Nat) :
    (List.range (n + 1)).map F = F 0 :: (List.range n).map (fun i => F (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hR1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := List.range_succ
    have hR2 : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    have hF1 : List.map F [n + 1] = [F (n + 1)] := rfl
    have hG1 : List.map (fun i => F (i + 1)) [n] = [F (n + 1)] := rfl
    calc (List.range (n + 1 + 1)).map F
        = (List.range (n + 1)).map F ++ [F (n + 1)] := by rw [hR1, List.map_append, hF1]
      _ = (F 0 :: (List.range n).map (fun i => F (i + 1))) ++ [F (n + 1)] := by rw [ih]
      _ = F 0 :: (((List.range n).map (fun i => F (i + 1))) ++ [F (n + 1)]) := rfl
      _ = F 0 :: (List.range (n + 1)).map (fun i => F (i + 1)) := by rw [hR2, List.map_append, hG1]

theorem map_range_eq_aux (F G : Nat → Nat) (cnt n : Nat)
    (hFG : ∀ i, i < cnt → F i = G i) (hle : n ≤ cnt) :
    (List.range n).map F = (List.range n).map G := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hle2 : n ≤ cnt := by omega
    have hlt : n < cnt := by omega
    have hn : F n = G n := hFG n hlt
    have ih' := ih hle2
    have h1 : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [h1, List.map_append, List.map_append, ih']
    have hMap : List.map F [n] = List.map G [n] := by simp [hn]
    rw [hMap]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  unfold Valid at hV
  cases op with
  | enqueue x =>
    obtain ⟨⟨h0, h1, _h2⟩, h3⟩ := hV
    have hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := ⟨h0, h1, h3⟩
    simp [step, hc]
  | dequeue =>
    obtain ⟨⟨h0, h1, h2⟩, h3⟩ := hV
    have hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count :=
      ⟨h0, h1, h2, h3⟩
    simp [step, hc]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hV
  cases op with
  | enqueue x =>
    have hnc : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro h
      obtain ⟨h0, h1, hlt⟩ := h
      apply hV
      exact ⟨⟨h0, h1, by omega⟩, hlt⟩
    simp [step, hnc]
  | dequeue =>
    have hnc : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro h
      obtain ⟨h0, h1, h2, h3⟩ := h
      apply hV
      exact ⟨⟨h0, h1, h2⟩, h3⟩
    simp [step, hnc]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hW
  obtain ⟨h0, h1, h2⟩ := hW
  cases op with
  | enqueue x =>
    cases Decidable.em (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) with
    | inr hnc =>
      have hEq2 : (step s (.enqueue x)).2 = s := by simp [step, hnc]
      rw [hEq2]
      exact ⟨h0, h1, h2⟩
    | inl hc =>
      have hEq2 : (step s (.enqueue x)).2 =
          { capacity := s.capacity, buf := fun i => (if i = slot s s.count then x else s.buf i), head := s.head, count := s.count + 1 } := by simp [step, hc]
      rw [hEq2]
      obtain ⟨a0, a1, _alt⟩ := hc
      show 0 < s.capacity ∧ s.head < s.capacity ∧ s.count + 1 ≤ s.capacity
      exact ⟨by omega, by omega, by omega⟩
  | dequeue =>
    cases Decidable.em (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) with
    | inr hnc =>
      have hEq2 : (step s .dequeue).2 = s := by simp [step, hnc]
      rw [hEq2]
      exact ⟨h0, h1, h2⟩
    | inl hc =>
      have hEq2 : (step s .dequeue).2 =
          { capacity := s.capacity, buf := s.buf, head := (s.head + 1) % s.capacity, count := s.count - 1 } := by simp [step, hc]
      rw [hEq2]
      obtain ⟨a0, _a1, _a2, _a3⟩ := hc
      show 0 < s.capacity ∧ (s.head + 1) % s.capacity < s.capacity ∧ s.count - 1 ≤ s.capacity
      exact ⟨by omega, Nat.mod_lt _ a0, by omega⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hNe
  cases Decidable.em (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) with
  | inr hnc =>
    have hF : (step s (.enqueue x)).1 = .rejected := by simp [step, hnc]
    exact False.elim (hNe hF)
  | inl hc =>
    simp [step, hc]

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hNe
  cases Decidable.em (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) with
  | inr hnc =>
    have hF : (step s .dequeue).1 = .rejected := by simp [step, hnc]
    exact False.elim (hNe hF)
  | inl hc =>
    simp [step, hc]

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hNe
  cases Decidable.em (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) with
  | inr hnc =>
    have hF : (step s (.enqueue x)).1 = .rejected := by simp [step, hnc]
    exact False.elim (hNe hF)
  | inl hc =>
    have hcap : 0 < s.capacity := hc.1
    have hhead : s.head < s.capacity := hc.2.1
    have hcount : s.count < s.capacity := hc.2.2
    have hEq : step s (.enqueue x) =
        (.ok, { capacity := s.capacity, buf := fun i => (if i = slot s s.count then x else s.buf i), head := s.head, count := s.count + 1 }) := by simp [step, hc]
    have hStep2 : (step s (.enqueue x)).2 =
        { capacity := s.capacity, buf := fun i => (if i = slot s s.count then x else s.buf i), head := s.head, count := s.count + 1 } := by rw [hEq]
    have hTail : ∀ i, i < s.count →
        (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity :=
      fun i hi => tail_ne_aux s.head s.count s.capacity i hcap hhead hcount hi
    have hMapEq : (List.range s.count).map
        (fun i => (if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x
          else s.buf ((s.head + i) % s.capacity))) =
        (List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity)) := by
      apply map_range_eq_aux _ _ s.count s.count _ (by omega)
      intro i hi
      have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := hTail i hi
      simp [hne]
    have hRange : List.range (s.count + 1) = List.range s.count ++ [s.count] :=
      List.range_succ
    have hCs : contents s = (List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity)) := rfl
    have hCs2 : contents (step s (.enqueue x)).2 =
        (List.range (s.count + 1)).map (fun i => (if (s.head + i) % s.capacity =
          (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity))) := by
      rw [hStep2]
      rfl
    have hSingle : ([s.count].map (fun i => (if (s.head + i) % s.capacity =
        (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)))) = [x] := by
      simp
    rw [hCs2, hRange, List.map_append, hSingle, hMapEq, ← hCs]

theorem req_dequeue_contents : DequeueContents step := by
  intro s hNe
  cases Decidable.em (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) with
  | inr hnc =>
    have hF : (step s .dequeue).1 = .rejected := by simp [step, hnc]
    exact False.elim (hNe hF)
  | inl hc =>
    have hcap : 0 < s.capacity := hc.1
    have hhead : s.head < s.capacity := hc.2.1
    have hEq : step s .dequeue =
        (.got (s.buf s.head),
          { capacity := s.capacity, buf := s.buf, head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by simp [step, hc]
    have hOut : (step s .dequeue).1 = .got (s.buf s.head) := by rw [hEq]
    have hStep2 : (step s .dequeue).2 =
        { capacity := s.capacity, buf := s.buf, head := (s.head + 1) % s.capacity, count := s.count - 1 } := by rw [hEq]
    refine ⟨s.buf s.head, hOut, ?_⟩
    have hGEq : ∀ i, i < s.count - 1 →
        s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity) =
        s.buf ((s.head + (i + 1)) % s.capacity) := by
      intro i hi
      have hiCap : i < s.capacity := by omega
      have hshift := shift_mod_aux s.head s.capacity i hcap hhead hiCap
      rw [hshift]
    have hAux : (List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity)) =
        (fun i => s.buf ((s.head + i) % s.capacity)) 0 ::
        (List.range (s.count - 1)).map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) := by
      have hBase := range_map_succ_aux (fun i => s.buf ((s.head + i) % s.capacity)) (s.count - 1)
      have hCntEq : (s.count - 1) + 1 = s.count := by omega
      rw [hCntEq] at hBase
      exact hBase
    have hF0 : (fun i => s.buf ((s.head + i) % s.capacity)) 0 = s.buf s.head := by
      simp [Nat.add_zero, Nat.mod_eq_of_lt hhead]
    have hMapGEq : (List.range (s.count - 1)).map
        (fun i => s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity)) =
        (List.range (s.count - 1)).map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) := by
      apply map_range_eq_aux _ _ (s.count - 1) (s.count - 1) _ (by omega)
      intro i hi
      exact hGEq i hi
    have hCs : contents s = (List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity)) := rfl
    have hCs2 : contents (step s .dequeue).2 =
        (List.range (s.count - 1)).map
          (fun i => s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity)) := by
      rw [hStep2]
      rfl
    rw [hCs, hAux, hF0, ← hMapGEq, ← hCs2]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hRun : run step s (op :: ops) =
        ((op, (step s op).1) :: (run step (step s op).2 ops).1,
         (run step (step s op).2 ops).2) := by
      simp [run]
    rw [hRun]
    have hIn : ∀ (p : Op × Outcome) (t : List (Op × Outcome)),
        inflow (p :: t) = inflowOf p ++ inflow t := by
      intro p t
      simp [inflow]
    have hOutL : ∀ (p : Op × Outcome) (t : List (Op × Outcome)),
        outflow (p :: t) = outflowOf p ++ outflow t := by
      intro p t
      simp [outflow]
    rw [hIn, hOutL]
    cases op with
    | enqueue x =>
      cases Decidable.em (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) with
      | inr hnc =>
        have hStep : step s (.enqueue x) = (.rejected, s) := by simp [step, hnc]
        have hOutEq : (step s (.enqueue x)).1 = .rejected := by rw [hStep]
        have hS : (step s (.enqueue x)).2 = s := by rw [hStep]
        have hInEq : inflowOf ((.enqueue x : Op), (step s (.enqueue x)).1) = [] := by
          rw [hOutEq]
          rfl
        have hOutEq2 : outflowOf ((.enqueue x : Op), (step s (.enqueue x)).1) = [] := by
          rw [hOutEq]
          rfl
        rw [hInEq, hOutEq2, hS]
        simp only [List.nil_append]
        exact ih s
      | inl hc =>
        have hNe : (step s (.enqueue x)).1 ≠ .rejected := by simp [step, hc]
        have hC := req_enqueue_contents s x hNe
        have hEff := req_enqueue_effects s x hNe
        have hOutEq : (step s (.enqueue x)).1 = .ok := by rw [hEff]
        have hInEq : inflowOf ((.enqueue x : Op), (step s (.enqueue x)).1) = [x] := by
          rw [hOutEq]
          rfl
        have hOutEq2 : outflowOf ((.enqueue x : Op), (step s (.enqueue x)).1) = [] := by
          rw [hOutEq]
          rfl
        rw [hInEq, hOutEq2]
        simp only [List.nil_append]
        have ih' := ih ((step s (.enqueue x)).2)
        have hC2 : contents s ++ [x] = contents (step s (.enqueue x)).2 := by rw [hC]
        rw [← List.append_assoc, hC2]
        exact ih'
    | dequeue =>
      cases Decidable.em (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) with
      | inr hnc =>
        have hStep : step s .dequeue = (.rejected, s) := by simp [step, hnc]
        have hOutEq : (step s .dequeue).1 = .rejected := by rw [hStep]
        have hS : (step s .dequeue).2 = s := by rw [hStep]
        have hInEq : inflowOf ((.dequeue : Op), (step s .dequeue).1) = [] := by
          rw [hOutEq]
          rfl
        have hOutEq2 : outflowOf ((.dequeue : Op), (step s .dequeue).1) = [] := by
          rw [hOutEq]
          rfl
        rw [hInEq, hOutEq2, hS]
        simp only [List.nil_append]
        exact ih s
      | inl hc =>
        have hNe : (step s .dequeue).1 ≠ .rejected := by simp [step, hc]
        have hC := req_dequeue_contents s hNe
        obtain ⟨y, hyOut, hyCont⟩ := hC
        have hOutEq : outflowOf ((.dequeue : Op), (step s .dequeue).1) = [y] := by
          rw [hyOut]
          rfl
        have hInEq : inflowOf ((.dequeue : Op), (step s .dequeue).1) = [] := by
          rw [hyOut]
          rfl
        rw [hInEq, hOutEq]
        simp only [List.nil_append]
        have ih' := ih ((step s .dequeue).2)
        rw [hyCont, List.cons_append, ih']
        simp

end RingBuffer
