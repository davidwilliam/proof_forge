import RingBuffer.Spec
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

private theorem enqueue_cond_iff_valid (s : State) (x : Nat) :
    (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) ↔ Valid s (.enqueue x) := by
  unfold Valid WellFormed
  constructor
  · intro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2, Nat.le_of_lt h3⟩, h3⟩
  · intro ⟨⟨h1, h2, _⟩, h4⟩
    exact ⟨h1, h2, h4⟩

private theorem dequeue_cond_iff_valid (s : State) :
    (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) ↔ Valid s .dequeue := by
  unfold Valid WellFormed
  constructor
  · intro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h3⟩, h4⟩
  · intro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | enqueue x =>
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity :=
      (enqueue_cond_iff_valid s x).mpr hV
    simp [step, hcond]
  | dequeue =>
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count :=
      (dequeue_cond_iff_valid s).mpr hV
    simp [step, hcond]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv
  cases op with
  | enqueue x =>
    have h : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro hcond
      exact hInv ((enqueue_cond_iff_valid s x).mp hcond)
    simp [step, h]
  | dequeue =>
    have h : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hcond
      exact hInv ((dequeue_cond_iff_valid s).mp hcond)
    simp [step, h]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hwf
  cases op with
  | enqueue x =>
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · have hsimp : step s (Op.enqueue x) = (Outcome.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
        simp [step, h]
      rw [hsimp]
      simp only [WellFormed] at hwf ⊢
      exact ⟨hwf.1, hwf.2.1, by omega⟩
    · have hsimp : step s (Op.enqueue x) = (Outcome.rejected, s) := by simp [step, h]
      rw [hsimp]
      exact hwf
  | dequeue =>
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · have hsimp : step s Op.dequeue = (Outcome.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
        simp [step, h]
      rw [hsimp]
      simp only [WellFormed] at hwf ⊢
      exact ⟨hwf.1, Nat.mod_lt _ hwf.1, by omega⟩
    · have hsimp : step s Op.dequeue = (Outcome.rejected, s) := by simp [step, h]
      rw [hsimp]
      exact hwf

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hne
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · simp [step, hcond]
  · have hRej : (step s (Op.enqueue x)).1 = Outcome.rejected := by simp [step, hcond]
    exact absurd hRej hne

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · simp [step, hcond]
  · have hRej : (step s Op.dequeue).1 = Outcome.rejected := by simp [step, hcond]
    exact absurd hRej hne

private theorem mod_ne_of_lt_capacity (cap head i cnt : Nat) (hcap : 0 < cap) (hcntLt : cnt < cap) (hi : i < cnt) :
    (head + i) % cap ≠ (head + cnt) % cap := by
  intro heq
  have hdiff_lt : cnt - i < cap := by omega
  have h1 : head + i + (cnt - i) = head + cnt := by omega
  have hmod : (head + i + (cnt - i)) % cap = ((head + i) % cap + (cnt - i) % cap) % cap :=
    Nat.add_mod (head + i) (cnt - i) cap
  rw [h1] at hmod
  have hmod_k : (cnt - i) % cap = cnt - i := Nat.mod_eq_of_lt hdiff_lt
  rw [hmod_k] at hmod
  have h2 : (head + cnt) % cap = ((head + i) % cap + (cnt - i)) % cap := hmod
  have h2' : (head + cnt) % cap = ((head + cnt) % cap + (cnt - i)) % cap := by
    have : ((head + i) % cap + (cnt - i)) % cap = ((head + cnt) % cap + (cnt - i)) % cap := by rw [heq]
    rw [this] at h2
    exact h2
  let a := (head + cnt) % cap
  have ha_lt : a < cap := Nat.mod_lt _ hcap
  have hne : (a + (cnt - i)) % cap ≠ a := by
    by_cases hle : a + (cnt - i) < cap
    · rw [Nat.mod_eq_of_lt hle]; omega
    · have hsub_lt : a + (cnt - i) - cap < cap := by omega
      have h_eq : a + (cnt - i) = cap + (a + (cnt - i) - cap) := by omega
      have hmod2 : (a + (cnt - i)) % cap = a + (cnt - i) - cap := by
        calc (a + (cnt - i)) % cap = (cap + (a + (cnt - i) - cap)) % cap := by rw [← h_eq]
          _ = ((cap % cap) + ((a + (cnt - i) - cap) % cap)) % cap := Nat.add_mod cap (a + (cnt - i) - cap) cap
          _ = ((a + (cnt - i) - cap) % cap) := by simp [Nat.mod_self]
          _ = a + (cnt - i) - cap := by rw [Nat.mod_eq_of_lt hsub_lt]
      omega
  exact hne h2'.symm

private theorem enqueue_contents_aux (s : State) (x : Nat) (hcap : 0 < s.capacity) (hcnt : s.count < s.capacity) :
    contents { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } = contents s ++ [x] := by
  unfold contents slot
  simp only
  have hRange : List.range (s.count + 1) = List.range s.count ++ [s.count] := by
    rw [List.range_succ]
  rw [hRange, List.map_append]
  have hMapRange : List.map (fun i => if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)) (List.range s.count) = List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count) := by
    apply List.map_congr_left
    intro i hi
    have hi' : i < s.count := List.mem_range.mp hi
    have hneq := mod_ne_of_lt_capacity s.capacity s.head i s.count hcap hcnt hi'
    simp [hneq]
  rw [hMapRange]
  simp

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · have hEff := req_enqueue_effects (s := s) (x := x) hne
    rw [hEff]
    exact enqueue_contents_aux s x hcond.1 hcond.2.2
  · have hRej : (step s (Op.enqueue x)).1 = Outcome.rejected := by simp [step, hcond]
    exact absurd hRej hne

private theorem range_succ_cons (n : Nat) : List.range (n + 1) = 0 :: List.map Nat.succ (List.range n) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have h1 : List.range (m + 2) = List.range (m + 1) ++ [m + 1] := by simp [List.range_succ]
    have h2 : List.map Nat.succ (List.range (m + 1)) = List.map Nat.succ (List.range m) ++ [m + 1] := by
      rw [List.range_succ, List.map_append]
      rfl
    calc List.range (m + 2) = List.range (m + 1) ++ [m + 1] := h1
      _ = (0 :: List.map Nat.succ (List.range m)) ++ [m + 1] := by rw [ih]
      _ = 0 :: (List.map Nat.succ (List.range m) ++ [m + 1]) := by simp
      _ = 0 :: List.map Nat.succ (List.range (m + 1)) := by rw [← h2]

private theorem dequeue_contents_aux (s : State) (_hcap : 0 < s.capacity) (hhead : s.head < s.capacity) (hcntPos : 0 < s.count) :
    contents s = s.buf s.head :: contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
  match hcnt : s.count with
  | 0 => omega
  | Nat.succ n =>
    have hsc : s.count = n + 1 := by omega
    have h0mod : (s.head + 0) % s.capacity = s.head := Nat.mod_eq_of_lt hhead
    have hRange : List.range (n + 1) = 0 :: List.map Nat.succ (List.range n) := range_succ_cons n
    unfold contents slot
    have hc1 : List.range s.count = List.range (n + 1) := by rw [hsc]
    rw [hc1, hRange]
    simp only [List.map_cons, h0mod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hAddMod : (s.head + Nat.succ i) % s.capacity = ((s.head + 1) % s.capacity + i) % s.capacity := by
      have h1 : s.head + Nat.succ i = s.head + 1 + i := by omega
      rw [h1, Nat.mod_add_mod]
    exact congrArg (fun v => s.buf v) hAddMod

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · have hEff := req_dequeue_effects (s := s) hne
    have hAux := dequeue_contents_aux s hcond.1 hcond.2.1 hcond.2.2.2
    refine ⟨s.buf s.head, by rw [hEff], ?_⟩
    rw [hEff]
    simpa using hAux
  · have hRej : (step s Op.dequeue).1 = Outcome.rejected := by simp [step, hcond]
    exact absurd hRej hne

private theorem inflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (p :: t) = inflowOf p ++ inflow t := by simp [inflow]

private theorem outflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (p :: t) = outflowOf p ++ outflow t := by simp [outflow]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | enqueue x =>
      by_cases hRej : (step s (Op.enqueue x)).1 = Outcome.rejected
      · have hNotValid : ¬ Valid s (Op.enqueue x) := by intro hv; exact absurd hRej (req_valid_succeeds (s := s) (op := Op.enqueue x) hv)
        have hStep : step s (Op.enqueue x) = (Outcome.rejected, s) := req_invalid_noop (s := s) (op := Op.enqueue x) hNotValid
        have hRun : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, Outcome.rejected) :: (run step s ops).1, (run step s ops).2) := by simp [run, hStep]
        have hIn : inflowOf (Op.enqueue x, Outcome.rejected) = ([] : List Nat) := by rfl
        have hOut : outflowOf (Op.enqueue x, Outcome.rejected) = ([] : List Nat) := by rfl
        have hL : contents s ++ inflow (run step s (Op.enqueue x :: ops)).1 = contents s ++ inflow (run step s ops).1 := by
          have : inflow (run step s (Op.enqueue x :: ops)).1 = inflow (run step s ops).1 := by rw [hRun, inflow_cons, hIn, List.nil_append]
          rw [this]
        have hR : outflow (run step s (Op.enqueue x :: ops)).1 ++ contents (run step s (Op.enqueue x :: ops)).2 = outflow (run step s ops).1 ++ contents (run step s ops).2 := by
          have : outflow (run step s (Op.enqueue x :: ops)).1 = outflow (run step s ops).1 := by rw [hRun, outflow_cons, hOut, List.nil_append]
          have hSnd : (run step s (Op.enqueue x :: ops)).2 = (run step s ops).2 := by rw [hRun]
          rw [this, hSnd]
        rw [hL, hR]
        exact ih s
      · have hNe : (step s (Op.enqueue x)).1 ≠ Outcome.rejected := hRej
        have hOk : (step s (Op.enqueue x)).1 = Outcome.ok := by
          have hEff := req_enqueue_effects (s := s) (x := x) hNe
          rw [hEff]
        have hCont : contents (step s (Op.enqueue x)).2 = contents s ++ [x] := req_enqueue_contents (s := s) (x := x) hNe
        have hI : inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [x] := by rw [hOk]; rfl
        have hO : outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = ([] : List Nat) := by rw [hOk]; rfl
        have ih' := ih (step s (Op.enqueue x)).2
        have hRun : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, (step s (Op.enqueue x)).1) :: (run step (step s (Op.enqueue x)).2 ops).1, (run step (step s (Op.enqueue x)).2 ops).2) := by simp [run]
        have hInEq : inflow (run step s (Op.enqueue x :: ops)).1 = [x] ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by rw [hRun, inflow_cons, hI]
        have hOutEq : outflow (run step s (Op.enqueue x :: ops)).1 = outflow (run step (step s (Op.enqueue x)).2 ops).1 := by rw [hRun, outflow_cons, hO, List.nil_append]
        have hSndEq : (run step s (Op.enqueue x :: ops)).2 = (run step (step s (Op.enqueue x)).2 ops).2 := by rw [hRun]
        calc contents s ++ inflow (run step s (Op.enqueue x :: ops)).1
            = contents s ++ ([x] ++ inflow (run step (step s (Op.enqueue x)).2 ops).1) := by rw [hInEq]
          _ = (contents s ++ [x]) ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by rw [List.append_assoc]
          _ = contents (step s (Op.enqueue x)).2 ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by rw [← hCont]
          _ = outflow (run step (step s (Op.enqueue x)).2 ops).1 ++ contents (run step (step s (Op.enqueue x)).2 ops).2 := ih'
          _ = outflow (run step s (Op.enqueue x :: ops)).1 ++ contents (run step s (Op.enqueue x :: ops)).2 := by rw [hOutEq, hSndEq]
    | dequeue =>
      by_cases hRej : (step s Op.dequeue).1 = Outcome.rejected
      · have hNotValid : ¬ Valid s Op.dequeue := by intro hv; exact absurd hRej (req_valid_succeeds (s := s) (op := Op.dequeue) hv)
        have hStep : step s Op.dequeue = (Outcome.rejected, s) := req_invalid_noop (s := s) (op := Op.dequeue) hNotValid
        have hRun : run step s (Op.dequeue :: ops) = ((Op.dequeue, Outcome.rejected) :: (run step s ops).1, (run step s ops).2) := by simp [run, hStep]
        have hIn : inflowOf (Op.dequeue, Outcome.rejected) = ([] : List Nat) := by rfl
        have hOut : outflowOf (Op.dequeue, Outcome.rejected) = ([] : List Nat) := by rfl
        have hL : contents s ++ inflow (run step s (Op.dequeue :: ops)).1 = contents s ++ inflow (run step s ops).1 := by
          have : inflow (run step s (Op.dequeue :: ops)).1 = inflow (run step s ops).1 := by rw [hRun, inflow_cons, hIn, List.nil_append]
          rw [this]
        have hR : outflow (run step s (Op.dequeue :: ops)).1 ++ contents (run step s (Op.dequeue :: ops)).2 = outflow (run step s ops).1 ++ contents (run step s ops).2 := by
          have : outflow (run step s (Op.dequeue :: ops)).1 = outflow (run step s ops).1 := by rw [hRun, outflow_cons, hOut, List.nil_append]
          have hSnd : (run step s (Op.dequeue :: ops)).2 = (run step s ops).2 := by rw [hRun]
          rw [this, hSnd]
        rw [hL, hR]
        exact ih s
      · have hNe : (step s Op.dequeue).1 ≠ Outcome.rejected := hRej
        obtain ⟨y, hyGot, hyCont⟩ := req_dequeue_contents (s := s) hNe
        have hI : inflowOf (Op.dequeue, (step s Op.dequeue).1) = ([] : List Nat) := by simp [inflowOf]
        have hO : outflowOf (Op.dequeue, (step s Op.dequeue).1) = [y] := by simp [outflowOf, hyGot]
        have ih' := ih (step s Op.dequeue).2
        have hRun : run step s (Op.dequeue :: ops) = ((Op.dequeue, (step s Op.dequeue).1) :: (run step (step s Op.dequeue).2 ops).1, (run step (step s Op.dequeue).2 ops).2) := by simp [run]
        have hInEq : inflow (run step s (Op.dequeue :: ops)).1 = inflow (run step (step s Op.dequeue).2 ops).1 := by rw [hRun, inflow_cons, hI, List.nil_append]
        have hOutEq : outflow (run step s (Op.dequeue :: ops)).1 = [y] ++ outflow (run step (step s Op.dequeue).2 ops).1 := by rw [hRun, outflow_cons, hO]
        have hSndEq : (run step s (Op.dequeue :: ops)).2 = (run step (step s Op.dequeue).2 ops).2 := by rw [hRun]
        calc contents s ++ inflow (run step s (Op.dequeue :: ops)).1
            = contents s ++ inflow (run step (step s Op.dequeue).2 ops).1 := by rw [hInEq]
          _ = (y :: contents (step s Op.dequeue).2) ++ inflow (run step (step s Op.dequeue).2 ops).1 := by rw [hyCont]
          _ = y :: (contents (step s Op.dequeue).2 ++ inflow (run step (step s Op.dequeue).2 ops).1) := by rfl
          _ = y :: (outflow (run step (step s Op.dequeue).2 ops).1 ++ contents (run step (step s Op.dequeue).2 ops).2) := by rw [ih']
          _ = ([y] ++ outflow (run step (step s Op.dequeue).2 ops).1) ++ contents (run step (step s Op.dequeue).2 ops).2 := by rfl
          _ = outflow (run step s (Op.dequeue :: ops)).1 ++ contents (run step s (Op.dequeue :: ops)).2 := by rw [hOutEq, hSndEq]

end RingBuffer
