import PrioQueue.Spec
namespace PrioQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid Sorted <;> infer_instance

def ins (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs => if e.prio < x.prio then e :: x :: xs else x :: ins e xs

def step : Impl := fun s op =>
  if Valid s op then
    match op, s.items with
    | .insert e, _ => (.ok, { s with items := ins e s.items })
    | .pop, x :: xs => (.got x, { s with items := xs })
    | .pop, [] => (.rejected, s)
  else (.rejected, s)

def fooTest : Nat := 5

theorem fooTestLemma2 : 1 = 1 := rfl

theorem ins_length_aux (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    by_cases h : e.prio < x.prio <;> simp [h, ih, Nat.add_assoc]

theorem step_pop_eq_aux (s : State) (hV : Valid s .pop) :
    ∃ y ys, s.items = y :: ys ∧ step s .pop = (.got y, { s with items := ys }) := by
  have hne : s.items ≠ [] := hV.2
  obtain ⟨y, ys, hItems⟩ := List.exists_cons_of_ne_nil hne
  exact ⟨y, ys, hItems, by unfold step; rw [if_pos hV, hItems]⟩

theorem sorted_head_le_aux (y : Entry) (ys : List Entry) (h : Sorted (y :: ys)) :
    ∀ x ∈ ys, y.prio ≤ x.prio := by
  unfold Sorted at h
  rw [List.pairwise_cons] at h
  obtain ⟨h1, _⟩ := h
  intro x hx
  exact h1 x hx

theorem mem_ins_probe (e y x : Entry) (xs : List Entry) :
    y ∈ (e :: x :: xs) ↔ y = e ∨ y ∈ (x :: xs) := by
  simp only [List.mem_cons]

theorem memInsAux2 (e y : Entry) (l : List Entry) : y ∈ ins e l ↔ y = e ∨ y ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    by_cases h : e.prio < x.prio
    · simp only [ins, h, reduceIte, List.mem_cons]
    · simp only [ins, h, reduceIte, List.mem_cons, ih]
      constructor
      · rintro (rfl | rfl | hm)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hm)
      · rintro (rfl | rfl | hm)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hm)

theorem probeAppend (x : Entry) (l₁ l₂ : List Entry) : ((x :: l₁) ++ l₂) = (x :: (l₁ ++ l₂)) := rfl

theorem probeInsNil (e : Entry) : ins e [] = [e] := rfl

theorem probeInsCons (e x : Entry) (xs : List Entry) : ins e (x :: xs) = (if e.prio < x.prio then e :: x :: xs else x :: ins e xs) := rfl

theorem probeAppend2 (x : Entry) (l₁ l₂ : List Entry) : (x :: (l₁ ++ l₂)) = (x :: l₁ ++ l₂) := rfl

theorem probeInsStep (e x : Entry) (xs : List Entry) (h : ¬ e.prio < x.prio) : ins e (x :: xs) = x :: ins e xs := by simp [probeInsCons, h]

theorem insSplitSortedAux4 (e : Entry) (l : List Entry) (hs : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil =>
    refine ⟨[], [], rfl, rfl, ?_, ?_⟩
    · intro x hx
      simp at hx
    · intro x hx
      simp at hx
  | cons x xs ih =>
    unfold Sorted at hs
    rw [List.pairwise_cons] at hs
    obtain ⟨hle, hsorted⟩ := hs
    obtain ⟨l₁, l₂, heq, hins, h1, h2⟩ := ih hsorted
    by_cases h : e.prio < x.prio
    · refine ⟨[], x :: xs, rfl, ?_, ?_, ?_⟩
      · simp only [List.nil_append]
        have : ins e (x :: xs) = e :: x :: xs := by simp [probeInsCons, h]
        exact this
      · intro y hy
        simp at hy
      · intro y hy
        simp only [List.mem_cons] at hy
        cases hy with
        | inl heq2 =>
          rw [heq2]
          exact h
        | inr hm =>
          exact Nat.lt_of_lt_of_le h (hle y hm)
    · have hxe : x.prio ≤ e.prio := Nat.le_of_not_gt h
      have hh : ins e (x :: xs) = x :: ins e xs := probeInsStep e x xs h
      have e1 : x :: xs = (x :: l₁) ++ l₂ := by rw [heq]; rfl
      have e2 : ins e (x :: xs) = (x :: l₁) ++ e :: l₂ := by rw [hh, hins]; rfl
      exact ⟨x :: l₁, l₂, e1, e2, fun y hy => by
        simp only [List.mem_cons] at hy
        cases hy with
        | inl heq2 => rw [heq2]; exact hxe
        | inr hm => exact h1 y hm, h2⟩

theorem classOfAppendAux (p : Nat) (l₁ l₂ : List Entry) : classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by unfold classOf; rw [List.filter_append]

theorem classOfNilAux (p : Nat) : classOf p [] = [] := rfl

theorem classOfConsAux (p : Nat) (x : Entry) (xs : List Entry) :
    classOf p (x :: xs) = (if x.prio == p then [x] else []) ++ classOf p xs := by
  unfold classOf
  simp only [List.filter_cons]
  by_cases h : (x.prio == p) <;> simp [h]

theorem beqBridgeAux1 (a b : Nat) : (a == b) = true ↔ a = b := by
  simp [BEq.beq]

theorem beqBridgeAux2 (a b : Nat) : decide (a = b) = (a == b) := by
  simp [BEq.beq]

theorem insSortedAux2 (e : Entry) (l : List Entry) (hs : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil =>
    simp [ins, Sorted]
  | cons x xs ih =>
    unfold ins
    by_cases h : e.prio < x.prio
    · simp only [h, ↓reduceIte]
      have hhead : ∀ y ∈ (x :: xs), e.prio ≤ y.prio := by
        intro y hy
        simp only [List.mem_cons] at hy
        cases hy with
        | inl heq => rw [heq]; exact Nat.le_of_lt h
        | inr hmem =>
          have hx : Sorted (x :: xs) := hs
          cases hx with
          | cons h1 h2 => exact Nat.le_trans (Nat.le_of_lt h) (h1 y hmem)
      have htail : Sorted (x :: xs) := hs
      exact List.Pairwise.cons hhead htail
    · simp only [h, ↓reduceIte]
      cases hs with
      | cons h1 h2 =>
        have ih2 : Sorted (ins e xs) := ih h2
        have hhead : ∀ y ∈ ins e xs, x.prio ≤ y.prio := by
          intro y hy
          have hmem : y = e ∨ y ∈ xs := (memInsAux2 e y xs).mp hy
          cases hmem with
          | inl heq => rw [heq]; exact Nat.le_of_not_gt h
          | inr hmem2 => exact h1 y hmem2
        exact List.Pairwise.cons hhead ih2

theorem req_sorted_probe3 : KeepsSorted step := by
  intro s op hs
  obtain ⟨cap, items⟩ := s
  simp only at hs ⊢
  unfold step
  by_cases hV : Valid ⟨cap, items⟩ op
  · rw [if_pos hV]
    cases op with
    | insert e =>
      simp only
      exact insSortedAux2 e items hs
    | pop =>
      cases items with
      | nil => simp; exact hs
      | cons y ys =>
        simp only
        cases hs with
        | cons h1 h2 => exact h2
  · rw [if_neg hV]
    exact hs

theorem fifoTestA (p : Nat) (e : Entry) (h : e.prio = p) : classOf p [e] = [e] := by unfold classOf; simp [h]

theorem fifoTestB (p : Nat) (e : Entry) (h : e.prio ≠ p) : classOf p [e] = [] := by unfold classOf; simp [h]

theorem fifoTestC (p : Nat) (l₁ l₂ : List Entry) : classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := classOfAppendAux p l₁ l₂

theorem probeRun1 (s : State) (op : Op) (ops : List Op) : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by simp [run]

theorem fifoInflowCons2 (a : Op × Outcome) (t : List (Op × Outcome)) : inflow (a :: t) = inflowOf a ++ inflow t := by unfold inflow; simp

theorem fifoOutflowCons2 (a : Op × Outcome) (t : List (Op × Outcome)) : outflow (a :: t) = outflowOf a ++ outflow t := by unfold outflow; simp

theorem fifoInflowNil2 : inflow [] = ([] : List Entry) := rfl

theorem fifoOutflowNil2 : outflow [] = ([] : List Entry) := rfl

theorem fifoRunConsFst (s : State) (op : Op) (ops : List Op) : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by simp [run]

theorem fifoRunConsSnd (s : State) (op : Op) (ops : List Op) : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by simp [run]

theorem fifoClassAppend (p : Nat) (l₁ l₂ : List Entry) : classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by simp [classOf]

theorem fifoProbeA (p : Nat) (x : Entry) (h : x.prio ≠ p) : (x.prio == p) = false := by
  simp [h]

theorem classOfAllNeAux (p : Nat) (l : List Entry) (h : ∀ x ∈ l, x.prio ≠ p) : classOf p l = [] := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    have hy : y.prio ≠ p := h y (by simp)
    have hys : ∀ x ∈ ys, x.prio ≠ p := fun x hx => h x (List.mem_cons_of_mem y hx)
    have ih2 := ih hys
    unfold classOf at ih2 ⊢
    simp [hy, ih2]

theorem insClassOfAux (e : Entry) (l : List Entry) (hs : Sorted l) (p : Nat) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := by
  obtain ⟨l₁, l₂, heq, hins, h1, h2⟩ := insSplitSortedAux4 e l hs
  have hcons : classOf p (e :: l₂) = classOf p [e] ++ classOf p l₂ := by
    have h := classOfAppendAux p [e] l₂
    simpa using h
  have hL : classOf p l = classOf p l₁ ++ classOf p l₂ := by
    rw [heq]
    exact classOfAppendAux p l₁ l₂
  have hI : classOf p (ins e l) = classOf p l₁ ++ (classOf p [e] ++ classOf p l₂) := by
    rw [hins, classOfAppendAux, hcons]
  rw [hL, hI]
  by_cases hep : e.prio = p
  · have hCe : classOf p [e] = [e] := fifoTestA p e hep
    have hC2 : classOf p l₂ = [] := by
      apply classOfAllNeAux
      intro x hx
      have hlt : e.prio < x.prio := h2 x hx
      omega
    rw [hCe, hC2]
    simp
  · have hCe : classOf p [e] = [] := fifoTestB p e hep
    rw [hCe]
    simp

theorem singleProbe1 (e : Entry) : inflowOf (.insert e, .ok) = [e] := rfl

theorem singleProbe2 (e : Entry) : outflowOf ((.insert e : Op), .ok) = ([] : List Entry) := rfl

theorem singleProbe3 (y : Entry) : outflowOf ((.pop : Op), .got y) = [y] := rfl

theorem singleProbe4 : inflowOf ((.pop : Op), .got ⟨0, 0⟩) = ([] : List Entry) := rfl

theorem singleProbe5 (e : Entry) : inflowOf ((.insert e : Op), .rejected) = ([] : List Entry) := rfl

theorem singleProbe6 : outflowOf ((.pop : Op), .rejected) = ([] : List Entry) := rfl

theorem singleStepConservA (s : State) (e : Entry) (p : Nat) (hV : Valid s (.insert e)) :
    classOf p s.items ++ classOf p (inflowOf (.insert e, (step s (.insert e)).1))
      = classOf p (outflowOf (.insert e, (step s (.insert e)).1)) ++ classOf p (step s (.insert e)).2.items := by
  have hStep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
    unfold step
    simp [hV]
  have hOut : (step s (.insert e)).1 = .ok := by rw [hStep]
  have hNext : (step s (.insert e)).2.items = ins e s.items := by rw [hStep]
  have hs : Sorted s.items := hV.1
  have hIns := insClassOfAux e s.items hs p
  have e1 : inflowOf (.insert e, (step s (.insert e)).1) = [e] := by
    rw [hOut]
    exact singleProbe1 e
  have e2 : outflowOf (.insert e, (step s (.insert e)).1) = ([] : List Entry) := by
    rw [hOut]
    exact singleProbe2 e
  rw [e1, e2, hNext, hIns]
  have hC : classOf p ([] : List Entry) = [] := rfl
  rw [hC, List.nil_append]

theorem inflowPopGot (y : Entry) : inflowOf (.pop, .got y) = ([] : List Entry) := by
  unfold inflowOf
  simp

theorem outflowPopGot (y : Entry) : outflowOf (.pop, .got y) = [y] := by
  unfold outflowOf
  simp

theorem inflowInsRej (e : Entry) : inflowOf (.insert e, .rejected) = ([] : List Entry) := by
  unfold inflowOf
  simp

theorem outflowInsRej (e : Entry) : outflowOf (.insert e, .rejected) = ([] : List Entry) := by
  unfold outflowOf
  simp

theorem outflowPopRej : outflowOf (.pop, .rejected) = ([] : List Entry) := by
  unfold outflowOf
  simp

theorem inflowPopRej : inflowOf (.pop, .rejected) = ([] : List Entry) := by
  unfold inflowOf
  simp

theorem singleStepConservPop (s : State) (p : Nat) (hV : Valid s .pop) :
    classOf p s.items ++ classOf p (inflowOf (.pop, (step s .pop).1))
      = classOf p (outflowOf (.pop, (step s .pop).1)) ++ classOf p (step s .pop).2.items := by
  obtain ⟨y, ys, hItems, hStep⟩ := step_pop_eq_aux s hV
  have hOut : (step s .pop).1 = .got y := by rw [hStep]
  have hNext : (step s .pop).2.items = ys := by rw [hStep]
  have e1 : inflowOf (.pop, (step s .pop).1) = ([] : List Entry) := by
    rw [hOut]
    exact inflowPopGot y
  have e2 : outflowOf (.pop, (step s .pop).1) = [y] := by
    rw [hOut]
    exact outflowPopGot y
  have hNil : classOf p ([] : List Entry) = [] := rfl
  have hC : classOf p (y :: ys) = classOf p [y] ++ classOf p ys := by
    simpa using (classOfAppendAux p [y] ys)
  have hC2 : classOf p s.items = classOf p [y] ++ classOf p ys := by
    rw [hItems]
    exact hC
  rw [e1, e2, hNext, hNil, List.append_nil, hC2]

theorem singleConserv (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
      = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  cases op with
  | insert e =>
    by_cases hV : Valid s (.insert e)
    · exact singleStepConservA s e p hV
    · have hEq : step s (.insert e) = (.rejected, s) := by unfold step; rw [if_neg hV]
      have h1 : (step s (.insert e)).1 = .rejected := by rw [hEq]
      have h2 : (step s (.insert e)).2.items = s.items := by rw [hEq]
      have e1 : inflowOf (.insert e, (step s (.insert e)).1) = ([] : List Entry) := by
        rw [h1]
        exact inflowInsRej e
      have e2 : outflowOf (.insert e, (step s (.insert e)).1) = ([] : List Entry) := by
        rw [h1]
        exact outflowInsRej e
      have hNil : classOf p ([] : List Entry) = [] := rfl
      simp [e1, e2, h2, hNil]
  | pop =>
    by_cases hV : Valid s .pop
    · exact singleStepConservPop s p hV
    · have hEq : step s .pop = (.rejected, s) := by unfold step; rw [if_neg hV]
      have h1 : (step s .pop).1 = .rejected := by rw [hEq]
      have h2 : (step s .pop).2.items = s.items := by rw [hEq]
      have e1 : inflowOf (.pop, (step s .pop).1) = ([] : List Entry) := by
        rw [h1]
        exact inflowPopRej
      have e2 : outflowOf (.pop, (step s .pop).1) = ([] : List Entry) := by
        rw [h1]
        exact outflowPopRej
      have hNil : classOf p ([] : List Entry) = [] := rfl
      simp [e1, e2, h2, hNil]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | insert e =>
    show (step s _).1 ≠ .rejected
    unfold step
    rw [if_pos hV]
    simp
  | pop =>
    show (step s _).1 ≠ .rejected
    unfold step
    rw [if_pos hV]
    cases s with
    | mk cap items =>
      cases items with
      | nil =>
        unfold Valid at hV
        simp at hV
      | cons x xs => simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  unfold step
  rw [if_neg h]

theorem req_capacity : CapacityBound step := by
  intro s op hle
  unfold step
  by_cases hV : Valid s op
  · rw [if_pos hV]
    cases op with
    | insert e =>
      simp only
      have h1 : (ins e s.items).length = s.items.length + 1 := ins_length_aux e s.items
      have h2 : s.items.length < s.capacity := (hV : Sorted s.items ∧ s.items.length < s.capacity).2
      omega
    | pop =>
      obtain ⟨cap, items⟩ := s
      simp only at hle ⊢
      cases items with
      | nil =>
        simp
      | cons x xs =>
        simp only
        have hlen : (x :: xs).length = xs.length + 1 := rfl
        omega
  · rw [if_neg hV]
    exact hle

theorem req_pop_min : PopMin step := by
  intro s hne
  by_cases hV : Valid s .pop
  · obtain ⟨y, ys, hItems, hStep⟩ := step_pop_eq_aux s hV
    refine ⟨y, ?_, ?_⟩
    · rw [hStep]
    · rw [hStep]
      simp only
      exact sorted_head_le_aux y ys (hItems ▸ hV.1)
  · have hEq : step s .pop = (.rejected, s) := by unfold step; rw [if_neg hV]
    rw [hEq] at hne
    simp at hne

theorem req_sorted : KeepsSorted step := by
  intro s op hs
  obtain ⟨cap, items⟩ := s
  simp only at hs ⊢
  unfold step
  by_cases hV : Valid ⟨cap, items⟩ op
  · rw [if_pos hV]
    cases op with
    | insert e =>
      simp only
      exact insSortedAux2 e items hs
    | pop =>
      cases items with
      | nil => simp; exact hs
      | cons y ys =>
        simp only
        cases hs with
        | cons h1 h2 => exact h2
  · rw [if_neg hV]
    exact hs

theorem req_insert_effects : InsertEffects step := by
  intro s e hne
  have hV : Valid s (.insert e) := by
    by_cases hC : Valid s (.insert e)
    · exact hC
    · have hEq : step s (.insert e) = (.rejected, s) := by
        unfold step
        simp [hC]
      have hCon : (step s (.insert e)).1 = .rejected := by rw [hEq]
      exact False.elim (hne hCon)
  have hS : Sorted s.items := hV.1
  obtain ⟨l₁, l₂, heq, hins, h1, h2⟩ := insSplitSortedAux4 e s.items hS
  have hStep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
    unfold step
    simp [hV]
  have hOut : (step s (.insert e)).1 = .ok := by rw [hStep]
  have hCap : (step s (.insert e)).2.capacity = s.capacity := by rw [hStep]
  have hItems : (step s (.insert e)).2.items = l₁ ++ e :: l₂ := by rw [hStep]; simp; exact hins
  exact ⟨hOut, hCap, l₁, l₂, heq, hItems, h1, h2⟩

theorem req_pop_effects : PopEffects step := by
  intro s hne
  have hV : Valid s .pop := by
    by_cases hC : Valid s .pop
    · exact hC
    · have hEq : step s .pop = (.rejected, s) := by unfold step; rw [if_neg hC]
      have hCon : (step s .pop).1 = .rejected := by rw [hEq]
      exact False.elim (hne hCon)
  obtain ⟨y, ys, hItems, hStep⟩ := step_pop_eq_aux s hV
  have hCap : (step s .pop).2.capacity = s.capacity := by rw [hStep]
  have hOut : (step s .pop).1 = .got y := by rw [hStep]
  have hRest : (step s .pop).2.items = [] ++ ys := by rw [hStep]; simp
  have hSorted : Sorted s.items := hV.1
  have hle : ∀ x ∈ ys, y.prio ≤ x.prio := by
    have : Sorted (y :: ys) := hItems ▸ hSorted
    exact sorted_head_le_aux y ys this
  refine ⟨hCap, [], y, ys, ?_, hOut, ?_, ?_, ?_⟩
  · simp [hItems]
  · simp [hStep]
  · intro x hx
    simp at hx
  · exact hle

theorem req_fifo_ties : FifoTies step := by
  unfold FifoTies
  intro s ops p
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow, classOf]
  | cons op ops ih =>
    have hSingle := singleConserv s op p
    have hIH := ih (step s op).2
    have hRun1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := fifoRunConsFst s op ops
    have hRun2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := fifoRunConsSnd s op ops
    have hIn : inflow (run step s (op :: ops)).1 = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      rw [hRun1]
      exact fifoInflowCons2 _ _
    have hOut : outflow (run step s (op :: ops)).1 = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      rw [hRun1]
      exact fifoOutflowCons2 _ _
    have hCIn : classOf p (inflow (run step s (op :: ops)).1) = classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1) := by
      rw [hIn]
      exact classOfAppendAux p _ _
    have hCOut : classOf p (outflow (run step s (op :: ops)).1) = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1) := by
      rw [hOut]
      exact classOfAppendAux p _ _
    calc classOf p s.items ++ classOf p (inflow (run step s (op :: ops)).1)
        _ = classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1)) := by rw [hCIn]
        _ = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
        _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [hSingle]
        _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops).1)) := by rw [List.append_assoc]
        _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops).1) ++ classOf p (run step (step s op).2 ops).2.items) := by rw [hIH]
        _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1)) ++ classOf p (run step (step s op).2 ops).2.items := by rw [← List.append_assoc]
        _ = classOf p (outflow (run step s (op :: ops)).1) ++ classOf p (run step (step s op).2 ops).2.items := by rw [← hCOut]
        _ = classOf p (outflow (run step s (op :: ops)).1) ++ classOf p (run step s (op :: ops)).2.items := by rw [hRun2]

end PrioQueue
