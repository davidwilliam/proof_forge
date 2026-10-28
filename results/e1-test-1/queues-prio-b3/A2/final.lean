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

private def dummy1 : Nat := 0

def myTestFoo : Nat := 1

def myTestBar : Nat := 2

theorem myTestThm : 1 = 1 := rfl

theorem ins_length_thm2 : 1 = 1 := rfl

theorem ins_length_thm4 (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by induction l with | nil => simp [ins] | cons x xs ih => simp only [ins]; split; simp; simp [ih, Nat.add_comm, Nat.add_left_comm]

theorem ins_mem_aux5 (e y : Entry) (l : List Entry) : y ∈ ins e l → y = e ∨ y ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    simp only [ins]
    split
    · intro h
      simp at h ⊢
      rcases h with rfl | rfl | h
      · exact Or.inl rfl
      · exact Or.inr (by simp)
      · exact Or.inr (by simp [h])
    · intro h
      simp at h
      rcases h with rfl | h
      · exact Or.inr (by simp)
      · rcases ih h with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem x hm)

theorem sorted_tail_aux2 (x : Entry) (xs : List Entry) (h : Sorted (x :: xs)) : Sorted xs := by
  unfold Sorted at h ⊢
  cases h with
  | cons h1 h2 => exact h2

theorem pw_test (R : Entry → Entry → Prop) (a : Entry) (l : List Entry) : List.Pairwise R (a :: l) → (∀ x ∈ l, R a x) := by
  intro h
  exact (List.pairwise_cons.mp h).1
#check @Nat.le_trans
#check @Nat.le_of_lt

private theorem ins_split_helperIE (e : Entry) (l : List Entry) (hS : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil => exact ⟨[], [], rfl, by simp [ins], fun x hx => by simp at hx, fun x hx => by simp at hx⟩
  | cons x xs ih =>
    have hPair := (List.pairwise_cons.mp hS)
    have hHead : ∀ y ∈ xs, x.prio ≤ y.prio := hPair.1
    have hTail : Sorted xs := hPair.2
    obtain ⟨l₁', l₂', hEq, hIns, hLe1, hLt2⟩ := ih hTail
    by_cases hlt : e.prio < x.prio
    · refine ⟨[], x :: xs, by simp, by simp [ins, hlt], fun x hx => by simp at hx, ?_⟩
      intro y hy
      simp at hy
      rcases hy with rfl | hy
      · exact hlt
      · exact Nat.lt_of_lt_of_le hlt (hHead y hy)
    · have hle : x.prio ≤ e.prio := Nat.le_of_not_gt hlt
      refine ⟨x :: l₁', l₂', by simp [hEq], by simp [ins, hlt, hIns], ?_, hLt2⟩
      intro y hy
      simp at hy
      rcases hy with rfl | hy
      · exact hle
      · exact hLe1 y hy

private theorem testIE (s : State) (e : Entry) (hV : Valid s (.insert e)) :
    step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
  unfold step
  rw [if_pos hV]

private theorem dbgIE (s : State) (e : Entry) : True := by
  by_cases hV : Valid s (.insert e)
  · obtain ⟨hS, hLen⟩ := hV
    trivial
  · trivial

theorem req_pop_effects_aux_tmp : True := trivial

theorem req_pop_effects_clean_tmp2 : True := trivial

theorem fifoExplore1 (t : List (Op × Outcome)) (op : Op) (o : Outcome) :
    inflow ((op, o) :: t) = inflowOf (op, o) ++ inflow t := by
  simp [inflow, inflowOf]

theorem fifoExplore2 (t : List (Op × Outcome)) (op : Op) (o : Outcome) :
    outflow ((op, o) :: t) = outflowOf (op, o) ++ outflow t := by
  simp [outflow, outflowOf]

theorem fifoExplore3 (p : Nat) (l1 l2 : List Entry) :
    classOf p (l1 ++ l2) = classOf p l1 ++ classOf p l2 := by
  simp [classOf]
#check @List.filter_append

theorem fifoClassNil2 (p : Nat) : classOf p [] = [] := by simp [classOf]

theorem fifoClassAppend2 (p : Nat) (l1 l2 : List Entry) :
    classOf p (l1 ++ l2) = classOf p l1 ++ classOf p l2 := by simp [classOf, List.filter_append]

theorem fifoInflowNil : inflow [] = [] := by simp [inflow]

theorem fifoOutflowNil : outflow [] = [] := by simp [outflow]
#check @List.filter_append
#check @beq_iff_eq

theorem fifoBeqTrue2 (a b : Nat) (h : (a == b) = true) : a = b := (beq_iff_eq.mp h)

theorem fifoClassSingleEq2 (p : Nat) (e : Entry) (h : e.prio = p) : classOf p [e] = [e] := by simp [classOf, h]

theorem fifoTestSimp1 (x : Entry) (p : Nat) (h : x.prio = p) : (x.prio == p) = true := by simp [h]

theorem fifoTestSimp2 (x : Entry) (p : Nat) (h : x.prio ≠ p) : (x.prio == p) = false := by simp [h]

theorem fifoTestClassCons (p : Nat) (x : Entry) (xs : List Entry) (h : x.prio = p) :
    classOf p (x :: xs) = x :: classOf p xs := by simp [classOf, h]

theorem fifoTestClassConsNe (p : Nat) (x : Entry) (xs : List Entry) (h : x.prio ≠ p) :
    classOf p (x :: xs) = classOf p xs := by simp [classOf, h]

theorem fifoSingleNe (p : Nat) (e : Entry) (h : e.prio ≠ p) : classOf p [e] = [] := by
  simp [classOf, h]

theorem fifoSingleEqReuse (p : Nat) (e : Entry) (h : e.prio = p) : classOf p [e] = [e] := by
  simp [classOf, h]

theorem fifoFilterNil (p : Nat) (l : List Entry) (h : ∀ y ∈ l, y.prio ≠ p) : classOf p l = [] := by
  induction l with
  | nil => simp [classOf]
  | cons x xs ih =>
    have hx : x.prio ≠ p := h x (by simp)
    have hxs : ∀ y ∈ xs, y.prio ≠ p := fun y hy => h y (List.mem_cons_of_mem x hy)
    have ih' := ih hxs
    calc classOf p (x :: xs) = classOf p xs := fifoTestClassConsNe p x xs hx
      _ = [] := ih'

theorem fifoConsSplit2 (p : Nat) (x : Entry) (xs : List Entry) :
    classOf p (x :: xs) = classOf p [x] ++ classOf p xs := by
  by_cases h : x.prio = p
  · have h1 : classOf p (x :: xs) = x :: classOf p xs := fifoTestClassCons p x xs h
    have h2 : classOf p [x] = [x] := fifoClassSingleEq2 p x h
    rw [h1, h2, List.singleton_append]
  · have h1 : classOf p (x :: xs) = classOf p xs := fifoTestClassConsNe p x xs h
    have h2 : classOf p [x] = [] := fifoSingleNe p x h
    rw [h1, h2, List.nil_append]

theorem ins_sorted_RS (e : Entry) (l : List Entry) (hS : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil =>
    simp [ins, Sorted]
  | cons x xs ih =>
    have hPair := (List.pairwise_cons.mp hS)
    have hHead : ∀ y ∈ xs, x.prio ≤ y.prio := hPair.1
    have hTail : Sorted xs := hPair.2
    have ih' := ih hTail
    by_cases hlt : e.prio < x.prio
    · have hEq : ins e (x :: xs) = e :: x :: xs := by simp [ins, hlt]
      rw [hEq]
      apply List.pairwise_cons.mpr
      constructor
      · intro y hy
        simp at hy
        rcases hy with rfl | hy
        · exact Nat.le_of_lt hlt
        · exact Nat.le_trans (Nat.le_of_lt hlt) (hHead y hy)
      · exact hS
    · have hle : x.prio ≤ e.prio := Nat.le_of_not_gt hlt
      have hEq : ins e (x :: xs) = x :: ins e xs := by simp [ins, hlt]
      rw [hEq]
      have hmem : ∀ y ∈ ins e xs, x.prio ≤ y.prio := by
        intro y hy
        have hdisj := ins_mem_aux5 e y xs hy
        rcases hdisj with rfl | hm
        · exact hle
        · exact hHead y hm
      exact List.pairwise_cons.mpr ⟨hmem, ih'⟩

theorem req_pop_effects_tmp_ok : True := trivial

private theorem popAuxCheck (s : State) (x : Entry) (xs : List Entry) (hItems : s.items = x :: xs) :
    s.items = ([] : List Entry) ++ x :: xs := by simp [hItems]







theorem plan0_valid_pop_of_not_rejected (s : State)
    (hNe : (step s .pop).1 ≠ .rejected) :
    Valid s .pop := by
  by_cases hV : Valid s .pop
  · exact hV
  · have hEq : step s .pop = (.rejected, s) := by unfold step; rw [if_neg hV]
    have hRej : (step s .pop).1 = .rejected := by rw [hEq]
    exact absurd hRej hNe




theorem plan0_valid_pop_exists_cons (s : State) (hV : Valid s .pop) :
    ∃ x xs, s.items = x :: xs ∧ Sorted (x :: xs) := by
  cases s with
  | mk cap items =>
    simp only at hV ⊢
    unfold Valid at hV
    simp only at hV
    obtain ⟨hS, hNe⟩ := hV
    cases items with
    | nil => simp at hNe
    | cons x xs => exact ⟨x, xs, rfl, hS⟩

theorem plan0_sorted_head_le (x : Entry) (xs : List Entry)
    (hS : Sorted (x :: xs)) :
    ∀ y ∈ xs, x.prio ≤ y.prio := by
  unfold Sorted at hS
  exact (List.pairwise_cons.mp hS).1

theorem plan0_step_pop_eq_of_valid_cons (s : State) (x : Entry) (xs : List Entry)
    (hV : Valid s .pop) (hItems : s.items = x :: xs) :
    step s .pop = (.got x, { s with items := xs }) := by
  unfold step
  rw [if_pos hV]
  simp [hItems]

theorem plan0_valid_pop_of_not_rejected_aux_tmp : True := trivial

private theorem plan0_valid_pop_proof_helper (s : State)
    (hNe : (step s .pop).1 ≠ .rejected) :
    Valid s .pop := by
  by_cases hV : Valid s .pop
  · exact hV
  · have hEq : step s .pop = (.rejected, s) := by unfold step; rw [if_neg hV]
    have hRej : (step s .pop).1 = .rejected := by rw [hEq]
    exact absurd hRej hNe

theorem plan0_pop_effects_of_head (s : State) (e : Entry) (xs : List Entry)
    (hItems : s.items = e :: xs)
    (hCap : (step s .pop).2.capacity = s.capacity)
    (hGot : (step s .pop).1 = .got e)
    (hTail : (step s .pop).2.items = xs)
    (hLe : ∀ y ∈ xs, e.prio ≤ y.prio) :
    (step s .pop).2.capacity = s.capacity ∧
      ∃ l₁ e' l₂, s.items = l₁ ++ e' :: l₂ ∧
        (step s .pop).1 = .got e' ∧
        (step s .pop).2.items = l₁ ++ l₂ ∧
        (∀ x ∈ l₁, e'.prio < x.prio) ∧
        (∀ x ∈ l₂, e'.prio ≤ x.prio) := by
  refine ⟨hCap, [], e, xs, ?_, hGot, ?_, ?_, hLe⟩
  · simp [hItems]
  · simp [hTail]
  · intro x hx
    simp at hx

theorem fifo_ins_class_of_sorted (p : Nat) (e : Entry) (l : List Entry) (hS : Sorted l) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := by
  obtain ⟨l₁, l₂, hEq, hInsEq, hLe1, hLt2⟩ := ins_split_helperIE e l hS
  by_cases he : e.prio = p
  · have heFilt : classOf p [e] = [e] := fifoSingleEqReuse p e he
    have hL2Empty : classOf p l₂ = [] := by
      apply fifoFilterNil p l₂
      intro y hy
      have hlt : e.prio < y.prio := hLt2 y hy
      omega
    have hL : classOf p l = classOf p l₁ := by
      rw [hEq, fifoClassAppend2, hL2Empty, List.append_nil]
    have hCons : classOf p (e :: l₂) = e :: classOf p l₂ := fifoTestClassCons p e l₂ he
    have hIns : classOf p (ins e l) = classOf p l₁ ++ [e] := by
      rw [hInsEq, fifoClassAppend2, hCons, hL2Empty]
    rw [hIns, hL, heFilt]
  · have heFilt : classOf p [e] = [] := fifoSingleNe p e he
    have hConsNe : classOf p (e :: l₂) = classOf p l₂ := fifoTestClassConsNe p e l₂ he
    have hIns : classOf p (ins e l) = classOf p l := by
      rw [hInsEq, hEq, fifoClassAppend2, fifoClassAppend2, hConsNe]
    rw [hIns, heFilt, List.append_nil]

theorem fifo_probe1 (e : Entry) : inflowOf (.insert e, .ok) = [e] := by simp [inflowOf]

theorem fifo_probe2 (e : Entry) : outflowOf (.insert e, .ok) = ([] : List Entry) := by simp [outflowOf]

theorem fifo_probe3 (x : Entry) : outflowOf (.pop, .got x) = [x] := by simp [outflowOf]

theorem fifo_probe4 (x : Entry) : inflowOf (.pop, .got x) = ([] : List Entry) := by simp [inflowOf]

theorem plan1_step_class_invalid (s : State) (op : Op) (p : Nat)
    (h : ¬ Valid s op) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by
  have hEq : step s op = (.rejected, s) := by unfold step; rw [if_neg h]
  have h1 : (step s op).1 = .rejected := by rw [hEq]
  have h2 : (step s op).2.items = s.items := by rw [hEq]
  cases op with
  | insert e =>
    have hi : inflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
      rw [h1]; simp [inflowOf]
    have ho : outflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
      rw [h1]; simp [outflowOf]
    rw [hi, ho, h2]
    simp [classOf]
  | pop =>
    have hi : inflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
      rw [h1]; simp [inflowOf]
    have ho : outflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
      rw [h1]; simp [outflowOf]
    rw [hi, ho, h2]
    simp [classOf]






theorem plan1_step_class (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have hS : Sorted s.items := hV.1
      have hStep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := testIE s e hV
      have h1 : (step s (.insert e)).1 = .ok := by rw [hStep]
      have h2 : (step s (.insert e)).2.items = ins e s.items := by rw [hStep]
      rw [h1, h2]
      simp only [inflowOf, outflowOf]
      have hIns : classOf p (ins e s.items) = classOf p s.items ++ classOf p [e] :=
        fifo_ins_class_of_sorted p e s.items hS
      rw [hIns]
      simp [classOf]
    | pop =>
      obtain ⟨x, xs, hItems, hS⟩ := plan0_valid_pop_exists_cons s hV
      have hStep : step s .pop = (.got x, { s with items := xs }) :=
        plan0_step_pop_eq_of_valid_cons s x xs hV hItems
      have h1 : (step s .pop).1 = .got x := by rw [hStep]
      have h2 : (step s .pop).2.items = xs := by rw [hStep]
      rw [h1, h2, hItems]
      have hIn : inflowOf (.pop, .got x) = ([] : List Entry) := by simp [inflowOf]
      have hOut : outflowOf (.pop, .got x) = [x] := by simp [outflowOf]
      rw [hIn, hOut]
      rw [fifoConsSplit2 p x xs, fifoClassNil2 p, List.append_nil]
  · exact plan1_step_class_invalid s op p hV


theorem plan1_run_class (ops : List Op) (s : State) (p : Nat) :
    classOf p s.items ++ classOf p (inflow (run step s ops).1) =
      classOf p (outflow (run step s ops).1) ++
        classOf p (run step s ops).2.items := by
  induction ops generalizing s with
  | nil =>
    have hR : run step s ([] : List Op) = ([], s) := by simp [run]
    rw [hR]
    simp [inflow, outflow, classOf]
  | cons op ops ih =>
    have hStep := plan1_step_class s op p
    have hIH := ih ((step s op).2)
    have hRun1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by simp only [run]
    have hRun2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by simp only [run]
    rw [hRun1, hRun2]
    have hIn : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by simp [inflow, inflowOf]
    have hOut : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by simp [outflow, outflowOf]
    rw [hIn, hOut]
    rw [fifoClassAppend2, fifoClassAppend2]
    calc classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1))
        = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [hStep]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops).1)) := by rw [List.append_assoc]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops).1) ++ classOf p (run step (step s op).2 ops).2.items) := by rw [hIH]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1)) ++ classOf p (run step (step s op).2 ops).2.items := by rw [List.append_assoc]


theorem plan1_invalid_aux_unique_dummy : True := trivial


theorem plan1_step_class_invalid_selfcontained_test (s : State) (op : Op) (p : Nat)
    (h : ¬ Valid s op) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by
  have hEq : step s op = (.rejected, s) := by unfold step; rw [if_neg h]
  have h1 : (step s op).1 = .rejected := by rw [hEq]
  have h2 : (step s op).2.items = s.items := by rw [hEq]
  cases op with
  | insert e =>
    have hi : inflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
      rw [h1]; simp [inflowOf]
    have ho : outflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
      rw [h1]; simp [outflowOf]
    rw [hi] at *
    rw [ho] at *
    rw [h2] at *
    simp [classOf]
  | pop =>
    have hi : inflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
      rw [h1]; simp [inflowOf]
    have ho : outflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
      rw [h1]; simp [outflowOf]
    rw [hi] at *
    rw [ho] at *
    rw [h2] at *
    simp [classOf]









theorem plan2_step_class_of_invalid (s : State) (op : Op) (p : Nat)
    (h : ¬ Valid s op) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by
  have hEq : step s op = (.rejected, s) := by unfold step; rw [if_neg h]
  have h1 : (step s op).1 = .rejected := by rw [hEq]
  have h2 : (step s op).2.items = s.items := by rw [hEq]
  cases op with
  | insert e =>
    have hi : inflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
      rw [h1]; simp [inflowOf]
    have ho : outflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
      rw [h1]; simp [outflowOf]
    rw [hi, ho, h2]
    simp [classOf]
  | pop =>
    have hi : inflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
      rw [h1]; simp [inflowOf]
    have ho : outflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
      rw [h1]; simp [outflowOf]
    rw [hi, ho, h2]
    simp [classOf]


theorem plan2_step_rejected_eq (s : State) (op : Op) (h : ¬ Valid s op) :
    step s op = (.rejected, s) := by unfold step; rw [if_neg h]

theorem plan2_inflowOf_rejected (op : Op) :
    inflowOf (op, .rejected) = ([] : List Entry) := by
  cases op with
  | insert e => simp [inflowOf]
  | pop => simp [inflowOf]

theorem plan2_outflowOf_rejected (op : Op) :
    outflowOf (op, .rejected) = ([] : List Entry) := by
  cases op with
  | insert e => simp [outflowOf]
  | pop => simp [outflowOf]

theorem plan2_classOf_nil_eq (p : Nat) :
    classOf p ([] : List Entry) = ([] : List Entry) := by simp [classOf]

theorem plan2_step_class_of_invalid_test_unique (s : State) (op : Op) (p : Nat)
    (h : ¬ Valid s op) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by
  have hEq : step s op = (.rejected, s) := plan2_step_rejected_eq s op h
  have h1 : (step s op).1 = .rejected := by rw [hEq]
  have h2 : (step s op).2 = s := by rw [hEq]
  have hIn : inflowOf (op, (step s op).1) = ([] : List Entry) := by rw [h1]; exact plan2_inflowOf_rejected op
  have hOut : outflowOf (op, (step s op).1) = ([] : List Entry) := by rw [h1]; exact plan2_outflowOf_rejected op
  have hItems : (step s op).2.items = s.items := by rw [h2]
  rw [hIn, hOut, hItems]
  simp [classOf]

theorem plan2_selfcontained_check (s : State) (op : Op) (p : Nat)
    (h : ¬ Valid s op) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by
  have hEq : step s op = (.rejected, s) := by unfold step; rw [if_neg h]
  have h1 : (step s op).1 = .rejected := by rw [hEq]
  have h2 : (step s op).2.items = s.items := by rw [hEq]
  cases op with
  | insert e =>
    have hi : inflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
      rw [h1]; simp [inflowOf]
    have ho : outflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
      rw [h1]; simp [outflowOf]
    rw [hi, ho, h2]
    simp [classOf]
  | pop =>
    have hi : inflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
      rw [h1]; simp [inflowOf]
    have ho : outflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
      rw [h1]; simp [outflowOf]
    rw [hi, ho, h2]
    simp [classOf]

theorem plan1_step_class_invalid_check_tmp (s : State) (op : Op) (p : Nat)
    (h : ¬ Valid s op) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by
  have hEq : step s op = (.rejected, s) := by unfold step; rw [if_neg h]
  have h1 : (step s op).1 = .rejected := by rw [hEq]
  have h2 : (step s op).2.items = s.items := by rw [hEq]
  cases op with
  | insert e =>
    have hi : inflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
      rw [h1]; simp [inflowOf]
    have ho : outflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
      rw [h1]; simp [outflowOf]
    rw [hi, ho, h2]
    simp [classOf]
  | pop =>
    have hi : inflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
      rw [h1]; simp [inflowOf]
    have ho : outflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
      rw [h1]; simp [outflowOf]
    rw [hi, ho, h2]
    simp [classOf]

theorem plan1_step_class_insert (s : State) (e : Entry) (p : Nat)
    (hV : Valid s (.insert e)) :
    classOf p s.items ++
        classOf p (inflowOf (.insert e, (step s (.insert e)).1)) =
      classOf p (outflowOf (.insert e, (step s (.insert e)).1)) ++
        classOf p (step s (.insert e)).2.items := by
  have hS : Sorted s.items := hV.1
  have hStep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := testIE s e hV
  have h1 : (step s (.insert e)).1 = .ok := by rw [hStep]
  have h2 : (step s (.insert e)).2.items = ins e s.items := by rw [hStep]
  rw [h1, h2]
  simp only [inflowOf, outflowOf]
  have hIns : classOf p (ins e s.items) = classOf p s.items ++ classOf p [e] :=
    fifo_ins_class_of_sorted p e s.items hS
  rw [hIns]
  simp [classOf]

theorem plan1_step_class_pop (s : State) (p : Nat)
    (hV : Valid s .pop) :
    classOf p s.items ++ classOf p (inflowOf (.pop, (step s .pop).1)) =
      classOf p (outflowOf (.pop, (step s .pop).1)) ++
        classOf p (step s .pop).2.items := by
  obtain ⟨x, xs, hItems, hS⟩ := plan0_valid_pop_exists_cons s hV
  have hStep : step s .pop = (.got x, { s with items := xs }) :=
    plan0_step_pop_eq_of_valid_cons s x xs hV hItems
  have h1 : (step s .pop).1 = .got x := by rw [hStep]
  have h2 : (step s .pop).2.items = xs := by rw [hStep]
  rw [h1, h2, hItems]
  have hIn : inflowOf (.pop, .got x) = ([] : List Entry) := by simp [inflowOf]
  have hOut : outflowOf (.pop, .got x) = [x] := by simp [outflowOf]
  rw [hIn, hOut]
  rw [fifoConsSplit2 p x xs, fifoClassNil2 p, List.append_nil]

theorem plan1_step_class_proof_helper_unique (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by
  by_cases hV : Valid s op
  · cases op with
    | insert e => exact plan1_step_class_insert s e p hV
    | pop => exact plan1_step_class_pop s p hV
  · exact plan1_step_class_invalid s op p hV

theorem plan1_step_class_check_unique2 (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by
  by_cases hV : Valid s op
  · cases op with
    | insert e => exact plan1_step_class_insert s e p hV
    | pop => exact plan1_step_class_pop s p hV
  · exact plan1_step_class_invalid s op p hV

theorem plan1_step_class_final_unique_wrap (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items :=
  plan1_step_class_proof_helper_unique s op p

theorem plan1_step_class_inline_test (s : State) (op : Op) (p : Nat) :
    True := trivial

theorem plan1_run_class_test_unfold (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
  simp only [run]

theorem plan1_run_class_test_unfold2 (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
  simp only [run]

theorem plan1_run_class_pf2 (ops : List Op) (s : State) (p : Nat) :
    classOf p s.items ++ classOf p (inflow (run step s ops).1) =
      classOf p (outflow (run step s ops).1) ++
        classOf p (run step s ops).2.items := by
  induction ops generalizing s with
  | nil =>
    have hR : run step s ([] : List Op) = ([], s) := by simp [run]
    rw [hR]
    simp [inflow, outflow, classOf]
  | cons op ops ih =>
    have hStep := plan1_step_class s op p
    have hIH := ih ((step s op).2)
    have hRun1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by simp only [run]
    have hRun2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by simp only [run]
    rw [hRun1, hRun2]
    have hIn : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by simp [inflow, inflowOf]
    have hOut : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by simp [outflow, outflowOf]
    rw [hIn, hOut]
    rw [fifoClassAppend2, fifoClassAppend2]
    calc classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1))
        = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [hStep]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops).1)) := by rw [List.append_assoc]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops).1) ++ classOf p (run step (step s op).2 ops).2.items) := by rw [hIH]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1)) ++ classOf p (run step (step s op).2 ops).2.items := by rw [List.append_assoc]

theorem plan1_run_class_direct_inline_check (ops : List Op) (s : State) (p : Nat) :
    classOf p s.items ++ classOf p (inflow (run step s ops).1) =
      classOf p (outflow (run step s ops).1) ++
        classOf p (run step s ops).2.items := by
  induction ops generalizing s with
  | nil =>
    have hR : run step s ([] : List Op) = ([], s) := by simp [run]
    rw [hR]
    simp [inflow, outflow, classOf]
  | cons op ops ih =>
    have hStep := plan1_step_class s op p
    have hIH := ih ((step s op).2)
    have hRun1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by simp only [run]
    have hRun2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by simp only [run]
    rw [hRun1, hRun2]
    have hIn : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by simp [inflow, inflowOf]
    have hOut : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by simp [outflow, outflowOf]
    rw [hIn, hOut]
    rw [fifoClassAppend2, fifoClassAppend2]
    calc classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1))
        = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [hStep]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops).1)) := by rw [List.append_assoc]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops).1) ++ classOf p (run step (step s op).2 ops).2.items) := by rw [hIH]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1)) ++ classOf p (run step (step s op).2 ops).2.items := by rw [List.append_assoc]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  unfold step
  rw [if_pos hV]
  cases op with
  | insert e => simp
  | pop =>
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
  intro s op hLen
  by_cases hV : Valid s op
  · have hStep : step s op = if Valid s op then
      match op, s.items with
      | .insert e, _ => (.ok, { s with items := ins e s.items })
      | .pop, x :: xs => (.got x, { s with items := xs })
      | .pop, [] => (.rejected, s)
      else (.rejected, s) := by unfold step; rfl
    -- unfold step in context? Let's reason directly
    unfold CapacityBound at *
    -- Actually prove goal directly
    cases op with
    | insert e =>
      have hV' : Valid s (.insert e) := hV
      have hS : Sorted s.items := hV'.1
      have hLt : s.items.length < s.capacity := hV'.2
      have hEq : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
        unfold step; rw [if_pos hV']
      have hLenEq : (ins e s.items).length = s.items.length + 1 := ins_length_thm4 e s.items
      have hGoal1 : (step s (.insert e)).2.items = ins e s.items := by rw [hEq]
      have hGoal2 : (step s (.insert e)).2.capacity = s.capacity := by rw [hEq]
      rw [hGoal1, hGoal2]
      omega
    | pop =>
      have hV' : Valid s .pop := hV
      have hNe : s.items ≠ [] := hV'.2
      cases hItems : s.items with
      | nil => simp [hItems] at hNe
      | cons x xs =>
        have hEq : step s .pop = (.got x, { s with items := xs }) := by
          unfold step; rw [if_pos hV']; simp [hItems]
        have hG1 : (step s .pop).2.items = xs := by rw [hEq]
        have hG2 : (step s .pop).2.capacity = s.capacity := by rw [hEq]
        rw [hG1, hG2]
        rw [hItems] at hLen
        simp at hLen ⊢
        omega
  · have hEq : step s op = (.rejected, s) := by unfold step; rw [if_neg hV]
    have h1 : (step s op).2.items = s.items := by rw [hEq]
    have h2 : (step s op).2.capacity = s.capacity := by rw [hEq]
    rw [h1, h2]
    exact hLen

theorem req_pop_min : PopMin step := by
  intro s hNe
  by_cases hV : Valid s .pop
  · have hSort : Sorted s.items := hV.1
    have hNeList : s.items ≠ [] := hV.2
    cases hItems : s.items with
    | nil => simp [hItems] at hNeList
    | cons x xs =>
      have hStep : step s .pop = (.got x, { s with items := xs }) := by
        unfold step
        rw [if_pos hV]
        simp [hItems]
      refine ⟨x, ?_, ?_⟩
      · rw [hStep]
      · have hEq : (step s .pop).2.items = xs := by rw [hStep]
        rw [hEq]
        intro y hy
        have hPw : List.Pairwise (fun a b : Entry => a.prio ≤ b.prio) (x :: xs) := by
          rw [← hItems]; exact hSort
        have hMem := (List.pairwise_cons.mp hPw).1
        exact hMem y hy
  · have hStep : step s .pop = (.rejected, s) := req_invalid_noop s .pop hV
    have hRej : (step s .pop).1 = .rejected := by rw [hStep]
    exact absurd hRej hNe

theorem req_sorted : KeepsSorted step := by
  intro s op hS
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have hEq : (step s (.insert e)).2.items = ins e s.items := by
        unfold step
        rw [if_pos hV]
      rw [hEq]
      exact ins_sorted_RS e s.items hS
    | pop =>
      cases hItems : s.items with
      | nil =>
        have hNe : s.items ≠ [] := hV.2
        rw [hItems] at hNe
        exact absurd rfl hNe
      | cons x xs =>
        have hEq : (step s .pop).2.items = xs := by
          unfold step
          rw [if_pos hV]
          simp [hItems]
        rw [hEq]
        have hS' : Sorted (x :: xs) := by rw [← hItems]; exact hS
        exact sorted_tail_aux2 x xs hS'
  · have hEq : (step s op).2.items = s.items := by
      unfold step
      rw [if_neg hV]
    rw [hEq]
    exact hS

theorem req_insert_effects : InsertEffects step := by
  intro s e hNe
  by_cases hV : Valid s (.insert e)
  · have hS : Sorted s.items := hV.1
    obtain ⟨l₁, l₂, hEq, hInsEq, hLe1, hLt2⟩ := ins_split_helperIE e s.items hS
    have hStep := testIE s e hV
    have h1 : (step s (.insert e)).1 = .ok := by rw [hStep]
    have h2 : (step s (.insert e)).2.capacity = s.capacity := by rw [hStep]
    have h3 : (step s (.insert e)).2.items = l₁ ++ e :: l₂ := by
      have hI : (step s (.insert e)).2.items = ins e s.items := by rw [hStep]
      rw [hI, hInsEq]
    exact ⟨h1, h2, l₁, l₂, hEq, h3, hLe1, hLt2⟩
  · have hStep := req_invalid_noop s (.insert e) hV
    have hRej : (step s (.insert e)).1 = .rejected := by rw [hStep]
    exact absurd hRej hNe

theorem req_pop_effects : PopEffects step := by
  intro s hNe
  have hV : Valid s .pop := plan0_valid_pop_of_not_rejected s hNe
  obtain ⟨x, xs, hItems, hS⟩ := plan0_valid_pop_exists_cons s hV
  have hStep : step s .pop = (.got x, { s with items := xs }) :=
    plan0_step_pop_eq_of_valid_cons s x xs hV hItems
  have hCap : (step s .pop).2.capacity = s.capacity := by rw [hStep]
  have hGot : (step s .pop).1 = .got x := by rw [hStep]
  have hTail : (step s .pop).2.items = xs := by rw [hStep]
  have hLe : ∀ y ∈ xs, x.prio ≤ y.prio := plan0_sorted_head_le x xs hS
  exact plan0_pop_effects_of_head s x xs hItems hCap hGot hTail hLe

theorem req_fifo_ties : FifoTies step := fun s ops p => plan1_run_class ops s p

end PrioQueue
