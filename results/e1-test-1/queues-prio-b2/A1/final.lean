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

def fooTest : Nat := 1

theorem fooLemma2 : 1 = 1 := rfl

theorem ins_length_thm (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    split
    · simp
    · simp [ih]

theorem testPairwise (x : Entry) (xs : List Entry) (h : Sorted (x :: xs)) : Sorted xs := by
  cases h with
  | cons h1 h2 => exact h2
  def dummyTest2 : Nat := 2

theorem pairwiseNil : Sorted ([] : List Entry) := .nil

theorem pairwiseSingle (e : Entry) : Sorted [e] := .cons (fun y hy => by simp at hy) .nil
#check List.Pairwise
#check @List.pairwise_cons

theorem insMemAux (e y : Entry) (l : List Entry) (h : y ∈ ins e l) : y = e ∨ y ∈ l := by
  induction l with
  | nil =>
    simp [ins] at h
    exact Or.inl h
  | cons x xs ih =>
    unfold ins at h
    split at h
    · simp at h
      rcases h with rfl | rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (by simp)
      · exact Or.inr (by simp [hx])
    · simp at h
      rcases h with rfl | hm
      · exact Or.inr (by simp)
      · rcases ih hm with rfl | hm2
        · exact Or.inl rfl
        · exact Or.inr (by simp [hm2])

theorem pairwiseConsLem (R : Entry → Entry → Prop) (x : Entry) (l : List Entry) :
  List.Pairwise R (x :: l) → (∀ y ∈ l, R x y) ∧ List.Pairwise R l := by
  intro h
  cases h with
  | cons h1 h2 => exact ⟨h1, h2⟩

theorem pairwiseMkLem (R : Entry → Entry → Prop) (x : Entry) (l : List Entry)
  (h1 : ∀ y ∈ l, R x y) (h2 : List.Pairwise R l) : List.Pairwise R (x :: l) :=
  List.Pairwise.cons h1 h2

theorem ins_sorted_aux3 (e : Entry) (l : List Entry) (h : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil => simp [ins, Sorted]
  | cons x xs ih =>
    unfold ins
    split
    · next hlt =>
      have hle : e.prio ≤ x.prio := Nat.le_of_lt hlt
      apply List.Pairwise.cons _ h
      intro y hy
      simp at hy
      rcases hy with rfl | hy2
      · exact hle
      · obtain ⟨hhead, _⟩ := pairwiseConsLem _ _ _ h
        exact Nat.le_trans hle (hhead y hy2)
    · next hnge =>
      have hle : x.prio ≤ e.prio := Nat.le_of_not_gt hnge
      obtain ⟨hhead, htail⟩ := pairwiseConsLem _ _ _ h
      have ih' := ih htail
      apply List.Pairwise.cons _ ih'
      intro y hy
      rcases insMemAux e y xs hy with rfl | hy2
      · exact hle
      · exact hhead y hy2

theorem sortedProbe (s : State) (e : Entry) (hv : Valid s (.insert e)) :
  (step s (.insert e)).2.items = ins e s.items := by
  unfold step
  rw [if_pos hv]

theorem dummyInsertTest : True := trivial

theorem insSplitSortedAux2 (e : Entry) (l : List Entry) (h : Sorted l) :
  ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧
    (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil =>
    exact ⟨[], [], rfl, by simp [ins], by simp, by simp⟩
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := pairwiseConsLem _ _ _ h
    by_cases hlt : e.prio < x.prio
    · refine ⟨[], x :: xs, rfl, ?_, by simp, ?_⟩
      · simp [ins, hlt]
      · intro y hy
        simp at hy
        rcases hy with rfl | hy2
        · exact hlt
        · exact Nat.lt_of_lt_of_le hlt (hhead y hy2)
    · have hle : x.prio ≤ e.prio := Nat.le_of_not_gt hlt
      obtain ⟨l1', l2', heq, heq2, h1', h2'⟩ := ih htail
      refine ⟨x :: l1', l2', ?_, ?_, ?_, h2'⟩
      · simp [heq]
      · simp [ins, hlt, heq2]
      · intro y hy
        simp at hy
        rcases hy with rfl | hy2
        · exact hle
        · exact h1' y hy2

theorem class_append_thm (p : Nat) (l1 l2 : List Entry) : classOf p (l1 ++ l2) = classOf p l1 ++ classOf p l2 := by
  unfold classOf
  rw [List.filter_append]

theorem class_nil_thm (p : Nat) : classOf p [] = [] := by
  unfold classOf
  simp

theorem class_cons_thm (p : Nat) (x : Entry) (xs : List Entry) :
  classOf p (x :: xs) = (if x.prio == p then [x] else []) ++ classOf p xs := by
  unfold classOf
  simp
  split
  · simp_all
  · simp_all

theorem inflow_cons_thm (a : Op × Outcome) (t : List (Op × Outcome)) :
  inflow (a :: t) = inflowOf a ++ inflow t := by
  unfold inflow
  simp

theorem outflow_cons_thm (a : Op × Outcome) (t : List (Op × Outcome)) :
  outflow (a :: t) = outflowOf a ++ outflow t := by
  unfold outflow
  simp

theorem run_cons_fst (s : State) (op : Op) (ops : List Op) :
  (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
  simp [run]

theorem run_cons_snd (s : State) (op : Op) (ops : List Op) :
  (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
  simp [run]

theorem beq_true_probe (a b : Nat) (h : (a == b) = true) : a = b := by
  exact Nat.eq_of_beq_eq_true h
#check @Nat.eq_of_beq_eq_true
#check List.filter_cons

theorem req_capacity_aux_test (s : State) (e : Entry) (hv : Valid s (.insert e)) :
    step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
  unfold step
  simp [hv]

theorem myCapTest1 (s : State) (e : Entry) : True := by
  by_cases hv : Valid s (.insert e)
  · trivial
  · trivial

theorem myCapDbg2 (s : State) (e : Entry) (hv : Valid s (.insert e)) : s.items.length < s.capacity := by
  exact hv.2

theorem beqToEqAux (a b : Nat) (h : (a == b) = true) : a = b := by
  simpa using h

theorem beqFalseAux (a b : Nat) (h : a ≠ b) : (a == b) = false := by
  simp [h]

theorem classAppendAux2 (p : Nat) (l1 l2 : List Entry) :
  classOf p (l1 ++ l2) = classOf p l1 ++ classOf p l2 := by
  unfold classOf
  simp only [List.filter_append]

theorem classSingleEmptyAux (p : Nat) (e : Entry) (h : (e.prio == p) = false) :
  classOf p [e] = [] := by
  unfold classOf
  simp [h]

theorem classConsDistAux (p : Nat) (x : Entry) (xs : List Entry) :
  classOf p (x :: xs) = classOf p [x] ++ classOf p xs := by
  have h : ([x] ++ xs) = (x :: xs) := by simp
  have h2 : classOf p ([x] ++ xs) = classOf p [x] ++ classOf p xs := classAppendAux2 p [x] xs
  rw [h] at h2
  exact h2

theorem classTripleAux (p : Nat) (a b : Entry) (l : List Entry) :
  classOf p (a :: b :: l) = classOf p [a] ++ classOf p (b :: l) := by
  exact classConsDistAux p a (b :: l)

theorem classOfNilAux (p : Nat) : classOf p [] = [] := by
  unfold classOf
  simp

theorem classOfEmptyOfGtAux (p : Nat) (e : Entry) (a2 : List Entry)
  (heb : e.prio = p) (ha2 : ∀ x ∈ a2, e.prio < x.prio) : classOf p a2 = [] := by
  induction a2 with
  | nil => exact classOfNilAux p
  | cons y ys ih =>
    have hy : e.prio < y.prio := ha2 y (by simp)
    have hne : y.prio ≠ p := by omega
    have hfalse : (y.prio == p) = false := beqFalseAux y.prio p hne
    have hys : ∀ x ∈ ys, e.prio < x.prio := fun x hx => ha2 x (by simp [hx])
    have ih2 := ih hys
    have hdist := classConsDistAux p y ys
    rw [ih2] at hdist
    have hsing : classOf p [y] = [] := classSingleEmptyAux p y hfalse
    rw [hsing] at hdist
    simp at hdist
    exact hdist

theorem insFilterCommAux2 (p : Nat) (e : Entry) (l : List Entry) (h : Sorted l) :
  classOf p (ins e l) = classOf p l ++ classOf p [e] := by
  obtain ⟨a1, a2, haeq, hains, ha1, ha2⟩ := insSplitSortedAux2 e l h
  have e1 : classOf p (ins e l) = classOf p a1 ++ classOf p [e] ++ classOf p a2 := by
    rw [hains, classAppendAux2 p a1 (e :: a2), classConsDistAux p e a2, List.append_assoc]
  have e2 : classOf p l = classOf p a1 ++ classOf p a2 := by
    rw [haeq]
    exact classAppendAux2 p a1 a2
  rw [e1, e2]
  by_cases he : (e.prio == p) = true
  · have heb : e.prio = p := beqToEqAux e.prio p he
    have hnil : classOf p a2 = [] := classOfEmptyOfGtAux p e a2 heb ha2
    rw [hnil]
    simp
  · have hfalse : (e.prio == p) = false := by
      cases hh : (e.prio == p) with
      | true => simp [hh] at he
      | false => rfl
    have hsing : classOf p [e] = [] := classSingleEmptyAux p e hfalse
    rw [hsing]
    simp

theorem probeInflow1 (e : Entry) : inflowOf (.insert e, .ok) = [e] := rfl

theorem probeInflow2 (e : Entry) : outflowOf (.insert e, .ok) = [] := rfl

theorem probeInflow3 (e : Entry) : inflowOf (.insert e, .rejected) = [] := rfl

theorem probeOut3 (x : Entry) : outflowOf (.pop, .got x) = [x] := rfl

theorem probeIn4 (x : Entry) : inflowOf (.pop, .got x) = [] := rfl

theorem fifo_single_probe2 (s : State) : (s.items = s.items) := rfl

theorem fifo_pop_inflow_nil (o : Outcome) : inflowOf (.pop, o) = ([] : List Entry) := by
  cases o <;> rfl

theorem fifo_ins_outflow_nil (e : Entry) : outflowOf (.insert e, .ok) = ([] : List Entry) := rfl

theorem fifo_ins_inflow_ok (e : Entry) : inflowOf (.insert e, .ok) = [e] := rfl

theorem fifo_pop_outflow_got (x : Entry) : outflowOf (.pop, .got x) = [x] := rfl

theorem fifoSingleStepC (s : State) (op : Op) (p : Nat) :
  classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
    = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  cases op with
  | insert e =>
    by_cases hv : Valid s (.insert e)
    · have hstep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
        unfold step; rw [if_pos hv]
      have hout : (step s (.insert e)).1 = .ok := by rw [hstep]
      have hitems : (step s (.insert e)).2.items = ins e s.items := by rw [hstep]
      have hsorted : Sorted s.items := hv.1
      have hins : classOf p (ins e s.items) = classOf p s.items ++ classOf p [e] :=
        insFilterCommAux2 p e s.items hsorted
      have hinflow : inflowOf ((.insert e), (step s (.insert e)).1) = [e] := by
        simp [hout, inflowOf]
      have houtflow : outflowOf ((.insert e), (step s (.insert e)).1) = ([] : List Entry) := by
        simp [hout, outflowOf]
      rw [hinflow, houtflow, hitems, hins]
      simp [classOfNilAux]
    · have hstep : step s (.insert e) = (.rejected, s) := by
        unfold step; rw [if_neg hv]
      have hout : (step s (.insert e)).1 = .rejected := by rw [hstep]
      have hitems : (step s (.insert e)).2.items = s.items := by rw [hstep]
      have hinflow : inflowOf ((.insert e), (step s (.insert e)).1) = ([] : List Entry) := by
        simp [hout, inflowOf]
      have houtflow : outflowOf ((.insert e), (step s (.insert e)).1) = ([] : List Entry) := by
        simp [hout, outflowOf]
      rw [hinflow, houtflow, hitems]
      simp [classOfNilAux]
  | pop =>
    by_cases hv : Valid s .pop
    · have hne : s.items ≠ [] := hv.2
      cases hcon : s.items with
      | nil => exact absurd hcon hne
      | cons x xs =>
        have hstep : step s .pop = (.got x, { s with items := xs }) := by
          unfold step; rw [if_pos hv, hcon]
        have hout : (step s .pop).1 = .got x := by rw [hstep]
        have hitems2 : (step s .pop).2.items = xs := by rw [hstep]
        have hinflow : inflowOf (.pop, (step s .pop).1) = ([] : List Entry) := by
          simp [inflowOf]
        have houtflow : outflowOf (.pop, (step s .pop).1) = [x] := by
          simp [hout, outflowOf]
        rw [hinflow, houtflow, hitems2]
        have hdist := classConsDistAux p x xs
        have hnil : classOf p ([] : List Entry) = [] := classOfNilAux p
        rw [hnil, hdist]
        simp
    · have hstep : step s .pop = (.rejected, s) := by
        unfold step; rw [if_neg hv]
      have hout : (step s .pop).1 = .rejected := by rw [hstep]
      have hitems : (step s .pop).2.items = s.items := by rw [hstep]
      have hinflow : inflowOf (.pop, (step s .pop).1) = ([] : List Entry) := by
        simp [inflowOf]
      have houtflow : outflowOf (.pop, (step s .pop).1) = ([] : List Entry) := by
        simp [hout, outflowOf]
      rw [hinflow, houtflow, hitems]
      simp [classOfNilAux]

theorem fifoInOutConsB (a : Op × Outcome) (t : List (Op × Outcome)) (p : Nat) :
  classOf p (inflow (a :: t)) = classOf p (inflowOf a) ++ classOf p (inflow t) := by
  rw [inflow_cons_thm]
  exact classAppendAux2 p (inflowOf a) (inflow t)

theorem fifoOutConsAuxB (a : Op × Outcome) (t : List (Op × Outcome)) (p : Nat) :
  classOf p (outflow (a :: t)) = classOf p (outflowOf a) ++ classOf p (outflow t) := by
  rw [outflow_cons_thm]
  exact classAppendAux2 p (outflowOf a) (outflow t)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  unfold step
  rw [if_pos h]
  cases op with
  | insert e => simp
  | pop =>
    simp only [Valid] at h
    obtain ⟨hsorted, hne⟩ := h
    cases hitems : s.items
    case nil => exact absurd hitems hne
    case cons x xs => simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  unfold step
  rw [if_neg h]

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | insert e =>
    by_cases hv : Valid s (.insert e)
    · have hlt : s.items.length < s.capacity := hv.2
      have hstep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
        unfold step
        rw [if_pos hv]
      have hlen : (step s (.insert e)).2.items.length = s.items.length + 1 := by
        rw [hstep]
        simp [ins_length_thm]
      have hcap : (step s (.insert e)).2.capacity = s.capacity := by
        rw [hstep]
      rw [hlen, hcap]
      omega
    · have hstep : step s (.insert e) = (.rejected, s) := by
        unfold step
        rw [if_neg hv]
      rw [hstep]
      simpa using hle
  | pop =>
    by_cases hv : Valid s .pop
    · have hne : s.items ≠ [] := hv.2
      cases hitems : s.items with
      | nil => exact absurd hitems hne
      | cons x xs =>
        have hstep : step s .pop = (.got x, { s with items := xs }) := by
          unfold step
          rw [if_pos hv, hitems]
        have hlen : (step s .pop).2.items.length = xs.length := by
          rw [hstep]
        have hcap : (step s .pop).2.capacity = s.capacity := by
          rw [hstep]
        rw [hlen, hcap]
        have hlen2 : s.items.length = xs.length + 1 := by
          rw [hitems]; simp
        omega
    · have hstep : step s .pop = (.rejected, s) := by
        unfold step
        rw [if_neg hv]
      rw [hstep]
      simpa using hle

theorem req_pop_min : PopMin step := by
  intro s hrej
  by_cases hv : Valid s .pop
  · have hsort_ne : Sorted s.items ∧ s.items ≠ [] := hv
    obtain ⟨hsorted, hne⟩ := hsort_ne
    cases hitems : s.items with
    | nil => exact absurd hitems hne
    | cons x xs =>
      have heq : step s .pop = (.got x, { s with items := xs }) := by
        unfold step
        rw [if_pos hv, hitems]
      refine ⟨x, ?_, ?_⟩
      · rw [heq]
      · rw [heq]
        simp only
        intro y hy
        have hsorted' : Sorted (x :: xs) := hitems ▸ hsorted
        cases hsorted' with
        | cons hhead _ => exact hhead y hy
  · have heq : step s .pop = (.rejected, s) := by
      unfold step
      rw [if_neg hv]
    rw [heq] at hrej
    simp at hrej

theorem req_sorted : KeepsSorted step := by
  intro s op hsorted
  cases op with
  | insert e =>
    by_cases hv : Valid s (.insert e)
    · have hstep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
        unfold step
        rw [if_pos hv]
      have h2 : (step s (.insert e)).2.items = ins e s.items := by rw [hstep]
      rw [h2]
      exact ins_sorted_aux3 e s.items hsorted
    · have hstep : step s (.insert e) = (.rejected, s) := by
        unfold step
        rw [if_neg hv]
      have h2 : (step s (.insert e)).2.items = s.items := by rw [hstep]
      rw [h2]
      exact hsorted
  | pop =>
    by_cases hv : Valid s .pop
    · cases hitems : s.items with
      | nil =>
        have hne : s.items ≠ [] := hv.2
        exact absurd hitems hne
      | cons x xs =>
        have hstep : step s .pop = (.got x, { s with items := xs }) := by
          unfold step
          rw [if_pos hv, hitems]
        have h2 : (step s .pop).2.items = xs := by rw [hstep]
        rw [h2]
        have hsorted' : Sorted (x :: xs) := hitems ▸ hsorted
        exact testPairwise x xs hsorted'
    · have hstep : step s .pop = (.rejected, s) := by
        unfold step
        rw [if_neg hv]
      have h2 : (step s .pop).2.items = s.items := by rw [hstep]
      rw [h2]
      exact hsorted

theorem req_insert_effects : InsertEffects step := by
  intro s e hne
  by_cases hv : Valid s (.insert e)
  · have hstep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
      unfold step
      rw [if_pos hv]
    have hout : (step s (.insert e)).1 = .ok := by rw [hstep]
    have hcap : (step s (.insert e)).2.capacity = s.capacity := by rw [hstep]
    refine ⟨hout, hcap, ?_⟩
    have hsorted : Sorted s.items := (hv : Sorted s.items ∧ _).1
    obtain ⟨l1, l2, heq1, heq2, h1, h2⟩ := insSplitSortedAux2 e s.items hsorted
    exact ⟨l1, l2, heq1, by rw [hstep]; simp [heq2], h1, h2⟩
  · have heq : step s (.insert e) = (.rejected, s) := by
      unfold step
      rw [if_neg hv]
    rw [heq] at hne
    simp at hne

theorem req_pop_effects : PopEffects step := by
  intro s hne
  by_cases hv : Valid s .pop
  · have hsorted : Sorted s.items := hv.1
    have hne' : s.items ≠ [] := hv.2
    cases hitems : s.items with
    | nil => exact absurd hitems hne'
    | cons x xs =>
      have hstep : step s .pop = (.got x, { s with items := xs }) := by
        unfold step
        rw [if_pos hv, hitems]
      have hcap : (step s .pop).2.capacity = s.capacity := by rw [hstep]
      refine ⟨hcap, [], x, xs, by simp, ?_, ?_, ?_, ?_⟩
      · rw [hstep]
      · rw [hstep]; rfl
      · intro y hy; simp at hy
      · intro y hy
        have hsorted' : Sorted (x :: xs) := hitems ▸ hsorted
        cases hsorted' with
        | cons hhead _ => exact hhead y hy
  · have heq : step s .pop = (.rejected, s) := by
      unfold step
      rw [if_neg hv]
    rw [heq] at hne
    simp at hne

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow, classOfNilAux]
  | cons op ops ih =>
    have hsingle := fifoSingleStepC s op p
    have hIH := ih (step s op).2
    have hrun1 : (run step s (op :: ops)).1
      = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
      simp [run]
    have hrun2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
      simp [run]
    rw [hrun1, hrun2]
    rw [fifoInOutConsB, fifoOutConsAuxB]
    calc classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1))
        = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops).1) := by
          simp [List.append_assoc]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops).1) := by
          rw [hsingle]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops).1)) := by
          simp [List.append_assoc]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops).1) ++ classOf p (run step (step s op).2 ops).2.items) := by
          rw [hIH]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1)) ++ classOf p (run step (step s op).2 ops).2.items := by
          simp [List.append_assoc]

end PrioQueue
