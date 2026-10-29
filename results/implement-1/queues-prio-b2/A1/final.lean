import PrioQueue.Spec

namespace PrioQueue

def isSortedAux : Nat → List Entry → Bool
  | _, [] => true
  | prev, x :: xs => if prev ≤ x.prio then isSortedAux x.prio xs else false

def isSorted : List Entry → Bool
  | [] => true
  | x :: xs => isSortedAux x.prio xs

def insertSorted (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs => if e.prio < x.prio then e :: x :: xs else x :: insertSorted e xs

def step : Impl
  | s, .insert e =>
    if isSorted s.items && decide (s.items.length < s.capacity) then
      (Outcome.ok, { capacity := s.capacity, items := insertSorted e s.items })
    else
      (Outcome.rejected, s)
  | s, .pop =>
    if isSorted s.items then
      match s.items with
      | [] => (Outcome.rejected, s)
      | e :: rest => (Outcome.got e, { capacity := s.capacity, items := rest })
    else
      (Outcome.rejected, s)

theorem isSortedAux_of_forall_pairwise : ∀ (prev : Nat) (l : List Entry),
    (∀ x ∈ l, prev ≤ x.prio) → Sorted l → isSortedAux prev l = true := by
  intro prev l
  induction l generalizing prev with
  | nil => intro _ _; rfl
  | cons hd tl ih =>
    intro hall hsorted
    simp only [isSortedAux]
    have hhead : prev ≤ hd.prio := hall hd (by simp)
    simp [hhead]
    cases hsorted with
    | cons hrel htail =>
      exact ih _ hrel htail

theorem isSorted_of_Sorted : ∀ (l : List Entry), Sorted l → isSorted l = true := by
  intro l h
  cases l with
  | nil => rfl
  | cons hd tl =>
    simp only [isSorted]
    cases h with
    | cons hrel htail =>
      exact isSortedAux_of_forall_pairwise hd.prio tl hrel htail

theorem myTest1 (prev : Nat) (hd : Entry) (tl : List Entry)
    (hle : prev ≤ hd.prio) :
    isSortedAux prev (hd :: tl) = isSortedAux hd.prio tl := by
  simp only [isSortedAux, hle, ite_true]

theorem myAuxSound2 : ∀ (prev : Nat) (l : List Entry),
    isSortedAux prev l = true → (∀ x ∈ l, prev ≤ x.prio) ∧ Sorted l := by
  intro prev l
  induction l generalizing prev with
  | nil =>
    intro _
    constructor
    · intro x hx
      simp at hx
    · exact List.Pairwise.nil
  | cons hd tl ih =>
    intro h
    have hle : prev ≤ hd.prio := by
      simp only [isSortedAux] at h
      split at h
      · assumption
      · simp at h
    have htl : isSortedAux hd.prio tl = true := by
      simp only [isSortedAux] at h
      simp [hle] at h
      exact h
    obtain ⟨hall_tl, hsorted_tl⟩ := ih hd.prio htl
    constructor
    · intro x hx
      simp at hx
      cases hx with
      | inl heq => rw [heq]; exact hle
      | inr hmem => exact Nat.le_trans hle (hall_tl x hmem)
    · exact List.Pairwise.cons hall_tl hsorted_tl

theorem mySortedOfIsSortedAux : ∀ (l : List Entry), isSorted l = true → Sorted l := by
  intro l h
  cases l with
  | nil => exact List.Pairwise.nil
  | cons hd tl =>
    simp only [isSorted] at h
    obtain ⟨hall, hsorted⟩ := myAuxSound2 hd.prio tl h
    exact List.Pairwise.cons hall hsorted

theorem insertSorted_length_aux2 : ∀ (e : Entry) (l : List Entry), (insertSorted e l).length = l.length + 1 := by
  intro e l
  induction l with
  | nil => simp [insertSorted]
  | cons hd tl ih =>
    simp only [insertSorted]
    split
    · simp
    · simp [ih]

theorem tmpCapTest (s : State) (e : Entry) : (insertSorted e s.items).length = s.items.length + 1 :=
  insertSorted_length_aux2 e s.items

theorem tmpBoolCheck (a b : Bool) (h : (a && b) = true) : b = true := by
  simp at h
  exact h.2

theorem req_pop_min_test1 (s : State) (h : isSorted s.items = false) : (step s .pop).1 = .rejected := by
  simp [step, h]

theorem req_pop_min_test2 (s : State) (hd : Entry) (tl : List Entry) (hitems : s.items = hd :: tl) (his : isSorted s.items = true) : (step s .pop).1 = Outcome.got hd := by
  have hs : isSorted (hd :: tl) = true := hitems ▸ his
  simp [step, hitems, hs]

theorem req_pop_min_clean : True := trivial

theorem myHelperTest123 : True := trivial

theorem mem_insertSorted_test (e y : Entry) (l : List Entry) : y ∈ insertSorted e l → y = e ∨ y ∈ l := by
  induction l with
  | nil =>
    intro h
    simp [insertSorted] at h
    exact Or.inl h
  | cons hd tl ih =>
    intro h
    simp only [insertSorted] at h
    split at h
    · simp at h
      cases h with
      | inl heq => exact Or.inl heq
      | inr h2 =>
        cases h2 with
        | inl heq2 => exact Or.inr (by simp [heq2])
        | inr hmem => exact Or.inr (by simp [hmem])
    · simp at h
      cases h with
      | inl heq => exact Or.inr (by simp [heq])
      | inr hmem =>
        have h2 := ih hmem
        cases h2 with
        | inl heq => exact Or.inl heq
        | inr hin => exact Or.inr (by simp [hin])

theorem insertSorted_keeps_Sorted_aux2 (e : Entry) (l : List Entry) : Sorted l → Sorted (insertSorted e l) := by
  induction l with
  | nil =>
    intro _
    simp [insertSorted, Sorted]
  | cons hd tl ih =>
    intro hsorted
    have htail_rel : ∀ x ∈ tl, hd.prio ≤ x.prio := by
      cases hsorted with
      | cons hrel _ => exact hrel
    have htail_sorted : Sorted tl := by
      cases hsorted with
      | cons _ htail => exact htail
    have ih' := ih htail_sorted
    simp only [insertSorted]
    split
    · rename_i hlt
      have hle : e.prio ≤ hd.prio := Nat.le_of_lt hlt
      apply List.Pairwise.cons _ hsorted
      intro y hy
      simp at hy
      cases hy with
      | inl heq =>
        rw [heq]
        exact hle
      | inr hmem =>
        exact Nat.le_trans hle (htail_rel y hmem)
    · rename_i hnge
      have hle : hd.prio ≤ e.prio := Nat.le_of_not_gt hnge
      apply List.Pairwise.cons _ ih'
      intro y hy
      have hmem := mem_insertSorted_test e y tl hy
      cases hmem with
      | inl heq =>
        rw [heq]
        exact hle
      | inr hmem2 => exact htail_rel y hmem2

theorem sorted_tail_keep (hd : Entry) (tl : List Entry) : Sorted (hd :: tl) → Sorted tl := by
  intro h
  cases h with
  | cons _ htail => exact htail

theorem insertSorted_split_aux_test (e : Entry) (l : List Entry) (h : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ insertSorted e l = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil =>
    exact ⟨[], [], rfl, rfl, by simp, by simp⟩
  | cons hd tl ih =>
    have htail_sorted : Sorted tl := sorted_tail_keep hd tl h
    have hrel : ∀ x ∈ tl, hd.prio ≤ x.prio := by
      cases h with
      | cons hr _ => exact hr
    obtain ⟨t₁, t₂, heq, hins, h1, h2⟩ := ih htail_sorted
    simp only [insertSorted]
    by_cases hlt : e.prio < hd.prio
    · simp [hlt]
      refine ⟨[], hd :: tl, rfl, rfl, by simp, ?_⟩
      intro x hx
      simp at hx
      cases hx with
      | inl heq2 => rw [heq2]; exact hlt
      | inr hmem => exact Nat.lt_of_lt_of_le hlt (hrel x hmem)
    · simp [hlt]
      have hle : hd.prio ≤ e.prio := Nat.le_of_not_gt hlt
      refine ⟨hd :: t₁, t₂, ?_, ?_, ?_, h2⟩
      · simp [heq]
      · simp [hins]
      · intro x hx
        simp at hx
        cases hx with
        | inl heq2 => rw [heq2]; exact hle
        | inr hmem => exact h1 x hmem

theorem insertEffects_helper_lemma1 (s : State) (e : Entry) (hne : (step s (.insert e)).1 ≠ .rejected) :
    (isSorted s.items && decide (s.items.length < s.capacity)) = true := by
  simp only [step] at hne
  split at hne
  · rename_i h
    exact h
  · exact absurd rfl hne

theorem insertEffects_probe2 (s : State) (e : Entry) (hcond : (isSorted s.items && decide (s.items.length < s.capacity)) = true) :
    (step s (.insert e)).1 = .ok := by
  simp [step, hcond]

theorem fifo_probe1 (p : Nat) (l₁ l₂ : List Entry) : classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by
  simp [classOf]

theorem classOf_append2 (p : Nat) (l₁ l₂ : List Entry) : classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by
  unfold classOf
  rw [List.filter_append]

theorem classOf_nil2 (p : Nat) : classOf p [] = [] := by rfl

theorem classOf_cons2 (p : Nat) (x : Entry) (l : List Entry) :
    classOf p (x :: l) = (if x.prio == p then [x] else []) ++ classOf p l := by
  unfold classOf
  simp only [List.filter_cons]
  by_cases h : (x.prio == p) <;> simp [h]

theorem beq_nat_true2 (a b : Nat) : (a == b) = decide (a = b) := by rfl

theorem beq_eq_true_eq2 (a b : Nat) (h : (a == b) = true) : a = b := by
  have h2 : decide (a = b) = true := by rwa [← beq_nat_true2]
  exact of_decide_eq_true h2

theorem beq_of_eq_true2 (a b : Nat) (h : a = b) : (a == b) = true := by
  rw [beq_nat_true2, decide_eq_true h]

theorem prio_lt_beq_false_left2 (p : Nat) (e hd : Entry) (hlt : e.prio < hd.prio)
    (he : (e.prio == p) = true) : (hd.prio == p) = false := by
  have heq : e.prio = p := beq_eq_true_eq2 _ _ he
  have hne : hd.prio ≠ p := by omega
  by_cases h : (hd.prio == p) = true
  · have heq2 := beq_eq_true_eq2 _ _ h
    exact absurd heq2 hne
  · cases hh : (hd.prio == p) <;> simp_all

theorem prio_lt_beq_false_right2 (p : Nat) (e hd : Entry) (hlt : e.prio < hd.prio)
    (hh : (hd.prio == p) = true) : (e.prio == p) = false := by
  have heq : hd.prio = p := beq_eq_true_eq2 _ _ hh
  have hne : e.prio ≠ p := by omega
  by_cases h : (e.prio == p) = true
  · have heq2 := beq_eq_true_eq2 _ _ h
    exact absurd heq2 hne
  · cases hh2 : (e.prio == p) <;> simp_all

theorem classOf_single_true (p : Nat) (e : Entry) (h : (e.prio == p) = true) :
    classOf p [e] = [e] := by
  unfold classOf
  simp [h]

theorem classOf_single_false (p : Nat) (e : Entry) (h : (e.prio == p) = false) :
    classOf p [e] = [] := by
  unfold classOf
  simp [h]

theorem classOf_eq_nil_of_ne (p : Nat) (l : List Entry) (h : ∀ x ∈ l, x.prio ≠ p) :
    classOf p l = [] := by
  unfold classOf
  rw [List.filter_eq_nil_iff]
  intro a ha htrue
  have hne := h a ha
  have heq : a.prio = p := beq_eq_true_eq2 _ _ htrue
  exact hne heq

theorem classOf_l2_nil_of_mem (p : Nat) (e : Entry) (l₂ : List Entry)
    (h2 : ∀ x ∈ l₂, e.prio < x.prio) (he : (e.prio == p) = true) :
    classOf p l₂ = [] := by
  apply classOf_eq_nil_of_ne
  intro x hx
  have hlt := h2 x hx
  have heq : e.prio = p := beq_eq_true_eq2 _ _ he
  omega

theorem tmpBoolAnd1 (a b : Bool) (h : (a && b) = true) : a = true := by
  cases a with
  | false => simp at h
  | true => rfl

theorem tmpBoolAnd2 (a b : Bool) (h : (a && b) = true) : b = true := by
  cases a with
  | false => simp at h
  | true => simpa using h

theorem fifo_probe2 : True := trivial

theorem classOf_cons_eq2 (p : Nat) (x : Entry) (l : List Entry) :
    classOf p (x :: l) = classOf p [x] ++ classOf p l := by
  have h : (x :: l) = [x] ++ l := rfl
  rw [h, classOf_append2]

theorem classOf_insertSorted_helper (p : Nat) (e : Entry) (l₁ l₂ : List Entry)
    (h2 : ∀ x ∈ l₂, e.prio < x.prio) (he : (e.prio == p) = true) :
    classOf p (l₁ ++ e :: l₂) = classOf p (l₁ ++ l₂) ++ classOf p [e] := by
  have hl2 : classOf p l₂ = [] := classOf_l2_nil_of_mem p e l₂ h2 he
  have hsingle : classOf p [e] = [e] := classOf_single_true p e he
  have lhs : classOf p (l₁ ++ e :: l₂) = classOf p l₁ ++ (classOf p [e] ++ classOf p l₂) := by
    rw [classOf_append2, classOf_cons_eq2]
  have rhs : classOf p (l₁ ++ l₂) ++ classOf p [e] = (classOf p l₁ ++ classOf p l₂) ++ classOf p [e] := by
    rw [classOf_append2]
  rw [lhs, rhs, hl2, hsingle]
  simp

theorem classOf_insertSorted_helper2 (p : Nat) (e : Entry) (l₁ l₂ : List Entry)
    (hfalse : (e.prio == p) = false) :
    classOf p (l₁ ++ e :: l₂) = classOf p (l₁ ++ l₂) ++ classOf p [e] := by
  have hsingle : classOf p [e] = [] := classOf_single_false p e hfalse
  have lhs : classOf p (l₁ ++ e :: l₂) = classOf p l₁ ++ (classOf p [e] ++ classOf p l₂) := by
    rw [classOf_append2, classOf_cons_eq2]
  have rhs : classOf p (l₁ ++ l₂) ++ classOf p [e] = (classOf p l₁ ++ classOf p l₂) ++ classOf p [e] := by
    rw [classOf_append2]
  rw [lhs, rhs, hsingle]
  simp

theorem classOf_insertSorted_eq (p : Nat) (e : Entry) (l : List Entry)
    (h : Sorted l) :
    classOf p (insertSorted e l) = classOf p l ++ classOf p [e] := by
  obtain ⟨l₁, l₂, heq, hins, ha, hb⟩ := insertSorted_split_aux_test e l h
  by_cases he : (e.prio == p) = true
  · have h2 := classOf_insertSorted_helper p e l₁ l₂ hb he
    rw [hins, heq]
    exact h2
  · have hfalse : (e.prio == p) = false := by cases hbe : (e.prio == p) <;> simp_all
    have h2 := classOf_insertSorted_helper2 p e l₁ l₂ hfalse
    rw [hins, heq]
    exact h2

theorem inflow_cons (x : Op × Outcome) (xs : List (Op × Outcome)) :
    inflow (x :: xs) = inflowOf x ++ inflow xs := by
  simp [inflow]

theorem outflow_cons (x : Op × Outcome) (xs : List (Op × Outcome)) :
    outflow (x :: xs) = outflowOf x ++ outflow xs := by
  simp [outflow]

theorem run_cons_fst (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
  simp [run]

theorem run_cons_snd (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
  simp [run]

theorem classOf_nil_eq (p : Nat) : classOf p ([] : List Entry) = [] := by rfl

theorem inflow_nil_eq : inflow ([] : List (Op × Outcome)) = [] := by rfl

theorem outflow_nil_eq : outflow ([] : List (Op × Outcome)) = [] := by rfl

theorem single_step_fifo_aux4 (s : State) (p : Nat) (hd : Entry) (tl : List Entry)
    (hitems : s.items = hd :: tl)
    (h1 : (step s .pop).1 = Outcome.got hd)
    (h2 : (step s .pop).2.items = tl) :
    classOf p s.items ++ classOf p (inflowOf (Op.pop, (step s Op.pop).1))
    = classOf p (outflowOf (Op.pop, (step s Op.pop).1)) ++ classOf p (step s Op.pop).2.items := by
  have hcc : classOf p s.items = classOf p [hd] ++ classOf p tl := by
    rw [hitems]
    exact classOf_cons_eq2 p hd tl
  have e1 : inflowOf (Op.pop, Outcome.got hd) = ([] : List Entry) := rfl
  have e2 : outflowOf (Op.pop, Outcome.got hd) = [hd] := rfl
  rw [h1, h2, e1, e2, hcc]
  simp [classOf]

theorem single_step_fifo_v3 (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
    = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  cases op with
  | insert e =>
    cases hc : (isSorted s.items && decide (s.items.length < s.capacity)) with
    | false =>
      have h1 : (step s (.insert e)).1 = .rejected := by simp [step, hc]
      have h2 : (step s (.insert e)).2 = s := by simp [step, hc]
      simp only [h1, h2, inflowOf, outflowOf, classOf_nil_eq, List.append_nil, List.nil_append]
    | true =>
      have h1 : (step s (.insert e)).1 = .ok := by simp [step, hc]
      have h2 : (step s (.insert e)).2.items = insertSorted e s.items := by simp [step, hc]
      have hs : isSorted s.items = true := tmpBoolAnd1 _ _ hc
      have hsorted : Sorted s.items := mySortedOfIsSortedAux _ hs
      have hins : classOf p (insertSorted e s.items) = classOf p s.items ++ classOf p [e] :=
        classOf_insertSorted_eq p e s.items hsorted
      simp only [h1, h2, inflowOf, outflowOf, classOf_nil_eq, List.nil_append]
      exact hins.symm
  | pop =>
    cases his : isSorted s.items with
    | false =>
      have h1 : (step s .pop).1 = .rejected := by simp [step, his]
      have h2 : (step s .pop).2 = s := by simp [step, his]
      simp only [h1, h2, inflowOf, outflowOf, classOf_nil_eq, List.append_nil, List.nil_append]
    | true =>
      revert his
      cases hitems : s.items with
      | nil =>
        intro his
        have h1 : (step s .pop).1 = .rejected := by simp [step, hitems]
        have h2 : (step s .pop).2 = s := by simp [step, hitems]
        simp only [h1, h2, hitems, inflowOf, outflowOf, classOf_nil_eq, List.append_nil]
      | cons hd tl =>
        intro his
        have hs : isSorted (hd :: tl) = true := hitems ▸ his
        have h1 : (step s .pop).1 = Outcome.got hd := by simp [step, hitems, hs]
        have h2 : (step s .pop).2.items = tl := by simp [step, hitems, hs]
        have hcc : classOf p (hd :: tl) = classOf p [hd] ++ classOf p tl := classOf_cons_eq2 p hd tl
        have e1 : inflowOf (Op.pop, Outcome.got hd) = ([] : List Entry) := rfl
        have e2 : outflowOf (Op.pop, Outcome.got hd) = [hd] := rfl
        rw [h1, h2, e1, e2, hcc]
        simp [classOf_nil_eq]

theorem fifo_induct_aux3 (s : State) (ops : List Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflow (run step s ops).1)
    = classOf p (outflow (run step s ops).1) ++ classOf p (run step s ops).2.items := by
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow, classOf]
  | cons op rest ih =>
    have hfst : (run step s (op :: rest)).1 = (op, (step s op).1) :: (run step (step s op).2 rest).1 := by
      simp [run]
    have hsnd : (run step s (op :: rest)).2 = (run step (step s op).2 rest).2 := by
      simp [run]
    have hin : inflow ((op, (step s op).1) :: (run step (step s op).2 rest).1)
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1 := by
      simp [inflow]
    have hout : outflow ((op, (step s op).1) :: (run step (step s op).2 rest).1)
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1 := by
      simp [outflow]
    have hsingle := single_step_fifo_v3 s op p
    have hihr := ih (step s op).2
    have h1 : classOf p (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1)
        = classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 rest).1) :=
      classOf_append2 p _ _
    have h2 : classOf p (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1)
        = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 rest).1) :=
      classOf_append2 p _ _
    rw [hfst, hsnd, hin, hout, h1, h2, ← List.append_assoc _ _ (classOf p (inflow (run step (step s op).2 rest).1)), hsingle, List.append_assoc, hihr, List.append_assoc]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hvalid
  cases op with
  | insert e =>
    simp only [Valid] at hvalid
    obtain ⟨hsorted, hlen⟩ := hvalid
    have hs : isSorted s.items = true := isSorted_of_Sorted _ hsorted
    have hl : decide (s.items.length < s.capacity) = true := decide_eq_true hlen
    simp only [step, hs, hl, Bool.true_and]
    simp
  | pop =>
    simp only [Valid] at hvalid
    obtain ⟨hsorted, hne⟩ := hvalid
    have hs : isSorted s.items = true := isSorted_of_Sorted _ hsorted
    simp only [step, hs]
    cases hitems : s.items with
    | nil => simp at hne; exact absurd hitems hne
    | cons hd tl =>
      simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | insert e =>
    simp only [Valid] at h
    cases hc : (isSorted s.items && decide (s.items.length < s.capacity)) with
    | false => simp [step, hc]
    | true =>
      have h1 := tmpBoolAnd1 _ _ hc
      have h2 := tmpBoolAnd2 _ _ hc
      have hs : Sorted s.items := mySortedOfIsSortedAux _ h1
      have hl : s.items.length < s.capacity := of_decide_eq_true h2
      exact False.elim (h ⟨hs, hl⟩)
  | pop =>
    simp only [Valid] at h
    cases hsb : isSorted s.items with
    | false => simp [step, hsb]
    | true =>
      have hsorted : Sorted s.items := mySortedOfIsSortedAux _ hsb
      cases hitems : s.items with
      | nil => simp [step, hitems]
      | cons hd tl => exact False.elim (h ⟨hsorted, by simp [hitems]⟩)

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | insert e =>
    cases hc : (isSorted s.items && decide (s.items.length < s.capacity)) with
    | false =>
      have h2 : (step s (.insert e)).2 = s := by simp [step, hc]
      rw [h2]
      exact hle
    | true =>
      have hcap : (step s (.insert e)).2.capacity = s.capacity := by simp [step, hc]
      have hitems : (step s (.insert e)).2.items = insertSorted e s.items := by simp [step, hc]
      rw [hcap, hitems]
      have h2 := tmpBoolAnd2 _ _ hc
      have hlt : s.items.length < s.capacity := of_decide_eq_true h2
      have hlen : (insertSorted e s.items).length = s.items.length + 1 := insertSorted_length_aux2 e s.items
      omega
  | pop =>
    cases his : isSorted s.items with
    | false =>
      have h2 : (step s .pop).2 = s := by simp [step, his]
      rw [h2]
      exact hle
    | true =>
      cases hitems : s.items with
      | nil =>
        have h2 : (step s .pop).2 = s := by simp [step, hitems]
        rw [h2]
        exact hle
      | cons hd tl =>
        have his2 : isSorted (hd :: tl) = true := hitems ▸ his
        have hcap : (step s .pop).2.capacity = s.capacity := by simp [step, hitems, his2]
        have hit : (step s .pop).2.items = tl := by simp [step, hitems, his2]
        rw [hcap, hit]
        have hlen : (hd :: tl).length = tl.length + 1 := rfl
        have hrewrite : s.items.length = tl.length + 1 := by rw [hitems]; rfl
        omega

theorem req_pop_min : PopMin step := by
  intro s hne
  cases his : isSorted s.items with
  | false =>
    have hstep : (step s .pop).1 = .rejected := by simp [step, his]
    rw [hstep] at hne
    exact absurd rfl hne
  | true =>
    cases hitems : s.items with
    | nil =>
      have hstep : (step s .pop).1 = .rejected := by simp [step, hitems]
      rw [hstep] at hne
      exact absurd rfl hne
    | cons hd tl =>
      have hs : isSorted (hd :: tl) = true := hitems ▸ his
      have h1 : (step s .pop).1 = Outcome.got hd := by simp [step, hitems, hs]
      have h2 : (step s .pop).2.items = tl := by simp [step, hitems, hs]
      refine ⟨hd, h1, ?_⟩
      rw [h2]
      simp only [isSorted] at hs
      obtain ⟨hall, _⟩ := myAuxSound2 hd.prio tl hs
      exact hall

theorem req_sorted : KeepsSorted step := by
  intro s op hsorted
  cases op with
  | insert e =>
    cases hc : (isSorted s.items && decide (s.items.length < s.capacity)) with
    | true =>
      have h1 : (step s (.insert e)).2.items = insertSorted e s.items := by simp [step, hc]
      rw [h1]
      exact insertSorted_keeps_Sorted_aux2 e s.items hsorted
    | false =>
      have h1 : (step s (.insert e)).2 = s := by simp [step, hc]
      rw [h1]
      exact hsorted
  | pop =>
    cases his : isSorted s.items with
    | false =>
      have h1 : (step s .pop).2 = s := by simp [step, his]
      rw [h1]
      exact hsorted
    | true =>
      cases hitems : s.items with
      | nil =>
        have h1 : (step s .pop).2 = s := by simp [step, hitems]
        rw [h1]
        exact hsorted
      | cons hd tl =>
        have his2 : isSorted (hd :: tl) = true := by rw [← hitems]; exact his
        have h1 : (step s .pop).2.items = tl := by simp [step, hitems, his2]
        rw [h1]
        exact sorted_tail_keep hd tl (hitems ▸ hsorted)

theorem req_insert_effects : InsertEffects step := by
  intro s e hne
  have hcond := insertEffects_helper_lemma1 s e hne
  have hs : isSorted s.items = true := by
    have htmp := hcond
    simp at htmp
    exact htmp.1
  have hsorted : Sorted s.items := mySortedOfIsSortedAux _ hs
  have h1 : (step s (.insert e)).1 = .ok := by simp [step, hcond]
  have h2 : (step s (.insert e)).2.capacity = s.capacity := by simp [step, hcond]
  refine ⟨h1, h2, ?_⟩
  have h3 : (step s (.insert e)).2.items = insertSorted e s.items := by simp [step, hcond]
  obtain ⟨l₁, l₂, heq, hins, ha, hb⟩ := insertSorted_split_aux_test e s.items hsorted
  exact ⟨l₁, l₂, heq, by rw [h3, hins], ha, hb⟩

theorem req_pop_effects    : PopEffects step := by
  intro s hne
  cases his : isSorted s.items with
  | false =>
    have hstep : (step s .pop).1 = .rejected := by simp [step, his]
    rw [hstep] at hne
    exact absurd rfl hne
  | true =>
    match hitems : s.items with
    | [] =>
      have hstep : (step s .pop).1 = .rejected := by simp [step, hitems]
      rw [hstep] at hne
      exact absurd rfl hne
    | hd :: tl =>
      have hs : isSorted (hd :: tl) = true := hitems ▸ his
      have h1 : (step s .pop).1 = Outcome.got hd := by simp [step, hitems, hs]
      have h2 : (step s .pop).2.items = tl := by simp [step, hitems, hs]
      have hcap : (step s .pop).2.capacity = s.capacity := by simp [step, hitems, hs]
      refine ⟨hcap, [], hd, tl, ?_, h1, ?_, ?_, ?_⟩
      · simp [hitems]
      · simp [h2]
      · intro x hx
        simp at hx
      · simp only [isSorted] at hs
        obtain ⟨hall, _⟩ := myAuxSound2 hd.prio tl hs
        exact hall

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  exact fifo_induct_aux3 s ops p

end PrioQueue
