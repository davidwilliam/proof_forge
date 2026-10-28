import PrioQueue.Spec
namespace PrioQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid Sorted <;> infer_instance

def ins (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs => if e.prio < x.prio then e :: x :: xs else x :: ins e xs

def step : Impl := fun s op =>
  if Valid s op then
    match op with
    | .insert e => (.ok, { s with items := ins e s.items })
    | .pop =>
      match s.items with
      | e :: rest => (.got e, { s with items := rest })
      | [] => (.rejected, s)
  else (.rejected, s)

def fooTest := 1

theorem ins_length_aux (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    simp only [ins]
    split
    · simp
    · simp [ih, Nat.add_assoc]

theorem req_capacity_aux1 : ∀ (e : Entry) (l : List Entry), (ins e l).length = l.length + 1 := ins_length_aux

theorem req_capacity_probe : True := by
  have hv : Valid ⟨5, ([] : List Entry)⟩ (Op.insert ⟨1,2⟩) := by
    simp [Valid, Sorted]
  obtain ⟨h1, h2⟩ := hv
  trivial

theorem popmin_lemma_test (a : Entry) (l : List Entry) (h : Sorted (a :: l)) : ∀ x ∈ l, a.prio ≤ x.prio := by
  unfold Sorted at h
  intro x hx
  have h2 := List.rel_of_pairwise_cons h hx
  simpa using h2

theorem popmin_debug (s : State) (e : Entry) (rest : List Entry) (hV : Valid s Op.pop) (hitems : s.items = e :: rest) : (step s Op.pop).1 = Outcome.got e := by
  unfold step
  simp [hV, hitems]

theorem popmin_debug2 (s : State) (e : Entry) (rest : List Entry) (hV : Valid s Op.pop) (hitems : s.items = e :: rest) : (step s Op.pop).2.items = rest := by
  unfold step
  simp [hV, hitems]

theorem popmin_scope_test (s : State) (hV : Valid s Op.pop) : True := by
  cases hitems : s.items with
  | nil => trivial
  | cons e rest =>
    have h2 := hV
    trivial

theorem popmin_step1 (s : State) (hV : Valid s Op.pop) (hitems : s.items = ([] : List Entry)) : False := by
  unfold Valid at hV
  simp [hitems] at hV

theorem popmin_extract (s : State) (hV : Valid s Op.pop) : Sorted s.items ∧ s.items ≠ [] := hV

theorem popmin_obtain_test (s : State) (hV : Valid s Op.pop) : Sorted s.items := by
  obtain ⟨hSort, hNeN⟩ := hV
  exact hSort

theorem sorted_tail_aux (a : Entry) (l : List Entry) (h : Sorted (a :: l)) : Sorted l := by
  unfold Sorted at h ⊢
  cases h with
  | cons h1 h2 => exact h2

theorem sorted_tail_aux_ok : True := trivial

theorem pairwise_cons_iff (R : Entry → Entry → Prop) (x : Entry) (l : List Entry) : List.Pairwise R (x :: l) ↔ (∀ y ∈ l, R x y) ∧ List.Pairwise R l := by
  constructor
  · intro h
    cases h with
    | cons h1 h2 => exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact List.Pairwise.cons h1 h2

theorem pairwise_cons_iff_ok : True := trivial

theorem mem_ins_aux2 (e : Entry) (l : List Entry) : ∀ y : Entry, y ∈ ins e l → y = e ∨ y ∈ l := by
  induction l with
  | nil =>
    intro y hy
    simp [ins] at hy
    exact Or.inl hy
  | cons x xs ih =>
    intro y hy
    unfold ins at hy
    by_cases hc : e.prio < x.prio
    · simp only [hc, ↓reduceIte] at hy
      simp only [List.mem_cons] at hy ⊢
      cases hy with
      | inl hye => exact Or.inl hye
      | inr hr =>
        cases hr with
        | inl hyx => exact Or.inr (Or.inl hyx)
        | inr hyxs => exact Or.inr (Or.inr hyxs)
    · simp only [hc, ↓reduceIte] at hy
      simp only [List.mem_cons] at hy ⊢
      cases hy with
      | inl hyx => exact Or.inr (Or.inl hyx)
      | inr hr =>
        have hr2 := ih y hr
        cases hr2 with
        | inl hye => exact Or.inl hye
        | inr hm => exact Or.inr (Or.inr hm)

theorem mem_ins_aux2_ok : True := trivial

theorem ins_sorted_aux (e : Entry) (l : List Entry) (h : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil =>
    unfold Sorted ins
    exact List.Pairwise.cons (fun y hy => by cases hy) List.Pairwise.nil
  | cons x xs ih =>
    have hpair := (pairwise_cons_iff _ x xs).mp h
    obtain ⟨hhead, htail⟩ := hpair
    have ih' := ih htail
    unfold ins
    by_cases hc : e.prio < x.prio
    · simp only [hc, ↓reduceIte]
      unfold Sorted
      apply List.Pairwise.cons
      · intro y hy
        simp only [List.mem_cons] at hy
        cases hy with
        | inl hye =>
          subst hye
          exact Nat.le_of_lt hc
        | inr hyxs =>
          have hxle : x.prio ≤ y.prio := hhead y hyxs
          exact Nat.le_trans (Nat.le_of_lt hc) hxle
      · exact h
    · simp only [hc, ↓reduceIte]
      unfold Sorted
      apply List.Pairwise.cons
      · intro y hy
        have hmem := mem_ins_aux2 e xs y hy
        cases hmem with
        | inl hye =>
          subst hye
          exact Nat.le_of_not_gt hc
        | inr hyxs =>
          exact hhead y hyxs
      · exact ih'

theorem ins_sorted_aux_ok : True := trivial

theorem probe_le_of_not_gt (a b : Nat) (h : ¬ a < b) : b ≤ a := by
  exact Nat.le_of_not_gt h

theorem probe_by_cases (p : Prop) [Decidable p] : p ∨ ¬ p := by
  by_cases h : p
  · exact Or.inl h
  · exact Or.inr h

theorem probe_trivial_test : True := trivial

theorem probe_pushneg_test (a b : Nat) (h : ¬ a < b) : b ≤ a := by
  exact Nat.le_of_not_gt h

theorem probe_bycontra_test (p : Prop) [Decidable p] (h : ¬ ¬ p) : p := by
  exact Decidable.not_not.mp h

theorem probe_cases_nil (x : Entry) (h : x ∈ ([] : List Entry)) : False := by
  exact List.not_mem_nil h

theorem probe_refine_rw (l : List Entry) : [] ++ l = l := by
  refine List.nil_append l

theorem probe_false_elim (x : Entry) (hx : x ∈ ([] : List Entry)) : x.prio ≤ 0 := by
  exact False.elim (List.not_mem_nil hx)

theorem probe_absurd_test (e : Entry) : ∀ x : Entry, x ∈ ([] : List Entry) → x.prio ≤ e.prio := by
  intro x hx
  exact False.elim (List.not_mem_nil hx)

theorem ins_split_nil (e : Entry) :
    ∃ l₁ l₂, ([] : List Entry) = l₁ ++ l₂ ∧ ins e ([] : List Entry) = l₁ ++ e :: l₂ ∧
      (∀ x : Entry, x ∈ l₁ → x.prio ≤ e.prio) ∧ ∀ x : Entry, x ∈ l₂ → e.prio < x.prio := by
  refine ⟨[], [], rfl, ?_, ?_, ?_⟩
  · simp [ins]
  · intro x hx
    exact False.elim (List.not_mem_nil hx)
  · intro x hx
    exact False.elim (List.not_mem_nil hx)

theorem classOf_append_test (p : Nat) (l₁ l₂ : List Entry) : classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by
  unfold classOf
  rw [List.filter_append]

theorem beq_nat_true (a b : Nat) : (a == b) = true ↔ a = b := by
  simp [BEq.beq]

theorem inflow_nil_test : inflow ([] : List (Op × Outcome)) = [] := by simp [inflow]

theorem outflow_nil_test : outflow ([] : List (Op × Outcome)) = [] := by simp [outflow]

theorem inflow_cons_test (x : Op × Outcome) (xs : List (Op × Outcome)) :
    inflow (x :: xs) = inflowOf x ++ inflow xs := by simp [inflow]

theorem outflow_cons_test (x : Op × Outcome) (xs : List (Op × Outcome)) :
    outflow (x :: xs) = outflowOf x ++ outflow xs := by simp [outflow]

theorem ins_split_sorted_lem (e : Entry) (l : List Entry) (h : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil =>
    exact ⟨[], [], rfl, by simp [ins],
      fun x hx => False.elim (List.not_mem_nil hx),
      fun x hx => False.elim (List.not_mem_nil hx)⟩
  | cons x xs ih =>
    have hpair := (pairwise_cons_iff _ x xs).mp h
    obtain ⟨hhead, htail⟩ := hpair
    obtain ⟨l₁', l₂', hEq, hIns, hLe1, hLt2⟩ := ih htail
    by_cases hc : e.prio < x.prio
    · refine ⟨[], x :: xs, rfl, ?_, ?_, ?_⟩
      · simp [ins, hc]
      · intro y hy
        exact False.elim (List.not_mem_nil hy)
      · intro y hy
        simp only [List.mem_cons] at hy
        cases hy with
        | inl hye =>
          subst hye
          exact hc
        | inr hym =>
          have hxle : x.prio ≤ y.prio := hhead y hym
          exact Nat.lt_of_lt_of_le hc hxle
    · have hxle : x.prio ≤ e.prio := Nat.le_of_not_gt hc
      refine ⟨x :: l₁', l₂', ?_, ?_, ?_, hLt2⟩
      · simp [hEq]
      · simp [ins, hc, hIns]
      · intro y hy
        simp only [List.mem_cons] at hy
        cases hy with
        | inl hye =>
          subst hye
          exact hxle
        | inr hym => exact hLe1 y hym

theorem fifo_probe_beq (a b : Nat) (h : a ≠ b) : (a == b) = false := by
  simp [h]

theorem fifo_probe_beq2 (a : Nat) : (a == a) = true := by simp

theorem fifo_probe_filter_nil (p : Nat) : classOf p ([] : List Entry) = [] := by simp [classOf]

theorem fifo_probe_class_append (p : Nat) (l₁ l₂ : List Entry) : classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by simp [classOf, List.filter_append]

theorem fifo_probe_inflow_cons (x : Op × Outcome) (xs : List (Op × Outcome)) : inflow (x :: xs) = inflowOf x ++ inflow xs := by simp [inflow]

theorem fifo_probe_outflow_cons (x : Op × Outcome) (xs : List (Op × Outcome)) : outflow (x :: xs) = outflowOf x ++ outflow xs := by simp [outflow]

theorem beq_probe1 (a b : Nat) : (a == b) = decide (a = b) := by rfl

theorem beq_probe2 (a : Nat) : (a == a) = true := by simp

theorem beq_probe3 (a b : Nat) (h : a = b) : (a == b) = true := by simp [h]

theorem beq_probe4 (a b : Nat) (h : a ≠ b) : (a == b) = false := by simp [h]

theorem filter_probe1 (p : Nat) : classOf p ([] : List Entry) = [] := by simp [classOf]

theorem filter_probe2 (p : Nat) (x : Entry) (l : List Entry) : classOf p (x :: l) = (if x.prio == p then [x] else []) ++ classOf p l := by
  unfold classOf
  simp only [List.filter_cons]
  split
  · simp
  · simp

theorem cA2 (p : Nat) : classOf p ([] : List Entry) = [] := by unfold classOf; rfl

theorem cB2 (p : Nat) (e : Entry) : classOf p [e] = ([e].filter (fun x => decide (x.prio = p))) := by
  unfold classOf
  have h : (fun x : Entry => x.prio == p) = (fun x : Entry => decide (x.prio = p)) := by
    funext x; rfl
  rw [h]

theorem cC2 (p : Nat) (x : Entry) (l : List Entry) (h : (x.prio == p) = true) : x ∈ classOf p (x :: l) := by
  unfold classOf
  simp [h]

theorem classOf_eq_nil_of_ne (p : Nat) (l : List Entry) (h : ∀ x ∈ l, x.prio ≠ p) : classOf p l = [] := by
  induction l with
  | nil => simp [classOf]
  | cons x xs ih =>
    have hx : x.prio ≠ p := h x (by simp)
    have hxs : ∀ y ∈ xs, y.prio ≠ p := fun y hy => h y (by simp [hy])
    have ih' := ih hxs
    unfold classOf at ih' ⊢
    simp [hx, ih']











theorem plan0_classOf_append (p : Nat) (l₁ l₂ : List Entry) :
    classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by
  unfold classOf
  rw [List.filter_append]

theorem plan0_classOf_cons_singleton (p : Nat) (e : Entry) (l : List Entry) :
    classOf p (e :: l) = classOf p [e] ++ classOf p l := by
  unfold classOf
  simp only [List.filter_cons]
  by_cases h : e.prio == p <;> simp [h]

theorem plan0_classOf_ins_sorted_aux1 (p : Nat) (e : Entry) (l : List Entry) (h : Sorted l) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := by
  induction l with
  | nil =>
    simp [ins, classOf]
  | cons x xs ih =>
    have hpair := (pairwise_cons_iff _ x xs).mp h
    obtain ⟨hhead, htail⟩ := hpair
    have ih' := ih htail
    by_cases hc : e.prio < x.prio
    · simp only [ins, hc, ↓reduceIte]
      have hL : classOf p (e :: x :: xs) = classOf p [e] ++ classOf p (x :: xs) :=
        plan0_classOf_cons_singleton p e (x :: xs)
      rw [hL]
      by_cases he : (e.prio == p) = true
      · have hep : e.prio = p := by simpa using he
        have hxp : x.prio ≠ p := by omega
        have hxs_ne : ∀ y ∈ xs, y.prio ≠ p := by
          intro y hy
          have hxle : x.prio ≤ y.prio := hhead y hy
          omega
        have hx_cons_ne : ∀ y ∈ x :: xs, y.prio ≠ p := by
          intro y hy
          simp only [List.mem_cons] at hy
          cases hy with
          | inl hye => subst hye; exact hxp
          | inr hym => exact hxs_ne y hym
        have hCxs_nil : classOf p (x :: xs) = [] := classOf_eq_nil_of_ne p (x :: xs) hx_cons_ne
        have hCe : classOf p [e] = [e] := by unfold classOf; simp [he]
        rw [hCxs_nil, hCe]
        simp
      · have he_false : (e.prio == p) = false := by
          cases hbb : (e.prio == p) <;> simp_all
        have hCe_nil : classOf p [e] = [] := by unfold classOf; simp [he_false]
        rw [hCe_nil]
        simp
    · simp only [ins, hc, ↓reduceIte]
      have hL : classOf p (x :: ins e xs) = classOf p [x] ++ classOf p (ins e xs) :=
        plan0_classOf_cons_singleton p x (ins e xs)
      have hR : classOf p (x :: xs) = classOf p [x] ++ classOf p xs :=
        plan0_classOf_cons_singleton p x xs
      rw [hL, hR, ih', List.append_assoc]

theorem plan0_classOf_ins_sorted_dup (p : Nat) (e : Entry) (l : List Entry) (h : Sorted l) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] :=
  plan0_classOf_ins_sorted_aux1 p e l h

theorem plan0_classOf_ins_sorted (p : Nat) (e : Entry) (l : List Entry) (h : Sorted l) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] :=
  plan0_classOf_ins_sorted_aux1 p e l h

theorem probe_inflow_ok (e : Entry) : inflowOf (Op.insert e, Outcome.ok) = [e] := by simp [inflowOf]

theorem probe_inflow_rej (e : Entry) : inflowOf (Op.insert e, Outcome.rejected) = ([] : List Entry) := by simp [inflowOf]

theorem probe_outflow_ok (e : Entry) : outflowOf (Op.pop, Outcome.got e) = [e] := by simp [outflowOf]

theorem probe_outflow_rej : outflowOf (Op.pop, Outcome.rejected) = ([] : List Entry) := by simp [outflowOf]

theorem probe_step_insert_ok (s : State) (e : Entry) (hV : Valid s (Op.insert e)) :
    (step s (Op.insert e)).1 = Outcome.ok := by simp [step, hV]

theorem probe_step_insert_items (s : State) (e : Entry) (hV : Valid s (Op.insert e)) :
    (step s (Op.insert e)).2.items = ins e s.items := by simp [step, hV]

theorem probe_inflow_rw (s : State) (e : Entry) (h1 : (step s (Op.insert e)).1 = Outcome.ok) :
    inflowOf (Op.insert e, (step s (Op.insert e)).1) = [e] := by simp [h1, inflowOf]

theorem probe_outflow_rw (s : State) (e : Entry) (h1 : (step s (Op.insert e)).1 = Outcome.ok) :
    outflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by simp [h1, outflowOf]

theorem probe_rfl1 (e : Entry) : inflowOf (Op.insert e, Outcome.ok) = [e] := rfl

theorem probe_rfl2 (e : Entry) : outflowOf (Op.insert e, Outcome.ok) = ([] : List Entry) := rfl

theorem probe_rfl3 (e : Entry) : inflowOf (Op.pop, Outcome.got e) = ([] : List Entry) := rfl

theorem probe_rfl4 (e : Entry) : outflowOf (Op.pop, Outcome.got e) = [e] := rfl

theorem probe_rfl5 : outflowOf (Op.pop, Outcome.rejected) = ([] : List Entry) := rfl

theorem probe_rfl6 : inflowOf (Op.pop, Outcome.rejected) = ([] : List Entry) := rfl

theorem probe_rfl7 (e : Entry) : inflowOf (Op.insert e, Outcome.rejected) = ([] : List Entry) := rfl

theorem probe_rfl8 (e : Entry) : outflowOf (Op.insert e, Outcome.rejected) = ([] : List Entry) := rfl

theorem probe_pop_rw (s : State) (e : Entry) (rest : List Entry) (p : Nat)
    (hIn : inflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry))
    (hOut : outflowOf (Op.pop, (step s Op.pop).1) = [e])
    (h2 : (step s Op.pop).2.items = rest)
    (hitems : s.items = e :: rest)
    (hCl : classOf p (e :: rest) = classOf p [e] ++ classOf p rest) :
    classOf p s.items ++ classOf p (inflowOf (Op.pop, (step s Op.pop).1))
      = classOf p (outflowOf (Op.pop, (step s Op.pop).1)) ++ classOf p (step s Op.pop).2.items := by
  rw [hIn, hOut, h2, hitems]
  have hNil : classOf p ([] : List Entry) = [] := by simp [classOf]
  rw [hNil, List.append_nil]
  exact hCl



theorem plan1_classOf_ins_sorted (p : Nat) (e : Entry) (l : List Entry)
    (h : Sorted l) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := plan0_classOf_ins_sorted_aux1 p e l h










theorem plan1_classOf_cons_singleton (p : Nat) (e : Entry) (l : List Entry) :
    classOf p (e :: l) = classOf p [e] ++ classOf p l := by
  unfold classOf
  simp only [List.filter_cons]
  by_cases h : e.prio == p <;> simp [h]

theorem plan1_classOf_ins_sorted_fix (p : Nat) (e : Entry) (l : List Entry)
    (h : Sorted l) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] :=
  plan0_classOf_ins_sorted_aux1 p e l h

theorem plan1_step_classOf_not_valid (s : State) (op : Op) (p : Nat)
    (h : ¬ Valid s op) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
      = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  have hStep : step s op = (.rejected, s) := by unfold step; simp [h]
  have h1 : (step s op).1 = Outcome.rejected := by simp [hStep]
  have h2 : (step s op).2 = s := by simp [hStep]
  rw [h1, h2]
  cases op with
  | insert e =>
    simp [inflowOf, outflowOf, classOf]
  | pop =>
    simp [inflowOf, outflowOf, classOf]

theorem plan1_step_classOf_insert_valid (s : State) (e : Entry) (p : Nat)
    (h : Valid s (Op.insert e)) :
    classOf p s.items ++ classOf p (inflowOf (Op.insert e, (step s (Op.insert e)).1))
      = classOf p (outflowOf (Op.insert e, (step s (Op.insert e)).1))
        ++ classOf p (step s (Op.insert e)).2.items := by
  have hSort : Sorted s.items := h.1
  have hOk : (step s (Op.insert e)).1 = Outcome.ok := probe_step_insert_ok s e h
  have hItems : (step s (Op.insert e)).2.items = ins e s.items := probe_step_insert_items s e h
  have hIn : inflowOf (Op.insert e, (step s (Op.insert e)).1) = [e] := by
    rw [hOk]
    rfl
  have hOut : outflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
    rw [hOk]
    rfl
  rw [hIn, hOut, hItems]
  have hNil : classOf p ([] : List Entry) = [] := by simp [classOf]
  rw [hNil, List.nil_append]
  exact (plan0_classOf_ins_sorted_aux1 p e s.items hSort).symm

theorem plan1_step_classOf_pop_valid (s : State) (p : Nat)
    (h : Valid s Op.pop) :
    classOf p s.items ++ classOf p (inflowOf (Op.pop, (step s Op.pop).1))
      = classOf p (outflowOf (Op.pop, (step s Op.pop).1))
        ++ classOf p (step s Op.pop).2.items := by
  have hSort : Sorted s.items := h.1
  have hNe : s.items ≠ [] := h.2
  cases heq : s.items with
  | nil => exact False.elim (hNe heq)
  | cons e rest =>
    have hStep1 : (step s Op.pop).1 = Outcome.got e := by
      unfold step
      simp [h, heq]
    have hStep2 : (step s Op.pop).2.items = rest := by
      unfold step
      simp [h, heq]
    have hIn : inflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
      rw [hStep1]
      rfl
    have hOut : outflowOf (Op.pop, (step s Op.pop).1) = [e] := by
      rw [hStep1]
      rfl
    rw [hIn, hOut, hStep2]
    have hNil : classOf p ([] : List Entry) = [] := by simp [classOf]
    rw [hNil, List.append_nil]
    exact plan1_classOf_cons_singleton p e rest

theorem plan1_step_classOf (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
      = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      exact plan1_step_classOf_insert_valid s e p hV
    | pop =>
      exact plan1_step_classOf_pop_valid s p hV
  · exact plan1_step_classOf_not_valid s op p hV

theorem plan0_step_classOf_prover (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
      = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items :=
  plan1_step_classOf s op p

theorem plan0_step_classOf_selfContained4 (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
      = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have hSort : Sorted s.items := hV.1
      have hOk : (step s (Op.insert e)).1 = Outcome.ok := by simp [step, hV]
      have hItems : (step s (Op.insert e)).2.items = ins e s.items := by simp [step, hV]
      have hIn : inflowOf (Op.insert e, (step s (Op.insert e)).1) = [e] := by
        rw [hOk]; exact probe_rfl1 e
      have hOut : outflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
        rw [hOk]; rfl
      rw [hIn, hOut, hItems]
      have hNil : classOf p ([] : List Entry) = [] := by simp [classOf]
      rw [hNil, List.nil_append]
      exact (plan0_classOf_ins_sorted_aux1 p e s.items hSort).symm
    | pop =>
      have hNe : s.items ≠ [] := hV.2
      cases heq : s.items with
      | nil => exact False.elim (hNe heq)
      | cons e rest =>
        have hStep1 : (step s Op.pop).1 = Outcome.got e := by unfold step; simp [hV, heq]
        have hStep2 : (step s Op.pop).2.items = rest := by unfold step; simp [hV, heq]
        have hIn : inflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by rw [hStep1]; rfl
        have hOut : outflowOf (Op.pop, (step s Op.pop).1) = [e] := by rw [hStep1]; rfl
        rw [hIn, hOut, hStep2]
        have hNil : classOf p ([] : List Entry) = [] := by simp [classOf]
        rw [hNil, List.append_nil]
        exact plan0_classOf_cons_singleton p e rest
  · have hStep : step s op = (.rejected, s) := by unfold step; simp [hV]
    have h1 : (step s op).1 = Outcome.rejected := by simp [hStep]
    have h2 : (step s op).2 = s := by simp [hStep]
    rw [h1, h2]
    cases op with
    | insert e => simp [inflowOf, outflowOf, classOf]
    | pop => simp [inflowOf, outflowOf, classOf]

theorem testConsProof2 (q : Nat) (e : Entry) (l : List Entry) :
    classOf q (e :: l) = classOf q [e] ++ classOf q l := by
  unfold classOf
  simp only [List.filter_cons]
  split
  · simp
  · simp

theorem testNilIns (q : Nat) (e : Entry) :
    classOf q (ins e ([] : List Entry)) = classOf q ([] : List Entry) ++ classOf q [e] := by
  have h1 : ins e ([] : List Entry) = [e] := by simp only [ins]
  rw [h1]
  simp only [classOf, List.filter_nil, List.nil_append]

theorem testHInsStandalone (q : Nat) (e : Entry) (l : List Entry) (h : Sorted l) :
    classOf q (ins e l) = classOf q l ++ classOf q [e] := by
  induction l with
  | nil =>
    simp [ins, classOf]
  | cons x xs ih =>
    have hpair := (pairwise_cons_iff _ x xs).mp h
    obtain ⟨hhead, htail⟩ := hpair
    have ih' := ih htail
    by_cases hc : e.prio < x.prio
    · simp only [ins, hc, ↓reduceIte]
      have hL : classOf q (e :: x :: xs) = classOf q [e] ++ classOf q (x :: xs) := by
        unfold classOf
        simp only [List.filter_cons]
        split
        · simp
        · simp
      rw [hL]
      by_cases he : (e.prio == q) = true
      · have hep : e.prio = q := by simpa using he
        have hxp : x.prio ≠ q := by omega
        have hxs_ne : ∀ y ∈ xs, y.prio ≠ q := by
          intro y hy
          have hxle : x.prio ≤ y.prio := hhead y hy
          omega
        have hx_cons_ne : ∀ y ∈ x :: xs, y.prio ≠ q := by
          intro y hy
          simp only [List.mem_cons] at hy
          cases hy with
          | inl hye => subst hye; exact hxp
          | inr hym => exact hxs_ne y hym
        have hCxs_nil : classOf q (x :: xs) = [] := classOf_eq_nil_of_ne q (x :: xs) hx_cons_ne
        have hCe : classOf q [e] = [e] := by unfold classOf; simp [he]
        rw [hCxs_nil, hCe]
        simp
      · have he_false : (e.prio == q) = false := by
          cases hbb : (e.prio == q) <;> simp_all
        have hCe_nil : classOf q [e] = [] := by unfold classOf; simp [he_false]
        rw [hCe_nil]
        simp
    · simp only [ins, hc, ↓reduceIte]
      have hL : classOf q (x :: ins e xs) = classOf q [x] ++ classOf q (ins e xs) := by
        unfold classOf
        simp only [List.filter_cons]
        split
        · simp
        · simp
      have hR : classOf q (x :: xs) = classOf q [x] ++ classOf q xs := by
        unfold classOf
        simp only [List.filter_cons]
        split
        · simp
        · simp
      rw [hL, hR, ih', List.append_assoc]

theorem plan0_run_classOf_proof (ops : List Op) (s : State) (p : Nat) :
    classOf p s.items ++ classOf p (inflow (run step s ops).1)
      = classOf p (outflow (run step s ops).1) ++ classOf p (run step s ops).2.items := by
  induction ops generalizing s with
  | nil =>
    have hNil : classOf p ([] : List Entry) = [] := by simp [classOf]
    simp [run, inflow, outflow, hNil]
  | cons op ops ih =>
    have hStep := plan1_step_classOf s op p
    have hIH := ih (step s op).2
    have hRun1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
      simp [run]
    have hRun2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
      simp [run]
    rw [hRun1, hRun2]
    have hIn : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      simp [inflow]
    have hOut : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      simp [outflow]
    rw [hIn, hOut]
    rw [plan0_classOf_append p (inflowOf (op, (step s op).1)) _]
    rw [plan0_classOf_append p (outflowOf (op, (step s op).1)) _]
    calc classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1))
        = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [hStep]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops).1)) := by rw [List.append_assoc]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops).1) ++ classOf p (run step (step s op).2 ops).2.items) := by rw [hIH]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1)) ++ classOf p (run step (step s op).2 ops).2.items := by rw [List.append_assoc]

theorem plan0_run_classOf (ops : List Op) (s : State) (p : Nat) :
    classOf p s.items ++ classOf p (inflow (run step s ops).1)
      = classOf p (outflow (run step s ops).1) ++ classOf p (run step s ops).2.items := by
  induction ops generalizing s with
  | nil =>
    have hNil : classOf p ([] : List Entry) = [] := by simp [classOf]
    simp [run, inflow, outflow, hNil]
  | cons op ops ih =>
    have hStep := plan1_step_classOf s op p
    have hIH := ih (step s op).2
    have hRun1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
      simp [run]
    have hRun2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
      simp [run]
    rw [hRun1, hRun2]
    have hIn : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      simp [inflow]
    have hOut : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      simp [outflow]
    rw [hIn, hOut]
    rw [plan0_classOf_append p (inflowOf (op, (step s op).1)) _]
    rw [plan0_classOf_append p (outflowOf (op, (step s op).1)) _]
    calc classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1))
        = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [hStep]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops).1)) := by rw [List.append_assoc]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops).1) ++ classOf p (run step (step s op).2 ops).2.items) := by rw [hIH]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1)) ++ classOf p (run step (step s op).2 ops).2.items := by rw [List.append_assoc]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  unfold step
  simp only [h, if_true]
  cases op with
  | insert e => simp
  | pop =>
    cases hst : s.items with
    | nil =>
      unfold Valid at h
      simp [hst] at h
    | cons e rest => simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  unfold step
  simp [h]

theorem req_capacity : CapacityBound step := by
  intro s op hle
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have hEq : (step s (Op.insert e)).2.items = ins e s.items := by
        unfold step; simp [hV]
      have hCap : (step s (Op.insert e)).2.capacity = s.capacity := by
        unfold step; simp [hV]
      rw [hCap, hEq, ins_length_aux]
      have hlt : s.items.length < s.capacity := hV.2
      omega
    | pop =>
      cases hitems : s.items with
      | nil =>
        exfalso
        exact hV.2 hitems
      | cons hd tl =>
        have hEqI : (step s Op.pop).2.items = tl := by
          unfold step; simp [hV, hitems]
        have hCap : (step s Op.pop).2.capacity = s.capacity := by
          unfold step; simp [hV, hitems]
        rw [hCap, hEqI]
        rw [hitems] at hle
        simp at hle
        omega
  · have hEq : (step s op).2 = s := by unfold step; simp [hV]
    rw [hEq]
    exact hle

theorem req_pop_min : PopMin step := by
  intro s hNe
  by_cases hV : Valid s Op.pop
  · have hSort : Sorted s.items := hV.1
    have hNeNil : s.items ≠ [] := hV.2
    cases hitems : s.items with
    | nil => exact False.elim (hNeNil hitems)
    | cons e rest =>
      have hSort' : Sorted (e :: rest) := hitems ▸ hSort
      have hStepEq : step s Op.pop = (Outcome.got e, { s with items := rest }) := by
        simp [step, hV, hitems]
      have hOut1 : (step s Op.pop).1 = Outcome.got e := by rw [hStepEq]
      have hOut2 : (step s Op.pop).2.items = rest := by rw [hStepEq]
      refine ⟨e, hOut1, ?_⟩
      rw [hOut2]
      exact popmin_lemma_test e rest hSort'
  · have hStep : (step s Op.pop).1 = Outcome.rejected := by simp [step, hV]
    exact False.elim (hNe hStep)

theorem req_sorted : KeepsSorted step := by
  intro s op hsort
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have h1 : (step s (Op.insert e)).2.items = ins e s.items := by
        unfold step
        simp [hV]
      rw [h1]
      exact ins_sorted_aux e s.items hsort
    | pop =>
      cases hitems : s.items with
      | nil =>
        have h1 : (step s Op.pop).2.items = ([] : List Entry) := by
          unfold step
          simp [hV, hitems]
        rw [h1]
        unfold Sorted
        exact List.Pairwise.nil
      | cons hd tl =>
        have h1 : (step s Op.pop).2.items = tl := by
          unfold step
          simp [hV, hitems]
        rw [h1]
        exact sorted_tail_aux hd tl (hitems ▸ hsort)
  · have h1 : (step s op).2.items = s.items := by
      unfold step
      simp [hV]
    rw [h1]
    exact hsort

theorem req_insert_effects : InsertEffects step := by
  intro s e hNe
  by_cases hV : Valid s (Op.insert e)
  · have hOk : (step s (Op.insert e)).1 = Outcome.ok := by
      simp [step, hV]
    have hCap : (step s (Op.insert e)).2.capacity = s.capacity := by
      simp [step, hV]
    have hItems : (step s (Op.insert e)).2.items = ins e s.items := by
      simp [step, hV]
    refine ⟨hOk, hCap, ?_⟩
    obtain ⟨l₁, l₂, hEq, hInsEq, hLe, hLt⟩ := ins_split_sorted_lem e s.items hV.1
    exact ⟨l₁, l₂, hEq, by rw [hItems, hInsEq], hLe, hLt⟩
  · have hStep : (step s (Op.insert e)).1 = Outcome.rejected := by
      simp [step, hV]
    exact False.elim (hNe hStep)

theorem req_pop_effects : PopEffects step := by
  intro s hNe
  by_cases hV : Valid s Op.pop
  · have hSort : Sorted s.items := hV.1
    have hNeNil : s.items ≠ [] := hV.2
    cases hitems : s.items with
    | nil => exact False.elim (hNeNil hitems)
    | cons e rest =>
      have hSort' : Sorted (e :: rest) := hitems ▸ hSort
      have hStepEq : step s Op.pop = (Outcome.got e, { s with items := rest }) := by
        simp [step, hV, hitems]
      have hOut1 : (step s Op.pop).1 = Outcome.got e := by rw [hStepEq]
      have hOut2 : (step s Op.pop).2.items = rest := by rw [hStepEq]
      have hCap : (step s Op.pop).2.capacity = s.capacity := by rw [hStepEq]
      exact ⟨hCap, [], e, rest, by simp [hitems], hOut1, hOut2,
        fun x hx => False.elim (List.not_mem_nil hx),
        fun x hx => popmin_lemma_test e rest hSort' x hx⟩
  · have hStep : (step s Op.pop).1 = Outcome.rejected := by simp [step, hV]
    exact False.elim (hNe hStep)

theorem req_fifo_ties : FifoTies step := fun s ops p => plan0_run_classOf ops s p

end PrioQueue
