import PrioQueue.Spec

namespace PrioQueue

def sortedb : List Entry → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => (decide (a.prio ≤ b.prio) && sortedb (b :: t))

def insertSorted (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs => if x.prio ≤ e.prio then x :: insertSorted e xs else e :: x :: xs

def step : Impl := fun s op =>
  match op with
  | .insert e =>
    match sortedb s.items with
    | false => (Outcome.rejected, s)
    | true =>
      match decide (s.items.length < s.capacity) with
      | true => (Outcome.ok, ⟨s.capacity, insertSorted e s.items⟩)
      | false => (Outcome.rejected, s)
  | .pop =>
    match s.items with
    | [] => (Outcome.rejected, s)
    | hd :: tl =>
      match sortedb s.items with
      | true => (Outcome.got hd, ⟨s.capacity, tl⟩)
      | false => (Outcome.rejected, s)

theorem sortedb_true_of_Sorted : ∀ (l : List Entry), Sorted l → sortedb l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    simp only [sortedb]
    have hc := (List.pairwise_cons.mp h)
    have hab : a.prio ≤ b.prio := hc.1 b (by simp)
    have htail : Sorted (b :: t) := hc.2
    have ih := sortedb_true_of_Sorted (b :: t) htail
    simp [hab, ih]

theorem Sorted_of_sortedb_true_aux2 : ∀ (l : List Entry), sortedb l = true → Sorted l
  | [], _ => List.Pairwise.nil
  | [x], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    simp only [sortedb] at h
    have hAnd := (Bool.and_eq_true_iff.mp h)
    have h1 : decide (a.prio ≤ b.prio) = true := hAnd.1
    have h2 : sortedb (b :: t) = true := hAnd.2
    have hab : a.prio ≤ b.prio := of_decide_eq_true h1
    have htail : Sorted (b :: t) := Sorted_of_sortedb_true_aux2 (b :: t) h2
    unfold Sorted
    rw [List.pairwise_cons]
    constructor
    · intro y hy
      have hmem : y ∈ (b :: t) := hy
      have hcase : y = b ∨ y ∈ t := by simpa using hmem
      rcases hcase with rfl | hyT
      · exact hab
      · have hpair := (List.pairwise_cons.mp htail)
        have hby : b.prio ≤ y.prio := hpair.1 y hyT
        exact Nat.le_trans hab hby
    · exact htail

theorem insertSorted_length_aux2 (e : Entry) : ∀ (l : List Entry), (insertSorted e l).length = l.length + 1
  | [] => rfl
  | x :: xs => by
    unfold insertSorted
    by_cases h : x.prio ≤ e.prio
    · simp [h, insertSorted_length_aux2 e xs, Nat.add_comm, Nat.add_left_comm]
    · simp [h]

theorem popMin_head_le_aux : ∀ (hd : Entry) (tl : List Entry),
    Sorted (hd :: tl) → ∀ x ∈ tl, hd.prio ≤ x.prio := by
  intro hd tl h x hx
  exact (List.pairwise_cons.mp h).1 x hx

theorem insertSorted_mem_subset2 (e : Entry) : ∀ (l : List Entry) (y : Entry), y ∈ insertSorted e l → y = e ∨ y ∈ l
  | [], _, h => by simp [insertSorted] at h; exact Or.inl h
  | x :: xs, _, h => by
    unfold insertSorted at h
    by_cases hx : x.prio ≤ e.prio
    · simp only [hx, ↓reduceIte] at h
      simp at h
      rcases h with rfl | hmem
      · exact Or.inr (by simp)
      · have ih := insertSorted_mem_subset2 e xs _ hmem
        rcases ih with rfl | hxin
        · exact Or.inl rfl
        · exact Or.inr (by simp [hxin])
    · simp only [hx, ↓reduceIte] at h
      simp at h
      rcases h with rfl | h2
      · exact Or.inl rfl
      · rcases h2 with rfl | hmem2
        · exact Or.inr (by simp)
        · exact Or.inr (by simp [hmem2])

theorem insertSorted_preserves_sorted3 (e : Entry) : ∀ (l : List Entry), Sorted l → Sorted (insertSorted e l)
  | [], _ => by simp [insertSorted, Sorted]
  | x :: xs, hS => by
    have hcons := List.pairwise_cons.mp hS
    have htail : Sorted xs := hcons.2
    have hx_le : ∀ y ∈ xs, x.prio ≤ y.prio := fun y hy => hcons.1 y hy
    have ih : Sorted (insertSorted e xs) := insertSorted_preserves_sorted3 e xs htail
    unfold insertSorted
    by_cases hx : x.prio ≤ e.prio
    · simp only [hx, ↓reduceIte]
      unfold Sorted at *
      rw [List.pairwise_cons]
      constructor
      · intro y hy
        have hmem := insertSorted_mem_subset2 e xs y hy
        rcases hmem with rfl | hyxs
        · exact hx
        · exact hx_le y hyxs
      · exact ih
    · simp only [hx, ↓reduceIte]
      unfold Sorted at *
      rw [List.pairwise_cons]
      constructor
      · intro y hy
        have hy2 : y = x ∨ y ∈ xs := by simpa using hy
        rcases hy2 with rfl | hyxs
        · omega
        · have h1 : x.prio ≤ y.prio := hx_le y hyxs
          omega
      · rw [List.pairwise_cons]
        constructor
        · intro y hy
          have h1 : x.prio ≤ y.prio := hx_le y hy
          omega
        · exact htail

theorem insertSorted_split_helper2 (e : Entry) : ∀ (l : List Entry), Sorted l →
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ insertSorted e l = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio)
  | [], _ => ⟨[], [], rfl, rfl, by simp, by simp⟩
  | x :: xs, hS => by
    have hcons := List.pairwise_cons.mp hS
    have htail : Sorted xs := hcons.2
    have hx_le : ∀ y ∈ xs, x.prio ≤ y.prio := fun y hy => hcons.1 y hy
    obtain ⟨l₁', l₂', heq_xs, heq_ins, hle1, hlt2⟩ := insertSorted_split_helper2 e xs htail
    by_cases hx : x.prio ≤ e.prio
    · refine ⟨x :: l₁', l₂', ?_, ?_, ?_, hlt2⟩
      · simp [heq_xs]
      · simp [insertSorted, hx, heq_ins]
      · intro y hy
        simp at hy
        rcases hy with rfl | hy2
        · exact hx
        · exact hle1 y hy2
    · have hlt_x : e.prio < x.prio := Nat.lt_of_not_ge hx
      refine ⟨[], x :: xs, by simp, by simp [insertSorted, hx], by simp, ?_⟩
      · intro y hy
        simp at hy
        rcases hy with rfl | hy2
        · exact hlt_x
        · have h1 : x.prio ≤ y.prio := hx_le y hy2
          omega

theorem t1 (p : Nat) (l₁ l₂ : List Entry) : classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by unfold classOf; rw [List.filter_append]

theorem t3 (p : Nat) (a : Entry) (l : List Entry) : classOf p (a :: l) = classOf p [a] ++ classOf p l := by
  have h : (a :: l) = [a] ++ l := by simp
  rw [h, t1]

theorem t4 (p : Nat) (l : List Entry) (h : ∀ x ∈ l, x.prio ≠ p) : classOf p l = [] := by
  unfold classOf
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter_cons]
    have hhd : hd.prio ≠ p := h hd (by simp)
    have htl : ∀ x ∈ tl, x.prio ≠ p := fun x hx => h x (by simp [hx])
    have ihtl := ih htl
    simp [hhd, ihtl]

theorem t5 (p : Nat) (e : Entry) (h : e.prio = p) : classOf p [e] = [e] := by
  unfold classOf
  simp [h]

theorem t6 (p : Nat) (e : Entry) (h : e.prio ≠ p) : classOf p [e] = [] := by
  unfold classOf
  simp [h]

theorem inflow_cons_lemma (a : Op × Outcome) (t : List (Op × Outcome)) : inflow (a :: t) = inflowOf a ++ inflow t := by simp [inflow]

theorem outflow_cons_lemma (a : Op × Outcome) (t : List (Op × Outcome)) : outflow (a :: t) = outflowOf a ++ outflow t := by simp [outflow]

theorem classOf_insertSorted (p : Nat) (e : Entry) (l : List Entry) (hS : Sorted l) :
    classOf p (insertSorted e l) = classOf p l ++ classOf p [e] := by
  obtain ⟨l₁, l₂, heq1, heq2, hle, hlt⟩ := insertSorted_split_helper2 e l hS
  subst heq1
  rw [heq2]
  have hcons : ∀ (a : Entry) (t : List Entry), (a :: t) = [a] ++ t := by intro a t; simp
  rw [hcons e l₂]
  rw [t1 p l₁ ([e] ++ l₂)]
  rw [t1 p [e] l₂]
  rw [t1 p l₁ l₂]
  by_cases heq : e.prio = p
  · have h2nil : classOf p l₂ = [] := by
      apply t4
      intro x hx
      have hltx := hlt x hx
      omega
    rw [h2nil]
    have he : classOf p [e] = [e] := t5 p e heq
    rw [he]
    simp
  · have he : classOf p [e] = [] := t6 p e heq
    rw [he]
    simp

theorem req_invalid_noop_aux3 : InvalidNoop step := by
  intro s op hN
  cases op with
  | insert e =>
    have hN2 : ¬ (Sorted s.items ∧ s.items.length < s.capacity) := hN
    cases hsb : sortedb s.items with
    | false =>
      have hstep : step s (.insert e) = (Outcome.rejected, s) := by
        unfold step; rw [hsb]
      exact hstep
    | true =>
      have hS : Sorted s.items := Sorted_of_sortedb_true_aux2 s.items hsb
      by_cases hlen : s.items.length < s.capacity
      · have hFalse : False := hN2 ⟨hS, hlen⟩
        exact False.elim hFalse
      · have hdec : decide (s.items.length < s.capacity) = false := by simp [hlen]
        have hstep : step s (.insert e) = (Outcome.rejected, s) := by
          unfold step; rw [hsb, hdec]
        exact hstep
  | pop =>
    have hN2 : ¬ (Sorted s.items ∧ s.items ≠ []) := hN
    cases hitems : s.items with
    | nil =>
      have hstep : step s .pop = (Outcome.rejected, s) := by
        unfold step; rw [hitems]
      exact hstep
    | cons hd tl =>
      have heq : s.items = hd :: tl := hitems
      cases hsb : sortedb (hd :: tl) with
      | false =>
        have hstep : step s .pop = (Outcome.rejected, s) := by
          unfold step; rw [heq, hsb]
        exact hstep
      | true =>
        have hS : Sorted s.items := hitems ▸ Sorted_of_sortedb_true_aux2 (hd :: tl) hsb
        have hNe : s.items ≠ [] := by simp [hitems]
        have hFalse : False := hN2 ⟨hS, hNe⟩
        exact False.elim hFalse

theorem fifo_single (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
    classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  cases s with
  | mk cap items =>
    cases op with
    | insert e =>
      cases hsb : sortedb items with
      | false =>
        have hstep : step ⟨cap, items⟩ (Op.insert e) = (Outcome.rejected, ⟨cap, items⟩) := by
          simp [step, hsb]
        have hfst : (step ⟨cap, items⟩ (Op.insert e)).1 = Outcome.rejected := by rw [hstep]
        have hsnd : (step ⟨cap, items⟩ (Op.insert e)).2 = (⟨cap, items⟩ : State) := by rw [hstep]
        have e1 : inflowOf (Op.insert e, (step ⟨cap, items⟩ (Op.insert e)).1) = ([] : List Entry) := by
          rw [hfst]; rfl
        have e2 : outflowOf (Op.insert e, (step ⟨cap, items⟩ (Op.insert e)).1) = ([] : List Entry) := by
          rw [hfst]; rfl
        simp [e1, e2, hsnd, classOf]
      | true =>
        by_cases hlen : items.length < cap
        · have hdec : decide (items.length < cap) = true := by simp [hlen]
          have hstep : step ⟨cap, items⟩ (Op.insert e) = (Outcome.ok, ⟨cap, insertSorted e items⟩) := by
            simp [step, hsb, hdec]
          have hfst : (step ⟨cap, items⟩ (Op.insert e)).1 = Outcome.ok := by rw [hstep]
          have hsnd : (step ⟨cap, items⟩ (Op.insert e)).2.items = insertSorted e items := by rw [hstep]
          have e1 : inflowOf (Op.insert e, (step ⟨cap, items⟩ (Op.insert e)).1) = [e] := by
            rw [hfst]; rfl
          have e2 : outflowOf (Op.insert e, (step ⟨cap, items⟩ (Op.insert e)).1) = ([] : List Entry) := by
            rw [hfst]; rfl
          have hS : Sorted items := Sorted_of_sortedb_true_aux2 items hsb
          have hcis := classOf_insertSorted p e items hS
          simp only [e1, e2, hsnd, classOf, List.filter_nil, List.nil_append] at hcis ⊢
          simp only [hcis]
        · have hdec : decide (items.length < cap) = false := by simp [hlen]
          have hstep : step ⟨cap, items⟩ (Op.insert e) = (Outcome.rejected, ⟨cap, items⟩) := by
            simp [step, hsb, hdec]
          have hfst : (step ⟨cap, items⟩ (Op.insert e)).1 = Outcome.rejected := by rw [hstep]
          have hsnd : (step ⟨cap, items⟩ (Op.insert e)).2 = (⟨cap, items⟩ : State) := by rw [hstep]
          have e1 : inflowOf (Op.insert e, (step ⟨cap, items⟩ (Op.insert e)).1) = ([] : List Entry) := by
            rw [hfst]; rfl
          have e2 : outflowOf (Op.insert e, (step ⟨cap, items⟩ (Op.insert e)).1) = ([] : List Entry) := by
            rw [hfst]; rfl
          simp [e1, e2, hsnd, classOf]
    | pop =>
      cases items with
      | nil =>
        have hstep : step (⟨cap, []⟩ : State) Op.pop = (Outcome.rejected, (⟨cap, []⟩ : State)) := by
          simp [step]
        have hfst : (step (⟨cap, []⟩ : State) Op.pop).1 = Outcome.rejected := by rw [hstep]
        have hsnd : (step (⟨cap, []⟩ : State) Op.pop).2 = ((⟨cap, []⟩ : State)) := by rw [hstep]
        have e1 : inflowOf (Op.pop, (step (⟨cap, []⟩ : State) Op.pop).1) = ([] : List Entry) := by
          rw [hfst]; rfl
        have e2 : outflowOf (Op.pop, (step (⟨cap, []⟩ : State) Op.pop).1) = ([] : List Entry) := by
          rw [hfst]; rfl
        simp [e1, e2, hsnd, classOf]
      | cons hd tl =>
        cases hsb : sortedb (hd :: tl) with
        | false =>
          have hstep : step (⟨cap, hd :: tl⟩ : State) Op.pop = (Outcome.rejected, (⟨cap, hd :: tl⟩ : State)) := by
            simp [step, hsb]
          have hfst : (step (⟨cap, hd :: tl⟩ : State) Op.pop).1 = Outcome.rejected := by rw [hstep]
          have hsnd : (step (⟨cap, hd :: tl⟩ : State) Op.pop).2 = ((⟨cap, hd :: tl⟩ : State)) := by rw [hstep]
          have e1 : inflowOf (Op.pop, (step (⟨cap, hd :: tl⟩ : State) Op.pop).1) = ([] : List Entry) := by
            rw [hfst]; rfl
          have e2 : outflowOf (Op.pop, (step (⟨cap, hd :: tl⟩ : State) Op.pop).1) = ([] : List Entry) := by
            rw [hfst]; rfl
          simp [e1, e2, hsnd, classOf]
        | true =>
          have hstep : step (⟨cap, hd :: tl⟩ : State) Op.pop = (Outcome.got hd, (⟨cap, tl⟩ : State)) := by
            simp [step, hsb]
          have hfst : (step (⟨cap, hd :: tl⟩ : State) Op.pop).1 = Outcome.got hd := by rw [hstep]
          have hsnd : (step (⟨cap, hd :: tl⟩ : State) Op.pop).2.items = tl := by rw [hstep]
          have e1 : inflowOf (Op.pop, (step (⟨cap, hd :: tl⟩ : State) Op.pop).1) = ([] : List Entry) := by
            rw [hfst]; rfl
          have e2 : outflowOf (Op.pop, (step (⟨cap, hd :: tl⟩ : State) Op.pop).1) = [hd] := by
            rw [hfst]; rfl
          have hnil : classOf p ([] : List Entry) = [] := rfl
          rw [e1, e2, hsnd, hnil, List.append_nil]
          exact t3 p hd tl

theorem fifo_general (s : State) (ops : List Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflow (run step s ops).1) =
    classOf p (outflow (run step s ops).1) ++ classOf p (run step s ops).2.items := by
  induction ops generalizing s with
  | nil =>
    have hr : run step s [] = (([] : List (Op × Outcome)), s) := rfl
    rw [hr]
    simp [inflow, outflow, classOf]
  | cons op ops' ih =>
    have hT1 : (run step s (op :: ops')).1 = (op, (step s op).1) :: (run step (step s op).2 ops').1 := rfl
    have hT2 : (run step s (op :: ops')).2 = (run step (step s op).2 ops').2 := rfl
    have hSingle := fifo_single s op p
    have hIH := ih (step s op).2
    have hIn : classOf p (inflow ((op, (step s op).1) :: (run step (step s op).2 ops').1)) =
        classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops').1) := by
      have h : inflow ((op, (step s op).1) :: (run step (step s op).2 ops').1) =
        inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops').1 :=
        inflow_cons_lemma _ _
      rw [h]
      exact t1 p _ _
    have hOut : classOf p (outflow ((op, (step s op).1) :: (run step (step s op).2 ops').1)) =
        classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops').1) := by
      have h : outflow ((op, (step s op).1) :: (run step (step s op).2 ops').1) =
        outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops').1 :=
        outflow_cons_lemma _ _
      rw [h]
      exact t1 p _ _
    rw [hT1, hT2, hIn, hOut]
    calc classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops').1))
        _ = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops').1) := by rw [← List.append_assoc]
        _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops').1) := by rw [hSingle]
        _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops').1)) := by rw [List.append_assoc]
        _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops').1) ++ classOf p (run step (step s op).2 ops').2.items) := by rw [hIH]
        _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops').1)) ++ classOf p (run step (step s op).2 ops').2.items := by rw [← List.append_assoc]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | insert e =>
    obtain ⟨hS, hL⟩ := hV
    have hb : sortedb s.items = true := sortedb_true_of_Sorted s.items hS
    have hdec : decide (s.items.length < s.capacity) = true := by simp [hL]
    have hstep : step s (.insert e) = (Outcome.ok, ⟨s.capacity, insertSorted e s.items⟩) := by
      unfold step; rw [hb, hdec]
    rw [hstep]
    simp
  | pop =>
    obtain ⟨hS, hNe⟩ := hV
    have hb : sortedb s.items = true := sortedb_true_of_Sorted s.items hS
    cases hitems : s.items with
    | nil => contradiction
    | cons hd tl =>
      have hb2 : sortedb (hd :: tl) = true := hitems ▸ hb
      have hstep : step s .pop = (Outcome.got hd, ⟨s.capacity, tl⟩) := by
        unfold step; rw [hitems, hb2]
      rw [hstep]
      simp

theorem req_invalid_noop : InvalidNoop step := req_invalid_noop_aux3

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | insert e =>
    cases hsb : sortedb s.items with
    | false =>
      have hstep : step s (.insert e) = (Outcome.rejected, s) := by
        unfold step; rw [hsb]
      rw [hstep]
      exact hle
    | true =>
      by_cases hlen : s.items.length < s.capacity
      · have hdec : decide (s.items.length < s.capacity) = true := by simp [hlen]
        have hstep : step s (.insert e) = (Outcome.ok, ⟨s.capacity, insertSorted e s.items⟩) := by
          unfold step; rw [hsb, hdec]
        rw [hstep]
        show (insertSorted e s.items).length ≤ s.capacity
        rw [insertSorted_length_aux2]
        omega
      · have hdec : decide (s.items.length < s.capacity) = false := by simp [hlen]
        have hstep : step s (.insert e) = (Outcome.rejected, s) := by
          unfold step; rw [hsb, hdec]
        rw [hstep]
        exact hle
  | pop =>
    cases hitems : s.items with
    | nil =>
      have hstep : step s .pop = (Outcome.rejected, s) := by
        unfold step; rw [hitems]
      rw [hstep]
      exact hle
    | cons hd tl =>
      have heq : s.items = hd :: tl := hitems
      cases hsb : sortedb (hd :: tl) with
      | false =>
        have hstep : step s .pop = (Outcome.rejected, s) := by
          unfold step; rw [heq, hsb]
        rw [hstep]
        exact hle
      | true =>
        have hstep : step s .pop = (Outcome.got hd, ⟨s.capacity, tl⟩) := by
          unfold step; rw [heq, hsb]
        rw [hstep]
        simp only
        have hlen : (hd :: tl).length ≤ s.capacity := heq ▸ hle
        simp at hlen
        omega

theorem req_pop_min : PopMin step := by
  intro s hNe
  cases hitems : s.items with
  | nil =>
    have hstep : step s .pop = (Outcome.rejected, s) := by
      unfold step; rw [hitems]
    rw [hstep] at hNe
    simp at hNe
  | cons hd tl =>
    have heq : s.items = hd :: tl := hitems
    cases hsb : sortedb (hd :: tl) with
    | false =>
      have hStepR : step s .pop = (Outcome.rejected, s) := by
        unfold step; rw [heq, hsb]
      rw [hStepR] at hNe
      simp at hNe
    | true =>
      have hStep1 : step s .pop = (Outcome.got hd, ⟨s.capacity, tl⟩) := by
        unfold step; rw [heq, hsb]
      refine ⟨hd, ?_, ?_⟩
      · rw [hStep1]
      · rw [hStep1]
        simp only
        have hS : Sorted (hd :: tl) := Sorted_of_sortedb_true_aux2 (hd :: tl) hsb
        intro x hx
        exact popMin_head_le_aux hd tl hS x hx

theorem req_sorted : KeepsSorted step := by
  intro s op hS
  cases op with
  | insert e =>
    cases hsb : sortedb s.items with
    | false =>
      have hstep : step s (.insert e) = (Outcome.rejected, s) := by
        unfold step; rw [hsb]
      rw [hstep]
      exact hS
    | true =>
      by_cases hlen : s.items.length < s.capacity
      · have hdec : decide (s.items.length < s.capacity) = true := by simp [hlen]
        have hstep : step s (.insert e) = (Outcome.ok, ⟨s.capacity, insertSorted e s.items⟩) := by
          unfold step; rw [hsb, hdec]
        rw [hstep]
        simp only
        exact insertSorted_preserves_sorted3 e s.items hS
      · have hdec : decide (s.items.length < s.capacity) = false := by simp [hlen]
        have hstep : step s (.insert e) = (Outcome.rejected, s) := by
          unfold step; rw [hsb, hdec]
        rw [hstep]
        exact hS
  | pop =>
    cases hitems : s.items with
    | nil =>
      have hstep : step s .pop = (Outcome.rejected, s) := by
        unfold step; rw [hitems]
      rw [hstep]
      exact hS
    | cons hd tl =>
      have heq : s.items = hd :: tl := hitems
      cases hsb : sortedb (hd :: tl) with
      | false =>
        have hstep : step s .pop = (Outcome.rejected, s) := by
          unfold step; rw [heq, hsb]
        rw [hstep]
        exact hS
      | true =>
        have hstep : step s .pop = (Outcome.got hd, ⟨s.capacity, tl⟩) := by
          unfold step; rw [heq, hsb]
        rw [hstep]
        simp only
        have hS2 : Sorted (hd :: tl) := heq ▸ hS
        exact (List.pairwise_cons.mp hS2).2

theorem req_insert_effects : InsertEffects step := by
  intro s e hNe
  cases hsb : sortedb s.items with
  | false =>
    have hstep : step s (.insert e) = (Outcome.rejected, s) := by
      unfold step; rw [hsb]
    rw [hstep] at hNe
    simp at hNe
  | true =>
    by_cases hlen : s.items.length < s.capacity
    · have hdec : decide (s.items.length < s.capacity) = true := by simp [hlen]
      have hstep : step s (.insert e) = (Outcome.ok, ⟨s.capacity, insertSorted e s.items⟩) := by
        unfold step; rw [hsb, hdec]
      have hS : Sorted s.items := Sorted_of_sortedb_true_aux2 s.items hsb
      obtain ⟨l₁, l₂, heq1, heq2, hle, hlt⟩ := insertSorted_split_helper2 e s.items hS
      refine ⟨?_, ?_, l₁, l₂, heq1, ?_, hle, hlt⟩
      · rw [hstep]
      · rw [hstep]
      · rw [hstep]
        simp only
        exact heq2
    · have hdec : decide (s.items.length < s.capacity) = false := by simp [hlen]
      have hstep : step s (.insert e) = (Outcome.rejected, s) := by
        unfold step; rw [hsb, hdec]
      rw [hstep] at hNe
      simp at hNe

theorem req_pop_effects : PopEffects step := by
  intro s hNe
  cases hitems : s.items with
  | nil =>
    have hStepR : step s .pop = (Outcome.rejected, s) := by
      unfold step; rw [hitems]
    rw [hStepR] at hNe
    simp at hNe
  | cons hd tl =>
    have heq : s.items = hd :: tl := hitems
    cases hsb : sortedb (hd :: tl) with
    | false =>
      have hStepR : step s .pop = (Outcome.rejected, s) := by
        unfold step; rw [heq, hsb]
      rw [hStepR] at hNe
      simp at hNe
    | true =>
      have hStep : step s .pop = (Outcome.got hd, ⟨s.capacity, tl⟩) := by
        unfold step; rw [heq, hsb]
      have hS : Sorted (hd :: tl) := Sorted_of_sortedb_true_aux2 (hd :: tl) hsb
      refine ⟨by rw [hStep], [], hd, tl, by simp [heq], by rw [hStep], by rw [hStep]; simp, by simp, ?_⟩
      intro x hx
      exact popMin_head_le_aux hd tl hS x hx

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  exact fifo_general s ops p

end PrioQueue
