import PrioQueue.Spec

namespace PrioQueue

def isSorted : List Entry → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => if decide (a.prio ≤ b.prio) then isSorted (b :: rest) else false

def insertList (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs => if decide (e.prio < x.prio) then e :: x :: xs else x :: insertList e xs

def step : Impl := fun s op =>
  match op with
  | .insert e =>
    if isSorted s.items && decide (s.items.length < s.capacity) then
      (Outcome.ok, { capacity := s.capacity, items := insertList e s.items })
    else
      (Outcome.rejected, s)
  | .pop =>
    if isSorted s.items then
      match s.items with
      | [] => (Outcome.rejected, s)
      | e :: rest => (Outcome.got e, { capacity := s.capacity, items := rest })
    else
      (Outcome.rejected, s)

theorem sorted_of_isSorted : ∀ (l : List Entry), isSorted l = true → Sorted l := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a tl ih =>
    intro h
    cases tl with
    | nil => exact List.Pairwise.cons (by simp) List.Pairwise.nil
    | cons b rest =>
      have hstep : (if decide (a.prio ≤ b.prio) then isSorted (b :: rest) else false) = true := h
      have hdec : decide (a.prio ≤ b.prio) = true := by
        cases hd : decide (a.prio ≤ b.prio) with
        | true => rfl
        | false => simp [hd] at hstep
      have hle : a.prio ≤ b.prio := of_decide_eq_true hdec
      have htail : isSorted (b :: rest) = true := by simp [hdec] at hstep; exact hstep
      have ihS : Sorted (b :: rest) := ih htail
      exact List.Pairwise.cons (fun x hx => by
        cases hx with
        | head _ => exact hle
        | tail _ hm =>
          have hb : b.prio ≤ x.prio := (List.pairwise_cons.mp ihS).1 x hm
          exact Nat.le_trans hle hb) ihS

theorem isSorted_of_sorted : ∀ (l : List Entry), Sorted l → isSorted l = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a tl ih =>
    intro h
    cases tl with
    | nil => rfl
    | cons b rest =>
      have h1 : ∀ x ∈ b :: rest, a.prio ≤ x.prio := (List.pairwise_cons.mp h).1
      have h2 : Sorted (b :: rest) := (List.pairwise_cons.mp h).2
      have hle : a.prio ≤ b.prio := h1 b (List.Mem.head _)
      have hdec : decide (a.prio ≤ b.prio) = true := decide_eq_true hle
      have iht : isSorted (b :: rest) = true := ih h2
      simp [isSorted, hdec, iht]

theorem insertList_mem : ∀ (e y : Entry) (l : List Entry), y ∈ insertList e l → y = e ∨ y ∈ l := by
  intro e y l
  induction l with
  | nil => intro h; simp [insertList] at h; exact Or.inl h
  | cons x xs ih =>
    simp only [insertList]
    split
    · intro h
      rw [List.mem_cons] at h
      cases h with
      | inl he => exact Or.inl he
      | inr h2 =>
        rw [List.mem_cons] at h2
        cases h2 with
        | inl he2 => exact Or.inr (he2 ▸ List.Mem.head _)
        | inr hmem => exact Or.inr (List.Mem.tail _ hmem)
    · intro h
      rw [List.mem_cons] at h
      cases h with
      | inl he => exact Or.inr (he ▸ List.Mem.head _)
      | inr h2 =>
        have hr := ih h2
        cases hr with
        | inl he => exact Or.inl he
        | inr hm => exact Or.inr (List.Mem.tail _ hm)

theorem insertList_sorted : ∀ (e : Entry) (l : List Entry), Sorted l → Sorted (insertList e l) := by
  intro e l
  induction l with
  | nil => intro _; exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | cons x xs ih =>
    intro h
    have hall : ∀ y ∈ xs, x.prio ≤ y.prio := (List.pairwise_cons.mp h).1
    have htailS : Sorted xs := (List.pairwise_cons.mp h).2
    have ihS : Sorted (insertList e xs) := ih htailS
    by_cases hlt : e.prio < x.prio
    · have hdec : decide (e.prio < x.prio) = true := decide_eq_true hlt
      have hle : e.prio ≤ x.prio := Nat.le_of_lt hlt
      have hunfold : insertList e (x :: xs) = e :: x :: xs := by simp [insertList, hdec]
      rw [hunfold]
      apply List.Pairwise.cons _ h
      intro y hy
      rw [List.mem_cons] at hy
      cases hy with
      | inl heq => rw [heq]; exact hle
      | inr hm => exact Nat.le_trans hle (hall y hm)
    · have hdec : decide (e.prio < x.prio) = false := decide_eq_false hlt
      have hle : x.prio ≤ e.prio := by omega
      have hunfold : insertList e (x :: xs) = x :: insertList e xs := by simp [insertList, hdec]
      rw [hunfold]
      apply List.Pairwise.cons _ ihS
      intro y hy
      have hr := insertList_mem e y xs hy
      cases hr with
      | inl heq => rw [heq]; exact hle
      | inr hm => exact hall y hm

theorem insertList_len (e : Entry) (l : List Entry) : (insertList e l).length = l.length + 1 := by
  induction l with
  | nil => simp [insertList]
  | cons x xs ih =>
    simp only [insertList]
    split
    · simp
    · simp [ih, Nat.add_comm, Nat.add_left_comm]

theorem insertList_split_sorted (e : Entry) : ∀ (l : List Entry), Sorted l →
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ insertList e l = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  intro l hS
  induction l with
  | nil => exact ⟨[], [], rfl, rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩
  | cons x xs ih =>
    have hall : ∀ y ∈ xs, x.prio ≤ y.prio := (List.pairwise_cons.mp hS).1
    have htailS : Sorted xs := (List.pairwise_cons.mp hS).2
    obtain ⟨l₁, l₂, heq, hins, h1, h2⟩ := ih htailS
    by_cases hlt : e.prio < x.prio
    · have hdec : decide (e.prio < x.prio) = true := decide_eq_true hlt
      have hunfold : insertList e (x :: xs) = e :: x :: xs := by simp [insertList, hdec]
      refine ⟨[], x :: xs, rfl, ?_, ?_, ?_⟩
      · simp [hunfold]
      · intro y hy; simp at hy
      · intro y hy
        simp at hy
        cases hy with
        | inl heq2 => rw [heq2]; exact hlt
        | inr hm =>
          have hx : x.prio ≤ y.prio := hall y hm
          omega
    · have hdec : decide (e.prio < x.prio) = false := decide_eq_false hlt
      have hle : x.prio ≤ e.prio := by omega
      have hunfold : insertList e (x :: xs) = x :: insertList e xs := by simp [insertList, hdec]
      refine ⟨x :: l₁, l₂, ?_, ?_, ?_, h2⟩
      · simp [heq]
      · simp [hunfold, hins]
      · intro y hy
        simp at hy
        cases hy with
        | inl heq2 => rw [heq2]; exact hle
        | inr hm => exact h1 y hm

theorem class_append (p : Nat) (l1 l2 : List Entry) :
    classOf p (l1 ++ l2) = classOf p l1 ++ classOf p l2 := by
  unfold classOf; rw [List.filter_append]

theorem class_nil (p : Nat) : classOf p ([] : List Entry) = [] := rfl

theorem class_singleton (p : Nat) (x : Entry) (l : List Entry) :
    classOf p (x :: l) = classOf p [x] ++ classOf p l := by
  have h : (x :: l) = [x] ++ l := rfl
  rw [h]
  exact class_append p [x] l

theorem beq_false_of_ne (a b : Nat) (h : a ≠ b) : (a == b) = false := by simp [BEq.beq, h]

theorem beq_true_of_eq (a b : Nat) (h : a = b) : (a == b) = true := by simp [h]

theorem class_empty_of_ne : ∀ (p : Nat) (l : List Entry), (∀ x ∈ l, x.prio ≠ p) → classOf p l = [] := by
  intro p l h
  unfold classOf
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.prio ≠ p := h x (List.Mem.head _)
    have hxs : ∀ y ∈ xs, y.prio ≠ p := fun y hy => h y (List.Mem.tail _ hy)
    have ihv := ih hxs
    simp [beq_false_of_ne x.prio p hx, ihv]

theorem insert_class (p : Nat) (e : Entry) : ∀ (l : List Entry), Sorted l →
    classOf p (insertList e l) = classOf p l ++ classOf p [e] := by
  intro l hS
  obtain ⟨l₁, l₂, heq, hins, h1, h2⟩ := insertList_split_sorted e l hS
  have hL : classOf p l = classOf p l₁ ++ classOf p l₂ := by rw [heq]; exact class_append p l₁ l₂
  have hR : classOf p (insertList e l) = classOf p l₁ ++ (classOf p [e] ++ classOf p l₂) := by
    rw [hins]
    rw [class_append p l₁ (e :: l₂), class_singleton p e l₂]
  rw [hL, hR]
  by_cases heq2 : e.prio = p
  · have hCl2 : classOf p l₂ = [] := by
      apply class_empty_of_ne p l₂
      intro y hy
      have hlt : e.prio < y.prio := h2 y hy
      omega
    have hCe : classOf p [e] = [e] := by unfold classOf; simp [beq_true_of_eq e.prio p heq2]
    rw [hCl2, hCe]; simp
  · have hCe : classOf p [e] = [] := by unfold classOf; simp [beq_false_of_ne e.prio p heq2]
    by_cases hlt : e.prio < p
    · have hCl1 : classOf p l₁ = [] := by
        apply class_empty_of_ne p l₁
        intro y hy
        have hle : y.prio ≤ e.prio := h1 y hy
        omega
      rw [hCl1, hCe]; simp
    · have hCl2 : classOf p l₂ = [] := by
        apply class_empty_of_ne p l₂
        intro y hy
        have hlt3 : e.prio < y.prio := h2 y hy
        omega
      rw [hCl2, hCe]; simp

theorem inflow_cons (a : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (a :: t) = inflowOf a ++ inflow t := by simp [inflow]

theorem outflow_cons (a : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (a :: t) = outflowOf a ++ outflow t := by simp [outflow]

theorem inflowOf_pop_eq (o : Outcome) : inflowOf (Op.pop, o) = ([] : List Entry) := by
  cases o <;> simp [inflowOf]

theorem outflowOf_rej_pop : outflowOf (Op.pop, Outcome.rejected) = ([] : List Entry) := by
  simp [outflowOf]

theorem outflowOf_got_pop (e : Entry) : outflowOf (Op.pop, Outcome.got e) = [e] := by
  simp [outflowOf]

theorem inflowOf_ins_ok (e : Entry) : inflowOf (Op.insert e, Outcome.ok) = [e] := by
  simp [inflowOf]

theorem inflowOf_ins_rej (e : Entry) : inflowOf (Op.insert e, Outcome.rejected) = ([] : List Entry) := by
  simp [inflowOf]

theorem outflowOf_ins_ok (e : Entry) : outflowOf (Op.insert e, Outcome.ok) = ([] : List Entry) := by
  simp [outflowOf]

theorem outflowOf_ins_rej (e : Entry) : outflowOf (Op.insert e, Outcome.rejected) = ([] : List Entry) := by
  simp [outflowOf]

theorem step_single_class (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
    = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  obtain ⟨cap, its⟩ := s
  cases op with
  | insert e =>
    cases hC : (isSorted its && decide (its.length < cap)) with
    | true =>
      have hstep : step ⟨cap, its⟩ (.insert e) = (Outcome.ok, { capacity := cap, items := insertList e its }) := by
        simp [step, hC]
      have h1 : (step ⟨cap, its⟩ (.insert e)).1 = Outcome.ok := by rw [hstep]
      have h2 : (step ⟨cap, its⟩ (.insert e)).2.items = insertList e its := by rw [hstep]
      have hin : inflowOf (Op.insert e, (step ⟨cap, its⟩ (.insert e)).1) = [e] := by rw [h1]; exact inflowOf_ins_ok e
      have hout : outflowOf (Op.insert e, (step ⟨cap, its⟩ (.insert e)).1) = ([] : List Entry) := by rw [h1]; exact outflowOf_ins_ok e
      have hsort : isSorted its = true := by
        have hT : (isSorted its && decide (its.length < cap)) = true := hC
        rw [Bool.and_eq_true] at hT
        exact hT.1
      have hSorted : Sorted its := sorted_of_isSorted its hsort
      have hcls := insert_class p e its hSorted
      simp only [hin, hout, h2, hcls, class_nil, List.append_nil, List.nil_append]
    | false =>
      have hstep : step ⟨cap, its⟩ (.insert e) = (Outcome.rejected, ⟨cap, its⟩) := by
        simp [step, hC]
      have h1 : (step ⟨cap, its⟩ (.insert e)).1 = Outcome.rejected := by rw [hstep]
      have h2 : (step ⟨cap, its⟩ (.insert e)).2 = (⟨cap, its⟩ : State) := by rw [hstep]
      have hin : inflowOf (Op.insert e, (step ⟨cap, its⟩ (.insert e)).1) = ([] : List Entry) := by rw [h1]; exact inflowOf_ins_rej e
      have hout : outflowOf (Op.insert e, (step ⟨cap, its⟩ (.insert e)).1) = ([] : List Entry) := by rw [h1]; exact outflowOf_ins_rej e
      simp only [hin, hout, h2, class_nil, List.append_nil, List.nil_append]
  | pop =>
    cases hsort : isSorted its with
    | false =>
      have hstep : step ⟨cap, its⟩ Op.pop = (Outcome.rejected, ⟨cap, its⟩) := by
        simp [step, hsort]
      have h1 : (step ⟨cap, its⟩ Op.pop).1 = Outcome.rejected := by rw [hstep]
      have h2 : (step ⟨cap, its⟩ Op.pop).2 = (⟨cap, its⟩ : State) := by rw [hstep]
      have hin : inflowOf (Op.pop, (step ⟨cap, its⟩ Op.pop).1) = ([] : List Entry) := inflowOf_pop_eq _
      have hout : outflowOf (Op.pop, (step ⟨cap, its⟩ Op.pop).1) = ([] : List Entry) := by rw [h1]; exact outflowOf_rej_pop
      simp only [hin, hout, h2, class_nil, List.append_nil, List.nil_append]
    | true =>
      cases its with
      | nil =>
        have hstep : step ⟨cap, ([] : List Entry)⟩ Op.pop = (Outcome.rejected, ⟨cap, []⟩) := by
          simp [step, isSorted]
        have h1 : (step ⟨cap, ([] : List Entry)⟩ Op.pop).1 = Outcome.rejected := by rw [hstep]
        have h2 : (step ⟨cap, ([] : List Entry)⟩ Op.pop).2 = (⟨cap, []⟩ : State) := by rw [hstep]
        have hin : inflowOf (Op.pop, (step ⟨cap, ([] : List Entry)⟩ Op.pop).1) = ([] : List Entry) := inflowOf_pop_eq _
        have hout : outflowOf (Op.pop, (step ⟨cap, ([] : List Entry)⟩ Op.pop).1) = ([] : List Entry) := by rw [h1]; exact outflowOf_rej_pop
        simp only [hin, hout, h2, class_nil, List.append_nil, List.nil_append]
      | cons e rest =>
        have hstep : step ⟨cap, e :: rest⟩ Op.pop = (Outcome.got e, { capacity := cap, items := rest }) := by
          simp [step, hsort]
        have h1 : (step ⟨cap, e :: rest⟩ Op.pop).1 = Outcome.got e := by rw [hstep]
        have h2 : (step ⟨cap, e :: rest⟩ Op.pop).2.items = rest := by rw [hstep]
        have hin : inflowOf (Op.pop, (step ⟨cap, e :: rest⟩ Op.pop).1) = ([] : List Entry) := inflowOf_pop_eq _
        have hout : outflowOf (Op.pop, (step ⟨cap, e :: rest⟩ Op.pop).1) = [e] := by rw [h1]; exact outflowOf_got_pop e
        rw [hin, hout, h2]
        simp only [class_nil, List.append_nil]
        exact class_singleton p e rest

theorem fifo_trace : ∀ (s : State) (ops : List Op) (p : Nat),
    classOf p s.items ++ classOf p (inflow (run step s ops).1)
    = classOf p (outflow (run step s ops).1) ++ classOf p (run step s ops).2.items := by
  intro s ops p
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow, classOf]
  | cons op rest ih =>
    have hStep := step_single_class s op p
    have hIH := ih (step s op).2
    have hT1 : (run step s (op :: rest)).1 = (op, (step s op).1) :: (run step (step s op).2 rest).1 := rfl
    have hT2 : (run step s (op :: rest)).2 = (run step (step s op).2 rest).2 := rfl
    calc classOf p s.items ++ classOf p (inflow (run step s (op :: rest)).1)
        _ = classOf p s.items ++ classOf p (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1) := by
          rw [hT1, inflow_cons]
        _ = classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 rest).1)) := by
          rw [class_append]
        _ = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 rest).1) := by
          rw [List.append_assoc]
        _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 rest).1) := by
          rw [hStep]
        _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 rest).1)) := by
          rw [List.append_assoc]
        _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 rest).1) ++ classOf p (run step (step s op).2 rest).2.items) := by
          rw [hIH]
        _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 rest).1)) ++ classOf p (run step (step s op).2 rest).2.items := by
          rw [← List.append_assoc]
        _ = classOf p (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1) ++ classOf p (run step (step s op).2 rest).2.items := by
          rw [← class_append]
        _ = classOf p (outflow (run step s (op :: rest)).1) ++ classOf p (run step s (op :: rest)).2.items := by
          rw [hT1, hT2, outflow_cons]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | insert e =>
    obtain ⟨hSort, hlt⟩ := hV
    have hsortB : isSorted s.items = true := isSorted_of_sorted s.items hSort
    have hdec : decide (s.items.length < s.capacity) = true := decide_eq_true hlt
    have hcond : (isSorted s.items && decide (s.items.length < s.capacity)) = true := by simp [hsortB, hdec]
    have hstep : step s (.insert e) = (Outcome.ok, { capacity := s.capacity, items := insertList e s.items }) := by simp [step, hcond]
    have h1 : (step s (.insert e)).1 = Outcome.ok := by rw [hstep]
    intro hcon
    rw [h1] at hcon
    exact (by simp : Outcome.ok ≠ Outcome.rejected) hcon
  | pop =>
    obtain ⟨hSort, hne⟩ := hV
    have hsortB : isSorted s.items = true := isSorted_of_sorted s.items hSort
    cases hitems : s.items with
    | nil => exact False.elim (hne hitems)
    | cons e rest =>
      have hsortB2 : isSorted (e :: rest) = true := by rw [← hitems]; exact hsortB
      have hstep : step s .pop = (Outcome.got e, { capacity := s.capacity, items := rest }) := by simp [step, hitems, hsortB2]
      have h1 : (step s .pop).1 = Outcome.got e := by rw [hstep]
      intro hcon
      rw [h1] at hcon
      exact (by simp : ∀ e : Entry, Outcome.got e ≠ Outcome.rejected) e hcon

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hNot
  obtain ⟨cap, its⟩ := s
  cases op with
  | insert e =>
    have hcond_false : (isSorted its && decide (its.length < cap)) = false := by
      cases hcond : (isSorted its && decide (its.length < cap)) with
      | true =>
        exfalso
        apply hNot
        rw [Bool.and_eq_true] at hcond
        obtain ⟨hs, hd⟩ := hcond
        exact ⟨sorted_of_isSorted its hs, of_decide_eq_true hd⟩
      | false => rfl
    simp [step, hcond_false]
  | pop =>
    cases hsort : isSorted its with
    | false => simp [step, hsort]
    | true =>
      cases hIts : its with
      | nil => simp [step, isSorted, hIts]
      | cons e rest =>
        have hSorted : Sorted its := sorted_of_isSorted its hsort
        exfalso
        apply hNot
        refine ⟨hSorted, ?_⟩
        rw [hIts]
        simp

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | insert e =>
    simp only [step]
    split
    · simp only
      rw [insertList_len]
      have hlt : s.items.length < s.capacity := by
        have h2 : decide (s.items.length < s.capacity) = true := by
          have hcond : (isSorted s.items && decide (s.items.length < s.capacity)) = true := by assumption
          rw [Bool.and_eq_true] at hcond
          exact hcond.2
        exact of_decide_eq_true h2
      omega
    · exact hle
  | pop =>
    simp only [step]
    split
    · split
      · exact hle
      · rename_i heq e rest heq2
        simp [heq2] at hle ⊢
        omega
    · exact hle

theorem req_pop_min : PopMin step := by
  intro s hne
  cases s with
  | mk cap its =>
    cases its with
    | nil =>
      have hr : (step ⟨cap, ([] : List Entry)⟩ Op.pop).1 = Outcome.rejected := by simp [step, isSorted]
      exact False.elim (hne hr)
    | cons e rest =>
      have hsort : isSorted (e :: rest) = true := by
        cases h : isSorted (e :: rest) with
        | false =>
          have hr : (step ⟨cap, e :: rest⟩ Op.pop).1 = Outcome.rejected := by simp [step, h]
          exact False.elim (hne hr)
        | true => rfl
      have hSorted : Sorted (e :: rest) := sorted_of_isSorted _ hsort
      have hstep : step ⟨cap, e :: rest⟩ Op.pop = (Outcome.got e, { capacity := cap, items := rest }) := by simp [step, hsort]
      have h1 : (step ⟨cap, e :: rest⟩ Op.pop).1 = Outcome.got e := by rw [hstep]
      have h2 : (step ⟨cap, e :: rest⟩ Op.pop).2.items = rest := by rw [hstep]
      refine ⟨e, h1, ?_⟩
      rw [h2]
      intro x hx
      exact (List.pairwise_cons.mp hSorted).1 x hx

theorem req_sorted : KeepsSorted step := by
  intro s op hSort
  cases op with
  | insert e =>
    by_cases hC : (isSorted s.items && decide (s.items.length < s.capacity)) = true
    · have hstep : step s (.insert e) = (Outcome.ok, { capacity := s.capacity, items := insertList e s.items }) := by simp [step, hC]
      have hitems : (step s (.insert e)).2.items = insertList e s.items := by rw [hstep]
      rw [hitems]
      exact insertList_sorted e s.items hSort
    · have hF : (isSorted s.items && decide (s.items.length < s.capacity)) = false := eq_false_of_ne_true hC
      have hstep : step s (.insert e) = (Outcome.rejected, s) := by simp [step, hF]
      have hitems : (step s (.insert e)).2.items = s.items := by rw [hstep]
      rw [hitems]
      exact hSort
  | pop =>
    have hB : isSorted s.items = true := isSorted_of_sorted s.items hSort
    cases hI : s.items with
    | nil =>
      have hstep : step s Op.pop = (Outcome.rejected, s) := by simp [step, hI]
      have hitems : (step s Op.pop).2.items = s.items := by rw [hstep]
      rw [hitems]
      exact hSort
    | cons e rest =>
      have hB2 : isSorted (e :: rest) = true := by rw [← hI]; exact hB
      have hstep : step s Op.pop = (Outcome.got e, { capacity := s.capacity, items := rest }) := by simp [step, hI, hB2]
      have hitems : (step s Op.pop).2.items = rest := by rw [hstep]
      rw [hitems]
      exact (List.pairwise_cons.mp (hI ▸ hSort)).2

theorem req_insert_effects : InsertEffects step := by
  intro s e hne
  have hc : (isSorted s.items && decide (s.items.length < s.capacity)) = true := by
    cases h : (isSorted s.items && decide (s.items.length < s.capacity)) with
    | true => rfl
    | false =>
      have hstep : (step s (.insert e)).1 = Outcome.rejected := by simp [step, h]
      exact absurd hstep hne
  have hsort : isSorted s.items = true := by
    rw [Bool.and_eq_true] at hc
    exact hc.1
  have hSorted : Sorted s.items := sorted_of_isSorted s.items hsort
  have hstepOk : step s (.insert e) = (Outcome.ok, { capacity := s.capacity, items := insertList e s.items }) := by simp [step, hc]
  obtain ⟨l₁, l₂, heq, hins, h1, h2⟩ := insertList_split_sorted e s.items hSorted
  have hout : (step s (.insert e)).1 = Outcome.ok := by rw [hstepOk]
  have hcap : (step s (.insert e)).2.capacity = s.capacity := by rw [hstepOk]
  have hitems : (step s (.insert e)).2.items = l₁ ++ e :: l₂ := by rw [hstepOk]; simp [hins]
  exact ⟨hout, hcap, l₁, l₂, heq, hitems, h1, h2⟩

theorem req_pop_effects : PopEffects step := by
  intro s hne
  cases s with
  | mk cap its =>
    cases its with
    | nil =>
      have hr : (step ⟨cap, ([] : List Entry)⟩ Op.pop).1 = Outcome.rejected := by simp [step, isSorted]
      exact False.elim (hne hr)
    | cons e rest =>
      have hsort : isSorted (e :: rest) = true := by
        cases h : isSorted (e :: rest) with
        | false =>
          have hr : (step ⟨cap, e :: rest⟩ Op.pop).1 = Outcome.rejected := by simp [step, h]
          exact False.elim (hne hr)
        | true => rfl
      have hSorted : Sorted (e :: rest) := sorted_of_isSorted _ hsort
      have hstep : step ⟨cap, e :: rest⟩ Op.pop = (Outcome.got e, { capacity := cap, items := rest }) := by simp [step, hsort]
      have hcap : (step ⟨cap, e :: rest⟩ Op.pop).2.capacity = cap := by rw [hstep]
      have hg : (step ⟨cap, e :: rest⟩ Op.pop).1 = Outcome.got e := by rw [hstep]
      have hi : (step ⟨cap, e :: rest⟩ Op.pop).2.items = rest := by rw [hstep]
      have hall : ∀ x ∈ rest, e.prio ≤ x.prio := (List.pairwise_cons.mp hSorted).1
      refine ⟨hcap, [], e, rest, rfl, hg, ?_, ?_, hall⟩
      · simpa using hi
      · intro x hx
        cases hx

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  exact fifo_trace s ops p

end PrioQueue
