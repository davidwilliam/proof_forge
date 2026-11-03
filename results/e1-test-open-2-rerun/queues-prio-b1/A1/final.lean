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

theorem ins_length (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    simp only [ins]
    split
    · simp
    · simp [ih]

theorem ins_mem_aux (e : Entry) (l : List Entry) (y : Entry) (hm : y ∈ ins e l) : y = e ∨ y ∈ l := by
  induction l generalizing y with
  | nil =>
    simp [ins] at hm
    exact Or.inl hm
  | cons x xs ih =>
    simp only [ins] at hm
    split at hm
    · simp at hm
      rcases hm with rfl | rfl | hm'
      · left; rfl
      · right; exact List.mem_cons.mpr (Or.inl rfl)
      · right; exact List.mem_cons.mpr (Or.inr hm')
    · simp at hm
      rcases hm with rfl | hm'
      · right; exact List.mem_cons.mpr (Or.inl rfl)
      · have h2 := ih _ hm'
        rcases h2 with rfl | h2
        · left; rfl
        · right; exact List.mem_cons.mpr (Or.inr h2)

theorem ins_sorted_aux2 (e : Entry) (l : List Entry) (hs : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil => simp [Sorted, ins]
  | cons x xs ih =>
    simp only [ins]
    split
    · rename_i hlt
      have hle : e.prio ≤ x.prio := Nat.le_of_lt hlt
      have hpair : ∀ y ∈ xs, x.prio ≤ y.prio := (List.pairwise_cons.mp hs).1
      apply List.pairwise_cons.mpr
      constructor
      · intro y hy
        simp at hy
        rcases hy with rfl | hy
        · exact hle
        · have hxle : x.prio ≤ y.prio := hpair y hy
          exact Nat.le_trans hle hxle
      · exact hs
    · rename_i hge
      have hge' : x.prio ≤ e.prio := Nat.le_of_not_lt hge
      have hpair : ∀ y ∈ xs, x.prio ≤ y.prio := (List.pairwise_cons.mp hs).1
      have hsorted_tail : Sorted xs := (List.pairwise_cons.mp hs).2
      have ih' : Sorted (ins e xs) := ih hsorted_tail
      apply List.pairwise_cons.mpr
      constructor
      · intro y hy
        have hy' := ins_mem_aux e xs y hy
        rcases hy' with rfl | hyin
        · exact hge'
        · exact hpair y hyin
      · exact ih'

private theorem ins_split3 (e : Entry) (l : List Entry) (hs : Sorted l) :
  ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧ (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil =>
    exact ⟨[], [], by simp, by simp [ins], by simp, by simp⟩
  | cons x xs ih =>
    simp only [ins]
    split
    · rename_i hlt
      have hle_xs : ∀ y ∈ xs, x.prio ≤ y.prio := (List.pairwise_cons.mp hs).1
      refine ⟨[], x :: xs, by simp, by simp, by simp, ?_⟩
      intro y hy
      simp at hy
      rcases hy with rfl | hy
      · exact hlt
      · have hxy : x.prio ≤ y.prio := hle_xs y hy
        omega
    · rename_i hge
      have hxle : x.prio ≤ e.prio := Nat.le_of_not_lt hge
      have hs_tail : Sorted xs := (List.pairwise_cons.mp hs).2
      obtain ⟨l₁, l₂, hl_eq, hins_eq, h1, h2⟩ := ih hs_tail
      refine ⟨x :: l₁, l₂, ?_, ?_, ?_, h2⟩
      · simp [hl_eq]
      · simp [hins_eq]
      · intro y hy
        simp at hy
        rcases hy with rfl | hy
        · exact hxle
        · exact h1 y hy

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  unfold step
  rw [if_pos h]
  cases op with
  | insert e =>
    simp
  | pop =>
    cases hs : s.items with
    | nil =>
      exfalso
      unfold Valid at h
      simp [hs] at h
    | cons hd tl =>
      simp [hs]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  unfold step
  rw [if_neg h]

theorem req_capacity : CapacityBound step := by
  intro s op h
  unfold step
  by_cases hv : Valid s op
  · rw [if_pos hv]
    cases op with
    | insert e =>
      have hlt : s.items.length < s.capacity := hv.2
      simp
      rw [ins_length]
      omega
    | pop =>
      cases hs : s.items with
      | nil =>
        exfalso
        unfold Valid at hv
        simp [hs] at hv
      | cons hd tl =>
        simp [hs]
        rw [hs] at h
        simp at h
        omega
  · rw [if_neg hv]
    exact h

theorem req_pop_min : PopMin step := by
  intro s h
  unfold step at h
  by_cases hv : Valid s .pop
  · rw [if_pos hv] at h
    have hsort : Sorted s.items := hv.1
    cases hs : s.items with
    | nil => simp [hs] at h
    | cons hd tl =>
      have h1 : (step s Op.pop).1 = Outcome.got hd := by unfold step; rw [if_pos hv, hs]
      have h2 : (step s Op.pop).2.items = tl := by unfold step; rw [if_pos hv, hs]
      refine ⟨hd, h1, ?_⟩
      intro x hx
      rw [h2] at hx
      rw [hs] at hsort
      exact (List.pairwise_cons.mp hsort).1 x hx
  · rw [if_neg hv] at h
    simp at h

theorem req_sorted : KeepsSorted step := by
  intro s op hsorted
  unfold step
  by_cases hv : Valid s op
  · rw [if_pos hv]
    cases op with
    | insert e =>
      simp
      exact ins_sorted_aux2 e s.items hsorted
    | pop =>
      cases hs : s.items with
      | nil =>
        simp
        exact hsorted
      | cons hd tl =>
        simp [hs]
        have hsorted' : Sorted (hd :: tl) := by rw [←hs]; exact hsorted
        exact (List.pairwise_cons.mp hsorted').2
  · rw [if_neg hv]
    exact hsorted

theorem req_insert_effects : InsertEffects step := by
  intro s e hne
  by_cases hv : Valid s (Op.insert e)
  · have hstep : step s (Op.insert e) = (Outcome.ok, { s with items := ins e s.items }) := by
      unfold step; simp [if_pos hv]
    have h_ok : (step s (Op.insert e)).1 = Outcome.ok := by rw [hstep]
    have h_cap : (step s (Op.insert e)).2.capacity = s.capacity := by rw [hstep]
    have h_items : (step s (Op.insert e)).2.items = ins e s.items := by rw [hstep]
    refine ⟨h_ok, h_cap, ?_⟩
    obtain ⟨l₁, l₂, heq1, heq2, hp1, hp2⟩ := ins_split3 e s.items hv.1
    exact ⟨l₁, l₂, heq1, by rw [h_items, heq2], hp1, hp2⟩
  · have heq : step s (Op.insert e) = (Outcome.rejected, s) := by
      unfold step; simp [if_neg hv]
    have h1 : (step s (Op.insert e)).1 = Outcome.rejected := by rw [heq]
    exact absurd h1 hne

theorem req_pop_effects : PopEffects step := by
  intro s hne
  have hv : Valid s .pop := by
    by_cases h : Valid s .pop
    · exact h
    · exfalso
      have heq : step s .pop = (.rejected, s) := by unfold step; rw [if_neg h]
      have : (step s .pop).1 = .rejected := by rw [heq]
      exact hne this
  have hSorted : Sorted s.items := hv.1
  have hNe : s.items ≠ [] := hv.2
  obtain ⟨hd, tl, hs_eq⟩ : ∃ hd tl, s.items = hd :: tl := by
    match h : s.items with
    | [] => exact absurd h hNe
    | hd :: tl => exact ⟨hd, tl, rfl⟩
  have hstep : step s .pop = (.got hd, { s with items := tl }) := by
    unfold step; rw [if_pos hv, hs_eq]
  have hcap : (step s .pop).2.capacity = s.capacity := by rw [hstep]
  refine ⟨hcap, ?_⟩
  refine ⟨[], hd, tl, hs_eq, ?_, ?_, ?_, ?_⟩
  · rw [hstep]
  · simp [hstep]
  · intro x hx; simp at hx
  · intro x hx
    have hpair : ∀ y ∈ tl, hd.prio ≤ y.prio := by
      have hsorted' : Sorted (hd :: tl) := by rw [←hs_eq]; exact hSorted
      exact (List.pairwise_cons.mp hsorted').1
    exact hpair x hx

-- helpers for FifoTies
private theorem classOf_nil_eq (p : Nat) : classOf p [] = [] := by
  unfold classOf; simp

private theorem filter_append_classOf (p : Nat) (l₁ l₂ : List Entry) :
    classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by
  unfold classOf
  simp [List.filter_append]

private theorem beq_true_imp_eq {a p : Nat} (h : (a == p) = true) : a = p := by
  by_cases heq : a = p
  · exact heq
  · have hfalse : (a == p) = false := by simp [heq]
    rw [hfalse] at h
    contradiction

private theorem classOf_empty_of_gt {p : Nat} {a : Entry} {xs : List Entry}
    (hs : Sorted (a :: xs)) (hlt : p < a.prio) : classOf p (a :: xs) = [] := by
  unfold classOf
  rw [List.filter_eq_nil_iff]
  intro y hy
  simp at hy
  rcases hy with rfl | hy2
  · simp; omega
  · have hle : a.prio ≤ y.prio := (List.pairwise_cons.mp hs).1 y hy2
    simp; omega

private theorem classOf_cons_prop (p : Nat) (a : Entry) (xs : List Entry) :
    classOf p (a :: xs) = if a.prio = p then a :: classOf p xs else classOf p xs := by
  unfold classOf
  by_cases hBool : a.prio == p
  · have heq : a.prio = p := beq_true_imp_eq hBool
    simp [heq, hBool]
  · have hne : a.prio ≠ p := by
      intro heq; rw [heq] at hBool; simp at hBool
    simp [hne, hBool]

private theorem classOf_ins_sorted (p : Nat) (e : Entry) (l : List Entry) (hs : Sorted l) :
    classOf p (ins e l) = classOf p l ++ if e.prio = p then [e] else [] := by
  induction l with
  | nil =>
    simp only [ins, classOf_nil_eq]
    unfold classOf
    simp
    by_cases h : e.prio = p <;> simp [h]
  | cons x xs ih =>
    have hs_tail : Sorted xs := (List.pairwise_cons.mp hs).2
    have ih' := ih hs_tail
    simp only [ins]
    by_cases hlt : e.prio < x.prio
    · simp [hlt]
      have hsorted : Sorted (x :: xs) := hs
      by_cases heq : e.prio = p
      · have hp_lt : p < x.prio := by omega
        have h_empty : classOf p (x :: xs) = [] := classOf_empty_of_gt hsorted hp_lt
        have h_lhs : classOf p (e :: x :: xs) = [e] := by
          rw [classOf_cons_prop p e (x :: xs)]
          simp [heq, h_empty]
        have hrhs : classOf p (x :: xs) ++ (if e.prio = p then [e] else ([] : List Entry)) = [e] := by
          simp [h_empty, heq]
        rw [h_lhs, hrhs]
      · have h_lhs : classOf p (e :: x :: xs) = classOf p (x :: xs) := by
          rw [classOf_cons_prop p e (x :: xs)]
          simp [heq]
        rw [h_lhs]
        have : (if e.prio = p then [e] else ([] : List Entry)) = [] := by simp [heq]
        rw [this, List.append_nil]
    · simp [hlt]
      rw [classOf_cons_prop p x (ins e xs), classOf_cons_prop p x xs, ih']
      by_cases hx : x.prio = p
      · simp [hx, List.append_assoc]
      · simp [hx]

private theorem classOf_inflow_ok (p : Nat) (e : Entry) :
    classOf p (inflowOf (Op.insert e, Outcome.ok)) = if e.prio = p then [e] else [] := by
  unfold inflowOf classOf
  simp
  by_cases h : e.prio = p <;> simp [h]

private theorem classOf_outflow_got (p : Nat) (hd : Entry) :
    classOf p (outflowOf (Op.pop, Outcome.got hd)) = if hd.prio = p then [hd] else [] := by
  unfold outflowOf classOf
  simp
  by_cases h : hd.prio = p <;> simp [h]

private theorem single_step_fifo (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
    classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  by_cases hv : Valid s op
  · cases op with
    | insert e =>
      have hstep : step s (Op.insert e) = (Outcome.ok, { s with items := ins e s.items }) := by
        unfold step; simp [if_pos hv]
      have h_ins : classOf p (ins e s.items) = classOf p s.items ++ if e.prio = p then [e] else [] :=
        classOf_ins_sorted p e s.items hv.1
      have h_inflow : classOf p (inflowOf (Op.insert e, Outcome.ok)) = if e.prio = p then [e] else [] :=
        classOf_inflow_ok p e
      have h_outflow : classOf p (outflowOf (Op.insert e, Outcome.ok)) = [] := by
        simp [outflowOf, classOf_nil_eq]
      have h1 : (step s (Op.insert e)).1 = Outcome.ok := by rw [hstep]
      have h2 : (step s (Op.insert e)).2.items = ins e s.items := by rw [hstep]
      rw [h1, h2, h_inflow, h_outflow]
      calc classOf p s.items ++ (if e.prio = p then [e] else [])
          = classOf p (ins e s.items) := by rw [h_ins]
        _ = [] ++ classOf p (ins e s.items) := by rw [List.nil_append]
        _ = classOf p (outflowOf (Op.insert e, Outcome.ok)) ++ classOf p (ins e s.items) := by rw [h_outflow]
    | pop =>
      have hs_ne : s.items ≠ [] := hv.2
      obtain ⟨hd, tl, hs_eq⟩ : ∃ hd tl, s.items = hd :: tl := by
        match h : s.items with
        | [] => exact absurd h hs_ne
        | hd :: tl => exact ⟨hd, tl, rfl⟩
      have hstep : step s Op.pop = (Outcome.got hd, { s with items := tl }) := by
        unfold step; rw [if_pos hv, hs_eq]
      have h_inflow : classOf p (inflowOf (Op.pop, Outcome.got hd)) = [] := by
        simp [inflowOf, classOf_nil_eq]
      have h1 : (step s Op.pop).1 = Outcome.got hd := by rw [hstep]
      have h2 : (step s Op.pop).2.items = tl := by rw [hstep]
      rw [hs_eq, h1, h2, h_inflow]
      simp only [List.append_nil]
      have h2b : classOf p (outflowOf (Op.pop, Outcome.got hd)) ++ classOf p tl = (if hd.prio = p then [hd] else []) ++ classOf p tl := by
        rw [classOf_outflow_got]
      rw [h2b]
      have h_class : classOf p (hd :: tl) = (if hd.prio = p then [hd] else []) ++ classOf p tl := by
        rw [classOf_cons_prop p hd tl]
        by_cases h : hd.prio = p <;> simp [h]
      exact h_class
  · have hstep : step s op = (Outcome.rejected, s) := by
      unfold step; simp [if_neg hv]
    have h1 : (step s op).1 = Outcome.rejected := by rw [hstep]
    have h2 : (step s op).2.items = s.items := by rw [hstep]
    rw [h1, h2]
    have h_inflow : classOf p (inflowOf (op, Outcome.rejected)) = [] := by
      cases op with
      | insert e => simp [inflowOf, classOf_nil_eq]
      | pop => simp [inflowOf, classOf_nil_eq]
    have h_outflow : classOf p (outflowOf (op, Outcome.rejected)) = [] := by
      cases op with
      | insert e => simp [outflowOf, classOf_nil_eq]
      | pop => simp [outflowOf, classOf_nil_eq]
    rw [h_inflow, h_outflow]
    simp

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow, classOf, List.filter_append]
  | cons op rest ih =>
    have h_single := single_step_fifo s op p
    have h_run : run step s (op :: rest) =
        ((op, (step s op).1) :: (run step (step s op).2 rest).1, (run step (step s op).2 rest).2) := by
      simp [run]
    have h_inflow_cons : inflow ((op, (step s op).1) :: (run step (step s op).2 rest).1) =
        inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1 := by
      simp [inflow]
    have h_outflow_cons : outflow ((op, (step s op).1) :: (run step (step s op).2 rest).1) =
        outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1 := by
      simp [outflow]
    have ih' := ih (step s op).2
    have h_final : (run step s (op :: rest)).2 = (run step (step s op).2 rest).2 := by
      rw [h_run]
    have h_inf : inflow (run step s (op :: rest)).1 = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1 := by
      rw [h_run]; exact h_inflow_cons
    have h_outf : outflow (run step s (op :: rest)).1 = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1 := by
      rw [h_run]; exact h_outflow_cons
    rw [h_inf, h_outf, h_final]
    rw [filter_append_classOf, filter_append_classOf]
    calc classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 rest).1))
        = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 rest).1) := by
          simp only [List.append_assoc]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 rest).1) := by
          rw [h_single]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 rest).1)) := by
          simp only [List.append_assoc]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 rest).1) ++ classOf p (run step (step s op).2 rest).2.items) := by
          rw [ih']
      _ = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 rest).1) ++ classOf p (run step (step s op).2 rest).2.items := by
          simp only [List.append_assoc]

end PrioQueue
