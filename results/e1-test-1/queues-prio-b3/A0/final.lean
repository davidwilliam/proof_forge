import PrioQueue.Spec
namespace PrioQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid Sorted <;> infer_instance

def ins (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs => if e.prio < x.prio then e :: x :: xs else x :: ins e xs

theorem ins_def_cons (e x : Entry) (xs : List Entry) :
    ins e (x :: xs) = (if e.prio < x.prio then e :: x :: xs else x :: ins e xs) := rfl

theorem ins_nil_eq (e : Entry) : ins e [] = [e] := rfl

theorem ins_pos_eq (e x : Entry) (xs : List Entry) (h : e.prio < x.prio) :
    ins e (x :: xs) = e :: x :: xs := by
  rw [ins_def_cons, if_pos h]

theorem ins_neg_eq (e x : Entry) (xs : List Entry) (h : ¬ e.prio < x.prio) :
    ins e (x :: xs) = x :: ins e xs := by
  rw [ins_def_cons, if_neg h]

def step : Impl := fun s op =>
  if Valid s op then
    match op, s.items with
    | .insert e, _ => (.ok, { s with items := ins e s.items })
    | .pop, x :: xs => (.got x, { s with items := xs })
    | .pop, [] => (.rejected, s)
  else (.rejected, s)

/-! Helpers -/

theorem beq_true_eq {a b : Nat} (h : a = b) : (a == b) = true := by
  simp [h]

theorem beq_false_ne {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases hb : (a == b) with
  | true =>
    have heq : a = b := LawfulBEq.eq_of_beq hb
    exact absurd heq h
  | false => rfl

theorem ins_length (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hc : e.prio < x.prio
    · simp [ins_pos_eq e x xs hc]
    · simp [ins_neg_eq e x xs hc, ih]

theorem mem_ins' {e y : Entry} {l : List Entry} (h : y ∈ ins e l) : y = e ∨ y ∈ l := by
  induction l with
  | nil =>
    rw [ins_nil_eq] at h
    have hh := List.mem_cons.mp h
    rcases hh with rfl | hm
    · exact Or.inl rfl
    · simp at hm
  | cons x xs ih =>
    by_cases hc : e.prio < x.prio
    · rw [ins_pos_eq e x xs hc] at h
      have h1 := List.mem_cons.mp h
      rcases h1 with rfl | h2
      · exact Or.inl rfl
      · exact Or.inr h2
    · rw [ins_neg_eq e x xs hc] at h
      have h1 := List.mem_cons.mp h
      rcases h1 with rfl | hm
      · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
      · have hh := ih hm
        rcases hh with rfl | hm2
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons.mpr (Or.inr hm2))

theorem sorted_tail {x : Entry} {xs : List Entry} (h : Sorted (x :: xs)) : Sorted xs := by
  unfold Sorted at h ⊢
  cases h with
  | cons _ h2 => exact h2

theorem sorted_head {x : Entry} {xs : List Entry} (h : Sorted (x :: xs)) : ∀ y ∈ xs, x.prio ≤ y.prio := by
  unfold Sorted at h
  cases h with
  | cons h1 _ => exact h1

theorem ins_sorted (e : Entry) (l : List Entry) (h : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil =>
    show Sorted [e]
    apply List.Pairwise.cons
    · intro y hy
      simp at hy
    · exact List.Pairwise.nil
  | cons x xs ih =>
    have htail : Sorted xs := sorted_tail h
    have hhead : ∀ y ∈ xs, x.prio ≤ y.prio := sorted_head h
    have ih' := ih htail
    by_cases hc : e.prio < x.prio
    · rw [ins_pos_eq e x xs hc]
      apply List.Pairwise.cons
      · intro y hy
        have hy' := List.mem_cons.mp hy
        rcases hy' with rfl | hy2
        · exact Nat.le_of_lt hc
        · have hx := hhead y hy2
          omega
      · exact h
    · have hle : x.prio ≤ e.prio := Nat.le_of_not_gt hc
      rw [ins_neg_eq e x xs hc]
      apply List.Pairwise.cons
      · intro y hy
        have hmem := mem_ins' hy
        rcases hmem with rfl | hm
        · exact hle
        · exact hhead y hm
      · exact ih'

theorem ins_split (e : Entry) (l : List Entry) (h : Sorted l) :
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
    have htail : Sorted xs := sorted_tail h
    have hhead : ∀ y ∈ xs, x.prio ≤ y.prio := sorted_head h
    by_cases hc : e.prio < x.prio
    · refine ⟨[], x :: xs, rfl, ?_, ?_, ?_⟩
      · exact ins_pos_eq e x xs hc
      · intro x hx
        simp at hx
      · intro y hy
        have hy' := List.mem_cons.mp hy
        rcases hy' with rfl | hm
        · exact hc
        · have hx : x.prio ≤ y.prio := hhead y hm
          omega
    · have hle : x.prio ≤ e.prio := Nat.le_of_not_gt hc
      obtain ⟨l₁, l₂, heq, hins, h1, h2⟩ := ih htail
      refine ⟨x :: l₁, l₂, ?_, ?_, ?_, h2⟩
      · exact congrArg (x :: ·) heq
      · rw [ins_neg_eq e x xs hc]
        exact congrArg (x :: ·) hins
      · intro y hy
        have hy' := List.mem_cons.mp hy
        rcases hy' with rfl | hm
        · exact hle
        · exact h1 y hm

theorem classOf_cons_eq (p : Nat) (x : Entry) (xs : List Entry) :
    classOf p (x :: xs) = classOf p [x] ++ classOf p xs := by
  have h : (x :: xs) = [x] ++ xs := rfl
  unfold classOf
  rw [h, List.filter_append]

theorem classOf_empty (p : Nat) : classOf p [] = [] := rfl

theorem classOf_single_true {p : Nat} {e : Entry} (h : e.prio = p) : classOf p [e] = [e] := by
  unfold classOf
  simp [beq_true_eq h]

theorem classOf_single_false {p : Nat} {e : Entry} (h : e.prio ≠ p) : classOf p [e] = [] := by
  unfold classOf
  simp [beq_false_ne h]

theorem classOf_nil_of_forall_ne {p : Nat} {l : List Entry}
    (h : ∀ y ∈ l, y.prio ≠ p) : classOf p l = [] := by
  unfold classOf
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.prio ≠ p := h x (List.mem_cons.mpr (Or.inl rfl))
    have hxF : (x.prio == p) = false := beq_false_ne hx
    have ih' : List.filter (fun x => x.prio == p) xs = [] :=
      ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))
    simp [hxF, ih']

theorem ins_filter (e : Entry) (l : List Entry) (h : Sorted l) (p : Nat) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := by
  induction l with
  | nil =>
    rw [ins_nil_eq]
    unfold classOf
    simp
  | cons x xs ih =>
    have htail : Sorted xs := sorted_tail h
    have hhead : ∀ y ∈ xs, x.prio ≤ y.prio := sorted_head h
    have ih' := ih htail
    by_cases hc : e.prio < x.prio
    · rw [ins_pos_eq e x xs hc]
      rw [classOf_cons_eq p e (x :: xs)]
      by_cases he : e.prio = p
      · have hxp : x.prio ≠ p := by omega
        have hxs : ∀ y ∈ xs, y.prio ≠ p := by
          intro y hy
          have hle := hhead y hy
          omega
        have e1 : classOf p [e] = [e] := classOf_single_true he
        have e2 : classOf p [x] = [] := classOf_single_false hxp
        have e3 : classOf p xs = [] := classOf_nil_of_forall_ne hxs
        rw [e1]
        rw [classOf_cons_eq p x xs, e2, e3]
        simp
      · have e1 : classOf p [e] = [] := classOf_single_false he
        rw [e1]
        rw [classOf_cons_eq p x xs]
        simp
    · rw [ins_neg_eq e x xs hc]
      rw [classOf_cons_eq p x (ins e xs), classOf_cons_eq p x xs, ih',
        List.append_assoc]

theorem step_if_neg {s : State} {op : Op} (h : ¬ Valid s op) : step s op = (.rejected, s) := by
  unfold step
  rw [if_neg h]

theorem inflow_rejected (op : Op) : inflowOf (op, .rejected) = [] := by
  cases op with
  | insert e => rfl
  | pop => rfl

theorem outflow_rejected (op : Op) : outflowOf (op, .rejected) = [] := by
  cases op with
  | insert e => rfl
  | pop => rfl

theorem pop_ne_nil_of_valid {s : State} (hV : Valid s .pop) : s.items ≠ [] := by
  unfold Valid at hV
  exact hV.2

theorem step_ins_fst (s : State) (e : Entry) (hV : Valid s (.insert e)) :
    (step s (.insert e)).1 = Outcome.ok := by
  unfold step
  rw [if_pos hV]

theorem step_ins_items (s : State) (e : Entry) (hV : Valid s (.insert e)) :
    (step s (.insert e)).2.items = ins e s.items := by
  unfold step
  rw [if_pos hV]

theorem step_ins_cap (s : State) (e : Entry) (hV : Valid s (.insert e)) :
    (step s (.insert e)).2.capacity = s.capacity := by
  unfold step
  rw [if_pos hV]

theorem step_pop_fst (s : State) (x : Entry) (xs : List Entry)
    (hV : Valid s .pop) (hi : s.items = x :: xs) :
    (step s .pop).1 = Outcome.got x := by
  unfold step
  rw [if_pos hV, hi]

theorem step_pop_items (s : State) (x : Entry) (xs : List Entry)
    (hV : Valid s .pop) (hi : s.items = x :: xs) :
    (step s .pop).2.items = xs := by
  unfold step
  rw [if_pos hV, hi]

theorem step_pop_cap (s : State) (x : Entry) (xs : List Entry)
    (hV : Valid s .pop) (hi : s.items = x :: xs) :
    (step s .pop).2.capacity = s.capacity := by
  unfold step
  rw [if_pos hV, hi]

theorem single_step (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
      = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have hS : Sorted s.items := by unfold Valid at hV; exact hV.1
      have hstep1 := step_ins_fst s e hV
      have hstep2 := step_ins_items s e hV
      have hf : classOf p (ins e s.items) = classOf p s.items ++ classOf p [e] :=
        ins_filter e s.items hS p
      have hin : inflowOf (Op.insert e, Outcome.ok) = [e] := rfl
      have hout : outflowOf (Op.insert e, Outcome.ok) = ([] : List Entry) := rfl
      rw [hstep1, hstep2, hin, hout, classOf_empty p, hf, List.nil_append]
    | pop =>
      cases hitems : s.items with
      | nil =>
        exfalso
        exact absurd hitems (pop_ne_nil_of_valid hV)
      | cons x xs =>
        have hstep1 := step_pop_fst s x xs hV hitems
        have hstep2 := step_pop_items s x xs hV hitems
        have hin0 : inflowOf (Op.pop, Outcome.got x) = ([] : List Entry) := rfl
        have hout0 : outflowOf (Op.pop, Outcome.got x) = [x] := rfl
        rw [hstep1, hstep2, hin0, hout0, classOf_cons_eq p x xs, classOf_empty p,
          List.append_nil]
  · have hs := step_if_neg hV
    have h1 : (step s op).1 = .rejected := by rw [hs]
    have h2 : (step s op).2 = s := by rw [hs]
    rw [h1, h2, inflow_rejected, outflow_rejected, classOf_empty p, List.append_nil,
      List.nil_append]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | insert e =>
    have h1 := step_ins_fst s e hV
    rw [h1]
    simp
  | pop =>
    cases hitems : s.items with
    | nil =>
      exfalso
      exact absurd hitems (pop_ne_nil_of_valid hV)
    | cons x xs =>
      have h1 := step_pop_fst s x xs hV hitems
      rw [h1]
      simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hN
  exact step_if_neg hN

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | insert e =>
    by_cases hV : Valid s (.insert e)
    · have hstep := step_ins_items s e hV
      have hcap := step_ins_cap s e hV
      rw [hstep, hcap, ins_length]
      unfold Valid at hV
      omega
    · have hs := step_if_neg hV
      rw [hs]
      exact hle
  | pop =>
    by_cases hV : Valid s .pop
    · cases hitems : s.items with
      | nil =>
        exfalso
        exact absurd hitems (pop_ne_nil_of_valid hV)
      | cons x xs =>
        have hstep2 := step_pop_items s x xs hV hitems
        have hcap := step_pop_cap s x xs hV hitems
        rw [hstep2, hcap]
        have hlen : (x :: xs).length ≤ s.capacity := hitems ▸ hle
        simp only [List.length_cons] at hlen ⊢
        omega
    · have hs := step_if_neg hV
      rw [hs]
      exact hle

theorem req_pop_min : PopMin step := by
  intro s hne
  by_cases hV : Valid s .pop
  · cases hitems : s.items with
    | nil =>
      exfalso
      exact absurd hitems (pop_ne_nil_of_valid hV)
    | cons x xs =>
      have hstep1 := step_pop_fst s x xs hV hitems
      have hstep2 := step_pop_items s x xs hV hitems
      refine ⟨x, hstep1, ?_⟩
      rw [hstep2]
      intro y hy
      have hS : Sorted s.items := by unfold Valid at hV; exact hV.1
      rw [hitems] at hS
      have hh := sorted_head hS
      exact hh y hy
  · have hs := step_if_neg hV
    have h1 : (step s .pop).1 = .rejected := by rw [hs]
    exact absurd h1 hne

theorem req_sorted : KeepsSorted step := by
  intro s op hS
  cases op with
  | insert e =>
    by_cases hV : Valid s (.insert e)
    · have hstep := step_ins_items s e hV
      rw [hstep]
      exact ins_sorted e s.items hS
    · have hs := step_if_neg hV
      rw [hs]
      exact hS
  | pop =>
    by_cases hV : Valid s .pop
    · cases hitems : s.items with
      | nil =>
        exfalso
        exact absurd hitems (pop_ne_nil_of_valid hV)
      | cons x xs =>
        have hstep := step_pop_items s x xs hV hitems
        rw [hstep]
        have hS' : Sorted s.items := hS
        rw [hitems] at hS'
        exact sorted_tail hS'
    · have hs := step_if_neg hV
      rw [hs]
      exact hS

theorem req_insert_effects : InsertEffects step := by
  intro s e hne
  by_cases hV : Valid s (.insert e)
  · have hS : Sorted s.items := by unfold Valid at hV; exact hV.1
    obtain ⟨l₁, l₂, heq, hins, h1, h2⟩ := ins_split e s.items hS
    have h1ok := step_ins_fst s e hV
    have h2cap := step_ins_cap s e hV
    have h3items : (step s (.insert e)).2.items = l₁ ++ e :: l₂ := by
      have hstep := step_ins_items s e hV
      rw [hstep, ← hins, heq]
    exact ⟨h1ok, h2cap, l₁, l₂, heq, h3items, h1, h2⟩
  · have hs := step_if_neg hV
    have h1 : (step s (.insert e)).1 = .rejected := by rw [hs]
    exact absurd h1 hne

theorem req_pop_effects : PopEffects step := by
  intro s hne
  by_cases hV : Valid s .pop
  · cases hitems : s.items with
    | nil =>
      exfalso
      exact absurd hitems (pop_ne_nil_of_valid hV)
    | cons x xs =>
      have hcap := step_pop_cap s x xs hV hitems
      have h1 := step_pop_fst s x xs hV hitems
      have h2 := step_pop_items s x xs hV hitems
      have hS : Sorted s.items := by unfold Valid at hV; exact hV.1
      rw [hitems] at hS
      have hhead : ∀ y ∈ xs, x.prio ≤ y.prio := sorted_head hS
      refine ⟨hcap, [], x, xs, rfl, h1, h2, ?_, ?_⟩
      · intro y hy
        simp at hy
      · intro y hy
        exact hhead y hy
  · have hs := step_if_neg hV
    have h1 : (step s .pop).1 = .rejected := by rw [hs]
    exact absurd h1 hne

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  induction ops generalizing s with
  | nil =>
    have h0 : run step s [] = ([], s) := rfl
    simp [h0, inflow, outflow, classOf_empty]
  | cons op ops ih =>
    have hsingle := single_step s op p
    have hih := ih (step s op).2
    have hrun : run step s (op :: ops) = ((op, (step s op).1) :: (run step (step s op).2 ops).1, (run step (step s op).2 ops).2) := rfl
    rw [hrun]
    simp only
    have inflow_cons : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := rfl
    have outflow_cons : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := rfl
    rw [inflow_cons, outflow_cons]
    have cf_in : classOf p (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1) := by
      unfold classOf
      rw [List.filter_append]
    have cf_out : classOf p (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1)
        = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1) := by
      unfold classOf
      rw [List.filter_append]
    rw [cf_in, cf_out]
    calc classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1))
        _ = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops).1) := by
          rw [← List.append_assoc]
        _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops).1) := by
          rw [hsingle]
        _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops).1)) := by
          rw [List.append_assoc]
        _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops).1) ++ classOf p (run step (step s op).2 ops).2.items) := by
          rw [hih]
        _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1)) ++ classOf p (run step (step s op).2 ops).2.items := by
          rw [← List.append_assoc]

end PrioQueue
