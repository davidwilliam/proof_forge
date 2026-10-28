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

/- BEq helpers -/
theorem ne_beq_false {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases hb : (a == b) with
  | true => exact absurd (LawfulBEq.eq_of_beq hb) h
  | false => rfl

theorem beq_true_eq {a b : Nat} (h : (a == b) = true) : a = b :=
  LawfulBEq.eq_of_beq h

/- Sorted helpers -/
theorem sorted_tail {x : Entry} {xs : List Entry} (h : Sorted (x :: xs)) : Sorted xs := by
  cases h with
  | cons _ ht => exact ht

theorem sorted_head {x : Entry} {xs : List Entry} (h : Sorted (x :: xs)) :
    ∀ y ∈ xs, x.prio ≤ y.prio := by
  cases h with
  | cons h1 _ => exact h1

theorem sorted_singleton (e : Entry) : Sorted [e] := by
  apply List.Pairwise.cons
  · intro y hy
    cases hy
  · exact List.Pairwise.nil

theorem cons_of_ne {l : List Entry} (h : l ≠ []) : ∃ x xs, l = x :: xs := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => exact ⟨x, xs, rfl⟩

/- ins equation -/
theorem ins_cons_eq (e x : Entry) (xs : List Entry) :
    ins e (x :: xs) = (if e.prio < x.prio then e :: x :: xs else x :: ins e xs) := rfl

theorem mem_ins (e y : Entry) (l : List Entry) : y ∈ ins e l → y = e ∨ y ∈ l := by
  induction l with
  | nil =>
    intro h
    have heq : ins e ([] : List Entry) = [e] := rfl
    rw [heq] at h
    rw [List.mem_singleton] at h
    exact Or.inl h
  | cons x xs ih =>
    intro h
    have heq : ins e (x :: xs) =
      (if e.prio < x.prio then e :: x :: xs else x :: ins e xs) := rfl
    rw [heq] at h
    by_cases hc : e.prio < x.prio
    · rw [if_pos hc] at h
      rw [List.mem_cons] at h
      cases h with
      | inl he => exact Or.inl he
      | inr hr =>
        rw [List.mem_cons] at hr
        cases hr with
        | inl he => exact Or.inr (List.mem_cons.mpr (Or.inl he))
        | inr hm => exact Or.inr (List.mem_cons.mpr (Or.inr hm))
    · rw [if_neg hc] at h
      rw [List.mem_cons] at h
      cases h with
      | inl he => exact Or.inr (List.mem_cons.mpr (Or.inl he))
      | inr hr =>
        cases ih hr with
        | inl he => exact Or.inl he
        | inr hm => exact Or.inr (List.mem_cons.mpr (Or.inr hm))

theorem ins_length (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hc : e.prio < x.prio
    · simp [ins_cons_eq, if_pos hc]
    · rw [ins_cons_eq, if_neg hc]
      simp [ih]

theorem ins_sorted (e : Entry) (l : List Entry) (h : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil =>
    have h0 : ins e [] = [e] := rfl
    rw [h0]
    exact sorted_singleton e
  | cons x xs ih =>
    have hhead : ∀ y ∈ xs, x.prio ≤ y.prio := sorted_head h
    have htail : Sorted xs := sorted_tail h
    have ihs := ih htail
    rw [ins_cons_eq]
    by_cases hc : e.prio < x.prio
    · rw [if_pos hc]
      apply List.Pairwise.cons
      · intro y hy
        cases List.mem_cons.mp hy with
        | inl he =>
          rw [he]
          exact Nat.le_of_lt hc
        | inr hmem =>
          exact Nat.le_trans (Nat.le_of_lt hc) (hhead y hmem)
      · exact h
    · rw [if_neg hc]
      have hxle : x.prio ≤ e.prio := by omega
      apply List.Pairwise.cons
      · intro y hy
        cases mem_ins e y xs hy with
        | inl he =>
          rw [he]
          exact hxle
        | inr hmem => exact hhead y hmem
      · exact ihs

theorem ins_split_sorted (e : Entry) (l : List Entry) (h : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil =>
    refine ⟨[], [], rfl, rfl, ?_, ?_⟩
    · intro y hy
      cases hy
    · intro y hy
      cases hy
  | cons x xs ih =>
    have hhead : ∀ y ∈ xs, x.prio ≤ y.prio := sorted_head h
    have htail : Sorted xs := sorted_tail h
    obtain ⟨l₁', l₂', hx, hins, h1, h2⟩ := ih htail
    by_cases hc : e.prio < x.prio
    · have hins_eq : ins e (x :: xs) = e :: x :: xs := by
        rw [ins_cons_eq, if_pos hc]
      refine ⟨[], x :: xs, rfl, ?_, ?_, ?_⟩
      · simp only [List.nil_append]
        exact hins_eq
      · intro y hy
        cases hy
      · intro y hy
        rw [List.mem_cons] at hy
        cases hy with
        | inl he =>
          rw [he]
          exact hc
        | inr hmem =>
          exact Nat.lt_of_lt_of_le hc (hhead y hmem)
    · have hxle : x.prio ≤ e.prio := by omega
      have hstep : ins e (x :: xs) = x :: ins e xs := by
        rw [ins_cons_eq, if_neg hc]
      have hfirst : x :: xs = (x :: l₁') ++ l₂' := by
        simp only [List.cons_append, hx]
      have hsecond : ins e (x :: xs) = (x :: l₁') ++ e :: l₂' := by
        simp only [List.cons_append, hstep, hins]
      refine ⟨x :: l₁', l₂', hfirst, hsecond, ?_, h2⟩
      · intro y hy
        rw [List.mem_cons] at hy
        cases hy with
        | inl he =>
          rw [he]
          exact hxle
        | inr hmem => exact h1 y hmem

/- classOf lemmas -/
theorem classOf_nil_eq (p : Nat) : classOf p [] = [] := rfl

theorem classOf_append (p : Nat) (l₁ l₂ : List Entry) :
    classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by
  unfold classOf
  simp

theorem classOf_cons_split (p : Nat) (x : Entry) (xs : List Entry) :
    classOf p (x :: xs) = classOf p [x] ++ classOf p xs := by
  have h1 : (x :: xs) = ([x] ++ xs) := rfl
  rw [h1]
  exact classOf_append p [x] xs

theorem classOf_empty_of_ne (p : Nat) (l : List Entry) (h : ∀ y ∈ l, y.prio ≠ p) :
    classOf p l = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.prio ≠ p := h x (by simp)
    have hxs : ∀ y ∈ xs, y.prio ≠ p := by
      intro y hy
      apply h
      simp [hy]
    have ih' := ih hxs
    have hb : (x.prio == p) = false := ne_beq_false hx
    unfold classOf at *
    simp [hb, ih']

theorem classOf_singleton_eq (p : Nat) (e : Entry) (he : (e.prio == p) = true) :
    classOf p [e] = [e] := by
  unfold classOf
  simp [he]

theorem classOf_singleton_ne (p : Nat) (e : Entry) (he : (e.prio == p) = false) :
    classOf p [e] = [] := by
  unfold classOf
  simp [he]

theorem classOf_ins_sorted (p : Nat) (e : Entry) (l : List Entry) (h : Sorted l) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := by
  obtain ⟨l₁, l₂, hl, hins, h1, h2⟩ := ins_split_sorted e l h
  subst hl
  rw [hins]
  have lhs : classOf p (l₁ ++ e :: l₂) = classOf p l₁ ++ (classOf p [e] ++ classOf p l₂) := by
    have e1 : (l₁ ++ e :: l₂) = l₁ ++ ([e] ++ l₂) := rfl
    rw [e1, classOf_append, classOf_append]
  have rhs : classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ :=
    classOf_append p l₁ l₂
  rw [lhs, rhs]
  cases hb : (e.prio == p) with
  | true =>
    have hne2 : ∀ y ∈ l₂, y.prio ≠ p := by
      intro y hy
      have hlt := h2 y hy
      have heq : e.prio = p := beq_true_eq hb
      omega
    have hnil2 := classOf_empty_of_ne p l₂ hne2
    have hsing := classOf_singleton_eq p e hb
    rw [hnil2, hsing]
    simp
  | false =>
    have hsing := classOf_singleton_ne p e hb
    rw [hsing]
    simp

/- step equations -/
theorem step_invalid_eq (s : State) (op : Op) (h : ¬ Valid s op) :
    step s op = (.rejected, s) := by
  unfold step
  rw [if_neg h]

theorem step_insert_valid_eq (s : State) (e : Entry) (h : Valid s (.insert e)) :
    step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
  unfold step
  rw [if_pos h]

theorem step_pop_valid_eq (s : State) (x : Entry) (xs : List Entry)
    (hs : s.items = x :: xs) (h : Valid s .pop) :
    step s .pop = (.got x, { s with items := xs }) := by
  unfold step
  rw [if_pos h]
  simp [hs]

theorem step_success_valid (s : State) (op : Op) (h : (step s op).1 ≠ .rejected) :
    Valid s op := by
  by_cases hv : Valid s op
  · exact hv
  · have heq := step_invalid_eq s op hv
    have hcon : (step s op).1 = .rejected := congrArg Prod.fst heq
    exact absurd hcon h

theorem inflow_cons (a : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (a :: t) = inflowOf a ++ inflow t := rfl

theorem outflow_cons (a : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (a :: t) = outflowOf a ++ outflow t := rfl

/- single-step FIFO conservation -/
theorem single_step_fifo (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
      = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  cases op with
  | insert e =>
    by_cases hv : Valid s (.insert e)
    · have heq := step_insert_valid_eq s e hv
      have hsort : Sorted s.items := by unfold Valid at hv; exact hv.1
      have hins := classOf_ins_sorted p e s.items hsort
      have h1 : (step s (.insert e)).1 = .ok := by rw [heq]
      have h2i : (step s (.insert e)).2.items = ins e s.items := by rw [heq]
      have hi : inflowOf (.insert e, (step s (.insert e)).1) = [e] := by
        rw [h1]; rfl
      have ho : outflowOf (.insert e, (step s (.insert e)).1) = ([] : List Entry) := by
        rw [h1]; rfl
      rw [hi, ho, h2i]
      simp only [classOf_nil_eq, List.nil_append]
      exact hins.symm
    · have heq := step_invalid_eq s (.insert e) hv
      have h1 : (step s (.insert e)).1 = .rejected := by rw [heq]
      have h2 : (step s (.insert e)).2 = s := by rw [heq]
      have hi : inflowOf (.insert e, (step s (.insert e)).1) = ([] : List Entry) := by
        rw [h1]; rfl
      have ho : outflowOf (.insert e, (step s (.insert e)).1) = ([] : List Entry) := by
        rw [h1]; rfl
      have h2i : (step s (.insert e)).2.items = s.items := by rw [h2]
      rw [hi, ho, h2i]
      simp only [classOf_nil_eq, List.append_nil, List.nil_append]
  | pop =>
    by_cases hv : Valid s .pop
    · have hne : s.items ≠ [] := by unfold Valid at hv; exact hv.2
      obtain ⟨x, xs, hs⟩ := cons_of_ne (l := s.items) hne
      have heq := step_pop_valid_eq s x xs hs hv
      have h1 : (step s .pop).1 = .got x := by rw [heq]
      have h2i : (step s .pop).2.items = xs := by rw [heq]
      have hi : inflowOf (Op.pop, (step s .pop).1) = ([] : List Entry) := by
        rw [h1]; rfl
      have ho : outflowOf (Op.pop, (step s .pop).1) = [x] := by
        rw [h1]; rfl
      rw [hi, ho, h2i, hs]
      simp only [classOf_nil_eq, List.append_nil]
      exact classOf_cons_split p x xs
    · have heq := step_invalid_eq s .pop hv
      have h1 : (step s .pop).1 = .rejected := by rw [heq]
      have h2 : (step s .pop).2 = s := by rw [heq]
      have hi : inflowOf (Op.pop, (step s .pop).1) = ([] : List Entry) := by
        rw [h1]; rfl
      have ho : outflowOf (Op.pop, (step s .pop).1) = ([] : List Entry) := by
        rw [h1]; rfl
      have h2i : (step s .pop).2.items = s.items := by rw [h2]
      rw [hi, ho, h2i]
      simp only [classOf_nil_eq, List.append_nil, List.nil_append]

/- 8 required theorems -/
theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hv
  unfold step
  rw [if_pos hv]
  cases op with
  | insert e => simp
  | pop =>
    have hne : s.items ≠ [] := by unfold Valid at hv; exact hv.2
    obtain ⟨x, xs, hs⟩ := cons_of_ne (l := s.items) hne
    rw [hs]
    simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hn
  exact step_invalid_eq s op hn

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | insert e =>
    by_cases hv : Valid s (.insert e)
    · have heq := step_insert_valid_eq s e hv
      have hlen := ins_length e s.items
      have hlt : s.items.length < s.capacity := by unfold Valid at hv; exact hv.2
      have hcap : (step s (.insert e)).2.capacity = s.capacity := by rw [heq]
      have hitems : (step s (.insert e)).2.items.length = (ins e s.items).length := by rw [heq]
      rw [hcap, hitems, hlen]
      omega
    · have heq := step_invalid_eq s (.insert e) hv
      have hcap : (step s (.insert e)).2.capacity = s.capacity := by rw [heq]
      have hitems : (step s (.insert e)).2.items.length = s.items.length := by rw [heq]
      rw [hcap, hitems]
      exact hle
  | pop =>
    by_cases hv : Valid s .pop
    · have hne : s.items ≠ [] := by unfold Valid at hv; exact hv.2
      obtain ⟨x, xs, hs⟩ := cons_of_ne (l := s.items) hne
      have heq := step_pop_valid_eq s x xs hs hv
      have hcap : (step s .pop).2.capacity = s.capacity := by rw [heq]
      have hitems : (step s .pop).2.items = xs := by rw [heq]
      have hlen : s.items.length = xs.length + 1 := by rw [hs]; rfl
      have hlen2 : (step s .pop).2.items.length = xs.length := by rw [hitems]
      rw [hcap, hlen2]
      omega
    · have heq := step_invalid_eq s .pop hv
      have hcap : (step s .pop).2.capacity = s.capacity := by rw [heq]
      have hitems : (step s .pop).2.items.length = s.items.length := by rw [heq]
      rw [hcap, hitems]
      exact hle

theorem req_pop_min : PopMin step := by
  intro s hs
  have hv := step_success_valid s .pop hs
  have hsort : Sorted s.items := by unfold Valid at hv; exact hv.1
  have hne : s.items ≠ [] := by unfold Valid at hv; exact hv.2
  obtain ⟨x, xs, hitems⟩ := cons_of_ne (l := s.items) hne
  have heq := step_pop_valid_eq s x xs hitems hv
  refine ⟨x, by rw [heq], ?_⟩
  have hrest : (step s .pop).2.items = xs := by rw [heq]
  rw [hrest]
  intro y hy
  exact sorted_head (hitems ▸ hsort) y hy

theorem req_sorted : KeepsSorted step := by
  intro s op hsort
  cases op with
  | insert e =>
    by_cases hv : Valid s (.insert e)
    · have heq := step_insert_valid_eq s e hv
      have hitems : (step s (.insert e)).2.items = ins e s.items := by rw [heq]
      rw [hitems]
      exact ins_sorted e s.items hsort
    · have heq := step_invalid_eq s (.insert e) hv
      have hitems : (step s (.insert e)).2.items = s.items := by rw [heq]
      rw [hitems]
      exact hsort
  | pop =>
    by_cases hv : Valid s .pop
    · have hne : s.items ≠ [] := by unfold Valid at hv; exact hv.2
      obtain ⟨x, xs, hs⟩ := cons_of_ne (l := s.items) hne
      have heq := step_pop_valid_eq s x xs hs hv
      have hitems : (step s .pop).2.items = xs := by rw [heq]
      rw [hitems]
      have hcs : Sorted (x :: xs) := hs ▸ hsort
      exact sorted_tail hcs
    · have heq := step_invalid_eq s .pop hv
      have hitems : (step s .pop).2.items = s.items := by rw [heq]
      rw [hitems]
      exact hsort

theorem req_insert_effects : InsertEffects step := by
  intro s e hs
  have hv := step_success_valid s (.insert e) hs
  have hsort : Sorted s.items := by unfold Valid at hv; exact hv.1
  have heq := step_insert_valid_eq s e hv
  have hok : (step s (.insert e)).1 = .ok := by rw [heq]
  have hcap : (step s (.insert e)).2.capacity = s.capacity := by rw [heq]
  refine And.intro hok (And.intro hcap ?_)
  obtain ⟨l₁, l₂, hl, hins, h1, h2⟩ := ins_split_sorted e s.items hsort
  refine Exists.intro l₁ ?_
  refine Exists.intro l₂ ?_
  have hitems : (step s (.insert e)).2.items = l₁ ++ e :: l₂ := by rw [heq, hins]
  exact And.intro hl (And.intro hitems (And.intro h1 h2))

theorem req_pop_effects : PopEffects step := by
  intro s hs
  have hv := step_success_valid s .pop hs
  have hsort : Sorted s.items := by unfold Valid at hv; exact hv.1
  have hne : s.items ≠ [] := by unfold Valid at hv; exact hv.2
  obtain ⟨x, xs, hitems⟩ := cons_of_ne (l := s.items) hne
  have heq := step_pop_valid_eq s x xs hitems hv
  have hcap : (step s .pop).2.capacity = s.capacity := by rw [heq]
  have hgot : (step s .pop).1 = .got x := by rw [heq]
  have hrest : (step s .pop).2.items = ([] : List Entry) ++ xs := by rw [heq]; rfl
  have hfst : s.items = ([] : List Entry) ++ x :: xs := by rw [hitems]; rfl
  have hempty : ∀ y : Entry, y ∈ ([] : List Entry) → x.prio < y.prio := by
    intro y hy
    cases hy
  have htail : ∀ y ∈ xs, x.prio ≤ y.prio := sorted_head (hitems ▸ hsort)
  refine And.intro hcap ?_
  refine Exists.intro ([] : List Entry) ?_
  refine Exists.intro x ?_
  refine Exists.intro xs ?_
  exact And.intro hfst (And.intro hgot (And.intro hrest (And.intro hempty htail)))

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow, classOf]
  | cons op ops' ih =>
    have hsingle := single_step_fifo s op p
    have hih := ih (step s op).2
    have hrun : run step s (op :: ops')
        = ((op, (step s op).1) :: (run step (step s op).2 ops').1,
           (run step (step s op).2 ops').2) := rfl
    rw [hrun]
    have h_in : inflow ((op, (step s op).1) :: (run step (step s op).2 ops').1)
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops').1 := rfl
    have h_out : outflow ((op, (step s op).1) :: (run step (step s op).2 ops').1)
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops').1 := rfl
    rw [h_in, h_out, classOf_append, classOf_append]
    calc classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops').1))
        = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops').1) := by
            rw [← List.append_assoc]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops').1) := by
            rw [hsingle]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops').1)) := by
            rw [List.append_assoc]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops').1) ++ classOf p (run step (step s op).2 ops').2.items) := by
            rw [hih]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops').1)) ++ classOf p (run step (step s op).2 ops').2.items := by
            rw [← List.append_assoc]

end PrioQueue
