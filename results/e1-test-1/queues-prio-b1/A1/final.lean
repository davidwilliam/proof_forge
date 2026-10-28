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

theorem ins_length_aux2 (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by induction l with | nil => rfl | cons x xs ih => simp only [ins]; split <;> simp [ih, Nat.add_assoc]

theorem capNegHelper (s : State) (op : Op) (hle : s.items.length ≤ s.capacity) (h : ¬ Valid s op) : (step s op).2.items.length ≤ (step s op).2.capacity := by unfold step; simp [if_neg h, hle]

theorem capInsHelper2 (s : State) (e : Entry) (h : Valid s (Op.insert e)) : (step s (Op.insert e)).2 = { s with items := ins e s.items } := by unfold step; simp [if_pos h]

theorem capPopHelper (s : State) (x : Entry) (xs : List Entry) (heq : s.items = x :: xs) (h : Valid s Op.pop) : (step s Op.pop).2 = { s with items := xs } := by unfold step; simp [if_pos h, heq]

theorem tmpCheckPairwise (R : Entry → Entry → Prop) (a : Entry) (l : List Entry) : List.Pairwise R (a :: l) → (∀ x ∈ l, R a x) ∧ List.Pairwise R l := fun h => List.pairwise_cons.mp h

theorem tmpCheckPairwise2 (R : Entry → Entry → Prop) (a : Entry) (l : List Entry) (h : (∀ x ∈ l, R a x) ∧ List.Pairwise R l) : List.Pairwise R (a :: l) := List.pairwise_cons.mpr h

theorem tmpMemTest1 (x : Entry) (xs : List Entry) : x ∈ (x :: xs) := by simp

theorem tmpMemTest2 (x y : Entry) (xs : List Entry) (h : y ∈ xs) : y ∈ (x :: xs) := by simp [h]

theorem tmpPairTail (a : Entry) (l : List Entry) (h : List.Pairwise (fun a b : Entry => a.prio ≤ b.prio) (a :: l)) : List.Pairwise (fun a b : Entry => a.prio ≤ b.prio) l := (List.pairwise_cons.mp h).2

theorem tmpPairHead (a : Entry) (l : List Entry) (h : List.Pairwise (fun a b : Entry => a.prio ≤ b.prio) (a :: l)) : ∀ z ∈ l, a.prio ≤ z.prio := (List.pairwise_cons.mp h).1

theorem tmpMemApiTest (x y : Entry) (xs : List Entry) (h : y ∈ xs) : y ∈ (x :: xs) := List.Mem.tail _ h

theorem tmpMemApiTest2 (x : Entry) (xs : List Entry) : x ∈ (x :: xs) := List.Mem.head _

theorem sortedInsMem_uniq3 (e y : Entry) (l : List Entry) : y ∈ ins e l → y = e ∨ y ∈ l := by
  induction l with
  | nil =>
    intro h
    simp [ins] at h
    exact Or.inl h
  | cons x xs ih =>
    intro h
    simp only [ins] at h
    split at h
    · simp at h
      rcases h with rfl | rfl | h2
      · exact Or.inl rfl
      · exact Or.inr (List.Mem.head _)
      · exact Or.inr (List.Mem.tail _ h2)
    · simp at h
      rcases h with rfl | h2
      · exact Or.inr (List.Mem.head _)
      · rcases ih h2 with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr (List.Mem.tail _ hm)

theorem sortedInsHelper_uniq1 (e : Entry) (l : List Entry) : Sorted l → Sorted (ins e l) := by
  induction l with
  | nil =>
    intro _
    simp [ins, Sorted]
  | cons x xs ih =>
    intro hsort
    have hpair : List.Pairwise (fun a b : Entry => a.prio ≤ b.prio) (x :: xs) := hsort
    have hhead : ∀ z ∈ xs, x.prio ≤ z.prio := (List.pairwise_cons.mp hpair).1
    have htail : List.Pairwise (fun a b : Entry => a.prio ≤ b.prio) xs := (List.pairwise_cons.mp hpair).2
    simp only [ins]
    split
    · rename_i hlt
      have hle : e.prio ≤ x.prio := Nat.le_of_lt hlt
      have hall : ∀ z ∈ (x :: xs), e.prio ≤ z.prio := by
        intro z hz
        simp at hz
        rcases hz with rfl | hz2
        · exact hle
        · exact Nat.le_trans hle (hhead z hz2)
      have hsorted_cons : Sorted (x :: xs) := hsort
      exact List.pairwise_cons.mpr ⟨hall, hsorted_cons⟩
    · rename_i hnge
      have hle : x.prio ≤ e.prio := by omega
      have ihSorted : Sorted (ins e xs) := ih htail
      have hmem : ∀ y ∈ ins e xs, x.prio ≤ y.prio := by
        intro y hy
        rcases sortedInsMem_uniq3 e y (x :: xs |> fun _ => xs) hy with rfl | hy2
        -- note: ins e xs membership
        · exact hle
        · exact hhead y hy2
      exact List.pairwise_cons.mpr ⟨hmem, ihSorted⟩

theorem ins_split_aux2 (e : Entry) (l : List Entry) (h : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil =>
    exact ⟨[], [], rfl, rfl, by simp, by simp⟩
  | cons x xs ih =>
    by_cases hlt : e.prio < x.prio
    · have hins : ins e (x :: xs) = e :: x :: xs := by simp [ins, if_pos hlt]
      rw [hins]
      refine ⟨[], x :: xs, rfl, rfl, by simp, ?_⟩
      intro y hy
      simp at hy
      rcases hy with rfl | hy2
      · exact hlt
      · have hhead : ∀ z ∈ xs, x.prio ≤ z.prio := (List.pairwise_cons.mp h).1
        have hxle : x.prio ≤ y.prio := hhead y hy2
        omega
    · have hins : ins e (x :: xs) = x :: ins e xs := by simp [ins, if_neg hlt]
      rw [hins]
      have hle : x.prio ≤ e.prio := by omega
      have htail : Sorted xs := (List.pairwise_cons.mp h).2
      obtain ⟨l₁, l₂, heq, hins2, h1, h2⟩ := ih htail
      refine ⟨x :: l₁, l₂, ?_, ?_, ?_, h2⟩
      · simp [heq]
      · simp [hins2]
      · intro y hy
        simp at hy
        rcases hy with rfl | hy2
        · exact hle
        · exact h1 y hy2

theorem req_pop_effects_test2 : True := trivial

theorem popEff_proof2 : PopEffects step := by
  intro s hnr
  by_cases hV : Valid s Op.pop
  · have hSort : Sorted s.items := hV.1
    have hne : s.items ≠ [] := hV.2
    have hdecomp : ∃ x xs, s.items = x :: xs := by
      cases hs : s.items with
      | nil => exact absurd hs hne
      | cons x xs => exact ⟨x, xs, rfl⟩
    obtain ⟨x, xs, hitems⟩ := hdecomp
    have hstep : step s Op.pop = (.got x, { s with items := xs }) := by
      unfold step
      simp [if_pos hV, hitems]
    have hcap : (step s Op.pop).2.capacity = s.capacity := by rw [hstep]
    have hfst : (step s Op.pop).1 = .got x := by rw [hstep]
    have hsnd : (step s Op.pop).2.items = xs := by rw [hstep]
    have heq1 : s.items = ([] : List Entry) ++ x :: xs := by simp [hitems]
    have heq2 : (step s Op.pop).2.items = ([] : List Entry) ++ xs := by simp [hsnd]
    have hempty : ∀ x_1 ∈ ([] : List Entry), x.prio < x_1.prio := by simp
    have htail : ∀ y ∈ xs, x.prio ≤ y.prio := by
      have hpair : List.Pairwise (fun a b : Entry => a.prio ≤ b.prio) (x :: xs) := by
        rw [← hitems]
        exact hSort
      exact (List.pairwise_cons.mp hpair).1
    exact ⟨hcap, [], x, xs, heq1, hfst, heq2, hempty, htail⟩
  · have heq : step s Op.pop = (.rejected, s) := by unfold step; simp [if_neg hV]
    have h1 : (step s Op.pop).1 = .rejected := by rw [heq]
    exact absurd h1 hnr

theorem fifo_filter_append_test (p : Nat) (l₁ l₂ : List Entry) : classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by unfold classOf; simp

theorem probe_beq1 (a b : Nat) (h : a == b) : a = b := by exact Nat.eq_of_beq_eq_true h

theorem probe_beq2 (a b : Nat) (h : a = b) : (a == b) = true := by simp [h]

theorem fifo_probe1 (p : Nat) (l1 l2 : List Entry) : classOf p (l1 ++ l2) = classOf p l1 ++ classOf p l2 := by unfold classOf; rw [List.filter_append]

theorem fifo_probe2 (p : Nat) : classOf p ([] : List Entry) = [] := by unfold classOf; simp

theorem fifo_probe3 (p : Nat) (x : Entry) (xs : List Entry) : classOf p (x :: xs) = (if x.prio == p then [x] else []) ++ classOf p xs := by unfold classOf; simp; split <;> simp [*]

#check Nat.eq_of_beq_eq_true
#check List.filter_eq_nil_iff
#check List.filter_append

theorem fifo_beq_false_test (a b : Nat) (h : a ≠ b) : (a == b) = false := by
  cases hc : (a == b) with
  | true =>
    have heq : a = b := (beq_iff_eq.mp hc)
    exact absurd heq h
  | false => rfl

theorem fifo_beq_true_test (a b : Nat) (h : a = b) : (a == b) = true := by
  have := beq_iff_eq.mpr h
  exact this

theorem fifo_singleton_eq (p : Nat) (e : Entry) (h : e.prio = p) : classOf p [e] = [e] := by
  unfold classOf
  simp only [List.filter_cons]
  have hb : (e.prio == p) = true := fifo_beq_true_test e.prio p h
  simp [hb]

theorem fifo_singleton_ne (p : Nat) (e : Entry) (h : e.prio ≠ p) : classOf p [e] = [] := by
  unfold classOf
  simp only [List.filter_cons, List.filter_nil]
  have hb : (e.prio == p) = false := fifo_beq_false_test e.prio p h
  simp [hb]

theorem fifo_cons_eq (p : Nat) (x : Entry) (xs : List Entry) :
    classOf p (x :: xs) = classOf p [x] ++ classOf p xs := by
  unfold classOf
  simp only [List.filter_cons]
  split <;> simp

theorem fifo_nil_class (p : Nat) : classOf p ([] : List Entry) = [] := by unfold classOf; simp

theorem fifo_append_class (p : Nat) (l1 l2 : List Entry) :
    classOf p (l1 ++ l2) = classOf p l1 ++ classOf p l2 := fifo_probe1 p l1 l2

theorem fifo_ne_nil (p : Nat) (l : List Entry) (h : ∀ x ∈ l, x.prio ≠ p) : classOf p l = [] := by
  unfold classOf
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    have hb : (x.prio == p) = false := fifo_beq_false_test x.prio p (h x (List.Mem.head _))
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    apply ih
    intro y hy
    exact h y (List.Mem.tail _ hy)

theorem ins_classOf_sorted (p : Nat) (e : Entry) (l : List Entry) (h : Sorted l) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := by
  obtain ⟨l₁, l₂, heq, hins, h1, h2⟩ := ins_split_aux2 e l h
  have hcl : classOf p l = classOf p l₁ ++ classOf p l₂ := by rw [heq, fifo_append_class]
  have hci : classOf p (ins e l) = classOf p l₁ ++ classOf p (e :: l₂) := by rw [hins, fifo_append_class]
  have hce : classOf p (e :: l₂) = classOf p [e] ++ classOf p l₂ := by
    have ha : classOf p (e :: l₂) = classOf p [e] ++ classOf p l₂ := by
      rw [fifo_cons_eq]
    exact ha
  rw [hcl, hci, hce]
  by_cases heq2 : e.prio = p
  · have hce2 : classOf p [e] = [e] := fifo_singleton_eq p e heq2
    have hcl2 : classOf p l₂ = [] := by
      apply fifo_ne_nil
      intro x hx
      have hlt : e.prio < x.prio := h2 x hx
      rw [heq2] at hlt
      omega
    rw [hce2, hcl2]
    simp
  · have hce2 : classOf p [e] = [] := fifo_singleton_ne p e heq2
    rw [hce2]
    simp

theorem fifo_inflow_cons2 (op : Op) (o : Outcome) (t : List (Op × Outcome)) :
    inflow ((op, o) :: t) = inflowOf (op, o) ++ inflow t := by
  unfold inflow
  simp

theorem fifo_outflow_cons2 (op : Op) (o : Outcome) (t : List (Op × Outcome)) :
    outflow ((op, o) :: t) = outflowOf (op, o) ++ outflow t := by
  unfold outflow
  simp

theorem fifo_inflow_nil2 : inflow ([] : List (Op × Outcome)) = [] := by unfold inflow; simp

theorem fifo_outflow_nil2 : outflow ([] : List (Op × Outcome)) = [] := by unfold outflow; simp

theorem probe_inflow_a (e : Entry) : inflowOf (Op.insert e, Outcome.ok) = [e] := rfl

theorem probe_inflow_b (e : Entry) : outflowOf (Op.insert e, Outcome.ok) = ([] : List Entry) := rfl

theorem probe_inflow_c (x : Entry) : inflowOf (Op.pop, Outcome.got x) = ([] : List Entry) := rfl

theorem probe_inflow_d (x : Entry) : outflowOf (Op.pop, Outcome.got x) = [x] := rfl

theorem single_step_fifo_aux (p : Nat) (s : State) (op : Op) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
    = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have hsort : Sorted s.items := hV.1
      have h1 : (step s (Op.insert e)).1 = .ok := by unfold step; simp [if_pos hV]
      have h2 : (step s (Op.insert e)).2.items = ins e s.items := by unfold step; simp [if_pos hV]
      have hins : classOf p (ins e s.items) = classOf p s.items ++ classOf p [e] :=
        ins_classOf_sorted p e s.items hsort
      have hin : inflowOf (Op.insert e, (step s (Op.insert e)).1) = [e] := by
        rw [h1]; exact probe_inflow_a e
      have hout : outflowOf (Op.insert e, (step s (Op.insert e)).1) = ([] : List Entry) := by
        rw [h1]; exact probe_inflow_b e
      rw [hin, hout, h2, hins]
      simp [fifo_nil_class]
    | pop =>
      have hne : s.items ≠ [] := hV.2
      obtain ⟨x, xs, hitems⟩ : ∃ x xs, s.items = x :: xs := by
        cases hs : s.items with
        | nil => exact absurd hs hne
        | cons x xs => exact ⟨x, xs, rfl⟩
      have hstep : step s Op.pop = (.got x, { s with items := xs }) := by
        unfold step; simp [if_pos hV, hitems]
      have h1 : (step s Op.pop).1 = .got x := by rw [hstep]
      have h2 : (step s Op.pop).2.items = xs := by rw [hstep]
      have hin : inflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
        rw [h1]; exact probe_inflow_c x
      have hout : outflowOf (Op.pop, (step s Op.pop).1) = [x] := by
        rw [h1]; exact probe_inflow_d x
      rw [hin, hout, h2, hitems]
      simp only [fifo_nil_class, List.append_nil]
      exact fifo_cons_eq p x xs
  · have heq : step s op = (.rejected, s) := by unfold step; simp [if_neg hV]
    have h1 : (step s op).1 = .rejected := by rw [heq]
    have h2 : (step s op).2 = s := by rw [heq]
    rw [h2, h1]
    cases op with
    | insert e =>
      simp only [inflowOf, outflowOf]
      simp [fifo_nil_class]
    | pop =>
      simp only [inflowOf, outflowOf]
      simp [fifo_nil_class]

theorem runConsEq (s : State) (op : Op) (ops : List Op) :
    run step s (op :: ops) =
      ((op, (step s op).1) :: (run step (step s op).2 ops).1,
       (run step (step s op).2 ops).2) := rfl

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  show (step s op).1 ≠ .rejected
  unfold step
  rw [if_pos h]
  cases op with
  | insert e => simp
  | pop =>
    unfold Valid at h
    obtain ⟨_, hne⟩ := h
    cases hs : s.items with
    | nil => exact absurd hs hne
    | cons x xs => simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  unfold step
  rw [if_neg h]

theorem req_capacity : CapacityBound step := by
  intro s op hle
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have hlt : s.items.length < s.capacity := hV.2
      have hstep : (step s (Op.insert e)).2 = ({ s with items := ins e s.items } : State) := by
        unfold step; simp [if_pos hV]
      have hlen : (ins e s.items).length = s.items.length + 1 := ins_length_aux2 e s.items
      have hcap_eq : (step s (Op.insert e)).2.capacity = s.capacity := by rw [hstep]
      have hitems_eq : (step s (Op.insert e)).2.items = ins e s.items := by rw [hstep]
      rw [hitems_eq, hcap_eq, hlen]
      omega
    | pop =>
      have hne : s.items ≠ [] := hV.2
      obtain ⟨x, xs, hitems⟩ : ∃ x xs, s.items = x :: xs := by
        cases hs : s.items with
        | nil => exact absurd hs hne
        | cons x xs => exact ⟨x, xs, rfl⟩
      have hstep : (step s Op.pop).2 = ({ s with items := xs } : State) := by
        unfold step; simp [if_pos hV, hitems]
      have hcap_eq : (step s Op.pop).2.capacity = s.capacity := by rw [hstep]
      have hitems_eq : (step s Op.pop).2.items = xs := by rw [hstep]
      rw [hitems_eq, hcap_eq]
      rw [hitems] at hle
      simp at hle ⊢
      omega
  · have heq : step s op = (.rejected, s) := by unfold step; simp [if_neg hV]
    have h2 : (step s op).2 = s := by rw [heq]
    rw [h2]
    exact hle

theorem req_pop_min : PopMin step := by
  intro s hnr
  by_cases hV : Valid s Op.pop
  · have hSort : Sorted s.items := (by unfold Valid at hV; exact hV.1)
    have hne : s.items ≠ [] := (by unfold Valid at hV; exact hV.2)
    cases hitems : s.items with
    | nil => exact absurd hitems hne
    | cons x xs =>
      have hstep : step s Op.pop = (.got x, { s with items := xs }) := by
        unfold step
        simp [if_pos hV, hitems]
      refine ⟨x, ?_, ?_⟩
      · rw [hstep]
      · rw [hstep]
        simp only
        intro y hy
        have hpair : List.Pairwise (fun a b : Entry => a.prio ≤ b.prio) (x :: xs) := by
          rw [← hitems]; exact hSort
        have hmem : ∀ z ∈ xs, (fun a b : Entry => a.prio ≤ b.prio) x z := (List.pairwise_cons.mp hpair).1
        exact hmem y hy
  · have heq : step s Op.pop = (.rejected, s) := by unfold step; simp [if_neg hV]
    have h1 : (step s Op.pop).1 = .rejected := by rw [heq]
    exact absurd h1 hnr

theorem req_sorted : KeepsSorted step := by
  intro s op hsort
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have h2 : (step s (Op.insert e)).2.items = ins e s.items := by
        unfold step
        simp [if_pos hV]
      rw [h2]
      exact sortedInsHelper_uniq1 e s.items hsort
    | pop =>
      have hne : s.items ≠ [] := by
        unfold Valid at hV
        exact hV.2
      cases hitems : s.items with
      | nil => exact absurd hitems hne
      | cons x xs =>
        have h2 : (step s Op.pop).2.items = xs := by
          unfold step
          simp [if_pos hV, hitems]
        rw [h2]
        have hpair : List.Pairwise (fun a b : Entry => a.prio ≤ b.prio) (x :: xs) := by
          rw [← hitems]; exact hsort
        exact (List.pairwise_cons.mp hpair).2
  · have h2 : (step s op).2.items = s.items := by
      unfold step
      simp [if_neg hV]
    rw [h2]
    exact hsort

theorem req_insert_effects : InsertEffects step := by
  intro s e hnr
  by_cases hV : Valid s (Op.insert e)
  · have hstep1 : (step s (Op.insert e)).1 = .ok := by unfold step; simp [if_pos hV]
    have hstep2 : (step s (Op.insert e)).2 = ({ s with items := ins e s.items } : State) := by unfold step; simp [if_pos hV]
    have hcap : (step s (Op.insert e)).2.capacity = s.capacity := by rw [hstep2]
    have hsort : Sorted s.items := by unfold Valid at hV; exact hV.1
    obtain ⟨l₁, l₂, heq, hins, h1, h2⟩ := ins_split_aux2 e s.items hsort
    have hitems : (step s (Op.insert e)).2.items = l₁ ++ e :: l₂ := by rw [hstep2]; simp [hins]
    exact ⟨hstep1, hcap, l₁, l₂, heq, hitems, h1, h2⟩
  · have heq : step s (Op.insert e) = (.rejected, s) := by unfold step; simp [if_neg hV]
    have h1 : (step s (Op.insert e)).1 = .rejected := by rw [heq]
    exact absurd h1 hnr

theorem req_pop_effects : PopEffects step := by
  intro s hnr
  by_cases hV : Valid s Op.pop
  · have hSort : Sorted s.items := hV.1
    have hne : s.items ≠ [] := hV.2
    have hdecomp : ∃ x xs, s.items = x :: xs := by
      cases hs : s.items with
      | nil => exact absurd hs hne
      | cons x xs => exact ⟨x, xs, rfl⟩
    obtain ⟨x, xs, hitems⟩ := hdecomp
    have hstep : step s Op.pop = (.got x, { s with items := xs }) := by
      unfold step
      simp [if_pos hV, hitems]
    have hcap : (step s Op.pop).2.capacity = s.capacity := by rw [hstep]
    have hfst : (step s Op.pop).1 = .got x := by rw [hstep]
    have hsnd : (step s Op.pop).2.items = xs := by rw [hstep]
    have heq1 : s.items = ([] : List Entry) ++ x :: xs := by simp [hitems]
    have heq2 : (step s Op.pop).2.items = ([] : List Entry) ++ xs := by simp [hsnd]
    have hempty : ∀ x_1 ∈ ([] : List Entry), x.prio < x_1.prio := by simp
    have htail : ∀ y ∈ xs, x.prio ≤ y.prio := by
      have hpair : List.Pairwise (fun a b : Entry => a.prio ≤ b.prio) (x :: xs) := by
        rw [← hitems]
        exact hSort
      exact (List.pairwise_cons.mp hpair).1
    exact ⟨hcap, [], x, xs, heq1, hfst, heq2, hempty, htail⟩
  · have heq : step s Op.pop = (.rejected, s) := by unfold step; simp [if_neg hV]
    have h1 : (step s Op.pop).1 = .rejected := by rw [heq]
    exact absurd h1 hnr

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  induction ops generalizing s with
  | nil =>
    have h1 : (run step s []).1 = ([] : List (Op × Outcome)) := rfl
    have h2 : (run step s []).2 = s := rfl
    rw [h1, h2]
    unfold inflow outflow
    simp [fifo_nil_class]
  | cons op ops ih =>
    have hcon := runConsEq s op ops
    have hfst : (run step s (op :: ops)).1
        = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by rw [hcon]
    have hsnd : (run step s (op :: ops)).2
        = (run step (step s op).2 ops).2 := by rw [hcon]
    rw [hfst, hsnd]
    have hin : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      unfold inflow
      simp
    have hout : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      unfold outflow
      simp
    rw [hin, hout]
    rw [fifo_append_class, fifo_append_class]
    have hIH := ih (step s op).2
    have hsingle := single_step_fifo_aux p s op
    calc classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1))
        = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops).1) := by
          rw [List.append_assoc]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops).1) := by
          rw [hsingle]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops).1)) := by
          rw [List.append_assoc]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops).1) ++ classOf p (run step (step s op).2 ops).2.items) := by
          rw [hIH]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1)) ++ classOf p (run step (step s op).2 ops).2.items := by
          rw [List.append_assoc]

end PrioQueue
