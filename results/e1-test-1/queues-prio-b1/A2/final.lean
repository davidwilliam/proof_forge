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

private def fooTest : Nat := 1

theorem myTestLemma : 1 = 1 := rfl

theorem ins_length_thm (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    split
    · simp
    · simp [ih, Nat.add_assoc]

theorem cap_probe2 (s : State) (e : Entry) (h : Valid s (.insert e)) : (step s (.insert e)).2.capacity = s.capacity := by
  unfold step
  simp [if_pos h]

theorem ins_mem_helper : ∀ (a b : Entry) (l : List Entry), b ∈ ins a l → b = a ∨ b ∈ l := by
  intro a b l
  induction l with
  | nil =>
    intro h
    simp [ins] at h
    exact Or.inl h
  | cons x xs ih =>
    intro h
    simp only [ins] at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
      · have h2 := ih h
        rcases h2 with rfl | h2
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons.mpr (Or.inr h2))

theorem ins_sorted_helper : ∀ (e : Entry) (l : List Entry), Sorted l → Sorted (ins e l) := by
  intro e l
  induction l with
  | nil =>
    intro _
    simp [ins, Sorted]
  | cons x xs ih =>
    intro hP
    have hPair := (List.pairwise_cons.mp hP)
    obtain ⟨hall, htail⟩ := hPair
    simp only [ins]
    split
    · rename_i hlt
      have hax : e.prio ≤ x.prio := Nat.le_of_lt hlt
      have hmem : ∀ b ∈ (x :: xs), e.prio ≤ b.prio := by
        intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact hax
        · exact Nat.le_trans hax (hall b hb)
      exact (List.pairwise_cons.mpr ⟨hmem, hP⟩)
    · rename_i hnge
      have hxa : x.prio ≤ e.prio := by omega
      have ihP := ih htail
      have hx_all : ∀ y ∈ ins e xs, x.prio ≤ y.prio := by
        intro y hy
        have h2 := ins_mem_helper e y xs hy
        rcases h2 with rfl | h2
        · exact hxa
        · exact hall y h2
      exact (List.pairwise_cons.mpr ⟨hx_all, ihP⟩)

theorem tail_sorted_helper : ∀ (l : List Entry), Sorted l → Sorted l.tail := by
  intro l h
  cases l with
  | nil => exact List.Pairwise.nil
  | cons x xs => exact (List.pairwise_cons.mp h).2

theorem ins_split_aux_thm2 (e : Entry) (l : List Entry) (hS : Sorted l) :
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
    have hpair := (List.pairwise_cons.mp hS)
    obtain ⟨hall, htail⟩ := hpair
    obtain ⟨l₁', l₂', heq, hins, h1, h2⟩ := ih htail
    by_cases hlt : e.prio < x.prio
    · refine ⟨[], x :: xs, rfl, ?_, ?_, ?_⟩
      · show ins e (x :: xs) = ([] : List Entry) ++ e :: x :: xs
        simp [ins, if_pos hlt]
      · intro y hy
        simp at hy
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hlt
        · exact Nat.lt_of_lt_of_le hlt (hall y hy)
    · have hxa : x.prio ≤ e.prio := by omega
      refine ⟨x :: l₁', l₂', ?_, ?_, ?_, h2⟩
      · show x :: xs = (x :: l₁') ++ l₂'
        rw [heq, List.cons_append]
      · show ins e (x :: xs) = (x :: l₁') ++ e :: l₂'
        rw [show ins e (x :: xs) = x :: ins e xs from by simp [ins, if_neg hlt]]
        rw [hins, List.cons_append]
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hxa
        · exact h1 y hy

theorem probe1 (p : Nat) (l1 l2 : List Entry) :
    classOf p (l1 ++ l2) = classOf p l1 ++ classOf p l2 := by
  unfold classOf
  simp
#check @List.filter_append
#check List.append_assoc

theorem probe_beq1 (a b : Nat) : (a == b) = decide (a = b) := by
  simp [BEq.beq]
#check BEq.beq
#check LawfulBEq
#check decide_eq_true
#check beq_iff_eq

theorem probe_singleton_eq (p : Nat) (e : Entry) (h : e.prio = p) :
    classOf p [e] = [e] := by
  unfold classOf
  simp [h]

theorem probe_singleton_ne (p : Nat) (e : Entry) (h : e.prio ≠ p) :
    classOf p [e] = [] := by
  unfold classOf
  simp [h]
#check List.filter

theorem classOf_append2 (p : Nat) (l1 l2 : List Entry) :
    classOf p (l1 ++ l2) = classOf p l1 ++ classOf p l2 := probe1 p l1 l2

theorem classOf_empty_list (p : Nat) (l : List Entry) (h : ∀ x ∈ l, x.prio ≠ p) :
    classOf p l = [] := by
  unfold classOf
  induction l with
  | nil => simp
  | cons y ys ih =>
    have hy : y.prio ≠ p := h y (by simp)
    have ht : ∀ x ∈ ys, x.prio ≠ p := fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
    have ih' := ih ht
    simp only [List.filter_cons]
    have hcond : ((y.prio == p) = false) := by
      have : (y.prio == p) = decide (y.prio = p) := probe_beq1 y.prio p
      rw [this]
      simp [hy]
    simp [hcond, ih']

theorem ins_classOf_stable2 (e : Entry) (l : List Entry) (p : Nat) (hS : Sorted l) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := by
  obtain ⟨l₁, l₂, heqL, heqIns, h1, h2⟩ := ins_split_aux_thm2 e l hS
  have hC1 : classOf p l = classOf p l₁ ++ classOf p l₂ := by
    rw [heqL]
    exact probe1 p l₁ l₂
  have hC2 : classOf p (ins e l) = classOf p l₁ ++ (classOf p [e] ++ classOf p l₂) := by
    rw [heqIns]
    have hA : classOf p (l₁ ++ e :: l₂) = classOf p l₁ ++ classOf p (e :: l₂) :=
      probe1 p l₁ (e :: l₂)
    rw [hA]
    congr 1
    have hB : (e :: l₂) = [e] ++ l₂ := by simp
    rw [hB]
    exact probe1 p [e] l₂
  rw [hC1, hC2]
  by_cases heq : e.prio = p
  · have hSingle : classOf p [e] = [e] := probe_singleton_eq p e heq
    have hL2nil : classOf p l₂ = [] := by
      apply classOf_empty_list
      intro x hx
      have hlt : e.prio < x.prio := h2 x hx
      omega
    rw [hSingle, hL2nil]
    simp
  · have hSingle : classOf p [e] = [] := probe_singleton_ne p e heq
    rw [hSingle]
    simp

theorem cap_helper_unique123 : CapacityBound step := by
  intro s op hlen
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have hLt : s.items.length < s.capacity := hV.2
      have hStep : (step s (Op.insert e)).2 = ({ s with items := ins e s.items } : State) := by
        unfold step
        simp [if_pos hV]
      have hCap : (step s (Op.insert e)).2.capacity = s.capacity := by rw [hStep]
      have hLen : (step s (Op.insert e)).2.items = ins e s.items := by rw [hStep]
      rw [hLen, hCap]
      have hInsLen : (ins e s.items).length = s.items.length + 1 := ins_length_thm e s.items
      rw [hInsLen]
      omega
    | pop =>
      cases hitems : s.items with
      | nil =>
        have hNe : s.items ≠ [] := hV.2
        rw [hitems] at hNe
        exact absurd rfl hNe
      | cons x xs =>
        have hStep : step s Op.pop = (.got x, ({ s with items := xs } : State)) := by
          unfold step
          simp [if_pos hV, hitems]
        have hCap : (step s Op.pop).2.capacity = s.capacity := by rw [hStep]
        have hLen : (step s Op.pop).2.items = xs := by rw [hStep]
        rw [hLen, hCap]
        rw [hitems] at hlen
        simp at hlen ⊢
        omega
  · have hEq : step s op = (.rejected, s) := by
      unfold step
      simp [if_neg hV]
    have h2 : (step s op).2 = s := by rw [hEq]
    rw [h2]
    exact hlen

theorem fifo_probe_inflow_rej (op : Op) : inflowOf (op, .rejected) = [] := by
  cases op with
  | insert e => rfl
  | pop => rfl

theorem fifo_probe_outflow_rej (op : Op) : outflowOf (op, .rejected) = [] := by
  cases op with
  | insert e => rfl
  | pop => rfl

theorem fifo_probe_inflow_ok (e : Entry) : inflowOf (.insert e, .ok) = [e] := by rfl

theorem fifo_probe_outflow_ok (e : Entry) : outflowOf (.insert e, .ok) = ([] : List Entry) := by
  simp [outflowOf]

theorem fifo_probe_outflow_got (op : Op) (e : Entry) : outflowOf (op, .got e) = [e] := by
  cases op with
  | insert e2 => rfl
  | pop => rfl

theorem fifo_probe_inflow_got (op : Op) (e : Entry) : inflowOf (op, .got e) = ([] : List Entry) := by
  cases op with
  | insert e2 => rfl
  | pop => rfl

theorem fifo_probe_class_nil (p : Nat) : classOf p ([] : List Entry) = [] := by rfl

theorem fifo_probe_class_single_cons (p : Nat) (x : Entry) (xs : List Entry) :
    classOf p (x :: xs) = classOf p [x] ++ classOf p xs := by
  have h : (x :: xs) = [x] ++ xs := by simp
  rw [h]
  exact probe1 p [x] xs

theorem fifo_probe_red1 (e : Entry) : inflowOf (Op.insert e, Outcome.ok) = [e] := by
  simp only [inflowOf]

theorem fifo_probe_red2 (e : Entry) : outflowOf (Op.insert e, Outcome.ok) = ([] : List Entry) := by
  simp only [outflowOf]

theorem fifo_probe_red3 (x : Entry) : outflowOf (Op.pop, Outcome.got x) = [x] := by
  simp only [outflowOf]

theorem fifo_probe_red4 (x : Entry) : inflowOf (Op.pop, Outcome.got x) = ([] : List Entry) := by
  simp only [inflowOf]

theorem fifo_inflow_cons_thm (a : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (a :: t) = inflowOf a ++ inflow t := by
  simp [inflow]

theorem fifo_outflow_cons_thm (a : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (a :: t) = outflowOf a ++ outflow t := by
  simp [outflow]

theorem fifo_run_cons_fst (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
  simp [run]

theorem fifo_run_cons_snd (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
  simp [run]

theorem fifo_nil_fst (s : State) : (run step s []).1 = ([] : List (Op × Outcome)) := by
  simp [run]

theorem fifo_nil_snd (s : State) : (run step s []).2 = s := by
  simp [run]

theorem fifo_nil_inflow : inflow ([] : List (Op × Outcome)) = ([] : List Entry) := by
  simp [inflow]

theorem fifo_nil_outflow : outflow ([] : List (Op × Outcome)) = ([] : List Entry) := by
  simp [outflow]









theorem plan0_step_classOf (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have hSort : Sorted s.items := hV.1
      have hstep : step s (Op.insert e) = (.ok, ({ s with items := ins e s.items } : State)) := by
        unfold step
        simp [if_pos hV]
      have h1 : (step s (Op.insert e)).1 = .ok := by rw [hstep]
      have h2 : (step s (Op.insert e)).2.items = ins e s.items := by rw [hstep]
      rw [h1, h2]
      have hin : inflowOf (Op.insert e, Outcome.ok) = [e] := by rfl
      have hout : outflowOf (Op.insert e, Outcome.ok) = ([] : List Entry) := by rfl
      rw [hin, hout]
      simp only [fifo_probe_class_nil, List.nil_append]
      exact (ins_classOf_stable2 e s.items p hSort).symm
    | pop =>
      have hNe : s.items ≠ [] := hV.2
      match hm : s.items with
      | [] => exact absurd hm hNe
      | x :: xs =>
        have hstep : step s Op.pop = (.got x, ({ s with items := xs } : State)) := by
          unfold step
          simp [if_pos hV, hm]
        have h1 : (step s Op.pop).1 = .got x := by rw [hstep]
        have h2 : (step s Op.pop).2.items = xs := by rw [hstep]
        rw [h1, h2]
        have hin : inflowOf (Op.pop, Outcome.got x) = ([] : List Entry) := by rfl
        have hout : outflowOf (Op.pop, Outcome.got x) = [x] := by rfl
        rw [hin, hout]
        simp only [fifo_probe_class_nil, List.append_nil]
        exact fifo_probe_class_single_cons p x xs
  · have heq : step s op = (.rejected, s) := by
      unfold step
      simp [if_neg hV]
    have h1 : (step s op).1 = .rejected := by rw [heq]
    have h2 : (step s op).2 = s := by rw [heq]
    rw [h1, h2]
    have hin : inflowOf (op, Outcome.rejected) = ([] : List Entry) := fifo_probe_inflow_rej op
    have hout : outflowOf (op, Outcome.rejected) = ([] : List Entry) := fifo_probe_outflow_rej op
    rw [hin, hout]
    simp [fifo_probe_class_nil]

theorem plan0_classOf_inflow_run_cons (s : State) (op : Op) (ops : List Op) (p : Nat) :
    classOf p (inflow (run step s (op :: ops)).1) =
      classOf p (inflowOf (op, (step s op).1)) ++
        classOf p (inflow (run step (step s op).2 ops).1) := by
  have hRun : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 :=
    fifo_run_cons_fst s op ops
  rw [hRun, fifo_inflow_cons_thm]
  exact classOf_append2 p _ _

theorem plan0_classOf_outflow_run_cons (s : State) (op : Op) (ops : List Op) (p : Nat) :
    classOf p (outflow (run step s (op :: ops)).1) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (outflow (run step (step s op).2 ops).1) := by
  have hRun : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 :=
    fifo_run_cons_fst s op ops
  rw [hRun, fifo_outflow_cons_thm]
  exact classOf_append2 p _ _

theorem plan0_fifo_ties_by_ind (ops : List Op) (s : State) (p : Nat) :
    classOf p s.items ++ classOf p (inflow (run step s ops).1) =
      classOf p (outflow (run step s ops).1) ++
        classOf p (run step s ops).2.items := by
  induction ops generalizing s with
  | nil =>
    have h1 : (run step s []).1 = ([] : List (Op × Outcome)) := fifo_nil_fst s
    have h2 : (run step s []).2 = s := fifo_nil_snd s
    rw [h1, h2]
    simp [inflow, outflow, fifo_probe_class_nil]
  | cons op ops ih =>
    have hStep := plan0_step_classOf s op p
    have hIH := ih (step s op).2
    have hIn := plan0_classOf_inflow_run_cons s op ops p
    have hOut := plan0_classOf_outflow_run_cons s op ops p
    have hSnd : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 :=
      fifo_run_cons_snd s op ops
    calc classOf p s.items ++ classOf p (inflow (run step s (op :: ops)).1)
        _ = classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1)) := by rw [hIn]
        _ = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
        _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [hStep]
        _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops).1)) := by rw [List.append_assoc]
        _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops).1) ++ classOf p (run step (step s op).2 ops).2.items) := by rw [hIH]
        _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1)) ++ classOf p (run step (step s op).2 ops).2.items := by rw [← List.append_assoc]
        _ = classOf p (outflow (run step s (op :: ops)).1) ++ classOf p (run step s (op :: ops)).2.items := by rw [hOut, hSnd]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  show (step s op).1 ≠ .rejected
  simp only [step, if_pos h]
  cases op with
  | insert e =>
    cases h1 : s.items with
    | nil => simp
    | cons x xs => simp
  | pop =>
    cases h1 : s.items with
    | nil =>
      exfalso
      unfold Valid at h
      simp [h1] at h
    | cons x xs => simp

theorem req_invalid_noop   : InvalidNoop step := by
  intro s op h
  show step s op = (.rejected, s)
  simp only [step, if_neg h]

theorem req_capacity : CapacityBound step := cap_helper_unique123

theorem req_pop_min : PopMin step := by
  intro s hne
  by_cases hV : Valid s .pop
  · have hVcopy := hV
    obtain ⟨hSort, hNe⟩ := hVcopy
    cases hitems : s.items with
    | nil =>
      exfalso
      exact hNe hitems
    | cons x xs =>
      have hstep : step s .pop = (.got x, { s with items := xs }) := by
        unfold step
        simp [if_pos hV, hitems]
      refine ⟨x, ?_, ?_⟩
      · rw [hstep]
      · intro y hy
        have hEq : (step s .pop).2.items = xs := by rw [hstep]
        rw [hEq] at hy
        unfold Sorted at hSort
        rw [hitems] at hSort
        exact (List.pairwise_cons.mp hSort).1 y hy
  · have heq : step s .pop = (.rejected, s) := by
      unfold step
      simp [if_neg hV]
    have h1 : (step s .pop).1 = .rejected := by rw [heq]
    exact absurd h1 hne

theorem req_sorted : KeepsSorted step := by
  intro s op hSorted
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have hEq : (step s (Op.insert e)).2.items = ins e s.items := by
        unfold step
        simp only [if_pos hV]
      rw [hEq]
      exact ins_sorted_helper e s.items hSorted
    | pop =>
      cases hitems : s.items with
      | nil =>
        exfalso
        have hNe : s.items ≠ [] := hV.2
        rw [hitems] at hNe
        exact hNe rfl
      | cons x xs =>
        have hEq : (step s Op.pop).2.items = xs := by
          unfold step
          simp [if_pos hV, hitems]
        rw [hEq]
        rw [hitems] at hSorted
        exact (List.pairwise_cons.mp hSorted).2
  · have hEq : (step s op).2 = s := by
      unfold step
      simp [if_neg hV]
    have : (step s op).2.items = s.items := by rw [hEq]
    rw [this]
    exact hSorted

theorem req_insert_effects : InsertEffects step := by
  intro s e hne
  by_cases hV : Valid s (.insert e)
  · have hSort : Sorted s.items := hV.1
    obtain ⟨l₁, l₂, heqL, heqIns, h1, h2⟩ := ins_split_aux_thm2 e s.items hSort
    have hstep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
      unfold step
      simp [if_pos hV]
    have hstep1 : (step s (.insert e)).1 = .ok := by rw [hstep]
    have hstep2 : (step s (.insert e)).2.capacity = s.capacity := by rw [hstep]
    have hstep3 : (step s (.insert e)).2.items = ins e s.items := by rw [hstep]
    refine ⟨hstep1, hstep2, l₁, l₂, heqL, ?_, h1, h2⟩
    rw [hstep3, heqIns]
  · have heq : step s (.insert e) = (.rejected, s) := req_invalid_noop s _ hV
    have h1 : (step s (.insert e)).1 = .rejected := by rw [heq]
    exact absurd h1 hne

theorem req_pop_effects : PopEffects step := by
  intro s hne
  by_cases hV : Valid s .pop
  · have hSort : Sorted s.items := hV.1
    have hNe : s.items ≠ [] := hV.2
    cases hitems : s.items with
    | nil => exact absurd hitems hNe
    | cons x xs =>
      have hstep : step s .pop = (.got x, { s with items := xs }) := by
        unfold step
        simp [if_pos hV, hitems]
      have hcap : (step s .pop).2.capacity = s.capacity := by rw [hstep]
      have h1 : (step s .pop).1 = .got x := by rw [hstep]
      have hSortCons : Sorted (x :: xs) := by rw [← hitems]; exact hSort
      have hall : ∀ y ∈ xs, x.prio ≤ y.prio :=
        (List.pairwise_cons.mp hSortCons).1
      exact ⟨hcap, [], x, xs, by simp [hitems], h1, by simp [hstep], by simp, hall⟩
  · have heq : step s .pop = (.rejected, s) := by
      unfold step
      simp [if_neg hV]
    have h1 : (step s .pop).1 = .rejected := by rw [heq]
    exact absurd h1 hne

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  exact plan0_fifo_ties_by_ind ops s p

end PrioQueue
