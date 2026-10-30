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
      | [] => (.rejected, s)
      | x :: xs => (.got x, { s with items := xs })
  else (.rejected, s)

private theorem ins_length8 (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    simp only [ins]
    by_cases hc : e.prio < x.prio
    · simp [if_pos hc]
    · simp [if_neg hc, ih]

private theorem sorted_tail3e {a : Entry} {l : List Entry} (h : Sorted (a :: l)) : Sorted l :=
  (List.pairwise_cons.mp h).2

private theorem mem_ins2e (e : Entry) (l : List Entry) (y : Entry) (hy : y ∈ ins e l) : y = e ∨ y ∈ l := by
  induction l with
  | nil => simp [ins] at hy; exact Or.inl hy
  | cons x xs ih =>
    simp only [ins] at hy
    by_cases hc : e.prio < x.prio
    · simp [if_pos hc] at hy
      rcases hy with rfl | hy
      · exact Or.inl rfl
      · rcases hy with rfl | hy
        · exact Or.inr (List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem x hy)
    · simp [if_neg hc] at hy
      rcases hy with rfl | hy
      · exact Or.inr (List.mem_cons_self)
      · have hm := ih hy
        rcases hm with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem x hm)

private theorem ins_sorted3e (e : Entry) (l : List Entry) (hS : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil => simp [ins, Sorted]
  | cons x xs ih =>
    have hTail : Sorted xs := sorted_tail3e hS
    have ih' := ih hTail
    simp only [ins]
    by_cases hc : e.prio < x.prio
    · simp [if_pos hc]
      have h1 : e.prio ≤ x.prio := Nat.le_of_lt hc
      have hall : ∀ y ∈ (x :: xs), e.prio ≤ y.prio := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h1
        · have hxle : x.prio ≤ y.prio := (List.pairwise_cons.mp hS).1 y hy
          exact Nat.le_trans h1 hxle
      exact (List.pairwise_cons.mpr ⟨hall, hS⟩)
    · simp [if_neg hc]
      have hxe : x.prio ≤ e.prio := Nat.le_of_not_gt hc
      have hall : ∀ y ∈ ins e xs, x.prio ≤ y.prio := by
        intro y hy
        have hm := mem_ins2e e xs y hy
        rcases hm with rfl | hy2
        · exact hxe
        · exact (List.pairwise_cons.mp hS).1 y hy2
      exact (List.pairwise_cons.mpr ⟨hall, ih'⟩)

private theorem ins_split_sorted (e : Entry) (l : List Entry) (hS : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧ (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil =>
    exact ⟨[], [], by simp, by simp [ins], by simp, by simp⟩
  | cons x xs ih =>
    have hTail : Sorted xs := sorted_tail3e hS
    have hPair := List.pairwise_cons.mp hS
    have hle : ∀ y ∈ xs, x.prio ≤ y.prio := hPair.1
    simp only [ins]
    by_cases hc : e.prio < x.prio
    · simp [if_pos hc]
      refine ⟨[], x :: xs, by simp, rfl, by simp, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy2
      · exact hc
      · exact Nat.lt_of_lt_of_le hc (hle y hy2)
    · simp [if_neg hc]
      have hxe : x.prio ≤ e.prio := Nat.le_of_not_gt hc
      obtain ⟨l₁, l₂, hEq, hIns, h1, h2⟩ := ih hTail
      refine ⟨x :: l₁, l₂, ?_, ?_, ?_, h2⟩
      · simp [hEq]
      · simp [hIns]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy2
        · exact hxe
        · exact h1 y hy2

private theorem classOf_append' (p : Nat) (l₁ l₂ : List Entry) :
    classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by
  unfold classOf; simp

private theorem classOf_nil' (p : Nat) : classOf p [] = [] := by simp [classOf]

private theorem inflow_cons' (t : List (Op × Outcome)) (op : Op) (oc : Outcome) :
    inflow ((op, oc) :: t) = inflowOf (op, oc) ++ inflow t := by simp [inflow]

private theorem outflow_cons' (t : List (Op × Outcome)) (op : Op) (oc : Outcome) :
    outflow ((op, oc) :: t) = outflowOf (op, oc) ++ outflow t := by simp [outflow]

private theorem classOf_filter_nil_of_forall_ne {p : Nat} {l : List Entry}
    (h : ∀ x ∈ l, x.prio ≠ p) : classOf p l = [] := by
  unfold classOf
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  simp
  intro heq
  exact h x hx heq

private theorem ins_classOf' (e : Entry) (l : List Entry) (hS : Sorted l) (p : Nat) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := by
  obtain ⟨l₁, l₂, hEq, hIns, h1, h2⟩ := ins_split_sorted e l hS
  have hLeft : classOf p l = classOf p l₁ ++ classOf p l₂ := by
    rw [hEq]; exact classOf_append' p l₁ l₂
  have hRight : classOf p (ins e l) = classOf p l₁ ++ classOf p (e :: l₂) := by
    rw [hIns]; exact classOf_append' p l₁ (e :: l₂)
  have hECons : classOf p (e :: l₂) = classOf p [e] ++ classOf p l₂ := by
    have : (e :: l₂) = [e] ++ l₂ := by simp
    rw [this, classOf_append']
  rw [hLeft] at *
  rw [hRight]
  rw [hECons]
  by_cases he : e.prio == p
  · have heEq : e.prio = p := by simp [beq_iff_eq] at he; exact he
    have h2ne : ∀ x ∈ l₂, x.prio ≠ p := by
      intro x hx
      have hlt := h2 x hx
      rw [heEq] at hlt; omega
    have hCl2Nil : classOf p l₂ = [] := classOf_filter_nil_of_forall_ne h2ne
    rw [hCl2Nil]; simp
  · have hClSingle : classOf p [e] = [] := by unfold classOf; simp [he]
    rw [hClSingle]; simp

private theorem step_single_fifo (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
    classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  unfold step
  by_cases hV : Valid s op
  · simp only [hV, ↓reduceIte]
    cases op with
    | insert e =>
      simp only
      have hInsCl := ins_classOf' e s.items hV.1 p
      have hIn : inflowOf (Op.insert e, (Outcome.ok : Outcome)) = [e] := by simp [inflowOf]
      have hOut : outflowOf (Op.insert e, (Outcome.ok : Outcome)) = [] := by simp [outflowOf]
      have hClassIn : classOf p (inflowOf (Op.insert e, Outcome.ok)) = classOf p [e] := by rw [hIn]
      have hClassOut : classOf p (outflowOf (Op.insert e, Outcome.ok)) = [] := by rw [hOut]; exact classOf_nil' p
      calc classOf p s.items ++ classOf p (inflowOf (Op.insert e, Outcome.ok))
          = classOf p s.items ++ classOf p [e] := by rw [hClassIn]
        _ = classOf p (ins e s.items) := by rw [hInsCl]
        _ = [] ++ classOf p (ins e s.items) := by simp
        _ = classOf p (outflowOf (Op.insert e, Outcome.ok)) ++ classOf p (({ s with items := ins e s.items } : State).items) := by
            rw [hClassOut]
    | pop =>
      cases hItems : s.items with
      | nil =>
        have hNotV : ¬ Valid s Op.pop := by unfold Valid; simp [hItems]
        exact absurd hV hNotV |> False.elim
      | cons hd tl =>
        simp only [hItems]
        have hInPop : inflowOf (Op.pop, Outcome.got hd) = [] := by simp [inflowOf]
        have hOutPop : outflowOf (Op.pop, Outcome.got hd) = [hd] := by simp [outflowOf]
        have hClassInPop : classOf p (inflowOf (Op.pop, Outcome.got hd)) = [] := by rw [hInPop]; exact classOf_nil' p
        have hClassOutPop : classOf p (outflowOf (Op.pop, Outcome.got hd)) = classOf p [hd] := by rw [hOutPop]
        have hClassItems : classOf p (hd :: tl) = classOf p [hd] ++ classOf p tl := by
          have hEq : (hd :: tl) = [hd] ++ tl := by simp
          rw [hEq, classOf_append']
        rw [hClassInPop, hClassOutPop, hClassItems]
        simp
  · simp only [hV, ↓reduceIte]
    have hInRej : inflowOf (op, (Outcome.rejected : Outcome)) = [] := by cases op <;> simp [inflowOf]
    have hOutRej : outflowOf (op, (Outcome.rejected : Outcome)) = [] := by cases op <;> simp [outflowOf]
    rw [hInRej, hOutRej]
    simp [classOf_nil']

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV hR
  unfold step at hR
  simp [hV] at hR
  cases op with
  | insert e => simp at hR
  | pop =>
    cases hitems : s.items with
    | nil => unfold Valid at hV; simp [hitems] at hV
    | cons x xs => simp [hitems] at hR

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hV
  unfold step
  simp [hV]

theorem req_capacity : CapacityBound step := by
  intro s op hle
  unfold step
  by_cases hV : Valid s op
  · simp only [hV, ↓reduceIte]
    cases op with
    | insert e =>
      simp only
      have h1 : (ins e s.items).length = s.items.length + 1 := ins_length8 e s.items
      have hV2 : s.items.length < s.capacity := by
        have : Valid s (Op.insert e) := hV
        unfold Valid at this
        exact this.2
      omega
    | pop =>
      cases hs : s.items with
      | nil =>
        have : ¬ Valid s Op.pop := by unfold Valid; simp [hs]
        exact absurd hV this |> False.elim
      | cons x xs =>
        have : xs.length ≤ s.capacity := by
          have hlen : s.items.length = xs.length + 1 := by rw [hs]; simp
          omega
        simpa [hs] using this
  · simp only [hV, ↓reduceIte] at *
    exact hle

theorem req_pop_min : PopMin step := by
  intro s hNR
  unfold step at hNR
  by_cases hV : Valid s Op.pop
  · have hSorted : Sorted s.items := hV.1
    have hNe : s.items ≠ [] := hV.2
    obtain ⟨hd, tl, hEq⟩ : ∃ hd tl, s.items = hd :: tl := by
      match h : s.items with
      | [] => exact absurd h hNe
      | hd :: tl => exact ⟨hd, tl, rfl⟩
    have hStepEq : step s Op.pop = (.got hd, { capacity := s.capacity, items := tl }) := by
      unfold step; simp [hV, hEq]
    rw [hStepEq]
    refine ⟨hd, rfl, ?_⟩
    intro x hx
    have hPair : (hd :: tl).Pairwise (fun a b => a.prio ≤ b.prio) := by rw [←hEq]; exact hSorted
    exact (List.pairwise_cons.mp hPair).1 x hx
  · simp [hV] at hNR

theorem req_sorted : KeepsSorted step := by
  intro s op hS
  unfold step
  by_cases hV : Valid s op
  · simp only [hV, ↓reduceIte]
    cases op with
    | insert e =>
      simp only
      exact ins_sorted3e e s.items hS
    | pop =>
      cases hitems : s.items with
      | nil =>
        have : ¬ Valid s Op.pop := by unfold Valid; simp [hitems]
        exact absurd hV this |> False.elim
      | cons x xs =>
        change Sorted xs
        exact sorted_tail3e (hitems ▸ hS)
  · simp only [hV, ↓reduceIte]
    exact hS

theorem req_insert_effects : InsertEffects step := by
  intro s e hNR
  have hV : Valid s (Op.insert e) := by
    by_cases hv : Valid s (Op.insert e)
    · exact hv
    · have hSt : (step s (Op.insert e)).1 = .rejected := by unfold step; simp [hv]
      exact False.elim (hNR hSt)
  have hSorted : Sorted s.items := hV.1
  have hStep : step s (Op.insert e) = (.ok, { s with items := ins e s.items }) := by
    unfold step; simp [hV]
  have h1 : (step s (Op.insert e)).1 = .ok := by rw [hStep]
  have h2 : (step s (Op.insert e)).2.capacity = s.capacity := by rw [hStep]
  refine ⟨h1, h2, ?_⟩
  obtain ⟨l₁, l₂, hEq, hIns, ha, hb⟩ := ins_split_sorted e s.items hSorted
  refine ⟨l₁, l₂, hEq, ?_, ha, hb⟩
  have : (step s (Op.insert e)).2.items = ins e s.items := by rw [hStep]
  rw [this, hIns]

theorem req_pop_effects : PopEffects step := by
  intro s hNR
  have hV : Valid s Op.pop := by
    by_cases hv : Valid s Op.pop
    · exact hv
    · have hSt : (step s Op.pop).1 = .rejected := by unfold step; simp [hv]
      exact False.elim (hNR hSt)
  have hNe : s.items ≠ [] := hV.2
  obtain ⟨hd, tl, hEq⟩ : ∃ hd tl, s.items = hd :: tl := by
    match h : s.items with
    | [] => exact absurd h hNe
    | hd :: tl => exact ⟨hd, tl, rfl⟩
  have hStep : step s Op.pop = (.got hd, { capacity := s.capacity, items := tl }) := by
    unfold step; simp [hV, hEq]
  have hCap : (step s Op.pop).2.capacity = s.capacity := by rw [hStep]
  have hSorted : Sorted s.items := hV.1
  refine ⟨hCap, [], hd, tl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hEq]
  · rw [hStep]
  · simp [hStep]
  · intro x hx; simp at hx
  · intro x hx
    have hPair : (hd :: tl).Pairwise (fun a b => a.prio ≤ b.prio) := by rw [← hEq]; exact hSorted
    exact (List.pairwise_cons.mp hPair).1 x hx

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow, classOf_nil']
  | cons op ops' ih =>
    have hRun : run step s (op :: ops') =
        (((op, (step s op).1) :: (run step (step s op).2 ops').1), (run step (step s op).2 ops').2) := by
      simp [run]
    have hFinalItems : (run step s (op :: ops')).2.items = (run step (step s op).2 ops').2.items := by rw [hRun]
    have hTrace : (run step s (op :: ops')).1 = (op, (step s op).1) :: (run step (step s op).2 ops').1 := by rw [hRun]
    have hInTrace : inflow (run step s (op :: ops')).1 =
        inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops').1 := by
      rw [hTrace, inflow_cons']
    have hOutTrace : outflow (run step s (op :: ops')).1 =
        outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops').1 := by
      rw [hTrace, outflow_cons']
    have hClassInTrace : classOf p (inflow (run step s (op :: ops')).1) =
        classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops').1) := by
      rw [hInTrace, classOf_append']
    have hClassOutTrace : classOf p (outflow (run step s (op :: ops')).1) =
        classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops').1) := by
      rw [hOutTrace, classOf_append']
    have ihEq := ih (s := (step s op).2)
    have hSingle := step_single_fifo s op p
    calc classOf p s.items ++ classOf p (inflow (run step s (op :: ops')).1)
        = classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops').1)) := by
          rw [hClassInTrace]
      _ = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops').1) := by
          rw [List.append_assoc]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops').1) := by
          rw [hSingle]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops').1)) := by
          rw [List.append_assoc]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops').1) ++ classOf p (run step (step s op).2 ops').2.items) := by
          rw [ihEq]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops').1)) ++ classOf p (run step (step s op).2 ops').2.items := by
          rw [List.append_assoc]
      _ = classOf p (outflow (run step s (op :: ops')).1) ++ classOf p (run step s (op :: ops')).2.items := by
          rw [← hClassOutTrace, ← hFinalItems]

end PrioQueue
