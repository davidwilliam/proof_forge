import PrioQueue.Spec
namespace PrioQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op
  · unfold Valid; infer_instance
  · unfold Valid; infer_instance

def ins (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs => if e.prio < x.prio then e :: x :: xs else x :: ins e xs

theorem ins_length (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih => simp only [ins]; split <;> simp [ih]

theorem head_le_of_sorted (x : Entry) (xs : List Entry) (h : Sorted (x :: xs)) (y : Entry) (hy : y ∈ xs) : x.prio ≤ y.prio := by
  induction xs generalizing x with
  | nil => simp at hy
  | cons z zs ih =>
    have hp := List.pairwise_cons.mp h
    have hxz : x.prio ≤ z.prio := hp.1 z (by simp)
    simp at hy
    rcases hy with rfl | hy2
    · exact hxz
    · exact Nat.le_trans hxz (ih (x := z) hp.2 hy2)

theorem sorted_cons_tail (x : Entry) (xs : List Entry) (h : Sorted (x :: xs)) : Sorted xs :=
  (List.pairwise_cons.mp h).2

theorem sorted_ins (e : Entry) (l : List Entry) (h : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil => simp [ins, Sorted]
  | cons x xs ih =>
    have hxs : Sorted xs := sorted_cons_tail x xs h
    have ihs := ih hxs
    simp only [ins]
    split
    next hlt =>
      apply List.Pairwise.cons
      · intro y hy
        simp at hy
        rcases hy with rfl | hy
        · exact Nat.le_of_lt hlt
        · exact Nat.le_trans (Nat.le_of_lt hlt) (head_le_of_sorted x xs h y hy)
      · exact h
    next hge =>
      have hxle : x.prio ≤ e.prio := by omega
      have hm : ∀ y ∈ ins e xs, x.prio ≤ y.prio := by
        intro y hy
        have : y = e ∨ y ∈ xs := by
          induction xs generalizing y with
          | nil => simp [ins] at hy; simp [hy]
          | cons a as ih2 =>
            simp only [ins] at hy
            split at hy
            · simp at hy; rcases hy with rfl | rfl | hm2 <;> simp [*]
            · simp at hy; rcases hy with rfl | hm2
              · simp
              · have h2 := ih2 hm2; rcases h2 with rfl | hm3 <;> simp [hm3]
        rcases this with rfl | hmem
        · exact hxle
        · exact head_le_of_sorted x xs h y hmem
      exact List.Pairwise.cons hm ihs

theorem ins_split (e : Entry) (l : List Entry) (h : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧ (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil => exact ⟨[], [], rfl, rfl, by simp, by simp⟩
  | cons x xs ih =>
    have hxs : Sorted xs := sorted_cons_tail x xs h
    simp only [ins]
    split
    next hlt =>
      refine ⟨[], x :: xs, rfl, rfl, by simp, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy2
      · exact hlt
      · exact Nat.lt_of_lt_of_le hlt (head_le_of_sorted x xs h y hy2)
    next hge =>
      rcases ih hxs with ⟨l₁, l₂, heq, hins, h1, h2⟩
      exact ⟨x :: l₁, l₂, by simp [heq], by simp [hins], fun y hy => by simp at hy; rcases hy with rfl | hy2; omega; exact h1 y hy2, h2⟩

theorem classOf_append_eq (p : Nat) (a b : List Entry) : classOf p (a ++ b) = classOf p a ++ classOf p b := by
  simp [classOf]

theorem classOf_sing_eq (p : Nat) (e : Entry) : classOf p [e] = if e.prio == p then [e] else [] := by
  simp [classOf]

theorem classOf_ins (e : Entry) (l : List Entry) (h : Sorted l) (p : Nat) :
    classOf p (ins e l) = classOf p l ++ if e.prio == p then [e] else [] := by
  induction l with
  | nil => simp [ins, classOf]
  | cons x xs ih =>
    have hxs : Sorted xs := sorted_cons_tail x xs h
    have ihc := ih hxs
    simp only [ins]
    split
    next hlt =>
      simp only [classOf]
      by_cases he : (e.prio == p) = true
      · have heq : e.prio = p := by simpa [he] using (of_decide_eq_true (by simpa [BEq.beq] using he))
        have hnil : List.filter (fun x => x.prio == p) (x :: xs) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro y hy
          simp at hy
          rcases hy with rfl | hy2
          · simp [heq]; omega
          · have hle := head_le_of_sorted x xs h y hy2; simp [heq] at hle ⊢; omega
        simp [he, hnil, List.filter_cons]
      · simp [he, List.filter_cons, he]
    next hge =>
      simp only [classOf, ihc, List.append_assoc, List.filter_cons]

def step : Impl := fun s op =>
  if Valid s op then
    match op with
    | .insert e => (.ok, { s with items := ins e s.items })
    | .pop =>
      match s.items with
      | [] => (.rejected, s)
      | x :: xs => (.got x, { s with items := xs })
  else (.rejected, s)

theorem step_insert_items (s : State) (e : Entry) (hV : Valid s (.insert e)) :
    (step s (.insert e)).2.items = ins e s.items := by simp [step, hV]

theorem valid_of_not_rejected_insert (s : State) (e : Entry) (h : (step s (.insert e)).1 ≠ .rejected) : Valid s (.insert e) := by
  by_cases hV : Valid s (.insert e)
  · exact hV
  · exfalso; apply h; simp [step, hV]

theorem valid_of_not_rejected_pop (s : State) (h : (step s .pop).1 ≠ .rejected) : Valid s .pop := by
  by_cases hV : Valid s .pop
  · exact hV
  · exfalso; apply h; simp [step, hV]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV; intro hRej
  simp [step, hV] at hRej
  cases op with
  | insert => simp at hRej
  | pop =>
    cases h : s.items with
    | nil => simp at hV
    | cons _ _ => simp [h] at hRej

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv; simp [step, hInv]

theorem req_capacity : CapacityBound step := by
  intro s op hle
  simp only [step]
  split
  next hV =>
    cases op with
    | insert e =>
      simp
      have hlt : s.items.length < s.capacity := hV.2
      have hl := ins_length e s.items
      simp [hl]; omega
    | pop =>
      cases h : s.items with
      | nil => simp [h]; exact hle
      | cons x xs => simp [h]; simp [h] at hle; omega
  next => exact hle

theorem req_pop_min : PopMin step := by
  intro s hNotRej
  have hV := valid_of_not_rejected_pop s hNotRej
  cases hm : s.items with
  | nil =>
    have hne : s.items ≠ [] := hV.2
    rw [hm] at hne; contradiction
  | cons x xs =>
    have hGot : (step s .pop).1 = .got x := by simp [step, hV, hm]
    have hItems : (step s .pop).2.items = xs := by simp [step, hV, hm]
    refine ⟨x, hGot, ?_⟩
    intro y hy
    have hS : Sorted (x :: xs) := by rw [← hm]; exact hV.1
    rw [hItems] at hy
    exact head_le_of_sorted x xs hS y hy

theorem req_sorted : KeepsSorted step := by
  intro s op hS
  by_cases hV : Valid s op
  · simp [step, hV]
    cases op with
    | insert e => simp; exact sorted_ins e s.items hS
    | pop =>
      cases h : s.items with
      | nil => simp
      | cons x xs => simp [h]; exact sorted_cons_tail x xs (by rw [← h]; exact hS)
  · simp [step, hV]

theorem req_insert_effects : InsertEffects step := by
  intro s e hNotRej
  have hV := valid_of_not_rejected_insert s e hNotRej
  have hS : Sorted s.items := hV.1
  have hs1 : (step s (.insert e)).1 = .ok := by simp [step, hV]
  have hs2 : (step s (.insert e)).2.capacity = s.capacity := by simp [step, hV]
  obtain ⟨l₁, l₂, heq, hins, h1, h2⟩ := ins_split e s.items hS
  have hs3 : (step s (.insert e)).2.items = l₁ ++ e :: l₂ := by simp [step, hV, hins]
  exact ⟨hs1, hs2, l₁, l₂, heq, hs3, h1, h2⟩

theorem req_pop_effects : PopEffects step := by
  intro s hNotRej
  have hV := valid_of_not_rejected_pop s hNotRej
  cases hm : s.items with
  | nil =>
    have hne : s.items ≠ [] := hV.2
    rw [hm] at hne; contradiction
  | cons x xs =>
    have hsCap : (step s .pop).2.capacity = s.capacity := by simp [step, hV, hm]
    have hsGot : (step s .pop).1 = .got x := by simp [step, hV, hm]
    have hsItems : (step s .pop).2.items = xs := by simp [step, hV, hm]
    refine ⟨hsCap, [], x, xs, ?_, hsGot, hsItems, by simp, ?_⟩
    · simp [hm]
    · intro y hy; simp at hy

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op rest ih =>
    by_cases hV : Valid s op
    · cases op with
      | insert e =>
        have hOk : (step s (.insert e)).1 = .ok := by simp [step, hV]
        have hSorted : Sorted s.items := hV.1
        have hClassIns := classOf_ins e s.items hSorted p
        have hInflowOf : inflowOf ((.insert e), (step s (.insert e)).1) = [e] := by simp [inflowOf, hOk]
        have hOutflowOf : outflowOf ((.insert e), (step s (.insert e)).1) = [] := by simp [outflowOf, hOk]
        have hRunEq : run step s ((.insert e) :: rest) = (((.insert e), (step s (.insert e)).1) :: (run step (step s (.insert e)).2 rest).1, (run step (step s (.insert e)).2 rest).2) := by simp [run]
        have hStepItems : (step s (.insert e)).2.items = ins e s.items := step_insert_items s e hV
        have ih' : classOf p (ins e s.items) ++ classOf p (inflow (run step (step s (.insert e)).2 rest).1) = classOf p (outflow (run step (step s (.insert e)).2 rest).1) ++ classOf p (run step (step s (.insert e)).2 rest).2.items := by rw [← hStepItems]; exact ih _
        have hInflowCons : inflow (((.insert e), (step s (.insert e)).1) :: (run step (step s (.insert e)).2 rest).1) = [e] ++ inflow (run step (step s (.insert e)).2 rest).1 := by simp [inflow, hInflowOf]
        have hOutflowCons : outflow (((.insert e), (step s (.insert e)).1) :: (run step (step s (.insert e)).2 rest).1) = outflow (run step (step s (.insert e)).2 rest).1 := by simp [outflow, hOutflowOf]
        have hSing : classOf p [e] = if e.prio == p then [e] else [] := classOf_sing_eq p e
        have hInflowEq : inflow (run step s ((.insert e) :: rest)).1 = [e] ++ inflow (run step (step s (.insert e)).2 rest).1 := by rw [hRunEq, hInflowCons]
        have hOutflowEq : outflow (run step s ((.insert e) :: rest)).1 = outflow (run step (step s (.insert e)).2 rest).1 := by rw [hRunEq, hOutflowCons]
        have hFinalEq : (run step s ((.insert e) :: rest)).2 = (run step (step s (.insert e)).2 rest).2 := by rw [hRunEq]
        have lem1 : classOf p ([e] ++ inflow (run step (step s (.insert e)).2 rest).1) = classOf p [e] ++ classOf p (inflow (run step (step s (.insert e)).2 rest).1) := by simp [classOf]
        calc classOf p s.items ++ classOf p (inflow (run step s ((.insert e) :: rest)).1)
            = classOf p s.items ++ classOf p ([e] ++ inflow (run step (step s (.insert e)).2 rest).1) := by rw [hInflowEq]
          _ = classOf p s.items ++ (classOf p [e] ++ classOf p (inflow (run step (step s (.insert e)).2 rest).1)) := by rw [lem1]
          _ = (classOf p s.items ++ classOf p [e]) ++ classOf p (inflow (run step (step s (.insert e)).2 rest).1) := by rw [List.append_assoc]
          _ = (classOf p s.items ++ (if e.prio == p then [e] else [])) ++ classOf p (inflow (run step (step s (.insert e)).2 rest).1) := by rw [hSing]
          _ = classOf p (ins e s.items) ++ classOf p (inflow (run step (step s (.insert e)).2 rest).1) := by rw [hClassIns]
          _ = _ := ih'
          _ = classOf p (outflow (run step s ((.insert e) :: rest)).1) ++ classOf p (run step s ((.insert e) :: rest)).2.items := by rw [hOutflowEq, hFinalEq]
      | pop =>
        have hNe : s.items ≠ [] := hV.2
        obtain ⟨x, xs, hItems⟩ : ∃ x xs, s.items = x :: xs := by
          match hs : s.items with
          | [] => contradiction
          | x :: xs => exact ⟨x, xs, rfl⟩
        have hGotS : (step s .pop).1 = .got x := by simp [step, hV, hItems]
        have hNxtS : (step s .pop).2.items = xs := by simp [step, hV, hItems]
        have hInflowOf : inflowOf ((.pop), (step s .pop).1) = [] := by simp [inflowOf, hGotS]
        have hOutflowOf : outflowOf ((.pop), (step s .pop).1) = [x] := by simp [outflowOf, hGotS]
        have hRunEqS : run step s (.pop :: rest) = ((.pop, (step s .pop).1) :: (run step (step s .pop).2 rest).1, (run step (step s .pop).2 rest).2) := by simp [run]
        have ihS : classOf p xs ++ classOf p (inflow (run step (step s .pop).2 rest).1) = classOf p (outflow (run step (step s .pop).2 rest).1) ++ classOf p (run step (step s .pop).2 rest).2.items := by
          have := ih (step s .pop).2
          rw [hNxtS] at this
          exact this
        have hInflowEq : inflow (run step s (.pop :: rest)).1 = inflow (run step (step s .pop).2 rest).1 := by rw [hRunEqS]; simp [inflow, hInflowOf]
        have hOutflowEq : outflow (run step s (.pop :: rest)).1 = [x] ++ outflow (run step (step s .pop).2 rest).1 := by rw [hRunEqS]; simp [outflow, hOutflowOf]
        have hFinalEq : (run step s (.pop :: rest)).2 = (run step (step s .pop).2 rest).2 := by rw [hRunEqS]
        calc classOf p s.items ++ classOf p (inflow (run step s (.pop :: rest)).1)
            = classOf p (x :: xs) ++ classOf p (inflow (run step (step s .pop).2 rest).1) := by rw [hItems, hInflowEq]
          _ = (classOf p [x] ++ classOf p xs) ++ classOf p (inflow (run step (step s .pop).2 rest).1) := by simp [classOf]
          _ = classOf p [x] ++ (classOf p xs ++ classOf p (inflow (run step (step s .pop).2 rest).1)) := by rw [List.append_assoc]
          _ = classOf p [x] ++ (classOf p (outflow (run step (step s .pop).2 rest).1) ++ classOf p (run step (step s .pop).2 rest).2.items) := by rw [ihS]
          _ = (classOf p [x] ++ classOf p (outflow (run step (step s .pop).2 rest).1)) ++ classOf p (run step (step s .pop).2 rest).2.items := by rw [List.append_assoc]
          _ = classOf p (x :: outflow (run step (step s .pop).2 rest).1) ++ classOf p (run step (step s .pop).2 rest).2.items := by simp [classOf]
          _ = classOf p (outflow (run step s (.pop :: rest)).1) ++ classOf p (run step s (.pop :: rest)).2.items := by rw [hOutflowEq, hFinalEq]; simp [classOf]
    · have hRej : step s op = (.rejected, s) := by simp [step, hV]
      have hFst : (step s op).1 = .rejected := by rw [hRej]
      have hSnd : (step s op).2 = s := by rw [hRej]
      have hInflowOf : inflowOf (op, (step s op).1) = [] := by simp [inflowOf, hFst]
      have hOutflowOf : outflowOf (op, (step s op).1) = [] := by simp [outflowOf, hFst]
      have hRunEq : run step s (op :: rest) = ((op, (step s op).1) :: (run step (step s op).2 rest).1, (run step (step s op).2 rest).2) := by simp [run]
      have hEq1 : inflow (run step s (op :: rest)).1 = inflow (run step s rest).1 := by rw [hRunEq, hSnd]; simp [inflow, hInflowOf]
      have hEq2 : outflow (run step s (op :: rest)).1 = outflow (run step s rest).1 := by rw [hRunEq, hSnd]; simp [outflow, hOutflowOf]
      have hEq3 : (run step s (op :: rest)).2 = (run step s rest).2 := by rw [hRunEq, hSnd]
      rw [hEq1, hEq2, hEq3]; exact ih s

end PrioQueue
