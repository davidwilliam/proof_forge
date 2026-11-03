import PrioQueue.Spec
namespace PrioQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid Sorted <;> infer_instance

def ins (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs => if e.prio < x.prio then e :: x :: xs else x :: ins e xs

def step : Impl := fun s op =>
  if _h : Valid s op then
    match op with
    | .insert e => (.ok, { s with items := ins e s.items })
    | .pop =>
      match s.items with
      | [] => (.rejected, s)
      | x :: xs => (.got x, { s with items := xs })
  else (.rejected, s)

theorem ins_len (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih => simp only [ins]; split <;> simp [ih]

theorem ins_mem (e : Entry) (l : List Entry) (y : Entry) (h : y ∈ ins e l) : y = e ∨ y ∈ l := by
  induction l with
  | nil => simp [ins] at h; exact Or.inl h
  | cons x xs ih =>
    simp only [ins] at h
    by_cases hc : e.prio < x.prio
    · simp [hc] at h; rcases h with rfl | h2
      · left; rfl
      · rcases h2 with rfl | h3
        · right; exact List.Mem.head _
        · right; exact List.Mem.tail _ h3
    · simp [hc] at h; rcases h with rfl | h2
      · right; exact List.Mem.head _
      · rcases ih h2 with h3 | h3
        · left; exact h3
        · right; exact List.Mem.tail _ h3

theorem ins_sorted (e : Entry) (l : List Entry) (h : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil => simp [ins, Sorted]
  | cons x xs ih =>
    have hSortedXs : Sorted xs := (List.pairwise_cons.mp h).2
    have hForall : ∀ y ∈ xs, x.prio ≤ y.prio := (List.pairwise_cons.mp h).1
    simp only [ins]; split
    · next hlt =>
      have hle : e.prio ≤ x.prio := Nat.le_of_lt hlt
      rw [Sorted, List.pairwise_cons]
      constructor
      · intro y hy; simp at hy; rcases hy with rfl | hy
        · exact hle
        · exact Nat.le_trans hle (hForall y hy)
      · exact h
    · next hge =>
      have hle_ex : x.prio ≤ e.prio := Nat.le_of_not_gt hge
      have ihS := ih hSortedXs
      rw [Sorted, List.pairwise_cons]
      constructor
      · intro y hy
        rcases ins_mem e xs y hy with rfl | hin
        · exact hle_ex
        · exact hForall y hin
      · exact ihS

theorem ins_split (e : Entry) (l : List Entry) (hS : Sorted l) :
  ∃ l1 l2, l = l1 ++ l2 ∧ ins e l = l1 ++ e :: l2 ∧ (∀ x ∈ l1, x.prio ≤ e.prio) ∧ (∀ x ∈ l2, e.prio < x.prio) := by
  induction l with
  | nil => exact ⟨[], [], by simp, by simp [ins], by simp, by simp⟩
  | cons x xs ih =>
    have hSortedXs : Sorted xs := (List.pairwise_cons.mp hS).2
    have hForall : ∀ y ∈ xs, x.prio ≤ y.prio := (List.pairwise_cons.mp hS).1
    rcases ih hSortedXs with ⟨l1', l2', hEq, hInsEq, hLe1, hLt2⟩
    by_cases hc : e.prio < x.prio
    · refine ⟨[], x :: xs, by simp, ?_, by simp, ?_⟩
      · simp [ins, hc]
      · intro y hy; simp at hy; rcases hy with rfl | hy2
        · exact hc
        · exact Nat.lt_of_lt_of_le hc (hForall y hy2)
    · have hxle : x.prio ≤ e.prio := Nat.le_of_not_gt hc
      have hInsCons : ins e (x :: xs) = x :: ins e xs := by simp [ins, hc]
      refine ⟨x :: l1', l2', ?_, ?_, ?_, hLt2⟩
      · calc x :: xs = x :: (l1' ++ l2') := by rw [hEq]
          _ = (x :: l1') ++ l2' := by simp
      · calc ins e (x :: xs) = x :: ins e xs := hInsCons
          _ = x :: (l1' ++ e :: l2') := by rw [hInsEq]
          _ = (x :: l1') ++ e :: l2' := by simp
      · intro y hy; simp at hy; rcases hy with rfl | hy2
        · exact hxle
        · exact hLe1 y hy2

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV; unfold step; simp [hV]
  cases op with
  | insert e => simp
  | pop =>
    have hne : s.items ≠ [] := hV.2
    match h : s.items with
    | [] => exact absurd h hne
    | _ :: _ => simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv; unfold step; simp [hInv]

theorem req_capacity : CapacityBound step := by
  intro s op hle; by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have hStep : step s (Op.insert e) = (.ok, { s with items := ins e s.items }) := by unfold step; simp [hV]
      have hcap : (step s (Op.insert e)).2.capacity = s.capacity := by rw [hStep]
      have hlen : (step s (Op.insert e)).2.items.length = s.items.length + 1 := by rw [hStep]; exact ins_len _ _
      have hlt : s.items.length < s.capacity := hV.2
      rw [hcap, hlen]; omega
    | pop =>
      cases hitems : s.items with
      | nil => have hne : s.items ≠ [] := hV.2; exact absurd hitems hne
      | cons hd tl =>
        have hStep : step s Op.pop = (.got hd, { s with items := tl }) := by unfold step; simp [hV, hitems]
        have h2cap : (step s Op.pop).2.capacity = s.capacity := by rw [hStep]
        have h2items : (step s Op.pop).2.items = tl := by rw [hStep]
        rw [h2cap, h2items]
        have hlen : s.items.length = tl.length + 1 := by simp [hitems]
        omega
  · have h : step s op = (.rejected, s) := by unfold step; simp [hV]
    rw [h]; exact hle

theorem req_pop_min : PopMin step := by
  intro s hNot; unfold step at hNot; by_cases hV : Valid s Op.pop
  · cases hxs : s.items with
    | nil => have hne : s.items ≠ [] := hV.2; exact absurd hxs hne
    | cons hd tl =>
      have hStep : step s Op.pop = (.got hd, { s with items := tl }) := by unfold step; simp [hV, hxs]
      refine ⟨hd, by simp [hStep], ?_⟩
      intro x hx; have hEq : (step s Op.pop).2.items = tl := by simp [hStep]
      rw [hEq] at hx
      have hSorted : Sorted (hd :: tl) := by rw [← hxs]; exact hV.1
      exact (List.pairwise_cons.mp hSorted).1 x hx
  · simp [hV] at hNot

theorem req_sorted : KeepsSorted step := by
  intro s op hSort; unfold step; by_cases hV : Valid s op
  · simp [hV]; cases op with
    | insert e => exact ins_sorted e s.items hSort
    | pop =>
      cases hitems : s.items with
      | nil => exact hSort
      | cons hd tl => simp [hitems]; exact (List.pairwise_cons.mp (hitems ▸ hSort)).2
  · simp [hV]; exact hSort

theorem req_insert_effects : InsertEffects step := by
  intro s e hNot; unfold step at hNot; by_cases hV : Valid s (Op.insert e)
  · have hStepEq : step s (Op.insert e) = (.ok, { s with items := ins e s.items }) := by unfold step; simp [hV]
    have hOk : (step s (Op.insert e)).1 = .ok := by rw [hStepEq]
    have hCap : (step s (Op.insert e)).2.capacity = s.capacity := by rw [hStepEq]
    have hItems : (step s (Op.insert e)).2.items = ins e s.items := by rw [hStepEq]
    refine ⟨hOk, hCap, ?_⟩
    rcases ins_split e s.items hV.1 with ⟨l1, l2, hEq, hIns, hLe, hLt⟩
    exact ⟨l1, l2, hEq, by rw [hItems, hIns], hLe, hLt⟩
  · simp [hV] at hNot

theorem req_pop_effects : PopEffects step := by
  intro s hNot; by_cases hV : Valid s Op.pop
  · cases hItems : s.items with
    | nil => have hne : s.items ≠ [] := hV.2; exact absurd hItems hne
    | cons hd tl =>
      have hStep : step s Op.pop = (.got hd, { s with items := tl }) := by unfold step; simp [hV, hItems]
      refine ⟨by simp [hStep], [], hd, tl, by simp [hItems], by simp [hStep], by simp [hStep], ?_, ?_⟩
      · intro x hx; simp at hx
      · intro x hx; have hSorted : Sorted (hd :: tl) := by rw [← hItems]; exact hV.1
        exact (List.pairwise_cons.mp hSorted).1 x hx
  · have hEq : step s Op.pop = (.rejected, s) := by unfold step; simp [hV]
    rw [hEq] at hNot; simp at hNot

-- FIFO helpers
theorem classOf_append (p : Nat) (l1 l2 : List Entry) : classOf p (l1 ++ l2) = classOf p l1 ++ classOf p l2 := by
  unfold classOf; rw [List.filter_append]

theorem classOf_nil (p : Nat) : classOf p [] = [] := by unfold classOf; simp

theorem beq_eq_decide (a b : Nat) : (a == b) = decide (a = b) := by
  induction a generalizing b with
  | zero => cases b <;> rfl
  | succ a ih => cases b with
    | zero => rfl
    | succ b => simp [ih]

theorem ins_classOf (e : Entry) (l : List Entry) (hS : Sorted l) (p : Nat) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := by
  induction l with
  | nil => simp [ins, classOf]
  | cons x xs ih =>
    have hSortedXs : Sorted xs := (List.pairwise_cons.mp hS).2
    have hForall : ∀ y ∈ xs, x.prio ≤ y.prio := (List.pairwise_cons.mp hS).1
    have ih' := ih hSortedXs
    simp only [ins]
    by_cases hc : e.prio < x.prio
    · simp only [if_pos hc]
      have hNo : ∀ y ∈ x :: xs, y.prio ≠ e.prio := by
        intro y hy; simp at hy; rcases hy with rfl | hy
        · omega
        · have hle : x.prio ≤ y.prio := hForall y hy; omega
      have rew : ∀ a : Entry, (a.prio == p) = decide (a.prio = p) := fun a => beq_eq_decide _ _
      simp only [classOf, rew]
      by_cases hp : e.prio = p
      · have hx_ne : decide (x.prio = p) = false := by
          simp; intro heq; exact hNo x (List.Mem.head _) (heq ▸ hp.symm)
        have hfilter_xs : List.filter (fun a => decide (a.prio = p)) xs = [] := by
          rw [List.filter_eq_nil_iff]; intro y hy; simp; intro heq; exact hNo y (List.Mem.tail _ hy) (heq ▸ hp.symm)
        simp [hp, hx_ne, hfilter_xs]
      · have heq_false : decide (e.prio = p) = false := by simp [hp]
        simp [heq_false]
    · simp only [if_neg hc]
      have hEq1 : classOf p (x :: ins e xs) = classOf p [x] ++ classOf p (ins e xs) := by
        calc classOf p (x :: ins e xs) = classOf p ([x] ++ ins e xs) := by simp
          _ = classOf p [x] ++ classOf p (ins e xs) := classOf_append _ _ _
      have hEq2 : classOf p (x :: xs) = classOf p [x] ++ classOf p xs := by
        calc classOf p (x :: xs) = classOf p ([x] ++ xs) := by simp
          _ = classOf p [x] ++ classOf p xs := classOf_append _ _ _
      rw [hEq1, ih', hEq2, List.append_assoc]

theorem step_fifo_aux (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
    classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  by_cases hV : Valid s op
  · cases op with
    | insert e =>
      have hStep : step s (Op.insert e) = (.ok, { s with items := ins e s.items }) := by unfold step; simp [hV]
      have hOut : (step s (Op.insert e)).1 = .ok := by rw [hStep]
      have hSt : (step s (Op.insert e)).2.items = ins e s.items := by rw [hStep]
      have h1 : inflowOf (Op.insert e, (step s (Op.insert e)).1) = [e] := by
        have : inflowOf (Op.insert e, Outcome.ok) = [e] := by unfold inflowOf; rfl
        rw [hOut]; exact this
      have h2 : outflowOf (Op.insert e, (step s (Op.insert e)).1) = [] := by
        have : outflowOf (Op.insert e, Outcome.ok) = ([] : List Entry) := by unfold outflowOf; rfl
        rw [hOut]; exact this
      rw [h1, h2, hSt]; simp only [classOf_nil, List.append_nil]
      have hS : Sorted s.items := hV.1
      exact (ins_classOf e s.items hS p).symm
    | pop =>
      cases hitems : s.items with
      | nil => have hne : s.items ≠ [] := hV.2; exact absurd hitems hne
      | cons hd tl =>
        have hStep : step s Op.pop = (.got hd, { s with items := tl }) := by unfold step; simp [hV, hitems]
        have hOut : (step s Op.pop).1 = .got hd := by rw [hStep]
        have hSt : (step s Op.pop).2.items = tl := by rw [hStep]
        have h1 : inflowOf (Op.pop, (step s Op.pop).1) = ([] : List Entry) := by
          have : inflowOf (Op.pop, Outcome.got hd) = ([] : List Entry) := by unfold inflowOf; rfl
          rw [hOut]; exact this
        have h2 : outflowOf (Op.pop, (step s Op.pop).1) = [hd] := by
          have : outflowOf (Op.pop, Outcome.got hd) = [hd] := by unfold outflowOf; rfl
          rw [hOut]; exact this
        rw [h1, h2, hSt]
        simp only [classOf_nil, List.append_nil]
        have hEq : classOf p (hd :: tl) = classOf p [hd] ++ classOf p tl := by
          have : classOf p (hd :: tl) = classOf p ([hd] ++ tl) := by simp
          rw [this, classOf_append]
        rw [hEq]
  · have hStep : step s op = (.rejected, s) := by unfold step; simp [hV]
    have hOut : (step s op).1 = .rejected := by rw [hStep]
    have hSt : (step s op).2 = s := by rw [hStep]
    have h1 : inflowOf (op, (step s op).1) = [] := by rw [hOut]; cases op <;> rfl
    have h2 : outflowOf (op, (step s op).1) = [] := by rw [hOut]; cases op <;> rfl
    rw [h1, h2, hSt]
    simp only [classOf_nil, List.append_nil, List.nil_append]

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow, classOf_nil]
  | cons op ops ih =>
    have hRunUnfold : run step s (op :: ops) =
        ((op, (step s op).1) :: (run step (step s op).2 ops).1, (run step (step s op).2 ops).2) := by simp [run]
    simp only [hRunUnfold]
    have hInflowEq : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) =
        inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by unfold inflow; simp
    have hOutflowEq : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) =
        outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by unfold outflow; simp
    have hClassInflow : classOf p (inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)) =
        classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [hInflowEq, classOf_append]
    have hClassOutflow : classOf p (outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)) =
        classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1) := by rw [hOutflowEq, classOf_append]
    have ihEq := ih (s := (step s op).2)
    have hStepFifo := step_fifo_aux s op p
    calc classOf p s.items ++ classOf p (inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1))
        = classOf p s.items ++ (classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops).1)) := by rw [hClassInflow]
      _ = (classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items) ++ classOf p (inflow (run step (step s op).2 ops).1) := by rw [hStepFifo]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (step s op).2.items ++ classOf p (inflow (run step (step s op).2 ops).1)) := by rw [List.append_assoc]
      _ = classOf p (outflowOf (op, (step s op).1)) ++ (classOf p (outflow (run step (step s op).2 ops).1) ++ classOf p (run step (step s op).2 ops).2.items) := by rw [ihEq]
      _ = (classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops).1)) ++ classOf p (run step (step s op).2 ops).2.items := by rw [List.append_assoc]
      _ = classOf p (outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)) ++ classOf p (run step (step s op).2 ops).2.items := by rw [← hClassOutflow]

end PrioQueue
