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
    | .insert e => (.ok, { capacity := s.capacity, items := ins e s.items })
    | .pop =>
      match s.items with
      | [] => (.rejected, s)
      | x :: xs => (.got x, { capacity := s.capacity, items := xs })
  else (.rejected, s)

private theorem step_of_not_valid {s : State} {op : Op} (hv : ¬ Valid s op) : step s op = (.rejected, s) := by
  unfold step; simp [hv]

private theorem step_of_valid_insert {s : State} {e : Entry} (hv : Valid s (.insert e)) :
    step s (.insert e) = (.ok, { capacity := s.capacity, items := ins e s.items }) := by
  unfold step; simp [hv]

private theorem step_of_valid_pop {s : State} {x : Entry} {xs : List Entry}
    (hv : Valid s .pop) (hs : s.items = x :: xs) :
    step s .pop = (.got x, { capacity := s.capacity, items := xs }) := by
  unfold step; simp [hv, hs]

private theorem ins_length (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    by_cases h : e.prio < x.prio
    · simp [ins, h]
    · simp [ins, h, ih]

private theorem mem_ins_aux (e : Entry) (l : List Entry) :
    ∀ y, y ∈ ins e l ↔ y = e ∨ y ∈ l := by
  induction l with
  | nil =>
    intro y; simp [ins]
  | cons x xs ih =>
    intro y
    by_cases h : e.prio < x.prio
    · have heq : ins e (x :: xs) = e :: x :: xs := by simp [ins, h]
      rw [heq]
      simp only [List.mem_cons]
      constructor
      · intro hy
        rcases hy with rfl | hy
        · left; rfl
        · rcases hy with rfl | hy
          · right; left; rfl
          · right; right; exact hy
      · intro hy
        rcases hy with rfl | hy
        · left; rfl
        · rcases hy with rfl | hy
          · right; left; rfl
          · right; right; exact hy
    · have heq : ins e (x :: xs) = x :: ins e xs := by simp [ins, h]
      rw [heq, List.mem_cons, ih y, List.mem_cons]
      constructor
      · intro hy
        rcases hy with rfl | hy
        · right; left; rfl
        · rcases hy with rfl | hy
          · left; rfl
          · right; right; exact hy
      · intro hy
        rcases hy with rfl | hy
        · right; left; rfl
        · rcases hy with rfl | hy
          · left; rfl
          · right; right; exact hy

private theorem sorted_pairwise_cons {a : Entry} {l : List Entry} :
    Sorted (a :: l) → Sorted l := by
  intro h; cases h; assumption

private theorem sorted_head_le {a : Entry} {l : List Entry} :
    Sorted (a :: l) → ∀ x ∈ l, a.prio ≤ x.prio := by
  intro h x hx; cases h with
  | cons h1 _ => exact h1 x hx

private theorem ins_sorted (e : Entry) (l : List Entry) (hs : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil =>
    exact List.Pairwise.cons (fun y hy => by simp at hy) List.Pairwise.nil
  | cons x xs ih =>
    by_cases hlt : e.prio < x.prio
    · have heq : ins e (x :: xs) = e :: x :: xs := by simp [ins, hlt]
      rw [heq]
      apply List.Pairwise.cons
      · intro y hy
        have hy' : y = x ∨ y ∈ xs := by simpa using hy
        rcases hy' with rfl | hy2
        · exact Nat.le_of_lt hlt
        · exact Nat.le_trans (Nat.le_of_lt hlt) (sorted_head_le hs y hy2)
      · exact hs
    · have heq : ins e (x :: xs) = x :: ins e xs := by simp [ins, hlt]
      rw [heq]
      have hs' : Sorted xs := sorted_pairwise_cons hs
      have ih' := ih hs'
      apply List.Pairwise.cons
      · intro y hy
        have hy' := (mem_ins_aux e xs y).mp hy
        rcases hy' with rfl | hy2
        · exact Nat.le_of_not_gt hlt
        · exact sorted_head_le hs y hy2
      · exact ih'

private theorem ins_exists_split (e : Entry) (l : List Entry) (hs : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧ (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil => exact ⟨[], [], by simp, by simp [ins], by simp, by simp⟩
  | cons x xs ih =>
    have hs' : Sorted xs := sorted_pairwise_cons hs
    have hhead_le : ∀ y ∈ xs, x.prio ≤ y.prio := fun y hy => sorted_head_le hs y hy
    by_cases hlt : e.prio < x.prio
    · have heq : ins e (x :: xs) = e :: x :: xs := by simp [ins, hlt]
      refine ⟨[], x :: xs, by simp, ?_, by simp, ?_⟩
      · simp [heq]
      · intro y hy; simp at hy; rcases hy with rfl | hy2
        · exact hlt
        · exact Nat.lt_of_lt_of_le hlt (hhead_le y hy2)
    · have heq : ins e (x :: xs) = x :: ins e xs := by simp [ins, hlt]
      have hle : x.prio ≤ e.prio := Nat.le_of_not_gt hlt
      obtain ⟨l₁, l₂, hl, hins, h1, h2⟩ := ih hs'
      refine ⟨x :: l₁, l₂, ?_, ?_, ?_, h2⟩
      · simp [hl]
      · rw [heq, hins, List.cons_append]
      · intro y hy; simp at hy; rcases hy with rfl | hy2
        · exact hle
        · exact h1 y hy2

private theorem classOf_append (p : Nat) (a b : List Entry) : classOf p (a ++ b) = classOf p a ++ classOf p b := by
  simp [classOf, List.filter_append]

private theorem classOf_singleton (p : Nat) (e : Entry) :
    classOf p [e] = if e.prio == p then [e] else [] := by
  unfold classOf; simp only [List.filter_cons, List.filter_nil]
  by_cases h : e.prio == p <;> simp [h]

private theorem classOf_cons_append_eq (p : Nat) (x : Entry) (xs : List Entry) :
    classOf p (x :: xs) = classOf p [x] ++ classOf p xs := by
  have : x :: xs = [x] ++ xs := by simp
  rw [this, classOf_append]

private theorem classOf_nil_of_gt {p : Nat} {l : List Entry} {e : Entry}
    (h : ∀ y ∈ l, e.prio < y.prio) (he : e.prio == p) : classOf p l = [] := by
  unfold classOf
  apply List.filter_eq_nil_iff.mpr
  intro y hy
  have hlt : e.prio < y.prio := h y hy
  have heq : e.prio = p := of_decide_eq_true he
  simp [beq_iff_eq] at *
  omega

private theorem classOf_ins (p : Nat) (e : Entry) (l : List Entry) (hs : Sorted l) :
    classOf p (ins e l) = if e.prio == p then classOf p l ++ [e] else classOf p l := by
  obtain ⟨l₁, l₂, hl, hins, _, hlt2⟩ := ins_exists_split e l hs
  have hl_class : classOf p l = classOf p l₁ ++ classOf p l₂ := by rw [hl, classOf_append]
  have hins_class : classOf p (ins e l) = classOf p l₁ ++ classOf p [e] ++ classOf p l₂ := by
    calc classOf p (ins e l) = classOf p (l₁ ++ e :: l₂) := by rw [hins]
      _ = classOf p l₁ ++ classOf p (e :: l₂) := classOf_append p l₁ (e :: l₂)
      _ = classOf p l₁ ++ (classOf p [e] ++ classOf p l₂) := by rw [classOf_cons_append_eq p e l₂]
      _ = classOf p l₁ ++ classOf p [e] ++ classOf p l₂ := by rw [List.append_assoc]
  rw [hins_class, classOf_singleton, hl_class]
  by_cases he : e.prio == p
  · have hnil : classOf p l₂ = [] := classOf_nil_of_gt (p:=p) (e:=e) hlt2 he
    simp [he, hnil]
  · simp [he]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hv; unfold step; simp [hv]
  cases op with
  | insert e => simp
  | pop => cases hs : s.items with | nil => unfold Valid at hv; simp [hs] at hv | cons x xs => simp [hs]

theorem req_invalid_noop : InvalidNoop step := by intro s op hv; exact step_of_not_valid hv

theorem req_capacity : CapacityBound step := by
  intro s op hle; by_cases hv : Valid s op
  · cases op with
    | insert e =>
      have hst := step_of_valid_insert (s:=s) (e:=e) hv
      simp only [hst]
      have hlen : (ins e s.items).length = s.items.length + 1 := ins_length e s.items
      have hcap : s.items.length < s.capacity := by unfold Valid at hv; exact hv.2
      omega
    | pop =>
      cases hs : s.items with
      | nil => unfold Valid at hv; simp [hs] at hv
      | cons x xs =>
        have hst := step_of_valid_pop hv hs
        simp only [hst]
        have hlen : s.items.length = xs.length + 1 := by simp [hs]
        omega
  · have hst := step_of_not_valid hv; simp [hst, hle]

theorem req_pop_min : PopMin step := by
  intro s h
  have hv : Valid s .pop := by
    by_cases hv : Valid s .pop
    · exact hv
    · exfalso; have hst := step_of_not_valid hv; simp [hst] at h
  cases hs : s.items with
  | nil => unfold Valid at hv; simp [hs] at hv
  | cons x xs =>
    have hst := step_of_valid_pop hv hs
    refine ⟨x, ?_, ?_⟩
    · simp [hst]
    · intro y hy; simp only [hst] at hy
      have hsrt : Sorted (x :: xs) := by rw [← hs]; exact hv.1
      exact sorted_head_le hsrt y hy

theorem req_sorted : KeepsSorted step := by
  intro s op hs; by_cases hv : Valid s op
  · cases op with
    | insert e => have hst := step_of_valid_insert hv; simp only [hst]; exact ins_sorted e s.items hs
    | pop => cases hs2 : s.items with | nil => unfold Valid at hv; simp [hs2] at hv | cons x xs => have hst := step_of_valid_pop hv hs2; simp only [hst]; exact sorted_pairwise_cons (hs2 ▸ hs)
  · have hst := step_of_not_valid hv; simp [hst, hs]

theorem req_insert_effects : InsertEffects step := by
  intro s e h
  have hv : Valid s (.insert e) := by
    by_cases hv : Valid s (.insert e)
    · exact hv
    · exfalso; have hst := step_of_not_valid hv; simp [hst] at h
  have hst := step_of_valid_insert hv
  refine ⟨?_, ?_, ?_⟩
  · simp [hst]
  · simp [hst]
  · have hs : Sorted s.items := hv.1
    obtain ⟨l₁, l₂, hl, hins, h1, h2⟩ := ins_exists_split e s.items hs
    refine ⟨l₁, l₂, hl, ?_, h1, h2⟩
    have hitems : (step s (.insert e)).2.items = ins e s.items := by simp [hst]
    rw [hitems, hins]

theorem req_pop_effects : PopEffects step := by
  intro s h
  have hv : Valid s .pop := by
    by_cases hv : Valid s .pop
    · exact hv
    · exfalso; have hst := step_of_not_valid hv; simp [hst] at h
  cases hs : s.items with
  | nil => unfold Valid at hv; simp [hs] at hv
  | cons x xs =>
    have hst := step_of_valid_pop hv hs
    refine ⟨?_, ?_⟩
    · simp [hst]
    · refine ⟨[], x, xs, by simp [hs], by simp [hst], by simp [hst], by simp, ?_⟩
      intro y hy
      have hsrt : Sorted (x :: xs) := by rw [← hs]; exact hv.1
      exact sorted_head_le hsrt y hy

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  induction ops generalizing s with
  | nil =>
    simp only [run, inflow, outflow, List.flatMap]
    simp [classOf]
  | cons op rest ih =>
    by_cases hv : Valid s op
    · cases op with
      | insert e =>
        have hst : step s (.insert e) = (.ok, { capacity := s.capacity, items := ins e s.items }) := step_of_valid_insert hv
        have hrun : run step s (Op.insert e :: rest) =
          ((Op.insert e, Outcome.ok) :: (run step { capacity := s.capacity, items := ins e s.items } rest).1,
           (run step { capacity := s.capacity, items := ins e s.items } rest).2) := by simp [run, hst]
        have h_inflow : inflow ((Op.insert e, Outcome.ok) :: (run step { capacity := s.capacity, items := ins e s.items } rest).1)
          = [e] ++ inflow (run step { capacity := s.capacity, items := ins e s.items } rest).1 := by simp [inflow, inflowOf]
        have h_outflow : outflow ((Op.insert e, Outcome.ok) :: (run step { capacity := s.capacity, items := ins e s.items } rest).1)
          = outflow (run step { capacity := s.capacity, items := ins e s.items } rest).1 := by simp [outflow, outflowOf]
        have hc := classOf_ins (p:=p) (e:=e) (l:=s.items) hv.1
        have ih' := ih { capacity := s.capacity, items := ins e s.items }
        have goal_left : classOf p s.items ++ classOf p (inflow (run step s (Op.insert e :: rest)).1) =
            classOf p s.items ++ (classOf p [e] ++ classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } rest).1)) := by
          rw [hrun, h_inflow, classOf_append]
        have goal_right : classOf p (outflow (run step s (Op.insert e :: rest)).1) ++ classOf p (run step s (Op.insert e :: rest)).2.items =
            classOf p (outflow (run step { capacity := s.capacity, items := ins e s.items } rest).1) ++ classOf p (run step { capacity := s.capacity, items := ins e s.items } rest).2.items := by
          rw [hrun, h_outflow]
        rw [goal_left, goal_right, classOf_singleton]
        have h1 : classOf p s.items ++ ((if e.prio == p then [e] else []) ++ classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } rest).1))
            = (classOf p s.items ++ if e.prio == p then [e] else []) ++ classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } rest).1) := by
          rw [List.append_assoc]
        rw [h1]
        have h2 : classOf p s.items ++ (if e.prio == p then [e] else []) = classOf p (ins e s.items) := by
          rw [hc]; by_cases he : e.prio == p <;> simp [he]
        rw [h2]
        exact ih'
      | pop =>
        cases hs : s.items with
        | nil => unfold Valid at hv; simp [hs] at hv
        | cons x xs =>
          have hst : step s .pop = (.got x, { capacity := s.capacity, items := xs }) := step_of_valid_pop hv hs
          have hrun : run step s (Op.pop :: rest) =
            ((Op.pop, Outcome.got x) :: (run step { capacity := s.capacity, items := xs } rest).1,
             (run step { capacity := s.capacity, items := xs } rest).2) := by simp [run, hst]
          have hIEq : inflow (run step s (Op.pop :: rest)).1 = inflow (run step { capacity := s.capacity, items := xs } rest).1 := by
            rw [hrun]; simp [inflow, inflowOf]
          have hOEq : outflow (run step s (Op.pop :: rest)).1 = [x] ++ outflow (run step { capacity := s.capacity, items := xs } rest).1 := by
            rw [hrun]; simp [outflow, outflowOf]
          have hSEq : (run step s (Op.pop :: rest)).2 = (run step { capacity := s.capacity, items := xs } rest).2 := by
            rw [hrun]
          have ih' := ih { capacity := s.capacity, items := xs }
          have hcx : classOf p (x :: xs) = classOf p [x] ++ classOf p xs := classOf_cons_append_eq p x xs
          have hco : classOf p ([x] ++ outflow (run step { capacity := s.capacity, items := xs } rest).1) = classOf p [x] ++ classOf p (outflow (run step { capacity := s.capacity, items := xs } rest).1) := classOf_append p [x] _
          calc classOf p (x :: xs) ++ classOf p (inflow (run step s (Op.pop :: rest)).1)
              = (classOf p [x] ++ classOf p xs) ++ classOf p (inflow (run step { capacity := s.capacity, items := xs } rest).1) := by rw [hcx, hIEq]
            _ = classOf p [x] ++ (classOf p xs ++ classOf p (inflow (run step { capacity := s.capacity, items := xs } rest).1)) := by rw [List.append_assoc]
            _ = classOf p [x] ++ (classOf p (outflow (run step { capacity := s.capacity, items := xs } rest).1) ++ classOf p (run step { capacity := s.capacity, items := xs } rest).2.items) := by rw [ih']
            _ = (classOf p [x] ++ classOf p (outflow (run step { capacity := s.capacity, items := xs } rest).1)) ++ classOf p (run step { capacity := s.capacity, items := xs } rest).2.items := by rw [List.append_assoc]
            _ = classOf p ([x] ++ outflow (run step { capacity := s.capacity, items := xs } rest).1) ++ classOf p (run step { capacity := s.capacity, items := xs } rest).2.items := by rw [← hco]
            _ = classOf p (outflow (run step s (Op.pop :: rest)).1) ++ classOf p (run step s (Op.pop :: rest)).2.items := by rw [hOEq, hSEq]
    · have hstep : step s op = (.rejected, s) := step_of_not_valid hv
      have hrun : run step s (op :: rest) = ((op, .rejected) :: (run step s rest).1, (run step s rest).2) := by simp [run, hstep]
      rw [hrun]
      have h_inflow : inflow ((op, (Outcome.rejected : Outcome)) :: (run step s rest).1) = inflow (run step s rest).1 := by cases op <;> simp [inflow, inflowOf]
      have h_outflow : outflow ((op, (Outcome.rejected : Outcome)) :: (run step s rest).1) = outflow (run step s rest).1 := by cases op <;> simp [outflow, outflowOf]
      rw [h_inflow, h_outflow]; exact ih _

end PrioQueue
