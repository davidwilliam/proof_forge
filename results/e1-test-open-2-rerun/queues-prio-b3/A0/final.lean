import PrioQueue.Spec
namespace PrioQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op with
  | insert e => unfold Valid Sorted; infer_instance
  | pop => unfold Valid Sorted; infer_instance

def ins (e : Entry) : List Entry -> List Entry
  | [] => [e]
  | x :: xs => if e.prio < x.prio then e :: x :: xs else x :: ins e xs

theorem ins_length (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih => simp only [ins]; split <;> simp [ih]

theorem sorted_pairwise_cons {a : Entry} {l : List Entry} (h : Sorted (a :: l)) : Sorted l := by
  cases h with | cons _ ht => exact ht

theorem sorted_le_of_mem : ∀ (l : List Entry) (a x : Entry), Sorted (a :: l) → x ∈ l → a.prio ≤ x.prio := by
  intro l
  induction l with
  | nil => intro a x h hm; simp at hm
  | cons y ys ih =>
    intro a x h hm
    have ha_y : a.prio ≤ y.prio := by cases h with | cons ha _ => exact ha y (by simp)
    have htail : Sorted (y :: ys) := sorted_pairwise_cons h
    simp at hm
    rcases hm with rfl | hm'
    · exact ha_y
    · have hy_x : y.prio ≤ x.prio := ih y x htail hm'
      omega

theorem sorted_head_le {a x : Entry} {l : List Entry} (h : Sorted (a :: l)) (hmem : x ∈ l) : a.prio ≤ x.prio :=
  sorted_le_of_mem l a x h hmem

theorem exists_split_ins (e : Entry) (l : List Entry) (hs : Sorted l) :
    ∃ l1 l2, l = l1 ++ l2 ∧ ins e l = l1 ++ e :: l2 ∧ (∀ x ∈ l1, x.prio ≤ e.prio) ∧ (∀ x ∈ l2, e.prio < x.prio) := by
  induction l with
  | nil => exact ⟨[], [], rfl, rfl, by intro x hx; simp at hx, by intro x hx; simp at hx⟩
  | cons x xs ih =>
    have hxs_sorted : Sorted xs := sorted_pairwise_cons hs
    by_cases hlt : e.prio < x.prio
    · have hall_gt : ∀ y ∈ x :: xs, e.prio < y.prio := by
        intro y hy; simp at hy; rcases hy with rfl | hy
        · exact hlt
        · have hle : x.prio ≤ y.prio := sorted_head_le hs hy; omega
      have hins : ins e (x :: xs) = e :: x :: xs := by simp [ins, hlt]
      exact ⟨[], x :: xs, rfl, hins, by intro y hy; simp at hy, hall_gt⟩
    · have hle_xe : x.prio ≤ e.prio := Nat.le_of_not_gt hlt
      have hins : ins e (x :: xs) = x :: ins e xs := by simp [ins, hlt]
      obtain ⟨l1, l2, heq, hins_eq, hle_l1, hlt_l2⟩ := ih hxs_sorted
      exact ⟨x :: l1, l2, by simp [heq], by simp [hins, hins_eq], by intro y hy; simp at hy; rcases hy with rfl | hy; exact hle_xe; exact hle_l1 y hy, hlt_l2⟩

theorem mem_ins_imp (e y : Entry) (l : List Entry) : y ∈ ins e l → y = e ∨ y ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    simp only [ins]
    split
    · simp; intro h; rcases h with rfl | rfl | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · simp at h
    · simp
      intro h
      rcases h with rfl | h
      · exact Or.inr (Or.inl rfl)
      · have hm := ih h
        rcases hm with rfl | hm2
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hm2)

theorem sorted_ins (e : Entry) (l : List Entry) (hs : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    have hxs_sorted : Sorted xs := sorted_pairwise_cons hs
    by_cases hlt : e.prio < x.prio
    · have hins : ins e (x :: xs) = e :: x :: xs := by simp [ins, hlt]
      rw [hins]
      apply List.Pairwise.cons
      · intro y hy
        simp at hy
        rcases hy with rfl | hy
        · omega
        · have hle : x.prio ≤ y.prio := sorted_head_le hs hy; omega
      · exact hs
    · have hins : ins e (x :: xs) = x :: ins e xs := by simp [ins, hlt]
      rw [hins]
      apply List.Pairwise.cons
      · intro y hy
        have hy2 := mem_ins_imp e y xs hy
        rcases hy2 with rfl | hy_xs
        · exact Nat.le_of_not_gt hlt
        · exact sorted_head_le hs hy_xs
      · exact ih hxs_sorted

def step : Impl := fun s op =>
  if Valid s op then
    match op, s.items with
    | .insert e, _ => (.ok, { s with items := ins e s.items })
    | .pop, x :: xs => (.got x, { s with items := xs })
    | .pop, [] => (.rejected, s)
  else (.rejected, s)

theorem step_insert_eq (s : State) (e : Entry) (h : Valid s (.insert e)) :
    step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
  unfold step; simp [h]

theorem step_pop_eq {s : State} (h : Valid s .pop) :
    ∃ x xs, s.items = x :: xs ∧ step s .pop = (.got x, { s with items := xs }) := by
  have hne : s.items ≠ [] := by
    have : Valid s .pop = (Sorted s.items ∧ s.items ≠ []) := rfl
    rw [this] at h; exact h.2
  match heq : s.items with
  | [] => exact False.elim (hne heq)
  | x :: xs =>
    refine ⟨x, xs, heq, ?_⟩
    unfold step; simp [h, heq]

theorem step_invalid_rejected (s : State) (op : Op) (h : ¬ Valid s op) :
    step s op = (.rejected, s) := by
  unfold step; simp [h]

theorem step_not_rejected_valid (s : State) (op : Op) (h : (step s op).1 ≠ .rejected) : Valid s op := by
  unfold step at h
  split at h
  · assumption
  · simp at h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hv
  unfold step
  simp only [hv, ↓reduceIte]
  cases hm : s.items with
  | nil =>
    cases op with
    | insert e => simp
    | pop =>
      have : Valid s Op.pop = (Sorted s.items ∧ s.items ≠ []) := rfl
      rw [this] at hv; simp [hm] at hv
  | cons x xs =>
    cases op with
    | insert e => simp
    | pop => simp [hm]

theorem req_invalid_noop : InvalidNoop step :=
  fun s op hn => step_invalid_rejected s op hn

theorem req_capacity : CapacityBound step := by
  intro s op hle
  unfold step
  split
  · next hvalid =>
    match op, hvalid with
    | .insert e, hv =>
      simp
      have hlen : (ins e s.items).length = s.items.length + 1 := ins_length e s.items
      have hlt : s.items.length < s.capacity := by
        have : Valid s (.insert e) = (Sorted s.items ∧ s.items.length < s.capacity) := rfl
        rw [this] at hv; exact hv.2
      omega
    | .pop, hv =>
      match hm : s.items with
      | [] =>
        have : Valid s .pop = (Sorted s.items ∧ s.items ≠ []) := rfl
        rw [this] at hv; simp [hm] at hv
      | x :: xs =>
        simp [hm]
        have : xs.length ≤ s.items.length := by simp [hm]
        omega
  · next _ => exact hle

theorem req_pop_min : PopMin step := by
  intro s hnr
  have hvalid : Valid s .pop := step_not_rejected_valid s .pop hnr
  obtain ⟨x, xs, hm, hstep⟩ := step_pop_eq hvalid
  rw [hstep] at hnr ⊢
  refine ⟨x, rfl, ?_⟩
  intro y hy
  have hsorted : Sorted s.items := by
    have : Valid s .pop = (Sorted s.items ∧ s.items ≠ []) := rfl
    rw [this] at hvalid; exact hvalid.1
  rw [hm] at hsorted
  exact sorted_head_le (a:=x) (l:=xs) hsorted hy

theorem req_sorted : KeepsSorted step := by
  intro s op hs
  unfold step
  split
  · next hvalid =>
    cases op with
    | insert e => simp; exact sorted_ins e s.items hs
    | pop =>
      match hm : s.items with
      | [] =>
        have : Valid s .pop = (Sorted s.items ∧ s.items ≠ []) := rfl
        rw [this] at hvalid; simp [hm] at hvalid
      | x :: xs =>
        simp [hm]; exact sorted_pairwise_cons (by rwa [hm] at hs)
  · next _ => simp; exact hs

theorem req_insert_effects : InsertEffects step := by
  intro s e hnr
  have hvalid : Valid s (.insert e) := step_not_rejected_valid s (.insert e) hnr
  have hstep_eq := step_insert_eq s e hvalid
  have hsorted : Sorted s.items := by
    have : Valid s (.insert e) = (Sorted s.items ∧ s.items.length < s.capacity) := rfl
    rw [this] at hvalid; exact hvalid.1
  obtain ⟨l1, l2, heq1, heq2, hle, hlt⟩ := exists_split_ins e s.items hsorted
  have hfst : (step s (.insert e)).1 = .ok := by rw [hstep_eq]
  refine ⟨hfst, ?_, l1, l2, heq1, ?_, hle, hlt⟩
  · rw [hstep_eq]
  · rw [hstep_eq]; simp [heq2]

theorem req_pop_effects : PopEffects step := by
  intro s hnr
  have hvalid : Valid s .pop := step_not_rejected_valid s .pop hnr
  obtain ⟨x, xs, heq_items, hstep⟩ := step_pop_eq hvalid
  have hsorted : Sorted s.items := by
    have : Valid s .pop = (Sorted s.items ∧ s.items ≠ []) := rfl
    rw [this] at hvalid; exact hvalid.1
  rw [heq_items] at hsorted
  have hcap : (step s Op.pop).2.capacity = s.capacity := by rw [hstep]
  have hgot : (step s Op.pop).1 = Outcome.got x := by rw [hstep]
  have hitems : (step s Op.pop).2.items = ([] : List Entry) ++ xs := by rw [hstep]; simp
  refine ⟨hcap, [], x, xs, by simp [heq_items], hgot, hitems, ?_, ?_⟩
  · intro y hy; simp at hy
  · intro y hy; exact sorted_head_le (a:=x) (l:=xs) hsorted hy

theorem classOf_append (p : Nat) (a b : List Entry) : classOf p (a ++ b) = classOf p a ++ classOf p b := by
  simp [classOf, List.filter_append]

theorem classOf_cons_eq (p : Nat) (a : Entry) (l : List Entry) : classOf p (a :: l) = classOf p [a] ++ classOf p l := by
  have h : a :: l = [a] ++ l := by simp
  rw [h, classOf_append]

theorem classOf_ins (e : Entry) (l : List Entry) (hs : Sorted l) (p : Nat) :
    classOf p (ins e l) = if e.prio == p then classOf p l ++ [e] else classOf p l := by
  obtain ⟨l1, l2, heq, hins, _, hlt⟩ := exists_split_ins e l hs
  have h1 : classOf p l = classOf p l1 ++ classOf p l2 := by rw [heq, classOf_append]
  have h2 : classOf p (ins e l) = classOf p l1 ++ classOf p [e] ++ classOf p l2 := by
    calc classOf p (ins e l) = classOf p (l1 ++ e :: l2) := by rw [hins]
      _ = classOf p l1 ++ classOf p (e :: l2) := by rw [classOf_append]
      _ = classOf p l1 ++ (classOf p [e] ++ classOf p l2) := by rw [classOf_cons_eq]
      _ = classOf p l1 ++ classOf p [e] ++ classOf p l2 := by simp [List.append_assoc]
  by_cases heqP : e.prio == p
  · have hl2 : classOf p l2 = [] := by
      simp only [classOf, List.filter_eq_nil_iff]
      intro y hy
      have hlt_y : e.prio < y.prio := hlt y hy
      have heqP_eq : e.prio = p := by
        have h : decide (e.prio = p) = true := by simpa [beq_iff_eq] using heqP
        exact of_decide_eq_true h
      have hneq : y.prio ≠ p := by omega
      simp [hneq]
    have heSingle : classOf p [e] = [e] := by simp [classOf, heqP]
    calc classOf p (ins e l) = classOf p l1 ++ classOf p [e] ++ classOf p l2 := h2
      _ = classOf p l1 ++ [e] ++ [] := by rw [heSingle, hl2]
      _ = classOf p l1 ++ [e] := by simp
      _ = (classOf p l1 ++ classOf p l2) ++ [e] := by rw [hl2]; simp
      _ = classOf p l ++ [e] := by rw [h1]
      _ = if e.prio == p then classOf p l ++ [e] else classOf p l := by simp [heqP]
  · have heEmpty : classOf p [e] = [] := by simp [classOf, heqP]
    calc classOf p (ins e l) = classOf p l1 ++ classOf p [e] ++ classOf p l2 := h2
      _ = classOf p l1 ++ [] ++ classOf p l2 := by rw [heEmpty]
      _ = classOf p l1 ++ classOf p l2 := by simp
      _ = classOf p l := h1.symm
      _ = if e.prio == p then classOf p l ++ [e] else classOf p l := by simp [heqP]

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow, inflowOf, outflowOf, classOf]
  | cons op ops ih =>
    by_cases hvalid : Valid s op
    · cases op with
      | insert e =>
        have hstep := step_insert_eq s e hvalid
        have hsorted : Sorted s.items := by
          have : Valid s (.insert e) = (Sorted s.items ∧ s.items.length < s.capacity) := rfl
          rw [this] at hvalid; exact hvalid.1
        have hclass_ins : classOf p (ins e s.items) = if e.prio == p then classOf p s.items ++ [e] else classOf p s.items :=
          classOf_ins e s.items hsorted p
        have ih' := ih { capacity := s.capacity, items := ins e s.items }
        have hrun1 : (run step s (Op.insert e :: ops)).1 = (Op.insert e, Outcome.ok) :: (run step { capacity := s.capacity, items := ins e s.items } ops).1 := by simp [run, hstep]
        have hrun2 : (run step s (Op.insert e :: ops)).2 = (run step { capacity := s.capacity, items := ins e s.items } ops).2 := by simp [run, hstep]
        rw [hrun1, hrun2]
        have hIn : inflow ((Op.insert e, Outcome.ok) :: (run step { capacity := s.capacity, items := ins e s.items } ops).1) = e :: inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1 := by simp [inflow, inflowOf]
        have hOut : outflow ((Op.insert e, Outcome.ok) :: (run step { capacity := s.capacity, items := ins e s.items } ops).1) = outflow (run step { capacity := s.capacity, items := ins e s.items } ops).1 := by simp [outflow, outflowOf]
        rw [hIn, hOut]
        have hInClass : classOf p (e :: inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1) = classOf p [e] ++ classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1) := by
          rw [classOf_cons_eq]
        rw [hInClass]
        by_cases heqP : e.prio == p
        · have heSingle : classOf p [e] = [e] := by simp [classOf, heqP]
          have hclass_eq : classOf p (ins e s.items) = classOf p s.items ++ [e] := by rw [hclass_ins, if_pos heqP]
          have hleft : classOf p s.items ++ (classOf p [e] ++ classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1)) = (classOf p s.items ++ [e]) ++ classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1) := by
            rw [heSingle, List.append_assoc]
          rw [hleft, ← hclass_eq]; exact ih'
        · have heEmpty : classOf p [e] = [] := by simp [classOf, heqP]
          have hclass_eq : classOf p (ins e s.items) = classOf p s.items := by rw [hclass_ins, if_neg heqP]
          have hleft : classOf p s.items ++ (classOf p [e] ++ classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1)) = classOf p s.items ++ classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1) := by
            rw [heEmpty]; simp
          rw [hleft, ← hclass_eq]; exact ih'
      | pop =>
        obtain ⟨x, xs, heq_items, hstep⟩ := step_pop_eq (s:=s) hvalid
        have ih' := ih { capacity := s.capacity, items := xs }
        have hrun1 : (run step s (Op.pop :: ops)).1 = (Op.pop, Outcome.got x) :: (run step { capacity := s.capacity, items := xs } ops).1 := by simp [run, hstep]
        have hrun2 : (run step s (Op.pop :: ops)).2 = (run step { capacity := s.capacity, items := xs } ops).2 := by simp [run, hstep]
        rw [hrun1, hrun2]
        have hIn : inflow ((Op.pop, Outcome.got x) :: (run step { capacity := s.capacity, items := xs } ops).1) = inflow (run step { capacity := s.capacity, items := xs } ops).1 := by simp [inflow, inflowOf]
        have hOut : outflow ((Op.pop, Outcome.got x) :: (run step { capacity := s.capacity, items := xs } ops).1) = x :: outflow (run step { capacity := s.capacity, items := xs } ops).1 := by simp [outflow, outflowOf]
        rw [hIn, hOut]
        have hc : classOf p s.items = classOf p [x] ++ classOf p xs := by
          calc classOf p s.items = classOf p (x :: xs) := by rw [heq_items]
            _ = classOf p ([x] ++ xs) := by simp
            _ = classOf p [x] ++ classOf p xs := by rw [classOf_append]
        rw [hc]
        by_cases heqP : x.prio == p
        · have hx : classOf p [x] = [x] := by simp [classOf, heqP]
          have h_class_out : classOf p (x :: outflow (run step { capacity := s.capacity, items := xs } ops).1) = x :: classOf p (outflow (run step { capacity := s.capacity, items := xs } ops).1) := by simp [classOf, heqP]
          rw [hx, h_class_out]
          have hL : [x] ++ classOf p xs ++ classOf p (inflow (run step { capacity := s.capacity, items := xs } ops).1) = [x] ++ (classOf p xs ++ classOf p (inflow (run step { capacity := s.capacity, items := xs } ops).1)) := by simp [List.append_assoc]
          have hR : (x :: classOf p (outflow (run step { capacity := s.capacity, items := xs } ops).1)) ++ classOf p (run step { capacity := s.capacity, items := xs } ops).2.items = [x] ++ (classOf p (outflow (run step { capacity := s.capacity, items := xs } ops).1) ++ classOf p (run step { capacity := s.capacity, items := xs } ops).2.items) := by simp
          rw [hL, hR, ih']
        · have hx : classOf p [x] = [] := by simp [classOf, heqP]
          have h_class_out : classOf p (x :: outflow (run step { capacity := s.capacity, items := xs } ops).1) = classOf p (outflow (run step { capacity := s.capacity, items := xs } ops).1) := by simp [classOf, heqP]
          rw [hx, h_class_out]; simp [ih']
    · have hstep_eq := step_invalid_rejected s op hvalid
      have hrun1 : (run step s (op :: ops)).1 = (op, Outcome.rejected) :: (run step s ops).1 := by simp [run, hstep_eq]
      have hrun2 : (run step s (op :: ops)).2 = (run step s ops).2 := by simp [run, hstep_eq]
      rw [hrun1, hrun2]
      have hIn : inflow ((op, Outcome.rejected) :: (run step s ops).1) = inflow (run step s ops).1 := by
        cases op with
        | insert e => simp [inflow, inflowOf]
        | pop => simp [inflow, inflowOf]
      have hOut : outflow ((op, Outcome.rejected) :: (run step s ops).1) = outflow (run step s ops).1 := by
        cases op with
        | insert e => simp [outflow, outflowOf]
        | pop => simp [outflow, outflowOf]
      rw [hIn, hOut]; exact ih s

end PrioQueue
