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

theorem ins_length (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih => unfold ins; split <;> simp [ih]

theorem sorted_tail' {a : Entry} {l : List Entry} (h : Sorted (a :: l)) : Sorted l :=
  (List.pairwise_cons.mp h).2

theorem head_le_all {hd : Entry} {l : List Entry} (h : Sorted (hd :: l)) (y : Entry) (hm : y ∈ l) : hd.prio ≤ y.prio :=
  (List.pairwise_cons.mp h).1 y hm

theorem mem_ins (e : Entry) (l : List Entry) (x : Entry) (h : x ∈ ins e l) : x = e ∨ x ∈ l := by
  induction l with
  | nil => simp [ins] at h; exact Or.inl h
  | cons y ys ih =>
    unfold ins at h; split at h
    · simp at h; rcases h with rfl | rfl | hm <;> simp [*]
    · simp at h; rcases h with rfl | hm
      · exact Or.inr (List.Mem.head _)
      · rcases ih hm with rfl | hin
        · exact Or.inl rfl
        · exact Or.inr (List.Mem.tail _ hin)

theorem ins_sorted (e : Entry) (l : List Entry) (hs : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil => simp [Sorted, ins]
  | cons x xs ih =>
    have hs_tail : Sorted xs := by
      cases xs with
      | nil => exact List.Pairwise.nil
      | cons y ys => exact sorted_tail' (a:=x) (by simpa using hs)
    have ihs := ih hs_tail
    unfold ins; split
    · next hlt =>
      have he_le : e.prio ≤ x.prio := Nat.le_of_lt hlt
      have h1 : ∀ y ∈ x :: xs, e.prio ≤ y.prio := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hm
        · exact he_le
        · exact Nat.le_trans he_le (head_le_all (hd:=x) hs y hm)
      exact List.Pairwise.cons h1 hs
    · next _ =>
      have hxle_e : x.prio ≤ e.prio := by omega
      have h1 : ∀ y ∈ ins e xs, x.prio ≤ y.prio := by
        intro y hy
        rcases mem_ins e xs y hy with rfl | hin
        · exact hxle_e
        · exact head_le_all (hd:=x) hs y hin
      exact List.Pairwise.cons h1 ihs

theorem ins_split (e : Entry) (l : List Entry) (hs : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil => exact ⟨[], [], rfl, by simp [ins], by simp, by simp⟩
  | cons x xs ih =>
    have hs_tail : Sorted xs := by
      cases xs with
      | nil => exact List.Pairwise.nil
      | cons y ys => exact sorted_tail' (a:=x) (by simpa using hs)
    obtain ⟨l₁', l₂', heq, hins, hle1, hlt2⟩ := ih hs_tail
    by_cases hlt : e.prio < x.prio
    · refine ⟨[], x :: xs, rfl, ?_, by simp, ?_⟩
      · simp [ins, hlt]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hm
        · exact hlt
        · exact Nat.lt_of_lt_of_le hlt (head_le_all (hd:=x) hs y hm)
    · have hxle : x.prio ≤ e.prio := by omega
      have hins_x : ins e (x :: xs) = x :: ins e xs := by simp [ins, hlt]
      have heq' : x :: xs = (x :: l₁') ++ l₂' := by simp [heq]
      have hins' : ins e (x :: xs) = (x :: l₁') ++ e :: l₂' := by simp [hins_x, hins]
      exact ⟨x :: l₁', l₂', heq', hins', fun y hy => by rcases List.mem_cons.mp hy with rfl | hm; exact hxle; exact hle1 y hm, hlt2⟩

theorem classOf_append (p : Nat) (l₁ l₂ : List Entry) :
    classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by unfold classOf; rw [List.filter_append]

theorem filter_tail_eq_nil_of_lt {p : Nat} {hd : Entry} {tl : List Entry}
    (h : Sorted (hd :: tl)) (hlt : p < hd.prio) : classOf p tl = [] := by
  unfold classOf
  apply List.filter_eq_nil_iff.mpr
  intro a ha
  simp only [beq_iff_eq, decide_eq_true_eq]
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt (head_le_all (hd:=hd) h a ha))

theorem classOf_ins_sorted (p : Nat) (e : Entry) (l : List Entry) (hs : Sorted l) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := by
  induction l with
  | nil => simp [ins, classOf]
  | cons x xs ih =>
    have hs_tail : Sorted xs := by
      cases xs with
      | nil => exact List.Pairwise.nil
      | cons y ys => exact sorted_tail' (a:=x) (by simpa using hs)
    have ih' := ih hs_tail
    unfold ins; split
    · next hlt =>
      by_cases he : (e.prio == p) = true
      · have hp_lt_x : p < x.prio := by have heq : e.prio = p := beq_iff_eq.mp he; rw [← heq]; exact hlt
        have hx_ne : (x.prio == p) = false := by simp [Nat.ne_of_gt hp_lt_x]
        have h_filter_xs : classOf p xs = [] := filter_tail_eq_nil_of_lt (p:=p) (hd:=x) hs hp_lt_x
        show classOf p (e :: x :: xs) = classOf p (x :: xs) ++ classOf p [e]
        simp [classOf, he, hx_ne, h_filter_xs]
      · have he_f : (e.prio == p) = false := by cases h : (e.prio == p) <;> simp_all
        show classOf p (e :: x :: xs) = classOf p (x :: xs) ++ classOf p [e]
        simp [classOf, he_f]
    · next hge =>
      -- need to show classOf (x :: ins e xs) = classOf (x::xs) ++ classOf [e]
      -- unfold filter cons
      by_cases hx : (x.prio == p) = true
      · have lhs : classOf p (x :: ins e xs) = x :: classOf p (ins e xs) := by simp [classOf, hx]
        have rhs : classOf p (x :: xs) = x :: classOf p xs := by simp [classOf, hx]
        rw [lhs, rhs, ih']
        simp
      · have hx_f : (x.prio == p) = false := by simpa [hx] using rfl
        have lhs : classOf p (x :: ins e xs) = classOf p (ins e xs) := by simp [classOf, hx_f]
        have rhs : classOf p (x :: xs) = classOf p xs := by simp [classOf, hx_f]
        rw [lhs, rhs, ih']

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hv
  simp only [step, hv, ↓reduceIte]
  cases op with
  | insert e => simp
  | pop =>
    cases h : s.items with
    | nil => unfold Valid at hv; simp [h] at hv
    | cons hd tl => simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hv
  simp [step, hv]

theorem req_capacity : CapacityBound step := by
  intro s op hle
  simp only [step] at hle ⊢
  split
  · next hv =>
    cases op with
    | insert e =>
      simp
      have hlt : s.items.length < s.capacity := hv.2
      have hlen := ins_length e s.items
      omega
    | pop =>
      simp
      cases h : s.items with
      | nil => exact hle
      | cons hd tl =>
        simp
        have : tl.length ≤ s.items.length := by rw [h]; simp
        omega
  · next _ => exact hle

theorem req_pop_min : PopMin step := by
  intro s h
  by_cases hv : Valid s .pop
  · have hs : Sorted s.items := hv.1
    cases hs_items : s.items with
    | nil => unfold Valid at hv; simp [hs_items] at hv
    | cons x xs =>
      have hstep : (step s Op.pop).1 = .got x := by simp [step, hv, hs_items]
      have hstep2 : (step s Op.pop).2.items = xs := by simp [step, hv, hs_items]
      refine ⟨x, hstep, ?_⟩
      rw [hstep2]
      intro y hy
      exact head_le_all (hd:=x) (by rw [← hs_items]; exact hs) y hy
  · simp [step, hv] at h

theorem req_sorted : KeepsSorted step := by
  intro s op hs
  simp only [step]
  split
  · next hv =>
    cases op with
    | insert e => simp; exact ins_sorted e s.items hs
    | pop =>
      cases h : s.items with
      | nil => exact hs
      | cons hd tl => simp; exact sorted_tail' (by simpa [h] using hs)
  · exact hs

theorem req_insert_effects : InsertEffects step := by
  intro s e h
  have hv : Valid s (.insert e) := by
    by_cases hc : Valid s (.insert e)
    · exact hc
    · exfalso; apply h; simp [step, hc]
  have hs : Sorted s.items := hv.1
  obtain ⟨l₁,l₂,heq,hins,hle1,hlt2⟩ := ins_split e s.items hs
  have hstep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by simp [step, hv]
  refine ⟨by simp [hstep], by simp [hstep], l₁, l₂, heq, by simp [hstep, hins], hle1, hlt2⟩

theorem req_pop_effects : PopEffects step := by
  intro s h
  have hv : Valid s .pop := by
    by_cases hc : Valid s .pop
    · exact hc
    · exfalso; apply h; simp [step, hc]
  cases hs_items : s.items with
  | nil => unfold Valid at hv; simp [hs_items] at hv
  | cons hd tl =>
    have hstep2 : step s .pop = (.got hd, { capacity := s.capacity, items := tl }) := by simp [step, hv, hs_items]
    have hcap : (step s .pop).2.capacity = s.capacity := by rw [hstep2]
    have hs : Sorted (hd :: tl) := by rw [← hs_items]; exact hv.1
    have hitems : (step s .pop).2.items = tl := by rw [hstep2]
    have hg : (step s .pop).1 = .got hd := by rw [hstep2]
    refine ⟨hcap, [], hd, tl, by simp [hs_items], hg, hitems, ?_, ?_⟩
    · intro x hx; simp at hx
    · intro x hx; exact head_le_all (hd:=hd) hs x hx

theorem req_fifo_ties : FifoTies step := by
  intro s ops p; induction ops generalizing s with
  | nil => simp [run, inflow, outflow, classOf]
  | cons op rest ih =>
    by_cases hv : Valid s op
    · cases op with
      | insert e =>
        have hstep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by simp [step, hv]
        have hrun : run step s (Op.insert e :: rest) = ((Op.insert e, .ok) :: (run step { s with items := ins e s.items } rest).1, (run step { s with items := ins e s.items } rest).2) := by simp [run, hstep]
        rw [hrun]
        have hinf : inflow ((Op.insert e, .ok) :: (run step { s with items := ins e s.items } rest).1) = [e] ++ inflow (run step { s with items := ins e s.items } rest).1 := by simp [inflow, inflowOf]
        have hout : outflow ((Op.insert e, .ok) :: (run step { s with items := ins e s.items } rest).1) = outflow (run step { s with items := ins e s.items } rest).1 := by simp [outflow, outflowOf]
        rw [hinf, hout]
        have hca : classOf p ([e] ++ inflow (run step { s with items := ins e s.items } rest).1) = classOf p [e] ++ classOf p (inflow (run step { s with items := ins e s.items } rest).1) := classOf_append p [e] _
        rw [hca]
        have left_eq : classOf p s.items ++ (classOf p [e] ++ classOf p (inflow (run step { s with items := ins e s.items } rest).1)) = classOf p (ins e s.items) ++ classOf p (inflow (run step { s with items := ins e s.items } rest).1) := by
          rw [← List.append_assoc, ← classOf_ins_sorted p e s.items hv.1]
        rw [left_eq]; exact ih { s with items := ins e s.items }
      | pop =>
        cases hs_items : s.items with
        | nil => unfold Valid at hv; simp [hs_items] at hv
        | cons hd tl =>
          have hstep : step s .pop = (.got hd, { s with items := tl }) := by simp [step, hv, hs_items]
          have hrun : run step s (Op.pop :: rest) = ((Op.pop, .got hd) :: (run step { s with items := tl } rest).1, (run step { s with items := tl } rest).2) := by simp [run, hstep]
          rw [hrun]
          have hinf : inflow ((Op.pop, .got hd) :: (run step { s with items := tl } rest).1) = inflow (run step { s with items := tl } rest).1 := by simp [inflow, inflowOf]
          have hout : outflow ((Op.pop, .got hd) :: (run step { s with items := tl } rest).1) = [hd] ++ outflow (run step { s with items := tl } rest).1 := by simp [outflow, outflowOf]
          rw [hinf, hout]
          have hca_out : classOf p ([hd] ++ outflow (run step { s with items := tl } rest).1) = classOf p [hd] ++ classOf p (outflow (run step { s with items := tl } rest).1) := classOf_append p [hd] _
          rw [hca_out]
          have hclass_head : classOf p (hd :: tl) = classOf p [hd] ++ classOf p tl := by rw [show hd :: tl = [hd] ++ tl from rfl, classOf_append]
          rw [hclass_head]
          have ih' := ih { s with items := tl }
          calc classOf p [hd] ++ classOf p tl ++ classOf p (inflow (run step { s with items := tl } rest).1)
              = classOf p [hd] ++ (classOf p tl ++ classOf p (inflow (run step { s with items := tl } rest).1)) := by rw [List.append_assoc]
            _ = classOf p [hd] ++ (classOf p (outflow (run step { s with items := tl } rest).1) ++ classOf p (run step { s with items := tl } rest).2.items) := by rw [ih']
            _ = (classOf p [hd] ++ classOf p (outflow (run step { s with items := tl } rest).1)) ++ classOf p (run step { s with items := tl } rest).2.items := by rw [List.append_assoc]
    · have hstep : step s op = (.rejected, s) := by simp [step, hv]
      have hrun : run step s (op :: rest) = ((op, .rejected) :: (run step s rest).1, (run step s rest).2) := by simp [run, hstep]
      rw [hrun]
      have hinf : inflow ((op, .rejected) :: (run step s rest).1) = inflow (run step s rest).1 := by
        have h1 : inflowOf (op, .rejected) = ([] : List Entry) := by cases op <;> simp [inflowOf]
        unfold inflow; simp [h1]
      have hout : outflow ((op, .rejected) :: (run step s rest).1) = outflow (run step s rest).1 := by
        have h1 : outflowOf (op, .rejected) = ([] : List Entry) := by cases op <;> simp [outflowOf]
        unfold outflow; simp [h1]
      rw [hinf, hout]; exact ih s

end PrioQueue
