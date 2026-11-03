import PrioQueue.Spec
namespace PrioQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid Sorted <;> infer_instance

def ins (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs => if e.prio < x.prio then e :: x :: xs else x :: ins e xs

def step : Impl := fun s op =>
  match op with
  | .insert e =>
    if Valid s (Op.insert e) then
      (.ok, { capacity := s.capacity, items := ins e s.items })
    else (.rejected, s)
  | .pop =>
    if Valid s Op.pop then
      match s.items with
      | [] => (.rejected, s)
      | x :: xs => (.got x, { capacity := s.capacity, items := xs })
    else (.rejected, s)

private theorem ins_length (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih => simp only [ins]; split <;> simp [ih]

private theorem sorted_tail {a : Entry} {l : List Entry} (h : Sorted (a :: l)) : Sorted l :=
  (List.pairwise_cons.mp h).2

private theorem sorted_head_le_aux (a : Entry) (l : List Entry) (h : Sorted (a :: l)) :
    ∀ y ∈ l, a.prio ≤ y.prio := by
  intro y hy
  induction l generalizing a with
  | nil => simp at hy
  | cons b bs ih =>
    have hab : a.prio ≤ b.prio := (List.pairwise_cons.mp h).1 b (by simp)
    have htail : Sorted (b :: bs) := sorted_tail h
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact hab
    · exact Nat.le_trans hab (ih b htail hmem)

private theorem mem_ins_imp_aux (e : Entry) (l : List Entry) (y : Entry) (h : y ∈ ins e l) : y = e ∨ y ∈ l := by
  induction l with
  | nil => simp [ins] at h; exact Or.inl h
  | cons x xs ih =>
    simp only [ins] at h
    split at h
    · simp at h; rcases h with rfl | rfl | hm
      · left; rfl
      · right; simp
      · right; simp [hm]
    · simp at h; rcases h with rfl | hm
      · right; simp
      · rcases ih hm with heq | hin
        · left; exact heq
        · right; simp [hin]

private theorem ins_split (e : Entry) (l : List Entry) (hs : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧ (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil => exact ⟨[], [], by simp, by simp [ins], by simp, by simp⟩
  | cons x xs ih =>
    have hs_tail : Sorted xs := sorted_tail hs
    obtain ⟨l₁', l₂', heq', hins', hle1', hlt2'⟩ := ih hs_tail
    by_cases h : e.prio < x.prio
    · refine ⟨[], x :: xs, by simp, ?_, by simp, ?_⟩
      · simp [ins, h]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hm
        · omega
        · have hle : x.prio ≤ y.prio := sorted_head_le_aux x xs hs y hm; omega
    · have hle_x : x.prio ≤ e.prio := by omega
      have hins_cons : ins e (x :: xs) = x :: ins e xs := by simp [ins, h]
      refine ⟨x :: l₁', l₂', ?_, ?_, ?_, ?_⟩
      · simp [heq']
      · simp [hins_cons, hins']
      · intro y hy; simp at hy; rcases hy with rfl | hy'
        · exact hle_x
        · exact hle1' y hy'
      · exact hlt2'

private theorem sorted_ins_direct (e : Entry) : ∀ l, Sorted l → Sorted (ins e l) := by
  intro l hs; induction l with
  | nil => simp [ins, Sorted]
  | cons x xs ih =>
    have hs_tail : Sorted xs := sorted_tail hs
    have ih' := ih hs_tail
    by_cases h : e.prio < x.prio
    · simp [ins, h]
      have hall : ∀ y ∈ (x :: xs), e.prio ≤ y.prio := by
        intro y hy; rcases List.mem_cons.mp hy with rfl | hm
        · omega
        · have hle : x.prio ≤ y.prio := sorted_head_le_aux x xs hs y hm; omega
      exact (List.pairwise_cons.mpr ⟨hall, hs⟩)
    · simp [ins, h]
      have hall : ∀ y ∈ ins e xs, x.prio ≤ y.prio := by
        intro y hy
        rcases mem_ins_imp_aux e xs y hy with rfl | hm
        · omega
        · exact sorted_head_le_aux x xs hs y hm
      exact (List.pairwise_cons.mpr ⟨hall, ih'⟩)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | insert e => simp [step, hV]
  | pop =>
    simp [step, hV]
    cases h : s.items
    · exfalso; exact hV.2 h
    · simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hN
  cases op with
  | insert e => simp [step, hN]
  | pop => simp [step, hN]

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | insert e =>
    by_cases hV : Valid s (Op.insert e)
    · have _hlt : s.items.length < s.capacity := hV.2
      have hlen : (ins e s.items).length = s.items.length + 1 := ins_length e s.items
      have hstep : step s (Op.insert e) = (.ok, { capacity := s.capacity, items := ins e s.items }) := by simp [step, hV]
      rw [hstep]; simp only; rw [hlen]; omega
    · have hstep : step s (Op.insert e) = (.rejected, s) := by simp [step, hV]
      rw [hstep]; simp only; exact hle
  | pop =>
    by_cases hV : Valid s Op.pop
    · cases hxs : s.items with
      | nil =>
        have hne : s.items ≠ [] := hV.2
        rw [hxs] at hne
        exact absurd rfl hne
      | cons x xs =>
        have hstep : step s Op.pop = (.got x, { capacity := s.capacity, items := xs }) := by simp [step, hV, hxs]
        rw [hstep]; simp only
        have heq : s.items.length = xs.length + 1 := by rw [hxs]; simp
        omega
    · have hstep : step s Op.pop = (.rejected, s) := by simp [step, hV]
      rw [hstep]; simp only; exact hle

theorem req_pop_min : PopMin step := by
  intro s h
  by_cases hV : Valid s Op.pop
  · cases hxs : s.items with
    | nil =>
      have hne : s.items ≠ [] := hV.2
      rw [hxs] at hne
      exact absurd rfl hne
    | cons x xs =>
      have hstep : step s Op.pop = (.got x, { capacity := s.capacity, items := xs }) := by simp [step, hV, hxs]
      have hfst : (step s Op.pop).1 = .got x := by rw [hstep]
      rw [hfst]
      refine ⟨x, rfl, ?_⟩
      have hsnd : (step s Op.pop).2.items = xs := by rw [hstep]
      rw [hsnd]
      intro y hy
      have hs : Sorted s.items := hV.1
      rw [hxs] at hs
      exact sorted_head_le_aux x xs hs y hy
  · have hstep : step s Op.pop = (.rejected, s) := by simp [step, hV]
    have hfst : (step s Op.pop).1 = .rejected := by rw [hstep]
    simp [hfst] at h

theorem req_sorted : KeepsSorted step := by
  intro s op hs
  cases op with
  | insert e =>
    by_cases hV : Valid s (Op.insert e)
    · have hstep : step s (Op.insert e) = (.ok, { capacity := s.capacity, items := ins e s.items }) := by simp [step, hV]
      rw [hstep]; exact sorted_ins_direct e s.items hs
    · have hstep : step s (Op.insert e) = (.rejected, s) := by simp [step, hV]
      rw [hstep]; exact hs
  | pop =>
    by_cases hV : Valid s Op.pop
    · cases hxs : s.items with
      | nil =>
        have hne : s.items ≠ [] := hV.2
        rw [hxs] at hne
        exact absurd rfl hne
      | cons x xs =>
        have hstep : step s Op.pop = (.got x, { capacity := s.capacity, items := xs }) := by simp [step, hV, hxs]
        rw [hstep]; simp only
        have hs' : Sorted (x :: xs) := by rw [← hxs]; exact hs
        exact sorted_tail hs'
    · have hstep : step s Op.pop = (.rejected, s) := by simp [step, hV]
      rw [hstep]; exact hs

theorem req_insert_effects : InsertEffects step := by
  intro s e hS
  by_cases hV : Valid s (Op.insert e)
  · have hst : step s (Op.insert e) = (.ok, { capacity := s.capacity, items := ins e s.items }) := by simp [step, hV]
    have hs : Sorted s.items := hV.1
    obtain ⟨l₁, l₂, heq, hins, hle1, hlt2⟩ := ins_split e s.items hs
    refine ⟨by rw [hst], by rw [hst], l₁, l₂, heq, ?_, hle1, hlt2⟩
    have : (step s (Op.insert e)).2.items = ins e s.items := by rw [hst]
    rw [this, hins]
  · have hst : step s (Op.insert e) = (.rejected, s) := by simp [step, hV]
    have : (step s (Op.insert e)).1 = .rejected := by rw [hst]
    simp [this] at hS

theorem req_pop_effects : PopEffects step := by
  intro s hS
  by_cases hV : Valid s Op.pop
  · cases hxs : s.items with
    | nil =>
      have hne : s.items ≠ [] := hV.2
      rw [hxs] at hne
      exact absurd rfl hne
    | cons x xs =>
      have hst2 : step s Op.pop = (.got x, { capacity := s.capacity, items := xs }) := by simp [step, hV, hxs]
      have hcap : (step s Op.pop).2.capacity = s.capacity := by rw [hst2]
      refine ⟨hcap, [], x, xs, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hxs]
      · rw [hst2]
      · simp
      · intro y hy; cases hy
      · intro y hy
        have hs : Sorted s.items := hV.1
        rw [hxs] at hs
        exact sorted_head_le_aux x xs hs y hy
  · have hst : step s Op.pop = (.rejected, s) := by simp [step, hV]
    have : (step s Op.pop).1 = .rejected := by rw [hst]
    simp [this] at hS

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  have h_append : ∀ (a b : List Entry), classOf p (a ++ b) = classOf p a ++ classOf p b := by intro a b; unfold classOf; rw [List.filter_append]
  have h_class_nil : classOf p ([] : List Entry) = [] := by unfold classOf; simp
  have h_single : ∀ (t : State) (o : Op),
      classOf p t.items ++ classOf p (inflowOf (o, (step t o).1)) =
      classOf p (outflowOf (o, (step t o).1)) ++ classOf p (step t o).2.items := by
    intro t o
    cases o with
    | insert e =>
      by_cases hV : Valid t (Op.insert e)
      · have hst : step t (Op.insert e) = (.ok, { capacity := t.capacity, items := ins e t.items }) := by simp [step, hV]
        have hfst : (step t (Op.insert e)).1 = Outcome.ok := by rw [hst]
        have hsnd : (step t (Op.insert e)).2.items = ins e t.items := by rw [hst]
        rw [hfst, hsnd]
        have hio1 : inflowOf (Op.insert e, Outcome.ok) = [e] := rfl
        have hoo1 : outflowOf (Op.insert e, Outcome.ok) = ([] : List Entry) := rfl
        rw [hio1, hoo1, h_class_nil]
        have hs : Sorted t.items := hV.1
        obtain ⟨l₁, l₂, heq, hins, _hle1, hlt2⟩ := ins_split e t.items hs
        have h1 : classOf p t.items = classOf p l₁ ++ classOf p l₂ := by rw [heq, h_append]
        have h2 : classOf p (ins e t.items) = classOf p l₁ ++ classOf p (e :: l₂) := by rw [hins, h_append]
        have h3 : classOf p (e :: l₂) = classOf p [e] ++ classOf p l₂ := by
          calc classOf p (e :: l₂) = classOf p ([e] ++ l₂) := by rfl
            _ = classOf p [e] ++ classOf p l₂ := h_append [e] l₂
        rw [h1, h2, h3]
        by_cases heq_p : e.prio = p
        · have hl₂ : classOf p l₂ = [] := by
            unfold classOf; apply List.filter_eq_nil_iff.mpr; intro y hy
            have hlt : e.prio < y.prio := hlt2 y hy
            have : y.prio ≠ p := by omega
            simp [this]
          have he : classOf p [e] = [e] := by unfold classOf; simp [heq_p]
          rw [hl₂, he]; simp only [List.append_nil, List.nil_append]
        · have he : classOf p [e] = [] := by unfold classOf; simp [heq_p]
          rw [he]; simp only [List.append_nil, List.nil_append]
      · have hst : step t (Op.insert e) = (.rejected, t) := by simp [step, hV]
        have hfst : (step t (Op.insert e)).1 = Outcome.rejected := by rw [hst]
        have hsnd : (step t (Op.insert e)).2.items = t.items := by rw [hst]
        rw [hfst, hsnd]
        have hio1 : inflowOf (Op.insert e, Outcome.rejected) = ([] : List Entry) := rfl
        have hoo1 : outflowOf (Op.insert e, Outcome.rejected) = ([] : List Entry) := rfl
        rw [hio1, hoo1, h_class_nil]
        simp only [List.append_nil, List.nil_append]
    | pop =>
      by_cases hV : Valid t Op.pop
      · cases hxs : t.items with
        | nil =>
          have hne : t.items ≠ [] := hV.2
          rw [hxs] at hne
          exact absurd rfl hne
        | cons x xs =>
          have hst : step t Op.pop = (.got x, { capacity := t.capacity, items := xs }) := by simp [step, hV, hxs]
          have hfst : (step t Op.pop).1 = Outcome.got x := by rw [hst]
          have hsnd : (step t Op.pop).2.items = xs := by rw [hst]
          rw [hfst, hsnd]
          have hio1 : inflowOf (Op.pop, Outcome.got x) = ([] : List Entry) := rfl
          have hoo1 : outflowOf (Op.pop, Outcome.got x) = [x] := rfl
          rw [hio1, hoo1, h_class_nil]
          have h1 : classOf p (x :: xs) = classOf p [x] ++ classOf p xs := by unfold classOf; simp
          rw [h1]
          simp only [List.append_nil, List.nil_append]
      · have hst : step t Op.pop = (.rejected, t) := by simp [step, hV]
        have hfst : (step t Op.pop).1 = Outcome.rejected := by rw [hst]
        have hsnd : (step t Op.pop).2.items = t.items := by rw [hst]
        rw [hfst, hsnd]
        have hio1 : inflowOf (Op.pop, Outcome.rejected) = ([] : List Entry) := rfl
        have hoo1 : outflowOf (Op.pop, Outcome.rejected) = ([] : List Entry) := rfl
        rw [hio1, hoo1, h_class_nil]
        simp only [List.append_nil, List.nil_append]
  have h_append' : ∀ a b, classOf p (a ++ b) = classOf p a ++ classOf p b := h_append
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow, h_class_nil]
  | cons op rest ih =>
    have h_run : run step s (op :: rest) =
        ((op, (step s op).1) :: (run step (step s op).2 rest).1,
         (run step (step s op).2 rest).2) := by simp [run]
    have h_inflow_cons : ∀ (o : Op) (ou : Outcome) (t : List (Op × Outcome)),
        inflow ((o, ou) :: t) = inflowOf (o, ou) ++ inflow t := by intro o ou t; unfold inflow; simp
    have h_outflow_cons : ∀ (o : Op) (ou : Outcome) (t : List (Op × Outcome)),
        outflow ((o, ou) :: t) = outflowOf (o, ou) ++ outflow t := by intro o ou t; unfold outflow; simp
    let s1 := (step s op).2; let out1 := (step s op).1
    have ih' := ih s1
    have hstep : classOf p s.items ++ classOf p (inflowOf (op, out1)) =
        classOf p (outflowOf (op, out1)) ++ classOf p s1.items := h_single s op
    have h_in_eq : inflow (run step s (op :: rest)).1 = inflowOf (op, out1) ++ inflow (run step s1 rest).1 := by
      have h1 : (run step s (op :: rest)).1 = (op, out1) :: (run step s1 rest).1 := by
        rw [h_run]
      rw [h1, h_inflow_cons]
    have h_out_eq : outflow (run step s (op :: rest)).1 = outflowOf (op, out1) ++ outflow (run step s1 rest).1 := by
      have h1 : (run step s (op :: rest)).1 = (op, out1) :: (run step s1 rest).1 := by
        rw [h_run]
      rw [h1, h_outflow_cons]
    have h_final_eq : (run step s (op :: rest)).2 = (run step s1 rest).2 := by
      rw [h_run]
    calc classOf p s.items ++ classOf p (inflow (run step s (op :: rest)).1)
        = classOf p s.items ++ classOf p (inflowOf (op, out1) ++ inflow (run step s1 rest).1) := by rw [h_in_eq]
      _ = classOf p s.items ++ (classOf p (inflowOf (op, out1)) ++ classOf p (inflow (run step s1 rest).1)) := by rw [h_append']
      _ = (classOf p s.items ++ classOf p (inflowOf (op, out1))) ++ classOf p (inflow (run step s1 rest).1) := by rw [List.append_assoc]
      _ = (classOf p (outflowOf (op, out1)) ++ classOf p s1.items) ++ classOf p (inflow (run step s1 rest).1) := by rw [hstep]
      _ = classOf p (outflowOf (op, out1)) ++ (classOf p s1.items ++ classOf p (inflow (run step s1 rest).1)) := by rw [List.append_assoc]
      _ = classOf p (outflowOf (op, out1)) ++ (classOf p (outflow (run step s1 rest).1) ++ classOf p (run step s1 rest).2.items) := by rw [ih']
      _ = (classOf p (outflowOf (op, out1)) ++ classOf p (outflow (run step s1 rest).1)) ++ classOf p (run step s1 rest).2.items := by rw [List.append_assoc]
      _ = classOf p (outflowOf (op, out1) ++ outflow (run step s1 rest).1) ++ classOf p (run step s (op :: rest)).2.items := by rw [← h_append', ← h_final_eq]
      _ = classOf p (outflow (run step s (op :: rest)).1) ++ classOf p (run step s (op :: rest)).2.items := by rw [← h_out_eq]

end PrioQueue
