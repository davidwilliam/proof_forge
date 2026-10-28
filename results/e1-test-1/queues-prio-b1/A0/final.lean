import PrioQueue.Spec
namespace PrioQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid Sorted <;> infer_instance

def ins (e : Entry) (l : List Entry) : List Entry :=
  match l with
  | [] => [e]
  | x :: xs => if x.prio ≤ e.prio then x :: ins e xs else e :: x :: xs

def step : Impl := fun s op =>
  if Valid s op then
    match op, s.items with
    | .insert e, _ => (.ok, { s with items := ins e s.items })
    | .pop, x :: xs => (.got x, { s with items := xs })
    | .pop, [] => (.rejected, s)
  else (.rejected, s)

/-! Helpers -/

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases hfb : (a == b) with
  | true =>
    exfalso
    exact h (LawfulBEq.eq_of_beq hfb)
  | false => rfl

theorem ins_length (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l
  · simp [ins]
  · next x xs ih =>
    by_cases h : x.prio ≤ e.prio
    · simp [ins, h, ih, Nat.add_assoc]
    · simp [ins, h]

theorem mem_ins (e y : Entry) (l : List Entry) : y ∈ ins e l ↔ y = e ∨ y ∈ l := by
  induction l
  · simp [ins]
  · next x xs ih =>
    by_cases h : x.prio ≤ e.prio
    · have e1 : ins e (x :: xs) = x :: ins e xs := by simp [ins, h]
      simp only [e1, List.mem_cons, ih]
      constructor
      · intro hy
        rcases hy with rfl | rfl | hmem
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hmem)
      · intro hy
        rcases hy with rfl | rfl | hmem
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hmem)
    · have e2 : ins e (x :: xs) = e :: x :: xs := by simp [ins, h]
      simp only [e2, List.mem_cons]

theorem sorted_tail {x : Entry} {xs : List Entry} : Sorted (x :: xs) → Sorted xs := by
  intro h
  unfold Sorted at h ⊢
  cases h with
  | cons h1 h2 => exact h2

theorem sorted_head_le {x y : Entry} {xs : List Entry} :
    Sorted (x :: xs) → y ∈ xs → x.prio ≤ y.prio := by
  intro h hy
  unfold Sorted at h
  cases h with
  | cons h1 h2 => exact h1 y hy

theorem sorted_singleton (x : Entry) : Sorted [x] := by
  unfold Sorted
  exact .cons (by simp) .nil

theorem sorted_nil : Sorted [] := by
  unfold Sorted
  exact .nil

theorem ins_sorted (e : Entry) (l : List Entry) : Sorted l → Sorted (ins e l) := by
  induction l
  · intro _
    simp [ins]
    exact sorted_singleton e
  · next x xs ih =>
    intro hs
    have hs_tail : Sorted xs := sorted_tail hs
    have ih' := ih hs_tail
    by_cases hle : x.prio ≤ e.prio
    · have heq : ins e (x :: xs) = x :: ins e xs := by simp [ins, hle]
      rw [heq]
      exact .cons (by
        intro y hy
        have hor := (mem_ins e y xs).mp hy
        cases hor with
        | inl heq2 => rw [heq2]; exact hle
        | inr hyxs => exact sorted_head_le hs hyxs) ih'
    · have heq : ins e (x :: xs) = e :: x :: xs := by simp [ins, hle]
      rw [heq]
      have hlt : e.prio < x.prio := Nat.lt_of_not_ge hle
      have hall : ∀ y ∈ (x :: xs), e.prio ≤ y.prio := by
        intro y hy
        simp [List.mem_cons] at hy
        cases hy with
        | inl hxy => rw [hxy]; exact Nat.le_of_lt hlt
        | inr hyxs =>
          have hxle : x.prio ≤ y.prio := sorted_head_le hs hyxs
          exact Nat.le_trans (Nat.le_of_lt hlt) hxle
      exact .cons hall hs

theorem ins_split (e : Entry) (l : List Entry) :
    Sorted l → ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l
  · intro _
    exact ⟨[], [], rfl, by simp [ins], by simp, by simp⟩
  · next x xs ih =>
    intro hs
    have hs_tail : Sorted xs := sorted_tail hs
    obtain ⟨l1', l2', h_eq, h_ins, h_le, h_lt⟩ := ih hs_tail
    by_cases hle : x.prio ≤ e.prio
    · refine ⟨x :: l1', l2', ?_, ?_, ?_, h_lt⟩
      · simp [h_eq]
      · have heq : ins e (x :: xs) = x :: ins e xs := by simp [ins, hle]
        rw [heq, h_ins, List.cons_append]
      · intro y hy
        simp [List.mem_cons] at hy
        cases hy with
        | inl hxy => rw [hxy]; exact hle
        | inr hy2 => exact h_le y hy2
    · refine ⟨[], x :: xs, rfl, ?_, by simp, ?_⟩
      · simp [ins, hle]
      · intro y hy
        have hlt : e.prio < x.prio := Nat.lt_of_not_ge hle
        simp only [List.mem_cons] at hy
        cases hy with
        | inl hxy => rw [hxy]; exact hlt
        | inr hyxs =>
          have hxle : x.prio ≤ y.prio := sorted_head_le hs hyxs
          exact Nat.lt_of_lt_of_le hlt hxle

theorem class_append (p : Nat) (l1 l2 : List Entry) :
    classOf p (l1 ++ l2) = classOf p l1 ++ classOf p l2 := by
  simp [classOf]

theorem class_single_eq (p : Nat) (e : Entry) (h : e.prio = p) :
    classOf p [e] = [e] := by
  have hbeq : (e.prio == p) = true := by simp [h]
  simp [classOf, hbeq]

theorem class_single_ne (p : Nat) (e : Entry) (h : e.prio ≠ p) :
    classOf p [e] = [] := by
  have hbeq : (e.prio == p) = false := beq_false_of_ne h
  simp [classOf, hbeq]

theorem filter_empty_of_ne (p : Nat) (l : List Entry) :
    (∀ y ∈ l, y.prio ≠ p) → classOf p l = [] := by
  induction l
  · intro _; simp [classOf]
  · next z zs ih =>
    intro hall
    have hz : z.prio ≠ p := hall z (by simp)
    have hzs : ∀ y ∈ zs, y.prio ≠ p :=
      fun y hy => hall y (List.mem_cons_of_mem _ hy)
    have ih' : classOf p zs = [] := ih hzs
    have h_single : classOf p [z] = [] := class_single_ne p z hz
    have h_app : classOf p ([z] ++ zs) = classOf p [z] ++ classOf p zs :=
      class_append p [z] zs
    have heq : ([z] ++ zs) = (z :: zs) := rfl
    calc classOf p (z :: zs)
        = classOf p ([z] ++ zs) := by rw [heq]
      _ = classOf p [z] ++ classOf p zs := h_app
      _ = [] ++ [] := by rw [h_single, ih']
      _ = [] := by simp

theorem class_ins (p : Nat) (e : Entry) (l : List Entry) :
    Sorted l → classOf p (ins e l) = classOf p l ++ classOf p [e] := by
  intro hs
  obtain ⟨l1, l2, heq1, heq2, hle, hlt⟩ := ins_split e l hs
  have h1 : classOf p l = classOf p l1 ++ classOf p l2 := by
    rw [heq1]
    exact class_append p l1 l2
  have h3 : classOf p (e :: l2) = classOf p [e] ++ classOf p l2 := by
    have h := class_append p [e] l2
    simpa using h
  have h2 : classOf p (ins e l) = classOf p l1 ++ (classOf p [e] ++ classOf p l2) := by
    rw [heq2]
    rw [class_append p l1 (e :: l2), h3]
  rw [h2, h1]
  by_cases he : e.prio = p
  · have h_l2_empty : classOf p l2 = [] := filter_empty_of_ne p l2 (by
      intro y hy
      have hlt_y : e.prio < y.prio := hlt y hy
      rw [he] at hlt_y
      omega)
    have h_e_single : classOf p [e] = [e] := class_single_eq p e he
    simp [h_l2_empty, h_e_single]
  · have h_e_empty : classOf p [e] = [] := class_single_ne p e he
    rw [h_e_empty]
    simp

theorem step_rejected_of_invalid (s : State) (op : Op) (h : ¬ Valid s op) :
    step s op = (.rejected, s) := by
  unfold step
  rw [if_neg h]

theorem valid_of_success (s : State) (op : Op) (h : (step s op).1 ≠ .rejected) :
    Valid s op := by
  by_cases hv : Valid s op
  · exact hv
  · exfalso
    apply h
    rw [step_rejected_of_invalid s op hv]

theorem inflow_cons (hd : Op × Outcome) (tl : List (Op × Outcome)) :
    inflow (hd :: tl) = inflowOf hd ++ inflow tl := by
  simp [inflow]

theorem outflow_cons (hd : Op × Outcome) (tl : List (Op × Outcome)) :
    outflow (hd :: tl) = outflowOf hd ++ outflow tl := by
  simp [outflow]

theorem class_nil (p : Nat) : classOf p ([] : List Entry) = [] := by
  simp [classOf]

/-! Single-step FIFO preservation -/

theorem step_class (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
      = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  cases op with
  | insert e =>
    by_cases hvalid : Valid s (.insert e)
    · have hsorted : Sorted s.items := hvalid.1
      have hstep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
        unfold step
        rw [if_pos hvalid]
      have hfst : (step s (.insert e)).1 = .ok := by rw [hstep]
      have hsnd : (step s (.insert e)).2.items = ins e s.items := by rw [hstep]
      have ho_in : inflowOf (.insert e, (step s (.insert e)).1) = [e] := by
        rw [hfst]; rfl
      have ho_out : outflowOf (.insert e, (step s (.insert e)).1) = ([] : List Entry) := by
        rw [hfst]; rfl
      rw [ho_in, ho_out, hsnd, class_nil, List.nil_append]
      exact (class_ins p e s.items hsorted).symm
    · have hstep := step_rejected_of_invalid s (.insert e) hvalid
      have hfst : (step s (.insert e)).1 = .rejected := by rw [hstep]
      have hsnd : (step s (.insert e)).2.items = s.items := by rw [hstep]
      have ho_in : inflowOf (.insert e, (step s (.insert e)).1) = ([] : List Entry) := by
        rw [hfst]; rfl
      have ho_out : outflowOf (.insert e, (step s (.insert e)).1) = ([] : List Entry) := by
        rw [hfst]; rfl
      simp [ho_in, ho_out, hsnd, class_nil]
  | pop =>
    by_cases hvalid : Valid s .pop
    · have hne : s.items ≠ [] := hvalid.2
      obtain ⟨x, xs, hitems⟩ : ∃ x xs, s.items = x :: xs := by
        match h : s.items with
        | [] => exact absurd h hne
        | _ :: _ => exact ⟨_, _, rfl⟩
      have hstep : step s .pop = (.got x, { s with items := xs }) := by
        unfold step
        rw [if_pos hvalid]
        rw [hitems]
      have hfst : (step s .pop).1 = .got x := by rw [hstep]
      have hsnd : (step s .pop).2.items = xs := by rw [hstep]
      have ho_in : inflowOf (.pop, (step s .pop).1) = ([] : List Entry) := by
        rw [hfst]; rfl
      have ho_out : outflowOf (.pop, (step s .pop).1) = [x] := by
        rw [hfst]; rfl
      rw [ho_in, ho_out, hsnd, hitems, class_nil, List.append_nil]
      simpa using (class_append p [x] xs)
    · have hstep := step_rejected_of_invalid s .pop hvalid
      have hfst : (step s .pop).1 = .rejected := by rw [hstep]
      have hsnd : (step s .pop).2.items = s.items := by rw [hstep]
      have ho_in : inflowOf (.pop, (step s .pop).1) = ([] : List Entry) := by
        rw [hfst]; rfl
      have ho_out : outflowOf (.pop, (step s .pop).1) = ([] : List Entry) := by
        rw [hfst]; rfl
      simp [ho_in, ho_out, hsnd, class_nil]

/-! Required theorems -/

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  unfold step
  rw [if_pos h]
  cases op with
  | insert e => simp
  | pop =>
    cases hitems : s.items with
    | nil =>
      exfalso
      have hne : s.items ≠ [] := h.2
      rw [hitems] at hne
      simp at hne
    | cons x xs => simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  exact step_rejected_of_invalid s op h

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | insert e =>
    by_cases hvalid : Valid s (.insert e)
    · have hlt : s.items.length < s.capacity := hvalid.2
      have hstep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
        unfold step
        rw [if_pos hvalid]
      have hlen := ins_length e s.items
      have hgoal : (step s (.insert e)).2.items.length ≤ (step s (.insert e)).2.capacity := by
        rw [hstep]
        simp only
        omega
      exact hgoal
    · have hr := step_rejected_of_invalid s (.insert e) hvalid
      rw [hr]
      exact hle
  | pop =>
    by_cases hvalid : Valid s .pop
    · have hne : s.items ≠ [] := hvalid.2
      obtain ⟨x, xs, hitems⟩ : ∃ x xs, s.items = x :: xs := by
        match h : s.items with
        | [] => exact absurd h hne
        | _ :: _ => exact ⟨_, _, rfl⟩
      have hstep : step s .pop = (.got x, { s with items := xs }) := by
        unfold step
        rw [if_pos hvalid]
        rw [hitems]
      have hgoal : (step s .pop).2.items.length ≤ (step s .pop).2.capacity := by
        rw [hstep]
        simp only
        have h1 : s.items.length = xs.length + 1 := by rw [hitems]; simp
        omega
      exact hgoal
    · have hr := step_rejected_of_invalid s .pop hvalid
      rw [hr]
      exact hle

theorem req_pop_min : PopMin step := by
  intro s hne
  have hv := valid_of_success s .pop hne
  have hsorted : Sorted s.items := hv.1
  have hne2 : s.items ≠ [] := hv.2
  cases hitems : s.items with
  | nil =>
    exfalso
    exact hne2 hitems
  | cons x xs =>
    have hstep : step s .pop = (.got x, { s with items := xs }) := by
      unfold step
      rw [if_pos hv]
      simp [hitems]
    refine ⟨x, ?_, ?_⟩
    · rw [hstep]
    · rw [hstep]
      simp only
      intro y hy
      exact sorted_head_le (by rw [← hitems]; exact hsorted) hy

theorem req_sorted : KeepsSorted step := by
  intro s op hsorted
  cases op with
  | insert e =>
    by_cases hvalid : Valid s (.insert e)
    · have hstep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
        unfold step
        rw [if_pos hvalid]
      rw [hstep]
      simp only
      exact ins_sorted e s.items hsorted
    · rw [step_rejected_of_invalid s (.insert e) hvalid]
      exact hsorted
  | pop =>
    by_cases hvalid : Valid s .pop
    · have hne : s.items ≠ [] := hvalid.2
      obtain ⟨x, xs, hitems⟩ : ∃ x xs, s.items = x :: xs := by
        match h : s.items with
        | [] => exact absurd h hne
        | _ :: _ => exact ⟨_, _, rfl⟩
      have hstep : step s .pop = (.got x, { s with items := xs }) := by
        unfold step
        rw [if_pos hvalid]
        rw [hitems]
      rw [hstep]
      simp only
      have hsorted' : Sorted (x :: xs) := by rw [← hitems]; exact hsorted
      exact sorted_tail hsorted'
    · rw [step_rejected_of_invalid s .pop hvalid]
      exact hsorted

theorem req_insert_effects : InsertEffects step := by
  intro s e hne
  have hv := valid_of_success s (.insert e) hne
  have hstep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := by
    unfold step
    rw [if_pos hv]
  have h1 : (step s (.insert e)).1 = .ok := by rw [hstep]
  have h2 : (step s (.insert e)).2.capacity = s.capacity := by rw [hstep]
  refine ⟨h1, h2, ?_⟩
  have hsorted : Sorted s.items := hv.1
  obtain ⟨l1, l2, heq1, heq2, hle, hlt⟩ := ins_split e s.items hsorted
  refine ⟨l1, l2, heq1, ?_, hle, hlt⟩
  rw [hstep]
  simp [heq2]

theorem req_pop_effects : PopEffects step := by
  intro s hne
  have hv := valid_of_success s .pop hne
  have hsorted : Sorted s.items := hv.1
  have hne2 : s.items ≠ [] := hv.2
  obtain ⟨x, xs, hitems⟩ : ∃ x xs, s.items = x :: xs := by
    match h : s.items with
    | [] => exact absurd h hne2
    | _ :: _ => exact ⟨_, _, rfl⟩
  have hstep : step s .pop = (.got x, { s with items := xs }) := by
    unfold step
    rw [if_pos hv]
    rw [hitems]
  have hcap : (step s .pop).2.capacity = s.capacity := by rw [hstep]
  refine ⟨hcap, [], x, xs, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hitems]
  · rw [hstep]
  · simp [hstep]
  · intro y hy
    exact absurd hy (by simp)
  · intro y hy
    have hsorted' : Sorted (x :: xs) := by rw [← hitems]; exact hsorted
    exact sorted_head_le hsorted' hy

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  induction ops generalizing s
  · simp [run, inflow, outflow, classOf]
  · next op ops' ih =>
    have h1 : (run step s (op :: ops')).1
        = (op, (step s op).1) :: (run step (step s op).2 ops').1 := rfl
    have h2 : (run step s (op :: ops')).2
        = (run step (step s op).2 ops').2 := rfl
    have hsingle := step_class s op p
    have htail := ih ((step s op).2)
    rw [h1, h2, inflow_cons, outflow_cons]
    have e1 : classOf p (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops').1)
        = classOf p (inflowOf (op, (step s op).1)) ++ classOf p (inflow (run step (step s op).2 ops').1) :=
      class_append _ _ _
    have e2 : classOf p (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops').1)
        = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (outflow (run step (step s op).2 ops').1) :=
      class_append _ _ _
    rw [e1, e2]
    rw [← List.append_assoc, hsingle, List.append_assoc, htail, ← List.append_assoc]

end PrioQueue
