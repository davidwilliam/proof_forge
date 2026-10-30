import PrioQueue.Spec
namespace PrioQueue

instance decSorted (l : List Entry) : Decidable (Sorted l) := by unfold Sorted; infer_instance
instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by cases op <;> unfold Valid <;> infer_instance

def ins (e : Entry) : List Entry → List Entry
| [] => [e]
| x :: xs => if e.prio < x.prio then e :: x :: xs else x :: ins e xs

theorem ins_length (e : Entry) (l : List Entry) : (ins e l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih => simp only [ins]; split <;> simp [ih]

def popRes (s : State) : Outcome × State :=
  match s.items with
  | [] => (.rejected, s)
  | x :: xs => (.got x, { s with items := xs })

def step : Impl := fun s op =>
  if hv : Valid s op then
    match op with
    | .insert e => (.ok, { s with items := ins e s.items })
    | .pop => popRes s
  else (.rejected, s)

theorem step_insert_eq (s : State) (e : Entry) (hv : Valid s (.insert e)) :
    step s (.insert e) = (.ok, { s with items := ins e s.items }) := by simp [step, hv]

theorem step_pop_eq (s : State) (hv : Valid s .pop) : step s .pop = popRes s := by simp [step, hv]

theorem step_rej (s : State) (op : Op) (hv : ¬ Valid s op) : step s op = (.rejected, s) := by simp [step, hv]

theorem sorted_tail_aux {x : Entry} {xs : List Entry} (h : Sorted (x :: xs)) : Sorted xs :=
  (List.pairwise_cons.mp h).2

theorem sorted_head_le_aux {x : Entry} {xs : List Entry} (h : Sorted (x :: xs)) (y : Entry) (hy : y ∈ xs) :
    x.prio ≤ y.prio := by
  induction xs generalizing x with
  | nil => simp at hy
  | cons z zs ih =>
    have hpair := List.pairwise_cons.mp h
    have hxz : x.prio ≤ z.prio := hpair.1 z (List.mem_cons.mpr (Or.inl rfl))
    have htail : Sorted (z :: zs) := hpair.2
    rcases List.mem_cons.mp hy with rfl | hm
    · exact hxz
    · exact Nat.le_trans hxz (ih htail hm)

theorem mem_ins_aux {e y : Entry} {l : List Entry} : y ∈ ins e l → y = e ∨ y ∈ l := by
  induction l with
  | nil => simp [ins]; intro h; exact Or.inl (List.mem_singleton.mp h)
  | cons x xs ih =>
    simp only [ins]; split
    · intro h; rcases List.mem_cons.mp h with rfl | h2
      · exact Or.inl rfl
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
        · simp at h3
    · intro h; rcases List.mem_cons.mp h with rfl | h2
      · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
      · rcases ih h2 with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons.mpr (Or.inr hm))

theorem ins_sorted_aux (e : Entry) (l : List Entry) (hs : Sorted l) : Sorted (ins e l) := by
  induction l with
  | nil => simp [ins, Sorted]
  | cons x xs ih =>
    have hs_tail : Sorted xs := sorted_tail_aux hs
    have ihs := ih hs_tail
    simp only [ins]; split
    · rename_i hlt
      have he_le_x : e.prio ≤ x.prio := by omega
      have he_le_all : ∀ y ∈ x :: xs, e.prio ≤ y.prio := by
        intro y hy; rcases List.mem_cons.mp hy with rfl | hym
        · exact he_le_x
        · exact Nat.le_trans he_le_x (sorted_head_le_aux hs y hym)
      exact List.pairwise_cons.mpr ⟨he_le_all, hs⟩
    · rename_i hge
      have hx_le_e : x.prio ≤ e.prio := by omega
      have hx_le_ins : ∀ y ∈ ins e xs, x.prio ≤ y.prio := by
        intro y hy; rcases mem_ins_aux hy with rfl | hym
        · exact hx_le_e
        · exact sorted_head_le_aux hs y hym
      exact List.pairwise_cons.mpr ⟨hx_le_ins, ihs⟩

theorem ins_split_sorted_aux (e : Entry) (l : List Entry) (hs : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧ (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil => exact ⟨[], [], rfl, rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩
  | cons x xs ih =>
    have hs_tail : Sorted xs := sorted_tail_aux hs
    obtain ⟨l₁, l₂, heq, hins, hle1, hlt2⟩ := ih hs_tail
    simp only [ins]; split
    · rename_i hlt
      exact ⟨[], x :: xs, rfl, rfl, fun _ h => by simp at h, fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hym
        · exact hlt
        · exact Nat.lt_of_lt_of_le hlt (sorted_head_le_aux hs y hym)⟩
    · rename_i hge
      have hxle : x.prio ≤ e.prio := by omega
      refine ⟨x :: l₁, l₂, ?_, ?_, ?_, hlt2⟩
      · simp [heq]
      · simp [hins]
      · intro y hy; rcases List.mem_cons.mp hy with rfl | hym
        · exact hxle
        · exact hle1 y hym

theorem classOf_ins_ne_aux (p : Nat) (e : Entry) (l : List Entry) (hne : e.prio ≠ p) :
    classOf p (ins e l) = classOf p l := by
  induction l with
  | nil => simp [ins, classOf, hne]
  | cons x xs ih =>
    unfold ins
    by_cases hlt : e.prio < x.prio
    · simp [hlt, hne]
      by_cases hx : x.prio == p
      · simp [hx]
      · simp [hx]
    · simp [hlt]
      simp only [classOf, List.filter_cons]
      by_cases hx : x.prio == p
      · simp [hx, ih]
      · simp [hx, ih]

theorem classOf_empty_of_gt_aux (p : Nat) (l : List Entry) (hs : Sorted l)
    (hgt : ∀ y ∈ l, p < y.prio) : classOf p l = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hxgt : p < x.prio := hgt x (List.mem_cons.mpr (Or.inl rfl))
    have hxfalse : (x.prio == p) = false := by simp [Nat.ne_of_gt hxgt]
    have hs_tail := sorted_tail_aux hs
    have ih' := ih hs_tail (fun y hy => hgt y (List.mem_cons.mpr (Or.inr hy)))
    simp [classOf, hxfalse, ih']

theorem classOf_ins_eq_aux (p : Nat) (e : Entry) (l : List Entry) (hs : Sorted l)
    (heq : e.prio = p) : classOf p (ins e l) = classOf p l ++ [e] := by
  induction l with
  | nil => simp [ins, classOf, heq]
  | cons x xs ih =>
    have hs_tail : Sorted xs := sorted_tail_aux hs
    by_cases hlt : e.prio < x.prio
    · have hins : ins e (x :: xs) = e :: x :: xs := by simp [ins, hlt]
      rw [hins]
      have hxne : x.prio ≠ p := by omega
      have hg2 : ∀ y ∈ x :: xs, p < y.prio := by
        intro y hy; rcases List.mem_cons.mp hy with rfl | hym
        · omega
        · have := sorted_head_le_aux hs y hym; omega
      have hempty : classOf p (x :: xs) = [] := classOf_empty_of_gt_aux p (x :: xs) hs hg2
      simp [classOf, hxne, heq, hempty]
    · have hins : ins e (x :: xs) = x :: ins e xs := by simp [ins, hlt]
      rw [hins]
      have ih' := ih hs_tail
      simp [classOf, ih']
      simp

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hv; simp [step, hv]
  cases op with
  | insert e => simp
  | pop =>
    cases hm : s.items with
    | nil => simp [hm] at hv
    | cons x xs => simp [popRes, hm]

theorem req_invalid_noop : InvalidNoop step := by intro s op hn; simp [step, hn]

theorem req_capacity : CapacityBound step := by
  intro s op hle; by_cases hv : Valid s op
  · cases op with
    | insert e =>
      have hstep := step_insert_eq s e hv
      have hlen : s.items.length < s.capacity := hv.2
      simp only [hstep]
      simp
      have : (ins e s.items).length = s.items.length + 1 := ins_length _ _
      omega
    | pop =>
      have hstep := step_pop_eq s hv
      cases hm : s.items with
      | nil => simp [hm] at hv
      | cons x xs =>
        have hpr : popRes s = (.got x, { capacity := s.capacity, items := xs }) := by simp [popRes, hm]
        simp [hstep, hpr]
        have : s.items.length = xs.length + 1 := by simp [hm]
        omega
  · have hstep := step_rej s op hv
    simp [hstep]; exact hle

theorem req_pop_min : PopMin step := by
  intro s hrej
  by_cases hv : Valid s .pop
  · cases hm : s.items with
    | nil => simp [hm] at hv
    | cons x xs =>
      have hstep : step s .pop = (.got x, { capacity := s.capacity, items := xs }) := by
        simp [step_pop_eq s hv, popRes, hm]
      refine ⟨x, by simp [hstep], ?_⟩
      intro y hy
      have hy' : y ∈ xs := by simp [hstep] at hy; exact hy
      have hs : Sorted s.items := hv.1
      exact sorted_head_le_aux (hm ▸ hs) y hy'
  · have hstep := step_rej s .pop hv
    have : (step s .pop).1 = .rejected := by simp [hstep]
    exact False.elim (hrej this)

theorem req_sorted : KeepsSorted step := by
  intro s op hs
  by_cases hv : Valid s op
  · cases op with
    | insert e =>
      have hstep := step_insert_eq s e hv
      simp [hstep]; exact ins_sorted_aux e s.items hs
    | pop =>
      have hstep := step_pop_eq s hv
      cases hm : s.items with
      | nil => simp [hm] at hv
      | cons x xs =>
        have hpr : popRes s = (.got x, { capacity := s.capacity, items := xs }) := by simp [popRes, hm]
        simp [hstep, hpr]; exact sorted_tail_aux (hm ▸ hs)
  · simp [step_rej s op hv, hs]

theorem req_insert_effects : InsertEffects step := by
  intro s e hrej
  by_cases hv : Valid s (.insert e)
  · have hstep := step_insert_eq s e hv
    have hs : Sorted s.items := hv.1
    obtain ⟨l₁, l₂, heq, hins, hle1, hlt2⟩ := ins_split_sorted_aux e s.items hs
    exact ⟨by simp [hstep], by simp [hstep], l₁, l₂, heq, by simp [hstep, hins], hle1, hlt2⟩
  · have hstep := step_rej s (.insert e) hv
    have : (step s (.insert e)).1 = .rejected := by simp [hstep]
    exact False.elim (hrej this)

theorem req_pop_effects : PopEffects step := by
  intro s hrej
  by_cases hv : Valid s .pop
  · have hs : Sorted s.items := hv.1
    cases hm : s.items with
    | nil => simp [hm] at hv
    | cons x xs =>
      have hstep : step s .pop = (.got x, { capacity := s.capacity, items := xs }) := by
        simp [step_pop_eq s hv, popRes, hm]
      exact ⟨by simp [hstep], [], x, xs, by simp [hm], by simp [hstep], by simp [hstep], fun y hy => by simp at hy, fun y hy => exact sorted_head_le_aux (hm ▸ hs) y hy⟩
  · have hstep := step_rej s .pop hv
    have : (step s .pop).1 = .rejected := by simp [hstep]
    exact False.elim (hrej this)

theorem req_fifo_ties : FifoTies step := by
  intro s ops p; induction ops generalizing s with
  | nil => simp [run, classOf, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | insert e =>
      simp only [run]
      by_cases hv : Valid s (.insert e)
      · have hstep : step s (.insert e) = (.ok, { s with items := ins e s.items }) := step_insert_eq s e hv
        rw [hstep]
        have ih' := ih { capacity := s.capacity, items := ins e s.items }
        have hin : inflow ((Op.insert e, Outcome.ok) :: (run step { capacity := s.capacity, items := ins e s.items } ops).1) = e :: inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1 := by simp [inflow, inflowOf]
        have hout : outflow ((Op.insert e, Outcome.ok) :: (run step { capacity := s.capacity, items := ins e s.items } ops).1) = outflow (run step { capacity := s.capacity, items := ins e s.items } ops).1 := by simp [outflow, outflowOf]
        rw [hin, hout]
        by_cases heq : e.prio = p
        · have hs : Sorted s.items := hv.1
          have hclass_ins : classOf p (ins e s.items) = classOf p s.items ++ [e] :=
            classOf_ins_eq_aux p e s.items hs heq
          have hfilter_true : (e.prio == p) = true := by simp [heq]
          have hclass_e : classOf p (e :: inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1) = e :: classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1) := by simp [classOf, hfilter_true]
          calc classOf p s.items ++ classOf p (e :: inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1)
              = classOf p s.items ++ (e :: classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1)) := by rw [hclass_e]
            _ = (classOf p s.items ++ [e]) ++ classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1) := by simp
            _ = classOf p (ins e s.items) ++ classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1) := by rw [hclass_ins]
            _ = _ := ih'
        · have hclass_ins : classOf p (ins e s.items) = classOf p s.items :=
            classOf_ins_ne_aux p e s.items heq
          have hfilter_false : (e.prio == p) = false := by simp [heq]
          have hclass_e : classOf p (e :: inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1) = classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1) := by simp [classOf, hfilter_false]
          calc classOf p s.items ++ classOf p (e :: inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1)
              = classOf p s.items ++ classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1) := by rw [hclass_e]
            _ = classOf p (ins e s.items) ++ classOf p (inflow (run step { capacity := s.capacity, items := ins e s.items } ops).1) := by rw [hclass_ins]
            _ = _ := ih'
      · have hstep : step s (.insert e) = (.rejected, s) := step_rej s (.insert e) hv
        rw [hstep]; simp [inflowOf, outflowOf]; exact ih s
    | pop =>
      simp only [run]
      by_cases hv : Valid s .pop
      · cases hm : s.items with
        | nil => simp [hm] at hv
        | cons x xs =>
          have hstep : step s .pop = (.got x, { capacity := s.capacity, items := xs }) := by
            simp [step_pop_eq s hv, popRes, hm]
          rw [hstep]
          have ih' := ih { capacity := s.capacity, items := xs }
          have hin : inflow ((Op.pop, Outcome.got x) :: (run step { capacity := s.capacity, items := xs } ops).1) = inflow (run step { capacity := s.capacity, items := xs } ops).1 := by simp [inflow, inflowOf]
          have hout : outflow ((Op.pop, Outcome.got x) :: (run step { capacity := s.capacity, items := xs } ops).1) = x :: outflow (run step { capacity := s.capacity, items := xs } ops).1 := by simp [outflow, outflowOf]
          rw [hin, hout]
          by_cases hxeq : x.prio = p
          · have hpop_eq : classOf p (x :: xs) = x :: classOf p xs := by simp [classOf, hxeq]
            have hout_eq : classOf p (x :: outflow (run step { capacity := s.capacity, items := xs } ops).1) = x :: classOf p (outflow (run step { capacity := s.capacity, items := xs } ops).1) := by simp [classOf, hxeq]
            calc classOf p (x :: xs) ++ classOf p (inflow (run step { capacity := s.capacity, items := xs } ops).1)
                = (x :: classOf p xs) ++ classOf p (inflow (run step { capacity := s.capacity, items := xs } ops).1) := by rw [hpop_eq]
              _ = x :: (classOf p xs ++ classOf p (inflow (run step { capacity := s.capacity, items := xs } ops).1)) := by simp
              _ = x :: (classOf p (outflow (run step { capacity := s.capacity, items := xs } ops).1) ++ classOf p (run step { capacity := s.capacity, items := xs } ops).2.items) := by rw [ih']
              _ = (x :: classOf p (outflow (run step { capacity := s.capacity, items := xs } ops).1)) ++ classOf p (run step { capacity := s.capacity, items := xs } ops).2.items := by simp
              _ = _ := by rw [← hout_eq]
          · have hpop_eq : classOf p (x :: xs) = classOf p xs := by simp [classOf, hxeq]
            have hout_eq : classOf p (x :: outflow (run step { capacity := s.capacity, items := xs } ops).1) = classOf p (outflow (run step { capacity := s.capacity, items := xs } ops).1) := by simp [classOf, hxeq]
            rw [hpop_eq, hout_eq, ih']
      · have hstep : step s .pop = (.rejected, s) := step_rej s .pop hv
        rw [hstep]; simp [inflowOf, outflowOf]; exact ih s

end PrioQueue
