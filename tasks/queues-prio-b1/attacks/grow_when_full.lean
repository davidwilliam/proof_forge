import PrioQueue.Spec
namespace PrioQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid Sorted <;> infer_instance

/-- Insert `e` before the first entry of larger priority. -/
def ins (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs => if e.prio < x.prio then e :: x :: xs else x :: ins e xs

def refStep : Impl := fun s op =>
  if Valid s op then
    match op, s.items with
    | .insert e, _ => (.ok, { s with items := ins e s.items })
    | .pop, x :: xs => (.got x, { s with items := xs })
    | .pop, [] => (.rejected, s)
  else (.rejected, s)

theorem step_invalid {s : State} {op : Op} (h : ¬ Valid s op) : refStep s op = (.rejected, s) := by
  simp [refStep, h]

theorem step_insert {s : State} {e : Entry} (h : Valid s (.insert e)) :
    refStep s (.insert e) = (.ok, { s with items := ins e s.items }) := by
  simp [refStep, h]

theorem step_pop {s : State} {x : Entry} {xs : List Entry} (hs : s.items = x :: xs)
    (h : Valid s .pop) : refStep s .pop = (.got x, { s with items := xs }) := by
  simp [refStep, h, hs]

theorem ok_valid {s : State} {op : Op} (h : (refStep s op).1 ≠ .rejected) : Valid s op := by
  by_cases hv : Valid s op
  · exact hv
  · rw [step_invalid hv] at h; exact absurd rfl h

/-- Where `ins` puts the new entry in a sorted list. -/
theorem ins_split (e : Entry) : ∀ l : List Entry, Sorted l →
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[], [], rfl, rfl, by simp, by simp⟩
  | cons x xs ih =>
    intro hs
    unfold Sorted at hs
    rw [List.pairwise_cons] at hs
    by_cases hlt : e.prio < x.prio
    · refine ⟨[], x :: xs, rfl, by simp [ins, hlt], by simp, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hlt
      · exact Nat.lt_of_lt_of_le hlt (hs.1 y hy)
    · obtain ⟨l₁, l₂, h1, h2, h3, h4⟩ := ih hs.2
      refine ⟨x :: l₁, l₂, by simp [h1], by simp [ins, hlt, h2], ?_, h4⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact h3 y hy

theorem length_ins (e : Entry) : ∀ l : List Entry, (ins e l).length = l.length + 1 := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih => unfold ins; split <;> simp [ih]

/-- Inserting at a split point that respects priorities keeps a list sorted. -/
theorem sorted_insert_at {l₁ l₂ : List Entry} {e : Entry} (hs : Sorted (l₁ ++ l₂))
    (h1 : ∀ x ∈ l₁, x.prio ≤ e.prio) (h2 : ∀ x ∈ l₂, e.prio < x.prio) :
    Sorted (l₁ ++ e :: l₂) := by
  unfold Sorted at *
  rw [List.pairwise_append] at hs ⊢
  refine ⟨hs.1, ?_, ?_⟩
  · rw [List.pairwise_cons]
    exact ⟨fun x hx => Nat.le_of_lt (h2 x hx), hs.2.1⟩
  · intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h1 a ha
    · exact hs.2.2 a ha b hb

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s op h
  cases op with
  | insert e => rw [step_insert h]; simp
  | pop =>
    cases hs : s.items with
    | nil => exact absurd hs h.2
    | cons x xs => rw [step_pop hs h]; simp

theorem ref_req_invalid_noop : InvalidNoop refStep := fun _ _ h => step_invalid h

theorem ref_req_capacity : CapacityBound refStep := by
  intro s op hle
  by_cases hv : Valid s op
  · cases op with
    | insert e => rw [step_insert hv]; simp only [length_ins]; exact hv.2
    | pop =>
      cases hs : s.items with
      | nil => exact absurd hs hv.2
      | cons x xs => rw [step_pop hs hv]; rw [hs] at hle; simp at hle ⊢; omega
  · rw [step_invalid hv]; exact hle

theorem ref_req_pop_min : PopMin refStep := by
  intro s h
  have hv := ok_valid h
  cases hs : s.items with
  | nil => exact absurd hs hv.2
  | cons x xs =>
    rw [step_pop hs hv]
    have hsort := hv.1
    unfold Sorted at hsort
    rw [hs, List.pairwise_cons] at hsort
    exact ⟨x, rfl, hsort.1⟩

theorem ref_req_sorted : KeepsSorted refStep := by
  intro s op hsort
  by_cases hv : Valid s op
  · cases op with
    | insert e =>
      rw [step_insert hv]
      obtain ⟨l₁, l₂, h1, h2, h3, h4⟩ := ins_split e s.items hsort
      show Sorted (ins e s.items)
      rw [h2]; rw [h1] at hsort
      exact sorted_insert_at hsort h3 h4
    | pop =>
      cases hs : s.items with
      | nil => exact absurd hs hv.2
      | cons x xs =>
        rw [step_pop hs hv]
        unfold Sorted at hsort ⊢
        rw [hs, List.pairwise_cons] at hsort
        exact hsort.2
  · rw [step_invalid hv]; exact hsort

theorem ref_req_insert_effects : InsertEffects refStep := by
  intro s e h
  have hv := ok_valid h
  rw [step_insert hv]
  obtain ⟨l₁, l₂, h1, h2, h3, h4⟩ := ins_split e s.items hv.1
  exact ⟨rfl, rfl, l₁, l₂, h1, h2, h3, h4⟩

theorem ref_req_pop_effects : PopEffects refStep := by
  intro s h
  have hv := ok_valid h
  cases hs : s.items with
  | nil => exact absurd hs hv.2
  | cons x xs =>
    rw [step_pop hs hv]
    have hsort := hv.1
    unfold Sorted at hsort
    rw [hs, List.pairwise_cons] at hsort
    exact ⟨rfl, [], x, xs, rfl, rfl, rfl, by simp, hsort.1⟩

/-- Per-priority bookkeeping of one insert at a split point. -/
theorem class_insert_at (p : Nat) {l₁ l₂ : List Entry} {e : Entry}
    (h2 : ∀ x ∈ l₂, e.prio < x.prio) :
    classOf p (l₁ ++ l₂) ++ classOf p [e] = classOf p (l₁ ++ e :: l₂) := by
  unfold classOf
  by_cases hp : e.prio = p
  · have hnil : l₂.filter (fun x => x.prio == p) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      have := h2 x hx
      simp; omega
    simp [List.filter_append, List.filter_cons, hp, hnil]
  · simp [List.filter_append, List.filter_cons, hp]

/-- Per-priority bookkeeping of one pop at a split point. -/
theorem class_pop_at (p : Nat) {l₁ l₂ : List Entry} {e : Entry}
    (h1 : ∀ x ∈ l₁, e.prio < x.prio) :
    classOf p (l₁ ++ e :: l₂) = classOf p [e] ++ classOf p (l₁ ++ l₂) := by
  unfold classOf
  by_cases hp : e.prio = p
  · have hnil : l₁.filter (fun x => x.prio == p) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      have := h1 x hx
      simp; omega
    simp [List.filter_append, List.filter_cons, hp, hnil]
  · simp [List.filter_append, List.filter_cons, hp]

/-- Any implementation whose single steps keep each priority class in order satisfies
REQ-FIFO-TIES. -/
theorem ties_of_flow (st : Impl)
    (h : ∀ s op p, classOf p s.items ++ classOf p (inflowOf (op, (st s op).1))
      = classOf p (outflowOf (op, (st s op).1)) ++ classOf p (st s op).2.items) :
    FifoTies st := by
  intro s ops p
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow, classOf]
  | cons op ops ih =>
    have hc : ∀ a b : List Entry, classOf p (a ++ b) = classOf p a ++ classOf p b := by
      intro a b; simp [classOf, List.filter_append]
    simp only [run, inflow, outflow, List.flatMap_cons, hc] at ih ⊢
    rw [← List.append_assoc, h, List.append_assoc, ih, List.append_assoc]

/-- One refStep of any implementation satisfying the success, no-op and effects requirements
keeps each priority class in order. -/
theorem flow_of_effects (st : Impl) (hs : ValidSucceeds st) (hn : InvalidNoop st)
    (hi : InsertEffects st) (hp : PopEffects st) (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (st s op).1))
      = classOf p (outflowOf (op, (st s op).1)) ++ classOf p (st s op).2.items := by
  by_cases hr : (st s op).1 = .rejected
  · have hnv : ¬ Valid s op := fun h => hs s op h hr
    rw [hn s op hnv]
    cases op <;> simp [inflowOf, outflowOf, classOf]
  · cases op with
    | insert e =>
      obtain ⟨h1, _, l₁, l₂, e1, e2, _, h4⟩ := hi s e hr
      rw [h1, e2, e1, ← class_insert_at p h4]
      simp [inflowOf, outflowOf, classOf]
    | pop =>
      obtain ⟨_, l₁, e, l₂, e1, h1, e2, h3, _⟩ := hp s hr
      rw [h1, e2, e1, class_pop_at p h3]
      simp [inflowOf, outflowOf, classOf]

theorem ref_req_fifo_ties : FifoTies refStep :=
  ties_of_flow refStep (flow_of_effects refStep ref_req_valid_succeeds ref_req_invalid_noop
    ref_req_insert_effects ref_req_pop_effects)

-- Side-effect fix: inserts are correct, but an insert that fills the queue grows the capacity.
def step : Impl := fun s op =>
  match op with
  | .insert e =>
    if (refStep s (.insert e)).1 ≠ .rejected ∧ s.items.length + 1 = s.capacity then
      ((refStep s (.insert e)).1, { (refStep s (.insert e)).2 with capacity := s.capacity + 1 })
    else refStep s (.insert e)
  | .pop => refStep s .pop

theorem fst_eq (s : State) (op : Op) : (step s op).1 = (refStep s op).1 := by
  cases op with
  | insert e => simp only [step]; split <;> rfl
  | pop => rfl
theorem items_eq (s : State) (op : Op) : (step s op).2.items = (refStep s op).2.items := by
  cases op with
  | insert e => simp only [step]; split <;> rfl
  | pop => rfl

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h; rw [fst_eq]; exact ref_req_valid_succeeds s op h
theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | insert e => simp only [step]; rw [ref_req_invalid_noop s _ h]; simp
  | pop => exact ref_req_invalid_noop s _ h
theorem req_capacity : CapacityBound step := by
  intro s op h
  have hr := ref_req_capacity s op h
  cases op with
  | insert e =>
    simp only [step]; split
    · next hg =>
      obtain ⟨_, _, l₁, l₂, e1, e2, _, _⟩ := ref_req_insert_effects s e hg.1
      have h2 := hg.2
      simp only; rw [e2]; rw [e1] at h2; simp at h2 ⊢; omega
    · exact hr
  | pop => exact hr
theorem req_sorted : KeepsSorted step := by
  intro s op h; rw [items_eq]; exact ref_req_sorted s op h
theorem req_pop_min : PopMin step := fun s h => ref_req_pop_min s h
-- Weakened restatement: the capacity after an insert is not promised.
theorem req_insert_effects : ∀ s e, (step s (.insert e)).1 ≠ .rejected →
    (step s (.insert e)).1 = .ok ∧
    ∃ l₁ l₂, s.items = l₁ ++ l₂ ∧ (step s (.insert e)).2.items = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  intro s e h
  rw [fst_eq] at h
  rw [fst_eq, items_eq]
  obtain ⟨h1, _, h3⟩ := ref_req_insert_effects s e h
  exact ⟨h1, h3⟩
theorem req_pop_effects : PopEffects step := fun s h => ref_req_pop_effects s h
theorem req_fifo_ties : FifoTies step := by
  apply ties_of_flow
  intro s op p
  rw [fst_eq, items_eq]
  exact flow_of_effects refStep ref_req_valid_succeeds ref_req_invalid_noop
    ref_req_insert_effects ref_req_pop_effects s op p

end PrioQueue
