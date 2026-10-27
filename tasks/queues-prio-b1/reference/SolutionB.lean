import PrioQueue.Spec
/-!
# Reference solution B (hidden from agents)

Order is checked on adjacent pairs; insert splits the list with `takeWhile` and
`dropWhile`; pop matches on the stored list.
-/

namespace PrioQueue

/-- Adjacent-pair check of service order. -/
def inOrder : List Entry → Bool
  | x :: y :: rest => decide (x.prio ≤ y.prio) && inOrder (y :: rest)
  | _ => true

/-- Split at the first entry of larger priority and put `e` there. -/
def insB (e : Entry) (l : List Entry) : List Entry :=
  l.takeWhile (fun x => decide (x.prio ≤ e.prio)) ++ e :: l.dropWhile (fun x => decide (x.prio ≤ e.prio))

def step : Impl
  | s, .insert e =>
    if inOrder s.items = true ∧ s.items.length < s.capacity then
      (.ok, { capacity := s.capacity, items := insB e s.items })
    else (.rejected, s)
  | s, .pop =>
    match s.items with
    | [] => (.rejected, s)
    | x :: xs => if inOrder (x :: xs) = true then (.got x, { capacity := s.capacity, items := xs })
                 else (.rejected, s)

theorem inOrder_iff : ∀ l : List Entry, inOrder l = true ↔ Sorted l := by
  intro l
  induction l with
  | nil => simp [inOrder, Sorted]
  | cons x t ih =>
    cases t with
    | nil => simp [inOrder, Sorted]
    | cons y rest =>
      unfold Sorted at ih ⊢
      simp only [inOrder, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · intro ⟨hxy, hs⟩
        rw [List.pairwise_cons]
        refine ⟨?_, hs⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hxy
        · rw [List.pairwise_cons] at hs
          exact Nat.le_trans hxy (hs.1 z hz)
      · intro h
        rw [List.pairwise_cons] at h
        exact ⟨h.1 y (by simp), h.2⟩

theorem dropWhile_gt (e : Entry) : ∀ l : List Entry, Sorted l →
    ∀ x ∈ l.dropWhile (fun x => decide (x.prio ≤ e.prio)), e.prio < x.prio := by
  intro l
  induction l with
  | nil => simp
  | cons y ys ih =>
    intro hs x hx
    unfold Sorted at hs
    rw [List.pairwise_cons] at hs
    by_cases hy : y.prio ≤ e.prio
    · rw [List.dropWhile_cons_of_pos (by simpa using hy)] at hx
      exact ih hs.2 x hx
    · rw [List.dropWhile_cons_of_neg (by simpa using hy)] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · have := hs.1 x hx; omega

theorem takeWhile_le (e : Entry) : ∀ l : List Entry,
    ∀ x ∈ l.takeWhile (fun x => decide (x.prio ≤ e.prio)), x.prio ≤ e.prio := by
  intro l
  induction l with
  | nil => simp
  | cons y ys ih =>
    intro x hx
    by_cases hy : y.prio ≤ e.prio
    · rw [List.takeWhile_cons_of_pos (by simpa using hy)] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact ih x hx
    · rw [List.takeWhile_cons_of_neg (by simpa using hy)] at hx
      simp at hx

theorem insert_valid {s : State} {e : Entry} (h : Valid s (.insert e)) :
    step s (.insert e) = (.ok, { s with items := insB e s.items }) := by
  have : inOrder s.items = true ∧ s.items.length < s.capacity := ⟨(inOrder_iff _).mpr h.1, h.2⟩
  simp only [step, if_pos this]

theorem insert_invalid {s : State} {e : Entry} (h : ¬ Valid s (.insert e)) :
    step s (.insert e) = (.rejected, s) := by
  have : ¬ (inOrder s.items = true ∧ s.items.length < s.capacity) := by
    rw [inOrder_iff]; exact h
  simp only [step, if_neg this]

theorem pop_valid {s : State} {x : Entry} {xs : List Entry} (hs : s.items = x :: xs)
    (h : Valid s .pop) : step s .pop = (.got x, { s with items := xs }) := by
  have : inOrder (x :: xs) = true := (inOrder_iff _).mpr (hs ▸ h.1)
  simp only [step, hs, if_pos this]

theorem pop_invalid {s : State} (h : ¬ Valid s .pop) : step s .pop = (.rejected, s) := by
  cases hs : s.items with
  | nil => simp only [step, hs]
  | cons x xs =>
    have : ¬ inOrder (x :: xs) = true := by
      rw [inOrder_iff]; intro hso; exact h ⟨hs ▸ hso, by simp [hs]⟩
    simp only [step, hs, if_neg this]

theorem step_invalid {s : State} {op : Op} (h : ¬ Valid s op) : step s op = (.rejected, s) := by
  cases op with
  | insert e => exact insert_invalid h
  | pop => exact pop_invalid h

theorem ok_valid {s : State} {op : Op} (h : (step s op).1 ≠ .rejected) : Valid s op := by
  by_cases hv : Valid s op
  · exact hv
  · rw [step_invalid hv] at h; exact absurd rfl h

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

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | insert e => rw [insert_valid h]; simp
  | pop =>
    cases hs : s.items with
    | nil => exact absurd hs h.2
    | cons x xs => rw [pop_valid hs h]; simp

theorem req_invalid_noop : InvalidNoop step := fun _ _ h => step_invalid h

theorem req_insert_effects : InsertEffects step := by
  intro s e h
  have hv := ok_valid h
  rw [insert_valid hv]
  exact ⟨rfl, rfl, _, _, (List.takeWhile_append_dropWhile).symm, rfl, takeWhile_le e _,
    dropWhile_gt e _ hv.1⟩

theorem req_pop_effects : PopEffects step := by
  intro s h
  have hv := ok_valid h
  cases hs : s.items with
  | nil => exact absurd hs hv.2
  | cons x xs =>
    rw [pop_valid hs hv]
    have hsort := hv.1
    unfold Sorted at hsort
    rw [hs, List.pairwise_cons] at hsort
    exact ⟨rfl, [], x, xs, rfl, rfl, rfl, by simp, hsort.1⟩

theorem req_capacity : CapacityBound step := by
  intro s op hle
  by_cases hv : Valid s op
  · cases op with
    | insert e =>
      obtain ⟨_, hc, l₁, l₂, e1, e2, _, _⟩ := req_insert_effects s e (by rw [insert_valid hv]; simp)
      rw [hc, e2]; have := hv.2; rw [e1] at this; simp at this ⊢; omega
    | pop =>
      cases hs : s.items with
      | nil => exact absurd hs hv.2
      | cons x xs => rw [pop_valid hs hv]; rw [hs] at hle; simp at hle ⊢; omega
  · rw [step_invalid hv]; exact hle

theorem req_pop_min : PopMin step := by
  intro s h
  obtain ⟨_, l₁, e, l₂, e1, h1, e2, h3, h4⟩ := req_pop_effects s h
  refine ⟨e, h1, ?_⟩
  rw [e2]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Nat.le_of_lt (h3 x hx)
  · exact h4 x hx

theorem req_sorted : KeepsSorted step := by
  intro s op hsort
  by_cases hr : (step s op).1 = .rejected
  · have hnv : ¬ Valid s op := fun h => req_valid_succeeds s op h hr
    rw [step_invalid hnv]; exact hsort
  · cases op with
    | insert e =>
      obtain ⟨_, _, l₁, l₂, e1, e2, h3, h4⟩ := req_insert_effects s e hr
      rw [e2]; rw [e1] at hsort
      exact sorted_insert_at hsort h3 h4
    | pop =>
      obtain ⟨_, l₁, e, l₂, e1, _, e2, _, _⟩ := req_pop_effects s hr
      rw [e2]; rw [e1] at hsort
      unfold Sorted at hsort ⊢
      rw [List.pairwise_append, List.pairwise_cons] at hsort
      rw [List.pairwise_append]
      exact ⟨hsort.1, hsort.2.1.2, fun a ha b hb => hsort.2.2 a ha b (List.mem_cons_of_mem _ hb)⟩

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
    simp [List.filter_append, hp, hnil]
  · simp [List.filter_append, hp]

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
    simp [List.filter_append, hp, hnil]
  · simp [List.filter_append, hp]

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

/-- One step of any implementation satisfying the success, no-op and effects requirements
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

theorem req_fifo_ties : FifoTies step :=
  ties_of_flow step (flow_of_effects step req_valid_succeeds req_invalid_noop
    req_insert_effects req_pop_effects)

end PrioQueue
