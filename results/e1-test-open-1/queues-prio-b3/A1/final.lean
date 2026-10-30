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

theorem ins_split_sorted_aux2 (l : List Entry) (e : Entry) (hs : Sorted l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧ (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
  induction l with
  | nil => exact ⟨[], [], rfl, rfl, by simp, by simp⟩
  | cons x xs ih =>
    have hpair2 := List.pairwise_cons.mp hs
    have hs_tail : Sorted xs := hpair2.2
    have hle_tail : ∀ y ∈ xs, x.prio ≤ y.prio := hpair2.1
    obtain ⟨l₁,l₂,hl_eq,hl_ins,h1,h2⟩ := ih hs_tail
    simp only [ins]
    by_cases hlt : e.prio < x.prio
    · simp [hlt]
      refine ⟨[], x :: xs, rfl, rfl, by simp, ?_⟩
      intro y hy
      have hy' : y = x ∨ y ∈ xs := by
        simp [List.mem_cons] at hy
        exact hy
      rcases hy' with rfl | hy2
      · exact hlt
      · have hxle := hle_tail y hy2
        omega
    · simp [hlt]
      have hxle : x.prio ≤ e.prio := by omega
      refine ⟨x :: l₁, l₂, ?_, ?_, ?_, h2⟩
      · simp [hl_eq]
      · simp [hl_ins]
      · intro y hy
        rw [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hxle
        · exact h1 y hy

theorem valid_of_not_rejected_insert_aux2 : ∀ {s : State} {e : Entry}, (step s (Op.insert e)).1 ≠ .rejected → Valid s (Op.insert e) := by
  intro s e h
  by_cases hv : Valid s (Op.insert e)
  · exact hv
  · have : step s (Op.insert e) = (.rejected, s) := by simp [step, hv]
    rw [this] at h
    exact absurd rfl h

theorem classOf_append_lem2 (p : Nat) (l₁ l₂ : List Entry) : classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by
  simp [classOf, List.filter_append]

theorem mem_ins_lem3 (e : Entry) (l : List Entry) (y : Entry) (h : y ∈ ins e l) : y ∈ l ∨ y = e := by
  induction l with
  | nil => simp [ins] at h; exact Or.inr h
  | cons x xs ih =>
    simp only [ins] at h
    split at h
    · simp at h; rcases h with rfl | rfl | hmem
      · exact Or.inr rfl
      · exact Or.inl (List.Mem.head _)
      · exact Or.inl (List.Mem.tail _ hmem)
    · simp at h
      rcases h with rfl | hmem
      · exact Or.inl (List.Mem.head _)
      · have hor := ih hmem
        rcases hor with hm | rfl
        · exact Or.inl (List.Mem.tail _ hm)
        · exact Or.inr rfl

theorem ins_sorted_lem3 : ∀ (l : List Entry) (e : Entry), Sorted l → Sorted (ins e l) := by
  intro l e hs
  induction l with
  | nil =>
    simp [ins, Sorted]
  | cons x xs ih =>
    have hpair := List.pairwise_cons.mp hs
    simp only [ins]
    by_cases hlt : e.prio < x.prio
    · simp [hlt]
      apply List.pairwise_cons.mpr
      constructor
      · intro y hy
        have hy' : y = x ∨ y ∈ xs := by
          simp at hy; exact hy
        rcases hy' with rfl | hym
        · omega
        · have h1 := hpair.1 y hym; omega
      · exact hs
    · simp [hlt]
      have hs_tail : Sorted xs := hpair.2
      have ih' := ih hs_tail
      apply List.pairwise_cons.mpr
      constructor
      · intro y hy
        have hmem := mem_ins_lem3 e xs y hy
        rcases hmem with hym | rfl
        · exact hpair.1 y hym
        · omega
      · exact ih'

def dummyAux : Nat := 0

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  simp only [step, hV, ↓reduceIte]
  cases op with
  | insert e => simp
  | pop =>
    simp only [Valid] at hV
    obtain ⟨_, hne⟩ := hV
    cases h : s.items with
    | nil => contradiction
    | cons hd tl => simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  simp only [step, h, ↓reduceIte]

theorem req_capacity : CapacityBound step := by
  intro s op hle
  by_cases hv : Valid s op
  · cases op with
    | insert e =>
      have h1 : (ins e s.items).length = s.items.length + 1 := by
        induction s.items with
        | nil => simp [ins]
        | cons x xs ih => simp [ins]; split <;> simp [ih]
      have hstep : (step s (Op.insert e)).2.items = ins e s.items := by simp [step, hv]
      have hcap : (step s (Op.insert e)).2.capacity = s.capacity := by simp [step, hv]
      rw [hstep, hcap, h1]
      simp only [Valid] at hv
      omega
    | pop =>
      cases h : s.items with
      | nil =>
        simp only [Valid] at hv
        obtain ⟨_, hne⟩ := hv
        contradiction
      | cons hd tl =>
        have hstep1 : (step s Op.pop).2.items.length = tl.length := by simp [step, hv, h]
        have hcap1 : (step s Op.pop).2.capacity = s.capacity := by simp [step, hv, h]
        rw [hstep1, hcap1]
        have : s.items.length = tl.length + 1 := by simp [h]
        omega
  · have hstep : step s op = (.rejected, s) := by simp [step, hv]
    simp [hstep, hle]

theorem req_pop_min : PopMin step := by
  intro s h
  have hV : Valid s Op.pop := by
    by_cases hv : Valid s Op.pop
    · exact hv
    · have : step s Op.pop = (.rejected, s) := by simp only [step, hv, ↓reduceIte]
      rw [this] at h
      exact absurd rfl h
  have hSorted : Sorted s.items := hV.1
  have hne : s.items ≠ [] := hV.2
  obtain ⟨hd, tl, hEq⟩ : ∃ hd tl, s.items = hd :: tl := by
    cases hs : s.items with
    | nil => exact absurd hs hne
    | cons hd tl => exact ⟨hd, tl, rfl⟩
  have hStep1 : (step s Op.pop).1 = .got hd := by simp [step, hV, hEq]
  have hStep2 : (step s Op.pop).2.items = tl := by simp [step, hV, hEq]
  refine ⟨hd, hStep1, ?_⟩
  rw [hStep2]
  intro x hx
  have hPair : List.Pairwise (fun a b => a.prio ≤ b.prio) (hd :: tl) := by rwa [←hEq]
  have hPair2 := List.pairwise_cons.mp hPair
  exact hPair2.1 x hx

theorem req_sorted : KeepsSorted step := by
  intro s op hs
  by_cases hv : Valid s op
  · cases op with
    | insert e =>
      have hItems : (step s (Op.insert e)).2.items = ins e s.items := by simp [step, hv]
      rw [hItems]
      exact ins_sorted_lem3 s.items e hs
    | pop =>
      have hne : s.items ≠ [] := hv.2
      cases h : s.items with
      | nil => contradiction
      | cons hd tl =>
        have hstep : (step s Op.pop).2.items = tl := by simp [step, hv, h]
        rw [hstep]
        have hs' : Sorted (hd :: tl) := by rwa [←h]
        exact (List.pairwise_cons.mp hs').2
  · have hstep : step s op = (.rejected, s) := by simp [step, hv]
    simp [hstep, hs]

theorem req_insert_effects : InsertEffects step := by
  intro s e h
  have hV : Valid s (Op.insert e) := valid_of_not_rejected_insert_aux2 h
  have hOk : (step s (Op.insert e)).1 = .ok := by simp [step, hV]
  have hCap : (step s (Op.insert e)).2.capacity = s.capacity := by simp [step, hV]
  have hItems : (step s (Op.insert e)).2.items = ins e s.items := by simp [step, hV]
  refine ⟨hOk, hCap, ?_⟩
  obtain ⟨l₁,l₂,hl,hl2,h1,h2⟩ := ins_split_sorted_aux2 s.items e hV.1
  exact ⟨l₁,l₂,hl, by rw [hItems, hl2], h1, h2⟩

theorem req_pop_effects : PopEffects step := by
  intro s h
  have hV : Valid s Op.pop := by
    by_cases hv : Valid s Op.pop
    · exact hv
    · have : step s Op.pop = (.rejected, s) := by simp [step, hv]
      rw [this] at h
      exact absurd rfl h
  have hNotEmpty : s.items ≠ [] := hV.2
  have hSorted : Sorted s.items := hV.1
  obtain ⟨hd, tl, hEq⟩ : ∃ hd tl, s.items = hd :: tl := by
    cases hs : s.items with
    | nil => exact absurd hs hNotEmpty
    | cons hd tl => exact ⟨hd, tl, rfl⟩
  have hGot : (step s Op.pop).1 = .got hd := by simp [step, hV, hEq]
  have hItems : (step s Op.pop).2.items = tl := by simp [step, hV, hEq]
  have hCap : (step s Op.pop).2.capacity = s.capacity := by simp [step, hV, hEq]
  refine ⟨hCap, [], hd, tl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hEq]
  · exact hGot
  · simp [hItems]
  · intro x hx; simp at hx
  · intro x hx
    have hPair : List.Pairwise (fun a b => a.prio ≤ b.prio) (hd :: tl) := by rwa [←hEq]
    have hPair2 := List.pairwise_cons.mp hPair
    exact hPair2.1 x hx

theorem req_fifo_ties      : FifoTies step := sorry

end PrioQueue
