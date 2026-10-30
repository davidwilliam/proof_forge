import PrioQueue.Spec
namespace PrioQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid Sorted <;> infer_instance

def ins (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs => if e.prio < x.prio then e :: x :: xs else x :: ins e xs

def step : Impl := fun s op =>
  if Valid s op then
    match op, s.items with
    | .insert e, _ => (.ok, { s with items := ins e s.items })
    | .pop, x :: xs => (.got x, { s with items := xs })
    | .pop, [] => (.rejected, s)
  else (.rejected, s)

theorem ins_split_aux2 (e : Entry) : (l : List Entry) → Sorted l →
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧ (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio)
  | [], _ => ⟨[], [], by simp, by simp [ins], by simp, by simp⟩
  | hd :: tl, hS => by
    have hS_tl : Sorted tl := (List.pairwise_cons.mp hS).2
    have h_head_le : ∀ y ∈ tl, hd.prio ≤ y.prio := (List.pairwise_cons.mp hS).1
    by_cases hlt : e.prio < hd.prio
    · have h_ins : ins e (hd :: tl) = e :: hd :: tl := by simp [ins, hlt]
      refine ⟨[], hd :: tl, by simp, h_ins, by simp, ?_⟩
      intro x hx
      simp at hx
      rcases hx with rfl | hmem
      · exact hlt
      · have hle : hd.prio ≤ x.prio := h_head_le x hmem
        omega
    · have h_nlt : ¬ e.prio < hd.prio := hlt
      have h_ge : hd.prio ≤ e.prio := by omega
      have h_ins_eq : ins e (hd :: tl) = hd :: ins e tl := by simp [ins, h_nlt]
      obtain ⟨l₁, l₂, h_eq, h_ins_tl, h_le1, h_lt2⟩ := ins_split_aux2 e tl hS_tl
      refine ⟨hd :: l₁, l₂, ?_, ?_, ?_, h_lt2⟩
      · simp [h_eq]
      · simp [h_ins_eq, h_ins_tl]
      · intro x hx
        simp at hx
        rcases hx with rfl | hmem
        · exact h_ge
        · exact h_le1 x hmem

theorem dummy : True := trivial

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  unfold step
  have hv : Valid s op := hV
  simp only [hv]
  cases op with
  | insert e => simp
  | pop =>
    cases h : s.items with
    | nil =>
      exfalso
      exact hV.2 h
    | cons hd tl => simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv
  unfold step
  simp [hInv]

theorem req_capacity : CapacityBound step := by
  intro s op hle
  unfold step
  by_cases hv : Valid s op
  · simp only [hv]
    cases op with
    | insert e =>
      simp
      have hlt : s.items.length < s.capacity := by
        unfold Valid at hv
        exact hv.2
      have hlen : (ins e s.items).length = s.items.length + 1 := by
        induction s.items with
        | nil => simp [ins]
        | cons x xs ih => simp [ins]; split <;> simp_all
      omega
    | pop =>
      have hne : s.items ≠ [] := by
        unfold Valid at hv
        exact hv.2
      match hsi : s.items with
      | [] => exact absurd hsi hne
      | hd :: tl =>
        simp
        have : s.items.length = tl.length + 1 := by simp [hsi]
        omega
  · simp only [hv, ↓reduceIte]
    exact hle

theorem req_pop_min : PopMin step := by
  intro s hne
  by_cases hv : Valid s Op.pop
  · cases hs : s.items with
    | nil => have hne2 : s.items ≠ [] := hv.2; rw [hs] at hne2; exact absurd rfl hne2
    | cons hd tl =>
      have hEq1 : (step s Op.pop).1 = .got hd := by unfold step; simp [hv, hs]
      have hEq2 : (step s Op.pop).2.items = tl := by unfold step; simp [hv, hs]
      refine ⟨hd, hEq1, ?_⟩
      rw [hEq2]
      intro x hx
      have hSorted : Sorted s.items := hv.1
      rw [hs] at hSorted
      -- Use pairwise_cons lemma
      have aux : ∀ (hd : Entry) (tl : List Entry), List.Pairwise (fun a b => a.prio ≤ b.prio) (hd :: tl) → ∀ x ∈ tl, hd.prio ≤ x.prio := by
        intro hd tl hP x hx
        induction tl generalizing hd with
        | nil => simp at hx
        | cons y ys ih =>
          have hpair : (∀ b ∈ y :: ys, hd.prio ≤ b.prio) ∧ List.Pairwise (fun a b => a.prio ≤ b.prio) (y :: ys) := (List.pairwise_cons.mp hP)
          have h1 : hd.prio ≤ y.prio := hpair.1 y (by simp)
          simp at hx
          rcases hx with rfl | hmem
          · exact h1
          · have hRest : List.Pairwise (fun a b => a.prio ≤ b.prio) (y :: ys) := hpair.2
            have h2 : y.prio ≤ x.prio := ih y hRest hmem
            exact Nat.le_trans h1 h2
      exact aux hd tl hSorted x hx
  · have heq : (step s Op.pop).1 = .rejected := by unfold step; simp [hv]
    exact absurd heq hne

theorem req_sorted         : KeepsSorted step := sorry

theorem req_insert_effects : InsertEffects step := by
  intro s e hNotRej
  have hValid : Valid s (.insert e) := by
    by_cases hv : Valid s (.insert e)
    · exact hv
    · have hEq : (step s (.insert e)).1 = .rejected := by unfold step; simp [hv]
      exact absurd hEq hNotRej
  have hSorted : Sorted s.items := hValid.1
  have hStepOk : (step s (.insert e)).1 = .ok := by unfold step; simp [hValid]
  have hStepCap : (step s (.insert e)).2.capacity = s.capacity := by unfold step; simp [hValid]
  have hStepItems : (step s (.insert e)).2.items = ins e s.items := by unfold step; simp [hValid]
  refine ⟨hStepOk, hStepCap, ?_⟩
  obtain ⟨l₁, l₂, h_eq, h_ins, h_le1, h_lt2⟩ := ins_split_aux2 e s.items hSorted
  exact ⟨l₁, l₂, h_eq, by rw [hStepItems, h_ins], h_le1, h_lt2⟩

theorem req_pop_effects : PopEffects step := by
  intro s hNotRej
  have hValid : Valid s Op.pop := by
    by_cases hv : Valid s Op.pop
    · exact hv
    · have hEq : (step s Op.pop).1 = .rejected := by unfold step; simp [hv]
      exact absurd hEq hNotRej
  have hSorted : Sorted s.items := hValid.1
  have hNe : s.items ≠ [] := hValid.2
  obtain ⟨hd, tl, hItems⟩ : ∃ hd tl, s.items = hd :: tl := by
    cases hsi : s.items with
    | nil => exact absurd hsi hNe
    | cons hd tl => exact ⟨hd, tl, rfl⟩
  have hStep1 : (step s Op.pop).1 = .got hd := by unfold step; simp [hValid, hItems]
  have hStep2 : (step s Op.pop).2.items = tl := by unfold step; simp [hValid, hItems]
  have hStepCap : (step s Op.pop).2.capacity = s.capacity := by unfold step; simp [hValid, hItems]
  have hSorted' : Sorted (hd :: tl) := hItems ▸ hSorted
  have hAllLe : ∀ x ∈ tl, hd.prio ≤ x.prio := by
    intro x hx
    have aux : ∀ (hd : Entry) (tl : List Entry), List.Pairwise (fun a b => a.prio ≤ b.prio) (hd :: tl) → ∀ x ∈ tl, hd.prio ≤ x.prio := by
      intro hd tl hP x hx
      induction tl generalizing hd with
      | nil => simp at hx
      | cons y ys ih =>
        have hpair2 := (List.pairwise_cons.mp hP)
        have h1 : hd.prio ≤ y.prio := hpair2.1 y (by simp)
        simp at hx
        rcases hx with rfl | hmem
        · exact h1
        · have hRest : List.Pairwise (fun a b => a.prio ≤ b.prio) (y :: ys) := hpair2.2
          have h2 : y.prio ≤ x.prio := ih y hRest hmem
          exact Nat.le_trans h1 h2
    exact aux hd tl hSorted' x hx
  refine ⟨hStepCap, ⟨[], hd, tl, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [hItems]
  · exact hStep1
  · simp [hStep2]
  · intro x hx; simp at hx
  · intro x hx; exact hAllLe x hx

theorem req_fifo_ties      : FifoTies step := sorry

end PrioQueue
