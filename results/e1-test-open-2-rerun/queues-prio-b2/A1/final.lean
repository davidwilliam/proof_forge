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

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  unfold Valid at hV
  unfold step
  split
  · next h =>
    cases op with
    | insert e =>
      simp
    | pop =>
      -- h : Valid s pop, so Sorted ∧ items ≠ []
      have hne : s.items ≠ [] := hV.2
      cases hitems : s.items with
      | nil => contradiction
      | cons hd tl => simp [hitems]
  · contradiction

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  unfold step
  simp only [ite_eq_right_iff]
  intro hV
  exact absurd hV h

theorem req_capacity : CapacityBound step := by
  intro s op hle
  unfold step
  split
  · next hV =>
    cases op with
    | insert e =>
      simp only
      have hlt : s.items.length < s.capacity := by
        have hValid : Valid s (Op.insert e) := hV
        unfold Valid at hValid
        exact hValid.2
      have hlen : (ins e s.items).length = s.items.length + 1 := by
        induction s.items with
        | nil => simp [ins]
        | cons x xs ih =>
          simp [ins]
          split
          · simp
          · simp [ih, Nat.add_assoc]
      simp [hlen]
      omega
    | pop =>
      simp only
      cases hitems : s.items with
      | nil =>
        have hValid : Valid s Op.pop := hV
        unfold Valid at hValid
        have hne : s.items ≠ [] := hValid.2
        rw [hitems] at hne
        contradiction
      | cons hd tl =>
        simp
        have : tl.length ≤ s.items.length := by simp [hitems]
        omega
  · simp [hle]

theorem req_pop_min : PopMin step := by
  intro s h
  unfold step at h ⊢
  by_cases hV : Valid s Op.pop
  · simp only [hV, ite_true] at h ⊢
    cases hitems : s.items with
    | nil =>
      exfalso
      unfold Valid at hV
      simp [hitems] at hV
    | cons hd tl =>
      simp only [hitems] at h ⊢
      simp
      intro x hx
      have hSorted : Sorted s.items := by
        unfold Valid at hV; exact hV.1
      rw [hitems] at hSorted
      unfold Sorted at hSorted
      have hp := (List.pairwise_cons.mp hSorted)
      exact hp.1 x hx
  · simp only [hV, ite_false] at h
    simp at h

theorem req_sorted : KeepsSorted step := by
  intro s op hS
  unfold step
  by_cases hV : Valid s op
  · simp only [hV, ite_true]
    cases op with
    | insert e =>
      simp only
      have go : ∀ (l : List Entry), l.Pairwise (fun a b => a.prio ≤ b.prio) → (ins e l).Pairwise (fun a b => a.prio ≤ b.prio) := by
        intro l
        induction l with
        | nil => intro _; simp [ins]
        | cons x xs ih =>
          intro hPair
          have hp := List.pairwise_cons.mp hPair
          simp only [ins]
          split
          · next hlt =>
            apply List.Pairwise.cons
            · intro y hy
              simp at hy
              rcases hy with rfl | hy2
              · exact Nat.le_of_lt hlt
              · exact Nat.le_trans (Nat.le_of_lt hlt) (hp.1 y hy2)
            · exact hPair
          · next hge =>
            have hle_xe : x.prio ≤ e.prio := Nat.le_of_not_gt hge
            apply List.Pairwise.cons
            · intro y hy
              have hmem_cases : ∀ (ys : List Entry) (z : Entry), z ∈ ins e ys → z = e ∨ z ∈ ys := by
                intro ys
                induction ys with
                | nil => intro z hz; simp [ins] at hz; exact Or.inl hz
                | cons a as ih2 =>
                  intro z hz
                  simp only [ins] at hz
                  split at hz
                  · simp at hz
                    rcases hz with rfl | rfl | hz2
                    · exact Or.inl rfl
                    · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
                    · exact Or.inr (List.mem_cons.mpr (Or.inr hz2))
                  · simp at hz
                    rcases hz with rfl | hz2
                    · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
                    · have h2 := ih2 z hz2
                      rcases h2 with rfl | hm
                      · exact Or.inl rfl
                      · exact Or.inr (List.mem_cons.mpr (Or.inr hm))
              have hc := hmem_cases xs y hy
              rcases hc with rfl | hIn
              · exact hle_xe
              · exact hp.1 y hIn
            · exact ih hp.2
      exact go s.items hS
    | pop =>
      cases hs : s.items with
      | nil => unfold Valid at hV; simp [hs] at hV
      | cons hd tl =>
        have hPair : (hd :: tl).Pairwise (fun a b => a.prio ≤ b.prio) := by rw [← hs]; exact hS
        exact (List.pairwise_cons.mp hPair).2
  · simp only [hV, ite_false]
    exact hS

theorem req_insert_effects : InsertEffects step := by
  intro s e hNe
  by_cases hV : Valid s (Op.insert e)
  · have hStepEq : step s (Op.insert e) = (.ok, { s with items := ins e s.items }) := by
      unfold step; simp [hV]
    have hFst : (step s (Op.insert e)).1 = .ok := by rw [hStepEq]
    have hCap : (step s (Op.insert e)).2.capacity = s.capacity := by rw [hStepEq]
    refine ⟨hFst, hCap, ?_⟩
    have hSorted : Sorted s.items := hV.1
    have hItems : (step s (Op.insert e)).2.items = ins e s.items := by rw [hStepEq]
    have aux : ∀ (l : List Entry), l.Pairwise (fun a b => a.prio ≤ b.prio) →
        ∃ l₁ l₂, l = l₁ ++ l₂ ∧ ins e l = l₁ ++ e :: l₂ ∧ (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio) := by
      intro l
      induction l with
      | nil =>
        intro _
        exact ⟨[], [], by simp, by simp [ins], by simp, by simp⟩
      | cons x xs ih =>
        intro hP
        have hPair := List.pairwise_cons.mp hP
        by_cases he : e.prio < x.prio
        · have hIns : ins e (x :: xs) = e :: x :: xs := by simp [ins, he]
          refine ⟨[], x :: xs, by simp, hIns, by simp, ?_⟩
          intro y hy
          have hxle : x.prio ≤ y.prio := by
            rcases List.mem_cons.mp (show y ∈ x :: xs by simp [hy]) with rfl | hym
            · exact Nat.le_refl _
            · exact hPair.1 y hym
          omega
        · have hIns : ins e (x :: xs) = x :: ins e xs := by simp [ins, he]
          have hle_xe : x.prio ≤ e.prio := Nat.le_of_not_gt he
          obtain ⟨l₁, l₂, hEq, hInsEq, hL₁, hL₂⟩ := ih hPair.2
          refine ⟨x :: l₁, l₂, by simp [hEq], by simp [hIns, hInsEq], ?_, hL₂⟩
          · intro y hy
            simp at hy
            rcases hy with rfl | hm
            · exact hle_xe
            · exact hL₁ y hm
    obtain ⟨l₁, l₂, hEq, hInsEq, h1, h2⟩ := aux s.items hSorted
    exact ⟨l₁, l₂, hEq, by rw [hItems, hInsEq], h1, h2⟩
  · exfalso
    have : (step s (Op.insert e)).1 = .rejected := by unfold step; simp [hV]
    exact hNe this

theorem req_pop_effects : PopEffects step := by
  intro s hNe
  have hV : Valid s Op.pop := by
    by_cases hc : Valid s Op.pop
    · exact hc
    · exfalso
      have hStep : (step s Op.pop).1 = .rejected := by unfold step; simp [hc]
      exact hNe hStep
  unfold step
  simp only [hV, ite_true]
  cases hitems : s.items with
  | nil =>
    unfold Valid at hV
    simp [hitems] at hV
  | cons hd tl =>
    simp
    refine ⟨[], hd, tl, by simp [hitems], rfl, rfl, ?_, ?_⟩
    · intro x hx; cases hx
    · intro x hx
      have hSorted : Sorted s.items := hV.1
      rw [hitems] at hSorted
      exact (List.pairwise_cons.mp hSorted).1 x hx

theorem req_fifo_ties      : FifoTies step := sorry

end PrioQueue
