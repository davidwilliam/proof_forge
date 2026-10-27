import EntryLog.Spec
/-!
# Generic helper lemmas (agent-visible)

Small proved facts about `sumOver`, `ids` and `receiptOf`. They add no trust and contain
nothing specific to any implementation.
-/

namespace EntryLog

@[simp] theorem sumOver_nil {α : Type} (f : α → Int) : sumOver [] f = 0 := rfl

@[simp] theorem sumOver_cons {α : Type} (a : α) (l : List α) (f : α → Int) :
    sumOver (a :: l) f = f a + sumOver l f := rfl

theorem sumOver_append {α : Type} (l₁ l₂ : List α) (f : α → Int) :
    sumOver (l₁ ++ l₂) f = sumOver l₁ f + sumOver l₂ f := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih]; omega

@[simp] theorem ids_append (l₁ l₂ : List Entry) : ids (l₁ ++ l₂) = ids l₁ ++ ids l₂ := by
  simp [ids]

theorem receiptOf_eq_none {log : List Entry} {i : EntryId} (h : i ∉ ids log) :
    receiptOf log i = none := by
  induction log with
  | nil => rfl
  | cons e es ih =>
    simp only [ids, List.map_cons, List.mem_cons, not_or] at h
    simp [receiptOf, Ne.symm h.1, ih h.2]

theorem receiptOf_isSome {log : List Entry} {i : EntryId} (h : i ∈ ids log) :
    ∃ n, receiptOf log i = some n := by
  induction log with
  | nil => simp [ids] at h
  | cons e es ih =>
    by_cases he : e.id = i
    · exact ⟨0, by simp [receiptOf, he]⟩
    · have h' : i ∈ ids es := by
        simp only [ids, List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm he
        · exact h
      obtain ⟨n, hn⟩ := ih h'
      exact ⟨n + 1, by simp [receiptOf, he, hn]⟩

end EntryLog
