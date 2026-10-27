import Reversal.Spec
/-!
# Generic helper lemmas (agent-visible)

Small proved facts about `sumOver`. They add no trust and contain nothing specific to
any implementation.
-/

namespace Reversal

@[simp] theorem sumOver_nil {α : Type} (f : α → Int) : sumOver [] f = 0 := rfl

@[simp] theorem sumOver_cons {α : Type} (a : α) (l : List α) (f : α → Int) :
    sumOver (a :: l) f = f a + sumOver l f := rfl

theorem sumOver_append {α : Type} (l₁ l₂ : List α) (f : α → Int) :
    sumOver (l₁ ++ l₂) f = sumOver l₁ f + sumOver l₂ f := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem sumOver_add {α : Type} (l : List α) (f g : α → Int) :
    sumOver l (fun a => f a + g a) = sumOver l f + sumOver l g := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem sumOver_sub {α : Type} (l : List α) (f g : α → Int) :
    sumOver l (fun a => f a - g a) = sumOver l f - sumOver l g := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem sumOver_congr {α : Type} (l : List α) (f g : α → Int) (h : ∀ a ∈ l, f a = g a) :
    sumOver l f = sumOver l g := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [sumOver_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- Summing an indicator over a duplicate-free list. -/
theorem sumOver_ite_eq {l : List Nat} (hl : l.Nodup) (x : Nat) (c : Int) :
    sumOver l (fun a => if a = x then c else 0) = if x ∈ l then c else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [sumOver_cons, ih hl.2, List.mem_cons]
    by_cases hax : a = x
    · subst hax; simp [hl.1]
    · have : x ≠ a := fun h => hax h.symm
      simp [hax, this]

end Reversal
