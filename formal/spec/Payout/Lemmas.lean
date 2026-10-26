import Payout.Spec
/-!
# Generic helper lemmas (agent-visible)

Small facts about `sumOver` and `indexOf?`. These are proved, so they add no trust; they
exist so that every solution doesn't have to rediscover list bookkeeping. They contain
nothing specific to any implementation.
-/

namespace Payout

@[simp] theorem sumOver_nil {α : Type} (f : α → Int) : sumOver [] f = 0 := rfl

@[simp] theorem sumOver_cons {α : Type} (a : α) (l : List α) (f : α → Int) :
    sumOver (a :: l) f = f a + sumOver l f := rfl

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

theorem indexOf?_eq_none {l : List Nat} {a : Nat} (h : a ∉ l) : indexOf? l a = none := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at h
    simp [indexOf?, Ne.symm h.1, ih h.2]

theorem indexOf?_getElem {l : List Nat} (hl : l.Nodup) (i : Nat) (hi : i < l.length) :
    indexOf? l l[i] = some i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    cases i with
    | zero => simp [indexOf?]
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      have hne : x ≠ xs[i] := fun h => hl.1 (h ▸ List.getElem_mem hi')
      simp [indexOf?, hne, ih hl.2 i hi']

end Payout
