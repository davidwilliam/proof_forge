import FixedWindow.Spec
/-!
# Generic helper lemmas (agent-visible)

Small facts about `lookup`. They are proved, so they add no trust, and they contain
nothing specific to any implementation.
-/

namespace FixedWindow

@[simp] theorem lookup_nil (i : ClientId) : lookup [] i = none := rfl

theorem lookup_cons (c : Client) (cs : List Client) (i : ClientId) :
    lookup (c :: cs) i = if c.id = i then some c else lookup cs i := rfl

/-- A found entry carries the requested id. -/
theorem lookup_id {l : List Client} {i : ClientId} {c : Client} (h : lookup l i = some c) :
    c.id = i := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [lookup_cons] at h
    by_cases hx : x.id = i
    · simp [hx] at h; subst h; exact hx
    · simp [hx] at h; exact ih h

/-- A found entry is a member of the list. -/
theorem lookup_mem {l : List Client} {i : ClientId} {c : Client} (h : lookup l i = some c) :
    c ∈ l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [lookup_cons] at h
    by_cases hx : x.id = i
    · simp [hx] at h; subst h; simp
    · simp [hx] at h; exact List.mem_cons_of_mem _ (ih h)

/-- No entry is found exactly when no member carries the id. -/
theorem lookup_eq_none {l : List Client} {i : ClientId} :
    lookup l i = none ↔ ∀ c ∈ l, c.id ≠ i := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [lookup_cons]
    by_cases hx : x.id = i
    · simp [hx]
    · simp [hx, ih]

end FixedWindow
