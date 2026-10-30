import ProofForgeFin.Ledger
import ProofForgeFin.Machine.Attr
/-!
# Records, function updates and projections

State machine proofs spend their last steps on bookkeeping: reading a function updated at one
key, pushing a projection through an `if` that builds the next state, and keeping track of
projections of structure literals such as `{ st := st, tr := tr }.st`. This module states those
facts once.

* Function update is `Ledger.upd f k v` (`fun j => if j = k then v else f j`), the form task
  specifications write by hand (`upd` in `rc-knight-router`, `adjust` in the ledger tasks).
  The lemmas: reading at the key and elsewhere, overwriting, commuting updates of different
  keys, updating with the current value, and per-key properties of an updated function.
* Projections of `if` and `dite`: `(if c then x else y).1 = if c then x.1 else y.1` and the same
  for `.2` and for application of an `if` of functions.
* The `machine_norm` tactic: `dsimp only` on the goal and every hypothesis (projections of
  structure literals, `{ s with f := v }.f`, beta reduction), then `simp only [machine_simps]`.

Structure projections of literals and structure eta are definitional in Lean 4: for a structure
`S` with fields `a` and `b`, `({ a := x, b := y } : S).a = x`, `{ s with a := v }.a = v`,
`{ s with a := v }.b = s.b` and `{ a := s.a, b := s.b } = s` all hold by `rfl`, and `rw`, `omega`
and `exact` see through them. What goes wrong in practice is different: after a propositional
rewrite inside a literal (rewriting the router's output in `⟨(step b x.st e).1,
x.tr.record (step b x.st e).2⟩`), a hypothesis stated over the literal and a lemma stated over the
unrewritten term are no longer definitionally equal, and the error message shows both sides with
unreduced projections. The remedy is to rewrite whole-state equations before projecting (state
step lemmas as `step b s e = (s', out)` and use `Machine.couple_of_eq`) and to normalize the goal
and every hypothesis the same way, which `machine_norm` does.
-/

namespace ProofForgeFin.Machine

open Ledger (upd upd_self upd_ne)

universe u v w

variable {κ : Type u} {β : Type v} {γ : Type w}

/-! ## Function update -/

/-- The definition of `upd`, for unfolding. -/
theorem upd_apply [DecidableEq κ] (f : κ → β) (k : κ) (v : β) (j : κ) :
    upd f k v j = if j = k then v else f j := rfl

/-- Other keys are unchanged, with the hypothesis in the order `k ≠ j`. -/
theorem upd_ne' [DecidableEq κ] (f : κ → β) {k j : κ} (v : β) (h : k ≠ j) : upd f k v j = f j :=
  upd_ne f v (fun e => h e.symm)

/-- Reading an update at a key known to be equal to the updated one. -/
theorem upd_of_eq [DecidableEq κ] (f : κ → β) {k j : κ} (v : β) (h : j = k) : upd f k v j = v := by
  subst h; exact upd_self f j v

/-- Updating the same key twice keeps the last value. -/
@[simp, machine_simps] theorem upd_upd_self [DecidableEq κ] (f : κ → β) (k : κ) (v w : β) :
    upd (upd f k v) k w = upd f k w := by
  funext j; unfold upd; split <;> rfl

/-- Updating a key with its current value changes nothing. -/
@[simp, machine_simps] theorem upd_eq_self [DecidableEq κ] (f : κ → β) (k : κ) : upd f k (f k) = f := by
  funext j; unfold upd; split
  · next h => subst h; rfl
  · rfl

/-- Updates of different keys commute. -/
theorem upd_comm [DecidableEq κ] (f : κ → β) {k k' : κ} (v w : β) (h : k ≠ k') :
    upd (upd f k v) k' w = upd (upd f k' w) k v := by
  funext j; unfold upd
  by_cases h1 : j = k'
  · subst h1; simp [Ne.symm h]
  · simp [h1]

/-- An updated function is equal to `g` exactly when the new value is `g k` and every other key
agrees. -/
theorem upd_eq_iff [DecidableEq κ] (f g : κ → β) (k : κ) (v : β) :
    upd f k v = g ↔ v = g k ∧ ∀ j, j ≠ k → f j = g j := by
  constructor
  · intro h; subst h
    exact ⟨(upd_self f k v).symm, fun j hj => (upd_ne f v hj).symm⟩
  · intro ⟨h1, h2⟩
    funext j; unfold upd
    split
    · next h => subst h; exact h1
    · next h => exact h2 j h

/-- Two updates of the same key agree when the values agree and the functions agree elsewhere. -/
theorem upd_congr [DecidableEq κ] {f g : κ → β} (k : κ) {v w : β} (hv : v = w)
    (h : ∀ j, j ≠ k → f j = g j) : upd f k v = upd g k w := by
  funext j; unfold upd; split
  · exact hv
  · next hj => exact h j hj

/-- Applying a function to the values of an updated function updates the composite. -/
theorem comp_upd [DecidableEq κ] (g : β → γ) (f : κ → β) (k : κ) (v : β) :
    (fun j => g (upd f k v j)) = upd (fun j => g (f j)) k (g v) := by
  funext j; unfold upd; split <;> rfl

/-- A per-key property survives an update when it holds for the new value at the updated key
and for the old values at every other key. -/
theorem forall_upd [DecidableEq κ] {P : κ → β → Prop} {f : κ → β} {k : κ} {v : β}
    (hk : P k v) (hother : ∀ j, j ≠ k → P j (f j)) : ∀ j, P j (upd f k v j) := by
  intro j; unfold upd; split
  · next h => subst h; exact hk
  · next h => exact hother j h

/-- The per-key form for a property that held for every key before the update. -/
theorem forall_upd_of_forall [DecidableEq κ] {P : κ → β → Prop} {f : κ → β} {k : κ} {v : β}
    (h : ∀ j, P j (f j)) (hk : P k v) : ∀ j, P j (upd f k v j) :=
  forall_upd hk (fun j _ => h j)

/-- A property of every key after an update is the property at the updated key for the new
value and at every other key for the old value. -/
theorem forall_upd_iff [DecidableEq κ] {P : κ → β → Prop} {f : κ → β} {k : κ} {v : β} :
    (∀ j, P j (upd f k v j)) ↔ P k v ∧ ∀ j, j ≠ k → P j (f j) := by
  constructor
  · intro h
    refine ⟨by simpa using h k, fun j hj => ?_⟩
    have := h j; rwa [upd_ne f v hj] at this
  · intro ⟨hk, h⟩; exact forall_upd hk h

/-- Updating at the key `k` the value computed from the old value at `k`. -/
theorem upd_modify_apply [DecidableEq κ] (f : κ → β) (k : κ) (g : β → β) (j : κ) :
    upd f k (g (f k)) j = if j = k then g (f j) else f j := by
  unfold upd; split
  · next h => subst h; rfl
  · rfl

/-! ## Projections of conditionals -/

/-- The first component of an `if` of pairs. -/
@[machine_simps] theorem fst_ite {α : Type u} {β : Type v} (c : Prop) [Decidable c] (x y : α × β) :
    (if c then x else y).1 = if c then x.1 else y.1 := by
  split <;> rfl

/-- The second component of an `if` of pairs. -/
@[machine_simps] theorem snd_ite {α : Type u} {β : Type v} (c : Prop) [Decidable c] (x y : α × β) :
    (if c then x else y).2 = if c then x.2 else y.2 := by
  split <;> rfl

/-- The first component of a dependent `if` of pairs. -/
@[machine_simps] theorem fst_dite {α : Type u} {β : Type v} (c : Prop) [Decidable c]
    (x : c → α × β) (y : ¬ c → α × β) :
    (if h : c then x h else y h).1 = if h : c then (x h).1 else (y h).1 := by
  split <;> rfl

/-- The second component of a dependent `if` of pairs. -/
@[machine_simps] theorem snd_dite {α : Type u} {β : Type v} (c : Prop) [Decidable c]
    (x : c → α × β) (y : ¬ c → α × β) :
    (if h : c then x h else y h).2 = if h : c then (x h).2 else (y h).2 := by
  split <;> rfl

/-- Applying an `if` of functions. -/
@[machine_simps] theorem ite_apply_fun {α : Type u} {β : Type v} (c : Prop) [Decidable c]
    (f g : α → β) (a : α) : (if c then f else g) a = if c then f a else g a := by
  split <;> rfl

/-- A function applied to an `if`, for any function (the core `apply_ite`, restated for
rewriting from the left). -/
theorem apply_ite' {α : Type u} {β : Type v} (f : α → β) (c : Prop) [Decidable c] (x y : α) :
    f (if c then x else y) = if c then f x else f y :=
  apply_ite f c x y

/-- A pair is determined by its projections. -/
theorem prod_ext_iff {α : Type u} {β : Type v} {p q : α × β} : p = q ↔ p.1 = q.1 ∧ p.2 = q.2 :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => Prod.ext h1 h2⟩

/-- An `if` whose branches agree when the condition holds and when it fails, for proving a
property of the result: the property holds in both branches. -/
theorem ite_prop {α : Type u} {P : α → Prop} (c : Prop) [Decidable c] {x y : α} (hx : c → P x)
    (hy : ¬ c → P y) : P (if c then x else y) := by
  split
  · next h => exact hx h
  · next h => exact hy h

/-! ## Option -/

/-- `getD` of a mapped option. -/
@[machine_simps] theorem getD_map {α : Type u} {β : Type v} (f : α → β) (o : Option α) (d : α) :
    (o.map f).getD (f d) = f (o.getD d) := by
  cases o <;> rfl

/-- An option is `some` of its value with any default, when it is not `none`. -/
theorem eq_some_getD {α : Type u} {o : Option α} (h : o ≠ none) (d : α) : o = some (o.getD d) := by
  cases o with
  | none => exact absurd rfl h
  | some a => rfl

attribute [machine_simps] Ledger.upd_self Seq.run_nil Seq.run_cons Seq.trace_nil Seq.trace_cons
  Ledger.sumOver_nil Ledger.sumOver_cons Seq.runAll_nil Option.getD_some Option.getD_none

/-! ## The `machine_norm` tactic -/

/-- Normalize the goal and every hypothesis of a state machine proof the same way: `dsimp only`
reduces projections of structure literals (`{ st := st, tr := tr }.st` to `st`), projections of
updated structures (`{ s with f := v }.f` to `v`, `{ s with f := v }.g` to `s.g`) and beta
redexes, then `simp only [machine_simps]` reduces function updates read at the updated key,
overwritten updates, projections and applications of `if`, and the unfolding equations tagged by
the library. Neither step fails when it makes no progress. -/
macro "machine_norm" : tactic =>
  `(tactic| ((try dsimp only at *) <;> (try simp only [machine_simps] at *)))

end ProofForgeFin.Machine
