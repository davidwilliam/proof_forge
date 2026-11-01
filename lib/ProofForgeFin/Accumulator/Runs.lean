import ProofForgeFin.Seq
/-!
# Induction over sequences of actions

A sequence-level bound is proved in three layers, and this module gives each layer its induction
principle so that a proof supplies only local facts.

* One action is a chain of primitive moves. An action of a protocol (a deposit, a claim, a speed
  change) runs one or more primitive transitions (an index update with a settlement, a balance
  change of a settled account, a payment), each of which may be refused. `Moves R s t` is the
  reflexive-transitive closure of a primitive relation `R`; a proof shows once that every action
  other than the passage of time is a chain of moves (`Moves.of_getD` for a call that may fail),
  and `Moves.bound` turns a bound on every primitive move into a bound on the action, for every
  potential at once.
* A run is a list of actions. Specifications define their own `run`, ghost totals (rewards
  emitted, which depend on the rates set by earlier actions) and ghost states (the rates after a
  run) by structural recursion; `run_bound` takes their defining equations as hypotheses, so it
  applies to them directly, without restating them in the library's terms
  (`run_eq_seq`, `total_eq_accum`, `ghost_eq_seq` restate them when that is wanted);
  `run_invariant` is its invariant half and `run_bound_after` the bound over a run that follows
  any history.
* From a potential to an amount. A potential at scale `c` that covers the amount (`Q * c ≤ P`)
  and grows by at most `c` times the emission bounds the amount by its start value, the
  remainder of the start potential rounded down once, and the emission (`amount_le_of_scaled`);
  with no remainder, by the start value and the emission (`amount_le_of_scaled_exact`).
-/

namespace ProofForgeFin.Accumulator

universe u v w

variable {σ : Type u} {α : Type v} {γ : Type w}

/-! ## Chains of primitive moves -/

/-- `Moves R s t`: `t` is reached from `s` by finitely many moves of `R`. -/
inductive Moves (R : σ → σ → Prop) : σ → σ → Prop
  /-- No move. -/
  | refl (s : σ) : Moves R s s
  /-- A chain followed by one more move. -/
  | tail {s t t' : σ} : Moves R s t → R t t' → Moves R s t'

namespace Moves

variable {R R' : σ → σ → Prop}

/-- One move is a chain. -/
theorem single {s t : σ} (h : R s t) : Moves R s t := tail (refl s) h

/-- Equal states are joined by the empty chain. -/
theorem of_eq {s t : σ} (h : s = t) : Moves R s t := h ▸ refl s

/-- Chains compose. -/
theorem trans {s t t' : σ} (h₁ : Moves R s t) (h₂ : Moves R t t') : Moves R s t' := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hr ih => exact tail ih hr

/-- A move followed by a chain. -/
theorem head {s t t' : σ} (h₁ : R s t) (h₂ : Moves R t t') : Moves R s t' := trans (single h₁) h₂

/-- A chain of moves of a smaller relation is a chain of the larger one. -/
theorem mono (hR : ∀ s t, R s t → R' s t) {s t : σ} (h : Moves R s t) : Moves R' s t := by
  induction h with
  | refl => exact refl _
  | tail _ hr ih => exact tail ih (hR _ _ hr)

/-- A property that every move preserves holds at the end of every chain. -/
theorem preserves {I : σ → Prop} (hI : ∀ s t, R s t → I s → I t) {s t : σ} (h : Moves R s t)
    (h0 : I s) : I t := by
  induction h with
  | refl => exact h0
  | tail _ hr ih => exact hI _ _ hr ih

/-- A potential that no move raises, on states where a property that every move preserves holds,
is not raised by any chain, and the property holds at its end. -/
theorem bound {I : σ → Prop} {P : σ → Nat} (hP : ∀ s t, R s t → I s → I t ∧ P t ≤ P s)
    {s t : σ} (h : Moves R s t) (h0 : I s) : I t ∧ P t ≤ P s := by
  induction h with
  | refl => exact ⟨h0, Nat.le_refl _⟩
  | tail _ hr ih =>
    have h2 := hP _ _ hr ih.1
    exact ⟨h2.1, Nat.le_trans h2.2 ih.2⟩

/-- A call that returns a new state or fails, where a failed call leaves the state unchanged
(`o.getD s`), is a chain when every result is. -/
theorem of_getD {o : Option σ} {s : σ} (h : ∀ t, o = some t → Moves R s t) : Moves R s (o.getD s) := by
  cases o with
  | none => exact refl s
  | some t => exact h t rfl

/-- `of_getD` for a call whose results are single moves. -/
theorem of_getD_single {o : Option σ} {s : σ} (h : ∀ t, o = some t → R s t) :
    Moves R s (o.getD s) :=
  of_getD fun t ht => single (h t ht)

end Moves

/-! ## Runs, totals and ghost states given by their equations -/

/-- A run defined by its equations is `Seq.run` of its step. -/
theorem run_eq_seq (run : σ → List α → σ) (step : σ → α → σ) (h0 : ∀ s, run s [] = s)
    (h1 : ∀ s a as, run s (a :: as) = run (step s a) as) (s : σ) (as : List α) :
    run s as = Seq.run step s as := by
  induction as generalizing s with
  | nil => exact h0 s
  | cons a as ih => rw [h1, ih]; rfl

/-- A total over the actions defined by its equations, with a ghost state updated by `next`, is
`Seq.accum`. -/
theorem total_eq_accum (total : γ → List α → Nat) (next : γ → α → γ) (f : γ → α → Nat)
    (h0 : ∀ g, total g [] = 0) (h1 : ∀ g a as, total g (a :: as) = f g a + total (next g a) as)
    (g : γ) (as : List α) : total g as = Seq.accum next f g as := by
  induction as generalizing g with
  | nil => exact h0 g
  | cons a as ih => rw [h1, ih]; rfl

/-- A ghost state after a run defined by its equations is `Seq.run` of its update. -/
theorem ghost_eq_seq (ghost : γ → List α → γ) (next : γ → α → γ) (h0 : ∀ g, ghost g [] = g)
    (h1 : ∀ g a as, ghost g (a :: as) = ghost (next g a) as) (g : γ) (as : List α) :
    ghost g as = Seq.run next g as :=
  run_eq_seq ghost next h0 h1 g as

/-- The induction over a run. `run`, the total `total` and the ghost state `ghost` are given by
their defining equations (for a specification's own definitions each equation holds by `rfl`).
When an invariant `I g s` relating the ghost state and the state is kept by every action, and
every action raises the potential `P` by at most `c` times its contribution to the total, a run
raises `P` by at most `c` times the total, and the invariant holds at its end. -/
theorem run_bound {step : σ → α → σ} {next : γ → α → γ} {f : γ → α → Nat}
    (run : σ → List α → σ) (total : γ → List α → Nat) (ghost : γ → List α → γ)
    (hr0 : ∀ s, run s [] = s) (hr1 : ∀ s a as, run s (a :: as) = run (step s a) as)
    (ht0 : ∀ g, total g [] = 0) (ht1 : ∀ g a as, total g (a :: as) = f g a + total (next g a) as)
    (hg0 : ∀ g, ghost g [] = g) (hg1 : ∀ g a as, ghost g (a :: as) = ghost (next g a) as)
    (I : γ → σ → Prop) (P : σ → Nat) (c : Nat)
    (hstep : ∀ g s a, I g s → I (next g a) (step s a) ∧ P (step s a) ≤ P s + c * f g a)
    {g : γ} {s : σ} (h0 : I g s) (as : List α) :
    P (run s as) ≤ P s + c * total g as ∧ I (ghost g as) (run s as) := by
  induction as generalizing g s with
  | nil => rw [hr0, ht0, hg0]; exact ⟨by omega, h0⟩
  | cons a as ih =>
    have h1 := hstep g s a h0
    have h2 := ih h1.1
    rw [hr1, ht1, hg1, Nat.mul_add]
    exact ⟨by omega, h2.2⟩

/-- The invariant half of `run_bound`: an invariant with a ghost state that every action keeps
holds after every run. -/
theorem run_invariant {step : σ → α → σ} {next : γ → α → γ}
    (run : σ → List α → σ) (ghost : γ → List α → γ)
    (hr0 : ∀ s, run s [] = s) (hr1 : ∀ s a as, run s (a :: as) = run (step s a) as)
    (hg0 : ∀ g, ghost g [] = g) (hg1 : ∀ g a as, ghost g (a :: as) = ghost (next g a) as)
    (I : γ → σ → Prop) (hstep : ∀ g s a, I g s → I (next g a) (step s a))
    {g : γ} {s : σ} (h0 : I g s) (as : List α) : I (ghost g as) (run s as) := by
  induction as generalizing g s with
  | nil => rw [hr0, hg0]; exact h0
  | cons a as ih => rw [hr1, hg1]; exact ih (hstep g s a h0)

/-- A bound from a state reached by a first run (a history): the invariant holds after the
history, so a second run raises the potential by at most `c` times the total from the ghost state
the history reached. This is the shape of a statement about what happens after any history, such
as an account that holds nothing after the history gaining at most what is emitted from then on. -/
theorem run_bound_after {step : σ → α → σ} {next : γ → α → γ} {f : γ → α → Nat}
    (run : σ → List α → σ) (total : γ → List α → Nat) (ghost : γ → List α → γ)
    (hr0 : ∀ s, run s [] = s) (hr1 : ∀ s a as, run s (a :: as) = run (step s a) as)
    (ht0 : ∀ g, total g [] = 0) (ht1 : ∀ g a as, total g (a :: as) = f g a + total (next g a) as)
    (hg0 : ∀ g, ghost g [] = g) (hg1 : ∀ g a as, ghost g (a :: as) = ghost (next g a) as)
    (I : γ → σ → Prop) (P : σ → Nat) (c : Nat)
    (hstep : ∀ g s a, I g s → I (next g a) (step s a) ∧ P (step s a) ≤ P s + c * f g a)
    {g : γ} {s : σ} (h0 : I g s) (history as : List α) :
    P (run (run s history) as) ≤ P (run s history) + c * total (ghost g history) as :=
  (run_bound run total ghost hr0 hr1 ht0 ht1 hg0 hg1 I P c hstep
    (run_invariant run ghost hr0 hr1 hg0 hg1 I (fun g s a h => (hstep g s a h).1) h0 history) as).1

/-! ## From a potential to an amount -/

/-- From a scaled potential to an amount. The potential at the end covers the amount at scale
`c` (`Q * c ≤ P`) and is at most the start potential plus `c` times the emission `e`; the start
potential is at most the start amount `Q₀` at scale `c`, plus a remainder `R` at scale `c` (owed
amounts not yet credited), plus `c` times `U` (emission not yet indexed). Then the amount is at
most `Q₀` plus the remainder rounded down once, plus `U`, plus `e`. -/
theorem amount_le_of_scaled {c Q Q₀ P P₀ R U e : Nat} (hc : 0 < c) (hQ : Q * c ≤ P)
    (hP : P ≤ P₀ + c * e) (h0 : P₀ ≤ Q₀ * c + R + c * U) : Q ≤ Q₀ + (R / c + U) + e := by
  have key : Q * c ≤ (Q₀ + U + e) * c + R := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm U, Nat.mul_comm e]
    omega
  have := ProofForgeFin.le_add_div_of_mul_le hc key
  omega

/-- From a scaled potential to an amount, with nothing owed at the start beyond the amount:
the amount is at most its start value plus the emission. -/
theorem amount_le_of_scaled_exact {c Q Q₀ P P₀ e : Nat} (hc : 0 < c) (hQ : Q * c ≤ P)
    (hP : P ≤ P₀ + c * e) (h0 : P₀ ≤ Q₀ * c) : Q ≤ Q₀ + e := by
  have key : Q * c ≤ (Q₀ + e) * c := by
    rw [Nat.add_mul, Nat.mul_comm e]
    omega
  exact Nat.le_of_mul_le_mul_right key hc

end ProofForgeFin.Accumulator
