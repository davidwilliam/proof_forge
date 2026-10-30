import ProofForgeFin.Tactic.Attr
import ProofForgeFin.Tactic.SimpSets
import ProofForgeFin.Tactic.Struct
import ProofForgeFin.Tactic.Induction
import ProofForgeFin.Tactic.Round
/-!
# Proof automation for financial code

Tactics that close the goals proofs about money code keep meeting: record projections and
updates of step functions, case splits of a step on its operation and conditions, inductions
over sequences of operations, and rounding bounds. They are metaprograms: they add no axiom,
and every proof they build is checked by the kernel like any other.

* `ProofForgeFin.Tactic.Attr`: the simp sets `fin_simp` and `struct_simp`.
* `ProofForgeFin.Tactic.SimpSets`: their lemmas and the simplification procedures `ctorEq`
  (constructor injectivity) and `iteEqSubst` (a condition whose branches agree).
* `ProofForgeFin.Tactic.Struct`: `struct_simp` and `step_cases`.
* `ProofForgeFin.Tactic.Induction`: `run_induction`.
* `ProofForgeFin.Tactic.Round`: `fin_simp`, `div_norm` and `round_bound`.

`lib/docs/Tactic.md` documents the syntax, examples, measurements and limits.
-/
