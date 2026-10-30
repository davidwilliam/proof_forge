import ProofForgeFin.Machine.Attr
import ProofForgeFin.Machine.Record
import ProofForgeFin.Machine.Accounts
import ProofForgeFin.Machine.Journal
import ProofForgeFin.Machine.Keyed
import ProofForgeFin.Machine.Refine
import ProofForgeFin.Machine.Invariant
import ProofForgeFin.Machine.Trace
/-!
# Ledgers, state machines and reasoning over operation sequences

The layer above `ProofForgeFin.Seq` and `ProofForgeFin.Ledger`.

* `ProofForgeFin.Machine.Attr`: the `machine_simps` simp set.
* `ProofForgeFin.Machine.Record`: function updates (`Ledger.upd`), projections of `if`, and the
  `machine_norm` tactic that reduces projections of structure literals and updates.
* `ProofForgeFin.Machine.Accounts`: balances as functions with an explicit account list; totals
  independent of order, finite support, exchange of sums, conservation under updates.
* `ProofForgeFin.Machine.Journal`: double-entry journal entries, posting, trial balance, exact
  reversal, commutation of postings, debits and credits, reversal marks, T-accounts.
* `ProofForgeFin.Machine.Keyed`: idempotent operations keyed by an identifier.
* `ProofForgeFin.Machine.Refine`: simulation and refinement, transfer of invariants, composition,
  partial steps, steps with outputs, cached fields kept against a specification's recomputed
  values.
* `ProofForgeFin.Machine.Invariant`: conjunctions, relative and mutual invariants, invariants over
  a ghost history, per-key invariants and frame lemmas.
* `ProofForgeFin.Machine.Trace`: always and never, stability, monotone quantities along a run,
  counting changes of a field, commuting operations and reordering, atomic batches.
-/
