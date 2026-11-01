import ProofForgeFin.Accumulator.Index
import ProofForgeFin.Accumulator.Potential
import ProofForgeFin.Accumulator.Runs
import ProofForgeFin.Accumulator.Floor
/-!
# Index-based reward accumulators over sequences of actions

Bounds of the form "the rewards credited to all accounts (or to one account) after any sequence
of actions never exceed what was owed at the start plus what was emitted since", for any
accumulator in which a global index grows by a rate times the time elapsed over the total units,
accounts record the index at their last interaction, and an interaction credits an account its
units times the index gained since, rounded down.

A proof of such a bound for a concrete accumulator supplies its state, its step function and a
potential, and proves local facts only: how each primitive transition moves the index and each
account's term. The modules prove everything above that.

* `ProofForgeFin.Accumulator.Index`: an index update (`catchUp`), the emission not yet indexed
  (`unindexed`), covered index movements (`Covered`) and the starts of accounts with and without
  a recorded checkpoint.
* `ProofForgeFin.Accumulator.Potential`: the potential over the accounts of a list across an
  update and a settlement, in total and for one account, and its split into credited and owed
  amounts.
* `ProofForgeFin.Accumulator.Runs`: chains of primitive moves inside one action, the induction
  over a run given by its defining equations with a ghost state and a ghost total, and the
  passage from a scaled potential to an amount.
* `ProofForgeFin.Accumulator.Floor`: sums of amounts rounded down against the total rounded down.
-/
