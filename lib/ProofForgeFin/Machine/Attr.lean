import Lean.Meta.Tactic.Simp.RegisterCommand
/-!
# The `machine_simps` simp set

A simp set for the goals that state machine proofs leave behind: function updates read at a
key, projections of a pair or a structure built by `if`, and the definitional unfolding lemmas
of the `ProofForgeFin.Machine` modules. Use it with `simp only [machine_simps]` or through the
`machine_norm` tactic of `ProofForgeFin.Machine.Record`.

The set is registered in a module of its own because Lean does not allow a simp attribute to be
used in the module that declares it.
-/

/-- Lemmas that reduce function updates, projections of `if` expressions and the unfolding
equations of the `ProofForgeFin.Machine` modules. -/
register_simp_attr machine_simps
