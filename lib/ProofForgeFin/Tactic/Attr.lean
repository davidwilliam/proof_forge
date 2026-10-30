import Lean
/-!
# Simp sets of the proof automation

Two simp sets, declared here so that the lemma modules can tag lemmas with them (an attribute
must be registered in a module imported by the module that uses it).

* `fin_simp`: normal forms for rounding and fixed-point terms. Every fixed-point operation of
  `ProofForgeFin.FixedPoint` and every share conversion of `ProofForgeFin.Shares` is rewritten to
  floor division `a / b` and `ceilDiv a b`; units, zeros and exact cancellations are removed.
* `struct_simp`: reduction of records and updates. Projections of structure instances, `Prod`
  and `Option` constructors, matches on constructors, `if` on decided conditions, the update
  functions of `ProofForgeFin.Ledger`, `List.modify` read back with `List.getD`, and the run
  equations of `ProofForgeFin.Seq`.

Neither set contains a commutativity or associativity lemma, and every lemma rewrites a term to
a smaller one or unfolds a non-recursive definition, so `simp only` with either set terminates.
-/

/-- Normal forms for rounding and fixed-point terms: fixed-point operations and share
conversions as floor division and `ceilDiv`, without units, zeros or exact cancellations. -/
register_simp_attr fin_simp

/-- Reduction of records and updates: projections of structure instances, constructor matches,
decided conditions, function updates, `List.modify` read back, and the run equations. -/
register_simp_attr struct_simp
