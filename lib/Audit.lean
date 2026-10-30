import Lean
import ProofForgeFin
import ProofForgeFinDemo
/-!
# Axiom audit

Run after `lake build` with `lake env lean Audit.lean`. For every constant declared in a module
of `ProofForgeFin` or `ProofForgeFinDemo`, the audit collects the axioms the constant depends on
(transitively, through every constant it uses) and reports any axiom outside `propext`,
`Classical.choice` and `Quot.sound`, and any axiom declared in those modules. A `sorry` shows up
as `sorryAx`; in Lean 4.35 `native_decide` and `bv_decide` declare an auxiliary axiom next to the
theorem (`<theorem>._native.native_decide.ax_...`, `<theorem>._native.bv_decide.ax_...`) that
the theorem depends on, so each of them is reported. The last line is
`audit: <n> constants, <m> theorems, <k> violations`.
-/

open Lean Elab Command

/-- The axioms a proof may use. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The library and demonstration modules. -/
def auditedRoots : List Name := [`ProofForgeFin, `ProofForgeFinDemo]

elab "#audit_axioms" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some idx =>
      if auditedRoots.contains (mods[idx.toNat]!).getRoot then acc.push n else acc
    | none => acc
  let names := names.qsort (fun a b => a.toString < b.toString)
  let mut theorems : Nat := 0
  let mut violations : Nat := 0
  let mut used : List Name := []
  for n in names do
    let some ci := env.find? n | continue
    if let .axiomInfo _ := ci then
      violations := violations + 1
      logInfo m!"violation: {n} is an axiom declared in an audited module"
    let axs ← liftCoreM <| collectAxioms n
    for a in axs do
      unless used.contains a do used := a :: used
    let bad := axs.filter (fun a => !allowedAxioms.contains a)
    unless bad.isEmpty do
      violations := violations + 1
      logInfo m!"violation: {n} depends on {bad.toList}"
    if let .thmInfo _ := ci then
      unless n.isInternal do theorems := theorems + 1
  let usedSorted := used.toArray.qsort (fun a b => a.toString < b.toString)
  logInfo m!"axioms used: {usedSorted.toList}"
  logInfo m!"audit: {names.size} constants, {theorems} theorems, {violations} violations"

#audit_axioms

/-! The main results, with `#print axioms`. -/

#print axioms ProofForgeFin.floor_spec
#print axioms ProofForgeFin.ceilDiv_spec
#print axioms ProofForgeFin.mulDown_spec
#print axioms ProofForgeFin.mulUp_spec
#print axioms ProofForgeFin.mulDown_le_mulUp
#print axioms ProofForgeFin.mulUp_le_mulDown_add_one
#print axioms ProofForgeFin.divDown_spec
#print axioms ProofForgeFin.divUp_spec
#print axioms ProofForgeFin.le_divUp_mulUp
#print axioms ProofForgeFin.mul_two_pow_lt_iff
#print axioms ProofForgeFin.toNat_fullMul
#print axioms ProofForgeFin.Shares.valueNotBelow_trans
#print axioms ProofForgeFin.Shares.deposit_value
#print axioms ProofForgeFin.Shares.withdraw_value
#print axioms ProofForgeFin.Shares.deposit_redeem_le
#print axioms ProofForgeFin.Shares.step_value
#print axioms ProofForgeFin.Shares.run_value
#print axioms ProofForgeFin.Seq.run_invariant
#print axioms ProofForgeFin.Seq.run_rel_of_trace
#print axioms ProofForgeFin.Seq.run_le_add_sum
#print axioms ProofForgeFin.Seq.run_total_invariant
#print axioms ProofForgeFin.Seq.run_bound_via_potential
#print axioms ProofForgeFin.Seq.runAll_rel
#print axioms ProofForgeFin.Seq.reachable_iff
#print axioms ProofForgeFin.Ledger.sumOver_transfer
#print axioms ProofForgeFin.Ledger.sumOver_applyMoves
#print axioms ProofForgeFin.Ledger.SupplyMatches.move
#print axioms ProofForgeFin.Ledger.sum_map_modify_modify
#print axioms ProofForgeFin.Ledger.sum_equalSplit
#print axioms ProofForgeFin.Ledger.mem_equalSplit_bounds
#print axioms ProofForgeFinDemo.ShareVault.req_share_value
#print axioms ProofForgeFinDemo.BatchTransfer.sum_applyLegs
#print axioms ProofForgeFinDemo.Compound.run_pot
#print axioms ProofForgeFinDemo.Compound.credited_bound
#print axioms ProofForgeFinDemo.Euler.noBadDebt_of_staysHealthy
