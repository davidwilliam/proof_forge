import ProofForgeFin
import ProofForgeFinDemo.ShareVault
import ProofForgeFinDemo.Compound
/-!
# Tactic tests: `run_induction`, with `step_cases` and `round_bound`

Statements over every sequence of operations of three models: the vault of `rw-hundred-vault`
and the Comptroller of `rw-compound-comp` (their definitions are the copies in
`ProofForgeFinDemo.ShareVault` and `ProofForgeFinDemo.Compound`), and an escrow written here.

* `exec_value'`: the case analysis `exec_value` of `ProofForgeFinDemo.ShareVault` (40 lines
  in the reference solution, 22 in the demonstration) as `step_cases` and `round_bound`.
* `assets_le_paid_in`: the accumulated bound (`Seq.run_le_add_sum`).
* `released_le_deposited`: an invariant through a stronger one (`run_induction using`).
* `run_pot'`: the ghost-total induction of `run_pot` (`Seq.run_total_invariant`), with the
  per-operation lemmas as hypotheses, as in `ProofForgeFinDemo.Compound`.
-/

namespace ProofForgeFinDemo.Tactic.RunInduction

open ProofForgeFin

section Vault

open ProofForgeFinDemo.ShareVault

/-- `exec_value` of the vault: each operation keeps share value while shares are outstanding.
`step_cases` splits the operation, the call and every condition of the implementation and
unfolds `mintTo`, `burnFrom` and `sharesUp`; each remaining goal is the cross-multiplied share
value of one rounded conversion, which `round_bound` closes. -/
theorem exec_value' (s : Vault) (op : Op) (hs : 0 < s.supply) : ValueNotBelow s (exec vault s op) := by
  step_cases op [exec, vault, mintTo, burnFrom, sharesUp, ValueNotBelow]
  all_goals round_bound

/-- Underlying paid into the vault by an operation: a deposit or a donation. -/
def paidIn : Op → Nat
  | .call (.deposit _ x) => x
  | .donate x => x
  | _ => 0

/-- The vault never holds more underlying than it started with plus what was paid in, after
any sequence of operations. -/
theorem assets_le_paid_in (s : Vault) (ops : List Op) :
    (run vault s ops).assets ≤ s.assets + (ops.map paidIn).sum := by
  run_induction [run_eq] with [vault, mintTo, burnFrom, paidIn]
  all_goals step_cases

/-- The same bound without the automation: the library's `Seq.run_le_add_sum` and a case
analysis by hand. -/
example (s : Vault) (ops : List Op) :
    (run vault s ops).assets ≤ s.assets + (ops.map paidIn).sum := by
  rw [run_eq]
  refine Seq.run_le_add_sum (fun v => v.assets) paidIn (fun v op => ?_) s ops
  cases op with
  | donate x => simp [exec, paidIn]
  | call c =>
    simp only [exec]
    cases h : vault v c with
    | none => simp
    | some v' =>
      cases c with
      | deposit who x =>
        simp only [vault] at h
        split at h
        · cases h; simp [mintTo, paidIn]
        · split at h
          · cases h
          · cases h; simp [mintTo, paidIn]
      | redeem who t =>
        simp only [vault] at h
        split at h
        · cases h; simp [burnFrom, paidIn]
        · cases h
      | withdraw who x =>
        simp only [vault] at h
        split at h
        · cases h; simp [burnFrom, paidIn]
        · cases h

end Vault

section Escrow

/-- An escrow: what it holds, what it has released, and what was deposited in all. -/
structure Escrow where
  /-- Funds held. -/
  held : Nat
  /-- Funds released so far. -/
  released : Nat
  /-- Funds deposited so far. -/
  deposited : Nat

/-- Operations on the escrow. -/
inductive EOp where
  /-- Deposit `x`. -/
  | deposit (x : Nat)
  /-- Release `x`, refused when more than is held. -/
  | release (x : Nat)

/-- One operation; a refused release leaves the escrow unchanged. -/
def estep (e : Escrow) : EOp → Escrow
  | .deposit x => { e with held := e.held + x, deposited := e.deposited + x }
  | .release x => if x ≤ e.held then { e with held := e.held - x, released := e.released + x } else e

/-- The escrow never releases more than was deposited, from a balanced start, through the
stronger invariant that held and released funds add up to the deposits. -/
theorem released_le_deposited (e : Escrow) (h0 : e.released + e.held = e.deposited) (ops : List EOp) :
    (Seq.run estep e ops).released ≤ (Seq.run estep e ops).deposited := by
  run_induction using fun x => x.released + x.held = x.deposited
  step_cases

/-- The same statement without the automation: the library's `Seq.run_invariant_of_imp` and a
case analysis by hand. -/
example (e : Escrow) (h0 : e.released + e.held = e.deposited) (ops : List EOp) :
    (Seq.run estep e ops).released ≤ (Seq.run estep e ops).deposited := by
  refine Seq.run_invariant_of_imp (step := estep) (I := fun x => x.released ≤ x.deposited)
    (J := fun x => x.released + x.held = x.deposited)
    (fun x (h : x.released + x.held = x.deposited) => by omega) (fun x op h => ?_) h0 ops
  cases op with
  | deposit y => simp only [estep] at h ⊢; omega
  | release y =>
    simp only [estep]
    split
    · simp only at h ⊢; omega
    · exact h

/-- `run_induction` fails with a message on a goal that mentions no run. -/
example (e : Escrow) (h : e.held ≤ e.deposited) : e.held ≤ e.deposited := by
  fail_if_success run_induction
  exact h

end Escrow

section Comptroller

open ProofForgeFinDemo.Compound

/-- `run_pot` of `rw-compound-comp` stated with the library's run and accumulator: the
ghost-total invariant carries the invariant `Inv` and the bound on the potential so far. The
per-operation lemmas are hypotheses, as in `ProofForgeFinDemo.Compound`; the step and the
ghost functions are left folded (`-exec`, `-nextSpeeds`, `-emittedBy`) so that the hypotheses
apply to every operation alike. -/
theorem run_pot' (impl : Impl) (Inv : Nat × Nat → St → Prop) (P : St → Nat)
    (exec_inv : ∀ sp s op, Inv sp s → Inv (nextSpeeds sp op) (exec impl s op))
    (exec_pot : ∀ sp s op, Inv sp s → P (exec impl s op) ≤ P s + doubleScale * emittedBy sp op)
    (ops : List Op) (sp : Nat × Nat) (s : St) (h0 : Inv sp s) :
    P (Seq.run (exec impl) s ops) ≤ P s + doubleScale * Seq.accum nextSpeeds emittedBy sp ops := by
  run_induction total (fun g e t => Inv g t ∧ P t ≤ P s + doubleScale * e)
    with [-exec, -nextSpeeds, -emittedBy]
  · exact hrun.2
  · exact ⟨h0, by omega⟩
  all_goals
    refine ⟨exec_inv _ _ _ ih.1, Nat.le_trans (exec_pot _ _ _ ih.1) ?_⟩
    rw [Nat.mul_add]
    omega

end Comptroller

end ProofForgeFinDemo.Tactic.RunInduction
