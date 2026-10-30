import ProofForgeFin
/-!
# Demonstration: REQ-NO-BAD-DEBT of `rw-euler-donate` with the library

The definitions in the first section are copied without change from
`realworld/tasks/rw-euler-donate/spec/EulerLending/Spec.lean`. The task files are not imported or
modified.

The reference solution (`reference/SolutionA.lean`) derives REQ-NO-BAD-DEBT from
REQ-STAYS-HEALTHY by induction on the task's `Reachable`. Here the task's `Reachable` and
`runAll` are shown to be the library's, and the derivation is `Seq.Reachable.invariant`, for every
implementation. The same invariant then holds after every successful atomic run from `genesis`.
-/

namespace ProofForgeFinDemo.Euler

open ProofForgeFin

/-! ## Copied from `spec/EulerLending/Spec.lean` -/

/-- One account's position: `e` is its eToken balance (its deposit, which is also its
collateral) and `d` its dToken balance (its debt), both in underlying units. -/
structure Acct where
  e : Nat
  d : Nat
  deriving DecidableEq, Repr

/-- Market state: every account's position, the underlying held by the pool (`cash`, Euler's
`poolSize`) and the reserves (eTokens owned by the protocol). Accounts are numbered. -/
structure St where
  acct : Nat → Acct
  cash : Nat
  reserves : Nat

/-- User operations, named after the Euler functions they model. Amounts are in underlying
units. -/
inductive Op where
  /-- `EToken.deposit`: account `u` deposits `x` from its wallet. -/
  | deposit (u x : Nat)
  /-- `EToken.withdraw`: account `u` withdraws `x` to its wallet. -/
  | withdraw (u x : Nat)
  /-- `DToken.borrow`: account `u` borrows `x` from the pool. -/
  | borrow (u x : Nat)
  /-- `DToken.repay`: account `u` repays up to `x` of its debt from its wallet. -/
  | repay (u x : Nat)
  /-- `EToken.mint`: account `u` mints `x` eTokens and `x` dTokens (a self-borrow). -/
  | mint (u x : Nat)
  /-- `EToken.burn`: account `u` burns up to `x` of its eTokens against the same amount of
  dTokens (a self-repay). -/
  | burn (u x : Nat)
  /-- `EToken.transferFrom`: account `u` transfers `x` eTokens to account `v`. -/
  | transfer (u v x : Nat)
  /-- `EToken.donateToReserves`: account `u` gives `x` eTokens to the reserves. -/
  | donate (u x : Nat)
  /-- `Liquidation.liquidate`: account `liq` takes over `r` of account `viol`'s debt and
  receives collateral from `viol` at a discount. -/
  | liquidate (liq viol r : Nat)
  deriving DecidableEq, Repr

/-- An implementation returns the next state, or `none` when the operation reverts. A reverted
operation changes nothing. -/
abbrev Impl := St → Op → Option St

/-- The market before any operation: every account empty, no cash, no reserves. -/
def genesis : St := ⟨fun _ => ⟨0, 0⟩, 0, 0⟩

/-- An account is healthy when its debt is covered by 95% of its collateral, as Euler's
liquidity check computes it for a self-collateralized loan: `debt * 20 / 19 ≤ collateral`
(floor division). An account without debt is always healthy. An unhealthy account is one that
holds more debt than its risk-adjusted collateral. -/
def Healthy (a : Acct) : Prop := a.d * 20 / 19 ≤ a.e

instance (a : Acct) : Decidable (Healthy a) := by unfold Healthy; infer_instance

/-- REQ-STAYS-HEALTHY: from any state, no successful operation makes a healthy account
unhealthy. -/
def StaysHealthy (step : Impl) : Prop :=
  ∀ s op s' w, step s op = some s' → Healthy (s.acct w) → Healthy (s'.acct w)

/-- The states reachable from `genesis` by any sequence of successful operations. -/
inductive Reachable (step : Impl) : St → Prop
  | genesis : Reachable step genesis
  | step {s s' : St} (op : Op) : Reachable step s → step s op = some s' → Reachable step s'

/-- Run operations in order; `none` as soon as one reverts. -/
def runAll (step : Impl) : St → List Op → Option St
  | s, [] => some s
  | s, op :: ops =>
    match step s op with
    | some s' => runAll step s' ops
    | none => none

/-- REQ-NO-BAD-DEBT: in every state reachable from `genesis` by any sequence of operations,
every account is healthy: no account holds more debt than its risk-adjusted collateral. -/
def NoBadDebt (step : Impl) : Prop :=
  ∀ s, Reachable step s → ∀ u, Healthy (s.acct u)


/-! ## Re-proved with the library -/

/-- The task's reachable states are the library's, from `genesis`. -/
theorem reachable_iff (step : Impl) (s : St) : Reachable step s ↔ Seq.Reachable step genesis s := by
  constructor
  · intro h
    induction h with
    | genesis => exact Seq.Reachable.init
    | step op _ hs ih => exact Seq.Reachable.step op ih hs
  · intro h
    induction h with
    | init => exact Reachable.genesis
    | step op _ hs ih => exact Reachable.step op ih hs

/-- The task's `runAll` is the library's. -/
theorem runAll_eq (step : Impl) (s : St) (ops : List Op) : runAll step s ops = Seq.runAll step s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    simp only [runAll, Seq.runAll]
    cases step s op with
    | none => rfl
    | some s' => exact ih s'

/-- Every account of `genesis` is healthy. -/
theorem genesis_healthy (u : Nat) : Healthy (genesis.acct u) := by
  show 0 * 20 / 19 ≤ 0
  decide

/-- REQ-NO-BAD-DEBT follows from REQ-STAYS-HEALTHY, for every implementation. -/
theorem noBadDebt_of_staysHealthy (step : Impl) (h : StaysHealthy step) : NoBadDebt step := by
  intro s hs
  have hr := (reachable_iff step s).1 hs
  exact Seq.Reachable.invariant (I := fun t : St => ∀ u, Healthy (t.acct u)) genesis_healthy
    (fun t op t' ht e u => h t op t' u e (ht u)) hr

/-- With REQ-STAYS-HEALTHY, every account is healthy after every successful session from
`genesis`. -/
theorem runAll_healthy (step : Impl) (h : StaysHealthy step) (ops : List Op) (s : St)
    (hr : runAll step genesis ops = some s) (u : Nat) : Healthy (s.acct u) := by
  rw [runAll_eq] at hr
  exact noBadDebt_of_staysHealthy step h s
    ((reachable_iff step s).2 (Seq.reachable_of_runAll Seq.Reachable.init hr)) u

end ProofForgeFinDemo.Euler
