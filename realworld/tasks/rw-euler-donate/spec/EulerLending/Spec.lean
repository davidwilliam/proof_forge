/-!
# Single-asset lending market specification (protected)

Owner-reviewed definitions for a lending market in the style of Euler Finance v1
(euler-xyz/euler-contracts): one asset, deposits held as eTokens, debt held as dTokens, and
self-collateralized loans, in which an account borrows the same asset it deposited. This is the
market configuration the March 2023 attack used.

Candidates may not edit this file. Every requirement is a predicate over an implementation
`step : Impl`; the locked challenge (`EulerLending/Challenge.lean`) applies each one to the
definition hole `EulerLending.step`.

Model, as a reader of Euler's contracts would map it:

* Amounts are in underlying units. The eToken to underlying exchange rate is fixed at 1 and no
  interest accrues (Euler's state within one block, with no interest accrued yet).
* The asset is priced at 1 (Euler's reference asset is pegged at 1e18) and its borrow factor is
  1, so an account's liability value is its debt.
* An account is healthy when Euler's liquidity check passes for a self-collateralized position:
  `RiskManager.computeLiquidityRaw` counts debt up to `balance * 0.95` as covered and fails the
  check exactly when `debt * 4e9 / 3.8e9 > balance`, which is `debt * 20 / 19 > balance`.
* Liquidation follows `Liquidation.computeLiqOpp` and `executeLiquidation` for the case where the
  repaid asset and the seized collateral are the same asset, with the discount booster at 1
  (the liquidator does not track average liquidity) and fixed-point arithmetic at 1e18 scale.
-/

namespace EulerLending

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

/-! ## Health -/

/-- An account is healthy when its debt is covered by 95% of its collateral, as Euler's
liquidity check computes it for a self-collateralized loan: `debt * 20 / 19 ≤ collateral`
(floor division). An account without debt is always healthy. An unhealthy account is one that
holds more debt than its risk-adjusted collateral. -/
def Healthy (a : Acct) : Prop := a.d * 20 / 19 ≤ a.e

instance (a : Acct) : Decidable (Healthy a) := by unfold Healthy; infer_instance

/-! ## Liquidation terms (Euler's `computeLiqOpp`, fixed point at 1e18) -/

/-- 1.0 in Euler's 1e18 fixed point. -/
def ONE : Nat := 1000000000000000000

/-- Health score of an unhealthy account: collateral value over liability value. The
collateral value of an unhealthy self-collateralized position is `e * 0.95`. -/
def healthScore (a : Acct) : Nat := a.e * 19 / 20 * ONE / a.d

/-- Liquidation discount: 2% plus the shortfall of the health score below 1, at most 20%. -/
def discount (a : Acct) : Nat := min (ONE / 5) (ONE / 50 + (ONE - healthScore a))

/-- Collateral received per unit of debt taken over: `1 / (1 - discount)`. -/
def conversionRate (a : Acct) : Nat := ONE * ONE / (ONE - discount a)

/-- Collateral the liquidator receives for taking over `r` of the violator's debt. -/
def liqYield (a : Acct) (r : Nat) : Nat := r * conversionRate a / ONE

/-- The largest debt a liquidator may take over: all of it, unless the collateral does not
cover the yield, in which case the debt whose yield is exactly all of the collateral. -/
def maxRepay (a : Acct) : Nat :=
  if a.d * conversionRate a / ONE ≤ a.e then a.d else a.e * ONE / conversionRate a

/-- Reserves fee of a liquidation: 2% of the repaid debt, added to the liquidator's debt and
credited to the reserves. -/
def liqFee (r : Nat) : Nat := r / 50

/-! ## Operations that must succeed -/

/-- The conditions under which an operation must succeed: the account has the balance it
spends, the pool has the cash it pays out, and the accounts Euler's liquidity checks cover end
healthy. A liquidation must succeed on an unhealthy violator when the liquidator ends healthy. -/
def Allowed (s : St) : Op → Prop
  | .deposit u x => (s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩
  | .withdraw u x => x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩
  | .borrow u x => x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩
  | .repay _ _ => True
  | .mint u x => Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩
  | .burn u x => min x (s.acct u).d ≤ (s.acct u).e ∧
      Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩
  | .transfer u v x => u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧
      ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩)
  | .donate u x => x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩
  | .liquidate l v r => l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧
      Healthy ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩

/-! ## Effects of a successful operation -/

/-- Every account other than `u` is unchanged. -/
def OthersSame (s s' : St) (u : Nat) : Prop := ∀ w, w ≠ u → s'.acct w = s.acct w

/-- Every account other than `u` and `v` is unchanged. -/
def OthersSame2 (s s' : St) (u v : Nat) : Prop := ∀ w, w ≠ u → w ≠ v → s'.acct w = s.acct w

/-- The complete next state of a successful operation: every account, the cash and the
reserves. Amounts taken from a balance never exceed it. -/
def EffectOn (s : St) (op : Op) (s' : St) : Prop :=
  match op with
  | .deposit u x =>
      s'.acct u = ⟨(s.acct u).e + x, (s.acct u).d⟩ ∧ OthersSame s s' u ∧
      s'.cash = s.cash + x ∧ s'.reserves = s.reserves
  | .withdraw u x =>
      x ≤ (s.acct u).e ∧ x ≤ s.cash ∧
      s'.acct u = ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ OthersSame s s' u ∧
      s'.cash = s.cash - x ∧ s'.reserves = s.reserves
  | .borrow u x =>
      x ≤ s.cash ∧
      s'.acct u = ⟨(s.acct u).e, (s.acct u).d + x⟩ ∧ OthersSame s s' u ∧
      s'.cash = s.cash - x ∧ s'.reserves = s.reserves
  | .repay u x =>
      s'.acct u = ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ ∧ OthersSame s s' u ∧
      s'.cash = s.cash + min x (s.acct u).d ∧ s'.reserves = s.reserves
  | .mint u x =>
      s'.acct u = ⟨(s.acct u).e + x, (s.acct u).d + x⟩ ∧ OthersSame s s' u ∧
      s'.cash = s.cash ∧ s'.reserves = s.reserves
  | .burn u x =>
      min x (s.acct u).d ≤ (s.acct u).e ∧
      s'.acct u = ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ ∧
      OthersSame s s' u ∧ s'.cash = s.cash ∧ s'.reserves = s.reserves
  | .transfer u v x =>
      u ≠ v ∧ x ≤ (s.acct u).e ∧
      s'.acct u = ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧
      s'.acct v = ⟨(s.acct v).e + x, (s.acct v).d⟩ ∧ OthersSame2 s s' u v ∧
      s'.cash = s.cash ∧ s'.reserves = s.reserves
  | .donate u x =>
      x ≤ (s.acct u).e ∧
      s'.acct u = ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ OthersSame s s' u ∧
      s'.cash = s.cash ∧ s'.reserves = s.reserves + x
  | .liquidate l v r =>
      l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧
      s'.acct v = ⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩ ∧
      s'.acct l = ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ ∧
      OthersSame2 s s' l v ∧ s'.cash = s.cash ∧ s'.reserves = s.reserves + liqFee r

/-- The accounts whose health an operation can lower, and which Euler's liquidity check covers
after it: the account that withdraws, borrows, mints, burns, transfers out or donates, and the
liquidator of a liquidation. -/
def Checked : Op → Nat → Prop
  | .withdraw u _, w => w = u
  | .borrow u _, w => w = u
  | .mint u _, w => w = u
  | .burn u _, w => w = u
  | .transfer u _ _, w => w = u
  | .donate u _, w => w = u
  | .liquidate l _ _, w => w = l
  | _, _ => False

/-! ## Reachable states -/

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

/-- An honest session: a lender deposits 1000; a borrower deposits 100, borrows 95 (exactly the
95% limit) and repays it; a third account deposits 10, mints 190 (leverage up to exactly the
95% limit), burns it and withdraws everything; the borrower withdraws its deposit. -/
def honestSession : List Op :=
  [.deposit 0 1000, .deposit 1 100, .borrow 1 95, .repay 1 95,
   .deposit 2 10, .mint 2 190, .burn 2 190, .withdraw 2 10, .withdraw 1 100]

/-- The honest session runs to completion and ends with every position settled. -/
def honestOutcome (step : Impl) : Bool :=
  match runAll step genesis honestSession with
  | some s => s.acct 0 == ⟨1000, 0⟩ && s.acct 1 == ⟨0, 0⟩ && s.acct 2 == ⟨0, 0⟩ &&
      s.cash == 1000 && s.reserves == 0
  | none => false

/-! ## Requirements -/

/-- REQ-HONEST-FLOW: honest lending, borrowing at the 95% limit, leverage by minting and
repayment remain possible: the honest session runs to completion with the expected result. -/
def HonestFlow (step : Impl) : Prop := honestOutcome step = true

/-- REQ-ALLOWED-SUCCEEDS: every allowed operation succeeds, from any state. -/
def AllowedSucceeds (step : Impl) : Prop :=
  ∀ s op, Allowed s op → (step s op).isSome

/-- REQ-EFFECTS: a successful operation produces exactly the specified next state. -/
def Effects (step : Impl) : Prop :=
  ∀ s op s', step s op = some s' → EffectOn s op s'

/-- REQ-ACTOR-HEALTHY: from any state, after a successful withdraw, borrow, mint, burn,
transfer or donation the acting account is healthy, and after a liquidation the liquidator is
healthy. -/
def ActorHealthy (step : Impl) : Prop :=
  ∀ s op s' w, step s op = some s' → Checked op w → Healthy (s'.acct w)

/-- REQ-STAYS-HEALTHY: from any state, no successful operation makes a healthy account
unhealthy. -/
def StaysHealthy (step : Impl) : Prop :=
  ∀ s op s' w, step s op = some s' → Healthy (s.acct w) → Healthy (s'.acct w)

/-- REQ-NO-BAD-DEBT: in every state reachable from `genesis` by any sequence of operations,
every account is healthy: no account holds more debt than its risk-adjusted collateral. -/
def NoBadDebt (step : Impl) : Prop :=
  ∀ s, Reachable step s → ∀ u, Healthy (s.acct u)

end EulerLending
