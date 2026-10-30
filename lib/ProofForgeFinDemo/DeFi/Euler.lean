import ProofForgeFin.DeFi
/-!
# Demonstration: the health requirements of `rw-euler-donate` with the library

The first section copies `realworld/tasks/rw-euler-donate/spec/EulerLending/Spec.lean` without
change (its namespace body, with every doc string). The task files are not imported or modified.

The second section proves REQ-STAYS-HEALTHY and REQ-NO-BAD-DEBT for every implementation that
meets REQ-EFFECTS and REQ-ACTOR-HEALTHY, with `ProofForgeFin.DeFi.Lending.keepsHealthy_of` and
`Lending.reachable_healthy`. The exploited `donateToReserves` of Euler v1 fails REQ-ACTOR-HEALTHY:
it lowers the donor's collateral without checking the donor.
-/

namespace ProofForgeFinDemo.DeFi.Euler

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

/-! ## Re-proved with the library

The reference solution proves REQ-STAYS-HEALTHY for its own implementation, from its
REQ-ACTOR-HEALTHY and REQ-EFFECTS. Here REQ-STAYS-HEALTHY and REQ-NO-BAD-DEBT are proved for every
implementation that meets REQ-EFFECTS and REQ-ACTOR-HEALTHY: each operation leaves every account
checked healthy, at least as safe, or unhealthy already (`Lending.keepsHealthy_of`), and the
induction over reachable states is `Lending.reachable_healthy`. -/

open ProofForgeFin ProofForgeFin.DeFi

/-- `b` is at least as safe as `a`: at least the collateral, at most the debt. -/
def Safer (a b : Acct) : Prop := a.e ≤ b.e ∧ b.d ≤ a.d

/-- Health is kept by a safer position. -/
theorem healthy_mono : Lending.Monotone Healthy Safer := fun _ _ h hs => by
  unfold Healthy at *
  exact Nat.le_trans (Nat.div_le_div_right (Nat.mul_le_mul_right _ hs.2)) (Nat.le_trans h hs.1)

/-- An unchanged position is as safe. -/
theorem safer_of_eq {a b : Acct} (h : b = a) : Safer a b := by
  subst h; exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- The task's `Reachable` is the library's. -/
theorem reachable_eq {step : Impl} {s : St} (h : Reachable step s) : Seq.Reachable step genesis s := by
  induction h with
  | genesis => exact .init
  | step op _ h ih => exact .step op ih h

section Requirements

variable {step : Impl} (hE : Effects step) (hA : ActorHealthy step)
include hE hA

/-- REQ-STAYS-HEALTHY for every implementation that meets REQ-EFFECTS and REQ-ACTOR-HEALTHY. -/
theorem stays_healthy : StaysHealthy step := by
  intro s op s' w h hw
  refine Lending.keepsHealthy_of (acct := St.acct) healthy_mono (fun k => ?_) w hw
  have he := hE s op s' h
  have act : ∀ k, Checked op k →
      Healthy (s'.acct k) ∨ Safer (s.acct k) (s'.acct k) ∨ ¬ Healthy (s.acct k) :=
    fun k hk => Or.inl (hA s op s' k h hk)
  cases op with
  | deposit u x =>
    by_cases hk : k = u
    · subst hk; rw [he.1]; exact Or.inr (Or.inl ⟨Nat.le_add_right _ _, Nat.le_refl _⟩)
    · exact Or.inr (Or.inl (safer_of_eq (he.2.1 k hk)))
  | repay u x =>
    by_cases hk : k = u
    · subst hk; rw [he.1]; exact Or.inr (Or.inl ⟨Nat.le_refl _, Nat.sub_le _ _⟩)
    · exact Or.inr (Or.inl (safer_of_eq (he.2.1 k hk)))
  | withdraw u x =>
    by_cases hk : k = u
    · exact act k hk
    · exact Or.inr (Or.inl (safer_of_eq (he.2.2.2.1 k hk)))
  | borrow u x =>
    by_cases hk : k = u
    · exact act k hk
    · exact Or.inr (Or.inl (safer_of_eq (he.2.2.1 k hk)))
  | mint u x =>
    by_cases hk : k = u
    · exact act k hk
    · exact Or.inr (Or.inl (safer_of_eq (he.2.1 k hk)))
  | burn u x =>
    by_cases hk : k = u
    · exact act k hk
    · exact Or.inr (Or.inl (safer_of_eq (he.2.2.1 k hk)))
  | donate u x =>
    by_cases hk : k = u
    · exact act k hk
    · exact Or.inr (Or.inl (safer_of_eq (he.2.2.1 k hk)))
  | transfer u v x =>
    by_cases hk : k = u
    · exact act k hk
    · by_cases hv : k = v
      · subst hv; rw [he.2.2.2.1]; exact Or.inr (Or.inl ⟨Nat.le_add_right _ _, Nat.le_refl _⟩)
      · exact Or.inr (Or.inl (safer_of_eq (he.2.2.2.2.1 k hk hv)))
  | liquidate l v r =>
    by_cases hk : k = l
    · exact act k hk
    · by_cases hv : k = v
      · subst hv; exact Or.inr (Or.inr he.2.1)
      · exact Or.inr (Or.inl (safer_of_eq (he.2.2.2.2.2.1 k hk hv)))

/-- REQ-NO-BAD-DEBT for every implementation that meets REQ-EFFECTS and REQ-ACTOR-HEALTHY. -/
theorem no_bad_debt : NoBadDebt step := fun _ hs =>
  Lending.reachable_healthy (acct := St.acct) (H := Healthy)
    (fun s o s' he k => stays_healthy hE hA s o s' k he) (fun _ => by simp [Healthy, genesis])
    (reachable_eq hs)

end Requirements

end ProofForgeFinDemo.DeFi.Euler
