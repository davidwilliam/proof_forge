import ProofForgeFin.Rounding
import ProofForgeFin.FixedPoint
import ProofForgeFin.Seq
import ProofForgeFin.Ledger
/-!
# Lending: health, liquidation, interest indices, pool solvency

The arithmetic of over-collateralized lending (Compound, Aave, Euler, Morpho Blue, Liquity) on
`Nat`, with fixed-point prices and factors at a scale `one`.

* Health preservation, for any health predicate: an operation keeps every healthy account healthy
  when each account it touches ends checked healthy, ends at least as safe, or was unhealthy
  before (`keepsHealthy_of`); then every reachable state is healthy (`reachable_healthy`). The
  Euler Finance exploit of March 2023 is an operation (`donateToReserves`) that lowered an
  account's collateral without the check.
* One collateral asset and one debt asset (`Params`, `Position`): the borrow limit
  `collateral * collPrice / one * factor / one` and the debt value `debt * debtPrice / one`,
  rounded in the protocol's favour (down and up), as Morpho Blue's `_isHealthy` computes them;
  `Healthy.exact` (the rounded check implies the exact inequality), monotonicity in the position
  and in prices.
* Liquidation: collateral seized for a repayment with an incentive (Compound's
  `liquidateCalculateSeizeTokens`), its value bound (`seize_value_le`: seized value at most the
  repaid value times the incentive), the close factor (`maxRepay_le`), and `liquidate_shortfall_le`
  (a liquidation does not raise the exact shortfall when incentive times factor is at most 1).
* Interest indices: `accrueIndex` (Compound's `borrowIndex` update) is monotone; debts recorded as a
  principal at a snapshot index and read at a later index, rounded down (`debtDown`, Compound's
  `borrowBalanceStored`) or up (`debtUp`, in the protocol's favour), with the effect of
  re-snapshotting (`debtUp_resnap`, `debtDown_resnap`) and the sum over accounts
  (`sum_debtDown_le`).
* A pool (`Pool`: cash, borrows, reserves, supplied) with supply, withdraw, borrow, repay,
  interest accrual split into reserves, and bad-debt write-off: the books stay balanced over every
  sequence (`run_balanced`), so total borrows never exceed what was supplied plus reserves
  (`run_borrows_le`).
-/

namespace ProofForgeFin.DeFi.Lending

open ProofForgeFin

universe u v w

/-! ## Keeping accounts healthy -/

section Health

variable {σ : Type u} {α : Type v} {κ : Type w}

/-- From `s` to `s'`, every account healthy before is healthy after. `acct s k` is the position of
account `k` in state `s`. -/
def KeepsHealthy (H : α → Prop) (acct : σ → κ → α) (s s' : σ) : Prop :=
  ∀ k, H (acct s k) → H (acct s' k)

/-- A health predicate that a safer position keeps: `Safer a b` means `b` is at least as safe as
`a` (more collateral, less debt). -/
def Monotone (H : α → Prop) (Safer : α → α → Prop) : Prop := ∀ a b, H a → Safer a b → H b

/-- An operation keeps every healthy account healthy when each account ends checked healthy, ends
at least as safe as it was, or was not healthy before (a liquidated account). -/
theorem keepsHealthy_of {H : α → Prop} {Safer : α → α → Prop} {acct : σ → κ → α} {s s' : σ}
    (hm : Monotone H Safer)
    (h : ∀ k, H (acct s' k) ∨ Safer (acct s k) (acct s' k) ∨ ¬ H (acct s k)) :
    KeepsHealthy H acct s s' := by
  intro k hk
  rcases h k with h1 | h1 | h1
  · exact h1
  · exact hm _ _ hk h1
  · exact absurd hk h1

/-- No bad debt in any reachable state: when every successful operation keeps healthy accounts
healthy and every account is healthy at the start, every account is healthy in every reachable
state. -/
theorem reachable_healthy {β : Type} {step : σ → β → Option σ} {init : σ} {H : α → Prop}
    {acct : σ → κ → α} (hstep : ∀ s o s', step s o = some s' → KeepsHealthy H acct s s')
    (h0 : ∀ k, H (acct init k)) {s : σ} (hs : Seq.Reachable step init s) : ∀ k, H (acct s k) :=
  hs.invariant h0 (fun s o s' hI he k => hstep s o s' he k (hI k))

/-- The state after a successful atomic run from a healthy state is healthy. -/
theorem runAll_healthy {β : Type} {step : σ → β → Option σ} {H : α → Prop} {acct : σ → κ → α}
    (hstep : ∀ s o s', step s o = some s' → KeepsHealthy H acct s s') {s s' : σ}
    (h0 : ∀ k, H (acct s k)) {ops : List β} (h : Seq.runAll step s ops = some s') :
    ∀ k, H (acct s' k) :=
  Seq.runAll_invariant (I := fun t => ∀ k, H (acct t k))
    (fun t o t' hI he k => hstep t o t' he k (hI k)) h0 h

/-- A checked update: the new position if it is healthy, otherwise a revert. -/
def checked (H : α → Prop) [DecidablePred H] (a : α) : Option α := if H a then some a else none

/-- A checked update that succeeds is healthy: any operation passing a health check leaves the
checked account healthy. -/
theorem checked_healthy {H : α → Prop} [DecidablePred H] {a b : α} (h : checked H a = some b) :
    H b := by
  unfold checked at h
  split at h
  · cases h; assumption
  · cases h

end Health

/-! ## One collateral asset, one debt asset -/

/-- An account's position: collateral held and debt owed, each in units of its asset. -/
structure Position where
  /-- Units of the collateral asset. -/
  collateral : Nat
  /-- Units of the debt asset owed. -/
  debt : Nat
  deriving DecidableEq, Repr

/-- `b` is at least as safe as `a`: at least as much collateral and at most as much debt. -/
def Position.Safer (a b : Position) : Prop := a.collateral ≤ b.collateral ∧ b.debt ≤ a.debt

/-- Market parameters: the fixed-point scale `one`, the prices of a unit of each asset in a common
numeraire (scale `one`), and the collateral factor (Compound's `collateralFactorMantissa`, Aave's
LTV, Morpho Blue's `lltv`; scale `one`, at most `one`). -/
structure Params where
  /-- The fixed-point scale (`1e18`). -/
  one : Nat
  /-- Price of one unit of collateral, at scale `one`. -/
  collPrice : Nat
  /-- Price of one unit of debt, at scale `one`. -/
  debtPrice : Nat
  /-- The collateral factor, at scale `one`. -/
  factor : Nat
  deriving DecidableEq, Repr

namespace Params

variable (m : Params)

/-- The borrow limit: collateral value times the factor, each product rounded down (Morpho Blue:
`collateral.mulDivDown(collateralPrice, ORACLE_PRICE_SCALE).wMulDown(lltv)`). -/
def borrowLimit (p : Position) : Nat := mulDown m.one (mulDown m.one p.collateral m.collPrice) m.factor

/-- The debt value, rounded up. -/
def debtValue (p : Position) : Nat := mulUp m.one p.debt m.debtPrice

/-- A position is healthy when its debt value is within its borrow limit. -/
def Healthy (p : Position) : Prop := m.debtValue p ≤ m.borrowLimit p

instance (p : Position) : Decidable (m.Healthy p) := by unfold Healthy; infer_instance

/-- The rounded check is conservative: a healthy position satisfies the exact inequality
`debt * debtPrice * one ≤ collateral * collPrice * factor` (debt value at most collateral value
times the factor, at scale `one * one`). -/
theorem Healthy.exact {m : Params} {p : Position} (hone : 0 < m.one) (h : m.Healthy p) :
    p.debt * m.debtPrice * m.one ≤ p.collateral * m.collPrice * m.factor := by
  have h1 := le_mulUp_mul m.one p.debt m.debtPrice hone
  have h2 := mulDown_mulDown_le m.one p.collateral m.collPrice m.factor
  have h3 : m.debtValue p * (m.one * m.one) ≤ m.borrowLimit p * (m.one * m.one) :=
    Nat.mul_le_mul_right _ h
  unfold debtValue borrowLimit at h3
  calc p.debt * m.debtPrice * m.one ≤ mulUp m.one p.debt m.debtPrice * m.one * m.one :=
        Nat.mul_le_mul_right _ h1
    _ = mulUp m.one p.debt m.debtPrice * (m.one * m.one) := Nat.mul_assoc _ _ _
    _ ≤ _ := Nat.le_trans h3 h2

/-- A position without debt is healthy. -/
theorem healthy_of_debt_eq_zero {p : Position} (h : p.debt = 0) : m.Healthy p := by
  unfold Healthy debtValue mulUp mulDivUp
  rw [h, Nat.zero_mul, ceilDiv_zero_left]
  exact Nat.zero_le _

/-- A safer position stays healthy. -/
theorem healthy_mono : Monotone m.Healthy Position.Safer := by
  intro a b h hs
  unfold Healthy debtValue borrowLimit at *
  exact Nat.le_trans (mulUp_mono _ hs.2 (Nat.le_refl _))
    (Nat.le_trans h (mulDown_mono _ (mulDown_mono _ hs.1 (Nat.le_refl _)) (Nat.le_refl _)))

/-- A higher collateral price, a lower debt price and a higher factor keep a position healthy
(price moves in the other direction can make it unhealthy, so no-bad-debt statements hold at
fixed prices). -/
theorem healthy_of_params {m m' : Params} {p : Position} (hone : m'.one = m.one)
    (hc : m.collPrice ≤ m'.collPrice) (hd : m'.debtPrice ≤ m.debtPrice) (hf : m.factor ≤ m'.factor)
    (h : m.Healthy p) : m'.Healthy p := by
  unfold Healthy debtValue borrowLimit at *
  rw [hone]
  exact Nat.le_trans (mulUp_mono _ (Nat.le_refl _) hd)
    (Nat.le_trans h (mulDown_mono _ (mulDown_mono _ (Nat.le_refl _) hc) hf))

/-- The health factor at scale `one` (Aave's `healthFactor`): the borrow limit over the debt
value, rounded down; 0 for a position without debt value (Aave reports the maximum there). -/
def healthFactor (p : Position) : Nat := m.borrowLimit p * m.one / m.debtValue p

/-- A position with debt is healthy exactly when its health factor is at least 1. -/
theorem one_le_healthFactor_iff {p : Position} (h : 0 < m.debtValue p) :
    m.one ≤ m.healthFactor p ↔ m.Healthy p := by
  unfold healthFactor Healthy
  rw [Nat.le_div_iff_mul_le h, Nat.mul_comm m.one]
  rcases Nat.eq_zero_or_pos m.one with h0 | h0
  · constructor
    · intro _
      unfold debtValue mulUp mulDivUp at h
      rw [h0] at h
      simp [ceilDiv] at h
    · intro _; rw [h0]; simp
  · exact ⟨fun h1 => Nat.le_of_mul_le_mul_right h1 h0, fun h1 => Nat.mul_le_mul_right _ h1⟩

/-! ### Liquidation -/

/-- Collateral seized for repaying `repay` units of debt with liquidation incentive `incentive`
(scale `one`; `1.08e18` is an 8% bonus): `repay * debtPrice * incentive / (collPrice * one)`,
rounded down (Compound's `liquidateCalculateSeizeTokens`, in units of the collateral). -/
def seize (incentive repay : Nat) : Nat := repay * m.debtPrice * incentive / (m.collPrice * m.one)

/-- The value seized is at most the value repaid times the incentive: seized collateral is at most
the debt repaid times its price times `1 + bonus`, cross-multiplied. -/
theorem seize_value_le (incentive repay : Nat) :
    m.seize incentive repay * m.collPrice * m.one ≤ repay * m.debtPrice * incentive := by
  unfold seize
  rw [Nat.mul_assoc]
  exact Nat.div_mul_le_self _ _

/-- The value seized falls short of the value repaid times the incentive by less than one unit of
collateral. -/
theorem seize_value_gt (incentive repay : Nat) (h : 0 < m.collPrice * m.one) :
    repay * m.debtPrice * incentive < (m.seize incentive repay + 1) * (m.collPrice * m.one) :=
  lt_div_add_one_mul _ _ h

/-- The largest repayment the close factor allows: `debt * closeFactor / one` (Compound's
`closeFactorMantissa`, 50% as `5e17`). -/
def maxRepay (closeFactor : Nat) (p : Position) : Nat := mulDown m.one p.debt closeFactor

/-- With a close factor at most 1, the largest repayment is at most the debt. -/
theorem maxRepay_le {closeFactor : Nat} (p : Position)
    (h : closeFactor ≤ m.one) : m.maxRepay closeFactor p ≤ p.debt := by
  unfold maxRepay mulDown mulDiv
  exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm m.one]; exact Nat.mul_le_mul_left _ h)

/-- A liquidation: `repay` units of debt repaid and the seized collateral taken. -/
def liquidate (incentive repay : Nat) (p : Position) : Position :=
  ⟨p.collateral - m.seize incentive repay, p.debt - repay⟩

/-- A liquidation does not raise the exact shortfall `debt * debtPrice * one - collateral *
collPrice * factor` when the incentive times the factor is at most 1 (`incentive * factor ≤ one *
one`) and the seizure and the repayment are within the position. Stated without subtraction:
`D' + C ≤ D + C'` for the debt terms `D`, `D'` and the collateral terms `C`, `C'` before and after.
With an incentive above `1 / factor` a liquidation makes an unhealthy position worse. -/
theorem liquidate_shortfall_le {incentive repay : Nat} {p : Position} (hone : 0 < m.one)
    (hif : incentive * m.factor ≤ m.one * m.one) (hs : m.seize incentive repay ≤ p.collateral)
    (hr : repay ≤ p.debt) :
    (m.liquidate incentive repay p).debt * m.debtPrice * m.one + p.collateral * m.collPrice * m.factor ≤
      p.debt * m.debtPrice * m.one +
        (m.liquidate incentive repay p).collateral * m.collPrice * m.factor := by
  have h1 := m.seize_value_le incentive repay
  have h2 : m.seize incentive repay * m.collPrice * m.factor * m.one ≤
      repay * m.debtPrice * m.one * m.one := by
    calc m.seize incentive repay * m.collPrice * m.factor * m.one
        = m.seize incentive repay * m.collPrice * m.one * m.factor := Nat.mul_right_comm _ _ _
      _ ≤ repay * m.debtPrice * incentive * m.factor := Nat.mul_le_mul_right _ h1
      _ = repay * m.debtPrice * (incentive * m.factor) := Nat.mul_assoc _ _ _
      _ ≤ repay * m.debtPrice * (m.one * m.one) := Nat.mul_le_mul_left _ hif
      _ = repay * m.debtPrice * m.one * m.one := (Nat.mul_assoc _ _ _).symm
  have h3 := Nat.le_of_mul_le_mul_right h2 hone
  unfold liquidate
  dsimp only
  rw [Nat.sub_mul, Nat.sub_mul, Nat.sub_mul, Nat.sub_mul]
  have h4 : repay * m.debtPrice * m.one ≤ p.debt * m.debtPrice * m.one :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hr)
  have h5 : m.seize incentive repay * m.collPrice * m.factor ≤ p.collateral * m.collPrice * m.factor :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hs)
  omega

/-- A liquidation leaves the position safer in the debt it owes. -/
theorem liquidate_debt_le (incentive repay : Nat) (p : Position) :
    (m.liquidate incentive repay p).debt ≤ p.debt := Nat.sub_le _ _

end Params

/-! ## Interest indices -/

/-- An interest index brought forward by `dt` periods at `rate` per period (scale `one`), with
simple interest over the interval, rounded down: Compound's `accrueInterest`,
`borrowIndex + borrowIndex * (borrowRate * blockDelta) / 1e18`. -/
def accrueIndex (one index rate dt : Nat) : Nat := index + mulDown one index (rate * dt)

/-- The index never falls. -/
theorem le_accrueIndex (one index rate dt : Nat) : index ≤ accrueIndex one index rate dt :=
  Nat.le_add_right _ _

/-- The index is monotone in the starting index. -/
theorem accrueIndex_mono {one index index' : Nat} (rate dt : Nat) (h : index ≤ index') :
    accrueIndex one index rate dt ≤ accrueIndex one index' rate dt :=
  Nat.add_le_add h (mulDown_mono _ h (Nat.le_refl _))

/-- The accrued index is at most the exact value: `accrueIndex * one ≤ index * (one + rate * dt)`. -/
theorem accrueIndex_mul_le (one index rate dt : Nat) :
    accrueIndex one index rate dt * one ≤ index * (one + rate * dt) := by
  have := mulDown_mul_le one index (rate * dt)
  unfold accrueIndex
  rw [Nat.add_mul, Nat.mul_add]
  omega

/-- The debt of a principal recorded at snapshot index `snap`, read at index `index`, rounded down:
`principal * index / snap` (Compound's `borrowBalanceStored`). -/
def debtDown (principal snap index : Nat) : Nat := principal * index / snap

/-- The same debt rounded up, in the protocol's favour. -/
def debtUp (principal snap index : Nat) : Nat := ceilDiv (principal * index) snap

/-- Rounding up never charges less than the exact debt. -/
theorem le_debtUp_mul (principal : Nat) {snap : Nat} (index : Nat) (h : 0 < snap) :
    principal * index ≤ debtUp principal snap index * snap :=
  le_ceilDiv_mul _ _ h

/-- Rounding down never charges more than the exact debt. -/
theorem debtDown_mul_le (principal snap index : Nat) :
    debtDown principal snap index * snap ≤ principal * index :=
  Nat.div_mul_le_self _ _

/-- Rounding down is at most rounding up, which is at most one unit more. -/
theorem debtDown_le_debtUp (principal snap index : Nat) :
    debtDown principal snap index ≤ debtUp principal snap index ∧
      debtUp principal snap index ≤ debtDown principal snap index + 1 :=
  ⟨div_le_ceilDiv _ _, ceilDiv_le_div_add_one _ _⟩

/-- At its own snapshot the debt is the principal. -/
theorem debtDown_self (principal : Nat) {snap : Nat} (h : 0 < snap) :
    debtDown principal snap snap = principal := Nat.mul_div_cancel _ h

/-- At its own snapshot the debt rounded up is the principal. -/
theorem debtUp_self (principal : Nat) {snap : Nat} (h : 0 < snap) :
    debtUp principal snap snap = principal := ceilDiv_mul_cancel _ h

/-- The debt grows with the index, rounded down. -/
theorem debtDown_mono_index (principal snap : Nat) {index index' : Nat} (h : index ≤ index') :
    debtDown principal snap index ≤ debtDown principal snap index' :=
  Nat.div_le_div_right (Nat.mul_le_mul_left _ h)

/-- The debt grows with the index, rounded up. -/
theorem debtUp_mono_index (principal snap : Nat) {index index' : Nat} (h : index ≤ index') :
    debtUp principal snap index ≤ debtUp principal snap index' :=
  ceilDiv_mono_left _ (Nat.mul_le_mul_left _ h)

/-- Re-recording a debt rounded up at an intermediate index never lowers the debt read later: the
protocol never loses by re-snapshotting (on every interaction, as Compound and Aave do). -/
theorem debtUp_resnap (principal : Nat) {snap mid : Nat} (index : Nat) (hs : 0 < snap)
    (hm : 0 < mid) :
    debtUp principal snap index ≤ debtUp (debtUp principal snap mid) mid index := by
  apply ceilDiv_le_ceilDiv_of_mul_le hs hm
  have h := le_debtUp_mul principal mid hs
  calc principal * index * mid = principal * mid * index := Nat.mul_right_comm _ _ _
    _ ≤ debtUp principal snap mid * snap * index := Nat.mul_le_mul_right _ h
    _ = debtUp principal snap mid * index * snap := Nat.mul_right_comm _ _ _

/-- Re-recording a debt rounded down at an intermediate index never raises the debt read later:
with rounding down, each re-snapshot can only favour the borrower. -/
theorem debtDown_resnap (principal : Nat) {snap mid : Nat} (index : Nat) (hs : 0 < snap)
    (hm : 0 < mid) :
    debtDown (debtDown principal snap mid) mid index ≤ debtDown principal snap index := by
  apply div_le_div_of_mul_le hm hs
  have h := debtDown_mul_le principal snap mid
  calc debtDown principal snap mid * index * snap = debtDown principal snap mid * snap * index :=
        Nat.mul_right_comm _ _ _
    _ ≤ principal * mid * index := Nat.mul_le_mul_right _ h
    _ = principal * index * mid := Nat.mul_right_comm _ _ _

/-- Debts recorded at one snapshot (Aave's scaled balances against one index), rounded down, add
up to at most the total read from the summed principals: the pool's total covers every account's
debt. -/
theorem sum_debtDown_le {β : Type u} (l : List β) (principal : β → Nat) (snap index : Nat) :
    (l.map fun b => debtDown (principal b) snap index).sum ≤
      debtDown (l.map principal).sum snap index := by
  unfold debtDown
  have := sum_div_le_div_sum (l.map fun b => principal b * index) snap
  rw [List.map_map] at this
  have e : (l.map fun b => principal b * index).sum = (l.map principal).sum * index :=
    Ledger.sum_map_mul_right l principal index
  rw [e] at this
  exact this

/-! ## A pool and its solvency -/

/-- A lending pool's books: underlying held (`cash`), lent out (`borrows`), owned by the protocol
(`reserves`), and owed to suppliers (`supplied`). -/
structure Pool where
  /-- Underlying held. -/
  cash : Nat
  /-- Underlying lent out and owed by borrowers. -/
  borrows : Nat
  /-- Underlying owned by the protocol. -/
  reserves : Nat
  /-- Underlying owed to suppliers. -/
  supplied : Nat
  deriving DecidableEq, Repr

/-- Operations on the pool. -/
inductive PoolOp where
  /-- `x` underlying supplied. -/
  | supply (x : Nat)
  /-- `x` underlying withdrawn by suppliers; refused above the cash or the amount supplied. -/
  | withdraw (x : Nat)
  /-- `x` underlying borrowed; refused above the cash. -/
  | borrow (x : Nat)
  /-- `x` underlying repaid; refused above the borrows. -/
  | repay (x : Nat)
  /-- `i` interest accrues on the borrows; the reserve factor's share goes to reserves, the rest to
  suppliers. -/
  | accrue (i : Nat)
  /-- `x` of bad debt written off against suppliers (Morpho Blue's bad-debt realization). -/
  | writeOff (x : Nat)
  deriving DecidableEq, Repr

/-- One operation, with reserve factor `rf` at scale `one`; a refused operation changes nothing. -/
def poolStep (one rf : Nat) (p : Pool) : PoolOp → Pool
  | .supply x => { p with cash := p.cash + x, supplied := p.supplied + x }
  | .withdraw x =>
    if x ≤ p.cash ∧ x ≤ p.supplied then { p with cash := p.cash - x, supplied := p.supplied - x }
    else p
  | .borrow x => if x ≤ p.cash then { p with cash := p.cash - x, borrows := p.borrows + x } else p
  | .repay x => if x ≤ p.borrows then { p with cash := p.cash + x, borrows := p.borrows - x } else p
  | .accrue i =>
    { p with borrows := p.borrows + i, reserves := p.reserves + mulDown one i rf,
             supplied := p.supplied + (i - mulDown one i rf) }
  | .writeOff x =>
    if x ≤ p.borrows ∧ x ≤ p.supplied then
      { p with borrows := p.borrows - x, supplied := p.supplied - x }
    else p

/-- The books balance: what is held plus what is lent out is what is owed to suppliers plus the
reserves. -/
def Pool.Balanced (p : Pool) : Prop := p.cash + p.borrows = p.supplied + p.reserves

/-- A reserve factor at most 1 takes at most the interest. -/
theorem mulDown_le_of_le_one {one i rf : Nat} (h : rf ≤ one) : mulDown one i rf ≤ i := by
  unfold mulDown mulDiv
  exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm one]; exact Nat.mul_le_mul_left _ h)

/-- Every operation keeps the books balanced, for a reserve factor at most 1. -/
theorem poolStep_balanced {one rf : Nat} (hrf : rf ≤ one) (p : Pool) (o : PoolOp)
    (h : p.Balanced) : (poolStep one rf p o).Balanced := by
  unfold Pool.Balanced at *
  cases o with
  | supply x => simp only [poolStep]; omega
  | withdraw x => simp only [poolStep]; split <;> (try dsimp only) <;> omega
  | borrow x => simp only [poolStep]; split <;> (try dsimp only) <;> omega
  | repay x => simp only [poolStep]; split <;> (try dsimp only) <;> omega
  | accrue i =>
    have := mulDown_le_of_le_one (i := i) hrf
    simp only [poolStep]; omega
  | writeOff x => simp only [poolStep]; split <;> (try dsimp only) <;> omega

/-- The books balance after every sequence of operations from balanced books. -/
theorem run_balanced {one rf : Nat} (hrf : rf ≤ one) {p : Pool} (h : p.Balanced)
    (ops : List PoolOp) : (Seq.run (poolStep one rf) p ops).Balanced :=
  Seq.run_invariant (fun q o hq => poolStep_balanced hrf q o hq) h ops

/-- Solvency: with balanced books, total borrows never exceed what is owed to suppliers plus the
reserves (the cash makes up the difference). -/
theorem Pool.borrows_le {p : Pool} (h : p.Balanced) : p.borrows ≤ p.supplied + p.reserves := by
  unfold Pool.Balanced at h; omega

/-- Solvency after every sequence of operations from balanced books. -/
theorem run_borrows_le {one rf : Nat} (hrf : rf ≤ one) {p : Pool}
    (h : p.Balanced) (ops : List PoolOp) :
    (Seq.run (poolStep one rf) p ops).borrows ≤
      (Seq.run (poolStep one rf) p ops).supplied + (Seq.run (poolStep one rf) p ops).reserves :=
  Pool.borrows_le (run_balanced hrf h ops)

/-- The cash covers what suppliers can withdraw beyond what is lent out: with balanced books,
`supplied + reserves - borrows` is the cash. -/
theorem Pool.cash_eq {p : Pool} (h : p.Balanced) : p.cash = p.supplied + p.reserves - p.borrows := by
  unfold Pool.Balanced at h; omega

end ProofForgeFin.DeFi.Lending
