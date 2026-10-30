import ProofForgeFin.Rounding
import ProofForgeFin.Seq
/-!
# Share accounting

A vault (an ERC-4626 vault, a Compound cToken, a liquidity pool) holds `assets` of an underlying
token and has issued `supply` shares; one share is worth the rational `assets / supply`. The four
conversions round in the vault's favour:

* `previewDeposit p x`: shares minted for `x` assets deposited, `x * supply / assets` rounded
  down;
* `previewMint p t`: assets charged to mint `t` shares, `t * assets / supply` rounded up;
* `previewRedeem p t`: assets paid for `t` shares redeemed, rounded down;
* `previewWithdraw p x`: shares burned to withdraw `x` assets, rounded up.

`ValueNotBelow p q` states, by cross-multiplication, that a share of `q` is worth at least a
share of `p`. The main results: each conversion rounded in the vault's favour never lowers share
value; donations never lower it; value comparisons chain through states with outstanding shares;
round trips (deposit then redeem, mint then redeem, redeem then deposit) never return more than
was put in; and, for the vault model `step`, share value never falls over any sequence of
operations while shares stay outstanding.

Exactness of each conversion (within one unit of the exact value, on the vault's side) is stated
as in `ProofForgeFin.Rounding`.
-/

namespace ProofForgeFin.Shares

open ProofForgeFin

/-- A vault's books: the underlying it holds and the shares it has issued. -/
structure Pool where
  /-- Underlying held by the vault, in its smallest unit. -/
  assets : Nat
  /-- Shares issued and outstanding. -/
  supply : Nat
  deriving DecidableEq, Repr

/-- `p` after `x` assets came in and `t` shares were issued. -/
def Pool.add (p : Pool) (x t : Nat) : Pool := ⟨p.assets + x, p.supply + t⟩

/-- `p` after `y` assets went out and `t` shares were burned. -/
def Pool.sub (p : Pool) (y t : Nat) : Pool := ⟨p.assets - y, p.supply - t⟩

/-- A share of `q` is worth at least as much underlying as a share of `p`:
`p.assets / p.supply ≤ q.assets / q.supply`, cross-multiplied. -/
def ValueNotBelow (p q : Pool) : Prop := p.assets * q.supply ≤ q.assets * p.supply

/-- Share value comparisons are decidable. -/
instance (p q : Pool) : Decidable (ValueNotBelow p q) := by unfold ValueNotBelow; infer_instance

/-! ## Conversions -/

/-- Shares minted for a deposit of `x` assets, rounded down (ERC-4626 `previewDeposit`). -/
def previewDeposit (p : Pool) (x : Nat) : Nat := x * p.supply / p.assets

/-- Assets charged to mint `t` shares, rounded up (ERC-4626 `previewMint`). -/
def previewMint (p : Pool) (t : Nat) : Nat := ceilDiv (t * p.assets) p.supply

/-- Assets paid for redeeming `t` shares, rounded down (ERC-4626 `previewRedeem`). -/
def previewRedeem (p : Pool) (t : Nat) : Nat := t * p.assets / p.supply

/-- Shares burned to withdraw `x` assets, rounded up (ERC-4626 `previewWithdraw`). -/
def previewWithdraw (p : Pool) (x : Nat) : Nat := ceilDiv (x * p.supply) p.assets

/-- A deposit mints the exact share count rounded down: never a share not paid for in full. -/
theorem previewDeposit_spec (p : Pool) (x : Nat) (h : 0 < p.assets) :
    previewDeposit p x * p.assets ≤ x * p.supply ∧
    x * p.supply < (previewDeposit p x + 1) * p.assets :=
  floor_spec _ _ h

/-- A mint charges the exact asset amount rounded up. -/
theorem previewMint_spec (p : Pool) (t : Nat) (h : 0 < p.supply) :
    t * p.assets ≤ previewMint p t * p.supply ∧
    previewMint p t * p.supply < t * p.assets + p.supply :=
  ceilDiv_spec _ _ h

/-- A redemption pays the exact asset amount rounded down. -/
theorem previewRedeem_spec (p : Pool) (t : Nat) (h : 0 < p.supply) :
    previewRedeem p t * p.supply ≤ t * p.assets ∧
    t * p.assets < (previewRedeem p t + 1) * p.supply :=
  floor_spec _ _ h

/-- A withdrawal burns the exact share count rounded up. -/
theorem previewWithdraw_spec (p : Pool) (x : Nat) (h : 0 < p.assets) :
    x * p.supply ≤ previewWithdraw p x * p.assets ∧
    previewWithdraw p x * p.assets < x * p.supply + p.assets :=
  ceilDiv_spec _ _ h

/-- Redeeming at most the supply pays at most the assets. -/
theorem previewRedeem_le_assets (p : Pool) {t : Nat} (h : t ≤ p.supply) :
    previewRedeem p t ≤ p.assets := mul_div_le_of_le h

/-- Withdrawing at most the assets burns at most the supply. -/
theorem previewWithdraw_le_supply (p : Pool) {x : Nat} (ha : 0 < p.assets) (h : x ≤ p.assets) :
    previewWithdraw p x ≤ p.supply := by
  apply (ceilDiv_le_iff ha).2
  rw [Nat.mul_comm p.supply p.assets]
  exact Nat.mul_le_mul_right _ h

/-- A deposit mints no share exactly when `x * supply < assets`: the condition a first-depositor
(inflation) attack creates by donating to a vault with few shares. -/
theorem previewDeposit_eq_zero_iff (p : Pool) (x : Nat) (h : 0 < p.assets) :
    previewDeposit p x = 0 ↔ x * p.supply < p.assets := by
  unfold previewDeposit
  constructor
  · intro e
    have := lt_div_add_one_mul (x * p.supply) p.assets h
    rw [e] at this; simpa using this
  · intro hl
    exact Nat.div_eq_of_lt hl

/-- Conversions are monotone in the amount converted. -/
theorem previewDeposit_mono (p : Pool) {x y : Nat} (h : x ≤ y) :
    previewDeposit p x ≤ previewDeposit p y :=
  div_mono_left _ (Nat.mul_le_mul_right _ h)

/-- `previewRedeem` is monotone in the shares redeemed. -/
theorem previewRedeem_mono (p : Pool) {t u : Nat} (h : t ≤ u) :
    previewRedeem p t ≤ previewRedeem p u :=
  div_mono_left _ (Nat.mul_le_mul_right _ h)

/-- `previewMint` is monotone in the shares minted. -/
theorem previewMint_mono (p : Pool) {t u : Nat} (h : t ≤ u) : previewMint p t ≤ previewMint p u :=
  ceilDiv_mono_left _ (Nat.mul_le_mul_right _ h)

/-- `previewWithdraw` is monotone in the assets withdrawn. -/
theorem previewWithdraw_mono (p : Pool) {x y : Nat} (h : x ≤ y) :
    previewWithdraw p x ≤ previewWithdraw p y :=
  ceilDiv_mono_left _ (Nat.mul_le_mul_right _ h)

/-- Rounding in the vault's favour: the shares minted for `x` never exceed the shares burned to
withdraw `x`. -/
theorem previewDeposit_le_previewWithdraw (p : Pool) (x : Nat) :
    previewDeposit p x ≤ previewWithdraw p x := div_le_ceilDiv _ _

/-- Rounding in the vault's favour: the assets paid for `t` shares never exceed the assets
charged to mint them. -/
theorem previewRedeem_le_previewMint (p : Pool) (t : Nat) : previewRedeem p t ≤ previewMint p t :=
  div_le_ceilDiv _ _

/-! ## Share value -/

/-- Share value is reflexive. -/
theorem valueNotBelow_refl (p : Pool) : ValueNotBelow p p := Nat.le_refl _

/-- Share value comparisons chain through a state with outstanding shares. -/
theorem valueNotBelow_trans {p q r : Pool} (h1 : ValueNotBelow p q) (h2 : ValueNotBelow q r)
    (hq : 0 < q.supply) : ValueNotBelow p r := by
  unfold ValueNotBelow at *
  apply Nat.le_of_mul_le_mul_right _ hq
  calc p.assets * r.supply * q.supply = (p.assets * q.supply) * r.supply := Nat.mul_right_comm _ _ _
    _ ≤ (q.assets * p.supply) * r.supply := Nat.mul_le_mul_right _ h1
    _ = (q.assets * r.supply) * p.supply := Nat.mul_right_comm _ _ _
    _ ≤ (r.assets * q.supply) * p.supply := Nat.mul_le_mul_right _ h2
    _ = r.assets * p.supply * q.supply := Nat.mul_right_comm _ _ _

/-- Issuing `t` shares for `x` assets keeps share value when the shares are worth at most what
was paid: `t * assets ≤ x * supply`. -/
theorem add_value (p : Pool) {x t : Nat} (h : t * p.assets ≤ x * p.supply) :
    ValueNotBelow p (p.add x t) := by
  unfold ValueNotBelow Pool.add
  simp only
  rw [Nat.mul_add, Nat.add_mul, Nat.mul_comm p.assets t]
  omega

/-- Paying out `y` assets for `t` burned shares keeps share value when the payout is worth at
most the shares: `y * supply ≤ t * assets`. -/
theorem sub_value (p : Pool) {y t : Nat} (h : y * p.supply ≤ t * p.assets) :
    ValueNotBelow p (p.sub y t) := by
  unfold ValueNotBelow Pool.sub
  simp only
  rw [Nat.mul_sub, Nat.sub_mul, Nat.mul_comm p.assets t]
  omega

/-- A donation (assets in, no shares issued) never lowers share value. -/
theorem donate_value (p : Pool) (x : Nat) : ValueNotBelow p (p.add x 0) :=
  add_value p (by simp)

/-- A deposit rounded down never lowers share value. -/
theorem deposit_value (p : Pool) (x : Nat) : ValueNotBelow p (p.add x (previewDeposit p x)) :=
  add_value p (div_mul_le _ _)

/-- A mint rounded up never lowers share value. -/
theorem mint_value (p : Pool) (t : Nat) (h : 0 < p.supply) :
    ValueNotBelow p (p.add (previewMint p t) t) :=
  add_value p (previewMint_spec p t h).1

/-- A redemption rounded down never lowers share value. -/
theorem redeem_value (p : Pool) (t : Nat) : ValueNotBelow p (p.sub (previewRedeem p t) t) :=
  sub_value p (div_mul_le _ _)

/-- A withdrawal rounded up never lowers share value. -/
theorem withdraw_value (p : Pool) (x : Nat) (h : 0 < p.assets) :
    ValueNotBelow p (p.sub x (previewWithdraw p x)) :=
  sub_value p (previewWithdraw_spec p x h).1

/-- Share value never falling means a later redemption of the same shares pays at least as
much. -/
theorem previewRedeem_le_of_value {p q : Pool} (h : ValueNotBelow p q) (hp : 0 < p.supply)
    (hq : 0 < q.supply) (t : Nat) : previewRedeem p t ≤ previewRedeem q t := by
  unfold previewRedeem
  apply div_le_div_of_mul_le hp hq
  unfold ValueNotBelow at h
  rw [Nat.mul_assoc, Nat.mul_assoc]
  exact Nat.mul_le_mul_left t h

/-! ## Round trips -/

/-- Depositing `x` and immediately redeeming the shares received pays out at most `x`. -/
theorem deposit_redeem_le (p : Pool) (x : Nat) :
    previewRedeem (p.add x (previewDeposit p x)) (previewDeposit p x) ≤ x := by
  have h : previewDeposit p x * p.assets ≤ x * p.supply := div_mul_le _ _
  unfold previewRedeem Pool.add
  simp only
  apply div_le_of_le_mul'
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm x (previewDeposit p x)]
  omega

/-- Minting `t` shares and immediately redeeming them pays out at most what the mint charged. -/
theorem mint_redeem_le (p : Pool) (t : Nat) (h : 0 < p.supply) :
    previewRedeem (p.add (previewMint p t) t) t ≤ previewMint p t := by
  have h1 := (previewMint_spec p t h).1
  unfold previewRedeem Pool.add
  simp only
  apply div_le_of_le_mul'
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm (previewMint p t) t]
  omega

/-- Redeeming `t` shares and immediately depositing the payout mints at most `t` shares. -/
theorem redeem_deposit_le (p : Pool) (t : Nat) :
    previewDeposit (p.sub (previewRedeem p t) t) (previewRedeem p t) ≤ t := by
  have h : previewRedeem p t * p.supply ≤ t * p.assets := div_mul_le _ _
  unfold previewDeposit Pool.sub
  simp only
  apply div_le_of_le_mul'
  rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_comm t (previewRedeem p t)]
  omega

/-- Withdrawing `x` and immediately minting back the shares burned charges at least `x`. -/
theorem withdraw_mint_ge (p : Pool) (x : Nat) (h : 0 < p.assets)
    (hs : 0 < p.supply - previewWithdraw p x) :
    x ≤ previewMint (p.sub x (previewWithdraw p x)) (previewWithdraw p x) := by
  have h1 := (previewWithdraw_spec p x h).1
  unfold previewMint Pool.sub
  simp only
  apply Nat.le_of_mul_le_mul_right _ hs
  refine Nat.le_trans ?_ (le_ceilDiv_mul _ _ hs)
  rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_comm x (previewWithdraw p x)]
  omega

/-! ## A vault and its operations -/

/-- Operations on a vault. `donate` sends assets without calling the vault (the vault reads its
holdings from the token balance). -/
inductive Op where
  /-- Deposit `assets` and receive the shares they buy, rounded down. -/
  | deposit (assets : Nat)
  /-- Mint `shares` and pay the assets they cost, rounded up. -/
  | mint (shares : Nat)
  /-- Redeem `shares` and receive the assets they are worth, rounded down. -/
  | redeem (shares : Nat)
  /-- Withdraw `assets` and burn the shares they are worth, rounded up. -/
  | withdraw (assets : Nat)
  /-- Send `assets` to the vault without calling it. -/
  | donate (assets : Nat)
  deriving DecidableEq, Repr

/-- A vault that prices every call from the exact ratio `assets / supply` and rounds in its own
favour. With no shares outstanding a deposit mints `initialRate` shares per unit and a mint is
refused. A refused call leaves the books unchanged. -/
def step (initialRate : Nat) (p : Pool) : Op → Pool
  | .deposit x =>
    if p.supply = 0 then p.add x (initialRate * x)
    else if p.assets = 0 then p
    else p.add x (previewDeposit p x)
  | .mint t => if p.supply = 0 then p else p.add (previewMint p t) t
  | .redeem t => if t ≤ p.supply then p.sub (previewRedeem p t) t else p
  | .withdraw x =>
    if 0 < p.assets ∧ x ≤ p.assets ∧ previewWithdraw p x ≤ p.supply then
      p.sub x (previewWithdraw p x)
    else p
  | .donate x => p.add x 0

/-- From a vault with outstanding shares, no operation lowers share value. -/
theorem step_value (r : Nat) (p : Pool) (op : Op) (h : 0 < p.supply) :
    ValueNotBelow p (step r p op) := by
  cases op with
  | deposit x =>
    simp only [step]
    split
    · omega
    · split
      · exact valueNotBelow_refl p
      · exact deposit_value p x
  | mint t =>
    simp only [step]
    split
    · exact valueNotBelow_refl p
    · exact mint_value p t h
  | redeem t =>
    simp only [step]
    split
    · exact redeem_value p t
    · exact valueNotBelow_refl p
  | withdraw x =>
    simp only [step]
    split
    · rename_i hc; exact withdraw_value p x hc.1
    · exact valueNotBelow_refl p
  | donate x => exact donate_value p x

/-- Share value never falls: after any sequence of operations along which shares stay
outstanding, a share is worth at least what it was worth at the start. -/
theorem run_value (r : Nat) (p : Pool) (ops : List Op)
    (h : ∀ q ∈ Seq.trace (step r) p ops, 0 < q.supply) :
    ValueNotBelow p (Seq.run (step r) p ops) :=
  Seq.run_rel_of_trace (C := fun q => 0 < q.supply) valueNotBelow_refl
    (fun _ _ _ h1 h2 hq => valueNotBelow_trans h1 h2 hq) (fun q op hq => step_value r q op hq)
    p ops h

/-- The vault never pays out assets it does not hold: the books stay consistent in the sense
that redeeming every share pays at most the assets, after any sequence of operations. -/
theorem run_redeem_all_le (r : Nat) (p : Pool) (ops : List Op) :
    previewRedeem (Seq.run (step r) p ops) (Seq.run (step r) p ops).supply ≤
      (Seq.run (step r) p ops).assets :=
  previewRedeem_le_assets _ (Nat.le_refl _)

end ProofForgeFin.Shares
