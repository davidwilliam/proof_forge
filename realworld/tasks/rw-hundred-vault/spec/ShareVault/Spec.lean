/-!
# Share vault specification (protected)

Owner-reviewed definitions for the share accounting of a lending market such as a Compound v2
cToken: actors deposit an underlying token and receive shares; shares are redeemed for the
underlying they are worth. The underlying value of one share is `assets / supply`. Anyone can
also send underlying to the vault directly, without calling it (a donation): this raises
`assets` and leaves `supply` unchanged, because the vault reads its holdings from the token
balance.

The implementation `vault : Impl` handles the three calls (deposit, redeem shares, withdraw
an amount of underlying). Donations are not calls and are modelled here, outside the
implementation. Candidates may not edit this file; the locked challenge
(`ShareVault/Challenge.lean`) applies every requirement to the definition hole
`ShareVault.vault`.

All quantities are natural numbers in the smallest unit (satoshi for WBTC, 1e-8 of a share
for an 8-decimal cToken). Exact share values are rationals; every requirement states them by
cross-multiplication, so `a * d ≤ c * b` reads "a / b ≤ c / d".
-/

namespace ShareVault

/-- Actors are numbered. -/
abbrev Actor := Nat

/-- Vault state. `assets` is the underlying that backs the shares (for a cToken:
`cash + totalBorrows - totalReserves`), `supply` the total number of shares, `balance a` the
shares held by actor `a`. -/
structure Vault where
  assets : Nat
  supply : Nat
  balance : Actor → Nat

/-- The empty vault: no underlying, no shares. -/
def empty : Vault := { assets := 0, supply := 0, balance := fun _ => 0 }

/-- Calls handled by the implementation.
* `deposit who x`: `who` pays in `x` underlying and receives shares (cToken `mint`).
* `redeem who t`: `who` gives back `t` shares and receives underlying (cToken `redeem`).
* `withdraw who x`: `who` receives exactly `x` underlying and gives back the shares it is
  worth (cToken `redeemUnderlying`). -/
inductive Call where
  | deposit (who : Actor) (amount : Nat)
  | redeem (who : Actor) (shares : Nat)
  | withdraw (who : Actor) (amount : Nat)

/-- An implementation returns the next state, or `none` when it refuses the call (the call
fails or reverts and the state is unchanged). -/
abbrev Impl := Vault → Call → Option Vault

/-- Shares minted to a vault holding no shares, per unit of underlying deposited. Compound
v2 prices the first deposit at `initialExchangeRateMantissa`; Hundred Finance's hWBTC market
uses 0.02 underlying per share (`2e16`), which is 50 shares per unit. -/
def initialSharesPerUnit : Nat := 50

/-! ## Effects of a call -/

/-- `s'` is `s` after `who` paid in `x` underlying and received `t` new shares; nobody
else's balance changes. -/
def Minted (s : Vault) (who : Actor) (x t : Nat) (s' : Vault) : Prop :=
  s'.assets = s.assets + x ∧ s'.supply = s.supply + t ∧
  s'.balance who = s.balance who + t ∧ ∀ b, b ≠ who → s'.balance b = s.balance b

/-- `s'` is `s` after `who` gave back `t` of its shares and received `y` underlying; nobody
else's balance changes. The shares and the underlying must exist. -/
def Burned (s : Vault) (who : Actor) (t y : Nat) (s' : Vault) : Prop :=
  t ≤ s.balance who ∧ t ≤ s.supply ∧ y ≤ s.assets ∧
  s'.assets = s.assets - y ∧ s'.supply = s.supply - t ∧
  s'.balance who = s.balance who - t ∧ ∀ b, b ≠ who → s'.balance b = s.balance b

/-! ## Operations and runs -/

/-- What can happen to the vault: a call to the implementation, or a donation of underlying
sent straight to the vault by anyone. -/
inductive Op where
  | call (c : Call)
  | donate (amount : Nat)

/-- One operation. A refused call leaves the state unchanged. -/
def exec (impl : Impl) (s : Vault) : Op → Vault
  | .call c => (impl s c).getD s
  | .donate x => { s with assets := s.assets + x }

/-- The state after a sequence of operations. -/
def run (impl : Impl) (s : Vault) : List Op → Vault
  | [] => s
  | op :: ops => run impl (exec impl s op) ops

/-- Every state a sequence of operations passes through, starting with `s` and ending with
`run impl s ops`. -/
def trace (impl : Impl) (s : Vault) : List Op → List Vault
  | [] => [s]
  | op :: ops => s :: trace impl (exec impl s op) ops

/-- A share of `s'` is worth at least as much underlying as a share of `s`:
`s.assets / s.supply ≤ s'.assets / s'.supply`, cross-multiplied. -/
def ValueNotBelow (s s' : Vault) : Prop :=
  s.assets * s'.supply ≤ s'.assets * s.supply

instance (s s' : Vault) : Decidable (ValueNotBelow s s') := by
  unfold ValueNotBelow; infer_instance

/-! ## Requirements on the implementation -/

/-- REQ-DEPOSIT-SUCCEEDS: a deposit succeeds whenever shares can be priced: the vault holds
no shares, or it holds some underlying. -/
def DepositSucceeds (vault : Impl) : Prop :=
  ∀ s who x, (s.supply = 0 ∨ 0 < s.assets) → (vault s (.deposit who x)).isSome

/-- REQ-REDEEM-SUCCEEDS: redeeming shares the caller holds succeeds. -/
def RedeemSucceeds (vault : Impl) : Prop :=
  ∀ s who t, t ≤ s.balance who → t ≤ s.supply → (vault s (.redeem who t)).isSome

/-- REQ-WITHDRAW-SUCCEEDS: withdrawing `x` underlying succeeds whenever the caller's shares
are worth at least `x` (`x ≤ balance * assets / supply`). -/
def WithdrawSucceeds (vault : Impl) : Prop :=
  ∀ s who x, 0 < s.supply → 0 < s.assets → s.balance who ≤ s.supply →
    x * s.supply ≤ s.balance who * s.assets → (vault s (.withdraw who x)).isSome

/-- REQ-DEPOSIT-EFFECTS: a deposit of `x` adds exactly `x` to the assets and mints shares
to the caller only. -/
def DepositEffects (vault : Impl) : Prop :=
  ∀ s s' who x, vault s (.deposit who x) = some s' → ∃ t, Minted s who x t s'

/-- REQ-REDEEM-EFFECTS: redeeming `t` shares burns exactly `t` of the caller's shares and
pays out underlying the vault holds; no other balance changes. -/
def RedeemEffects (vault : Impl) : Prop :=
  ∀ s s' who t, vault s (.redeem who t) = some s' → ∃ y, Burned s who t y s'

/-- REQ-WITHDRAW-EFFECTS: withdrawing `x` pays out exactly `x` and burns shares of the
caller only. -/
def WithdrawEffects (vault : Impl) : Prop :=
  ∀ s s' who x, vault s (.withdraw who x) = some s' → ∃ t, Burned s who t x s'

/-- REQ-DEPOSIT-ROUNDS-DOWN: a deposit of `x` mints `x * supply / assets` shares rounded
down (at the initial price when the vault holds no shares). Rounding down favours the vault:
the depositor never receives a share it has not paid for in full. -/
def DepositRoundsDown (vault : Impl) : Prop :=
  ∀ s s' who x t, vault s (.deposit who x) = some s' → Minted s who x t s' →
    (s.supply = 0 → t = initialSharesPerUnit * x) ∧
    (0 < s.supply → t * s.assets ≤ x * s.supply ∧ x * s.supply < (t + 1) * s.assets)

/-- REQ-REDEEM-ROUNDS-DOWN: redeeming `t` shares pays `t * assets / supply` rounded down.
Rounding down favours the vault. With no shares outstanding nothing is paid. -/
def RedeemRoundsDown (vault : Impl) : Prop :=
  ∀ s s' who t y, vault s (.redeem who t) = some s' → Burned s who t y s' →
    (s.supply = 0 → y = 0) ∧
    (0 < s.supply → y * s.supply ≤ t * s.assets ∧ t * s.assets < (y + 1) * s.supply)

/-- REQ-WITHDRAW-ROUNDS-UP: withdrawing `x` underlying burns `x * supply / assets` shares
rounded up. Rounding up favours the vault: the caller always gives back at least the shares
`x` is worth. A withdrawal needs outstanding shares. -/
def WithdrawRoundsUp (vault : Impl) : Prop :=
  ∀ s s' who x t, vault s (.withdraw who x) = some s' → Burned s who t x s' →
    0 < s.supply ∧ x * s.supply ≤ t * s.assets ∧ t * s.assets < x * s.supply + s.assets

/-- REQ-SHARE-VALUE: starting from the empty vault, after any history of operations by any
actors, no further sequence of operations by any actors, including donations and refused
calls, lowers the underlying value of a share while shares stay outstanding. Equivalently:
the vault always holds enough underlying to pay every outstanding share at least the value a
share had at any earlier point since which shares have stayed outstanding, so a holder (or a
lender who accepted the shares as collateral at that value) is never left with shares worth
less. -/
def ShareValueNeverFalls (vault : Impl) : Prop :=
  ∀ history ops : List Op,
    (∀ v ∈ trace vault (run vault empty history) ops, 0 < v.supply) →
    ValueNotBelow (run vault empty history) (run vault (run vault empty history) ops)

end ShareVault
