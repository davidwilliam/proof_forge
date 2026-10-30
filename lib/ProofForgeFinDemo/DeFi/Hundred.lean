import ProofForgeFin.DeFi
import ProofForgeFin.Shares
/-!
# Demonstration: REQ-SHARE-VALUE of `rw-hundred-vault` from the per-call requirements

The first section copies `realworld/tasks/rw-hundred-vault/spec/ShareVault/Spec.lean` without
change (its namespace body, with every doc string). The task files are not imported or modified.

The second section proves REQ-SHARE-VALUE for every implementation that meets REQ-DEPOSIT-EFFECTS,
REQ-DEPOSIT-ROUNDS-DOWN, REQ-REDEEM-EFFECTS, REQ-REDEEM-ROUNDS-DOWN, REQ-WITHDRAW-EFFECTS and
REQ-WITHDRAW-ROUNDS-UP (`share_value`). `ProofForgeFinDemo.ShareVault` proves it for the reference
implementation only.
-/

namespace ProofForgeFinDemo.DeFi.Hundred

/-! ## Copied from `spec/ShareVault/Spec.lean` -/


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

/-! ## Re-proved with the library

The reference solution proves REQ-SHARE-VALUE for its own implementation. Here it is proved for
every implementation that meets the effect and rounding requirements of the three calls: a vault
read as a `Shares.Pool` moves by `Pool.add` on a deposit and by `Pool.sub` on a redemption or a
withdrawal, the rounding requirements are exactly the hypotheses of `Shares.add_value` and
`Shares.sub_value`, and the induction is `Seq.run_rel_of_trace` with
`Shares.valueNotBelow_trans`. -/

open ProofForgeFin

/-- The books of a vault as a library pool. -/
def pool (s : Vault) : Shares.Pool := ⟨s.assets, s.supply⟩

/-- The task's share value comparison is the library's. -/
theorem valueNotBelow_iff (s s' : Vault) : ValueNotBelow s s' ↔ Shares.ValueNotBelow (pool s) (pool s') :=
  Iff.rfl

/-- The task's `run` is the library's. -/
theorem run_eq (impl : Impl) (s : Vault) (ops : List Op) : run impl s ops = Seq.run (exec impl) s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih _

/-- The task's `trace` is the library's. -/
theorem trace_eq (impl : Impl) (s : Vault) (ops : List Op) :
    trace impl s ops = Seq.trace (exec impl) s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => simp only [trace, Seq.trace_cons, ih]

/-- A mint of `t` shares for `x` assets moves the books by `Pool.add`. -/
theorem pool_minted {s s' : Vault} {who : Actor} {x t : Nat} (h : Minted s who x t s') :
    pool s' = (pool s).add x t := by
  simp only [pool, Shares.Pool.add, h.1, h.2.1]

/-- A burn of `t` shares for `y` assets moves the books by `Pool.sub`. -/
theorem pool_burned {s s' : Vault} {who : Actor} {t y : Nat} (h : Burned s who t y s') :
    pool s' = (pool s).sub y t := by
  simp only [pool, Shares.Pool.sub, h.2.2.2.1, h.2.2.2.2.1]

section Requirements

variable {vault : Impl} (hDE : DepositEffects vault) (hDR : DepositRoundsDown vault)
  (hRE : RedeemEffects vault) (hRR : RedeemRoundsDown vault) (hWE : WithdrawEffects vault)
  (hWR : WithdrawRoundsUp vault)
include hDE hDR hRE hRR hWE hWR

/-- From a vault with outstanding shares, no operation lowers share value, for every
implementation that meets the six requirements. -/
theorem exec_value (s : Vault) (op : Op) (hs : 0 < s.supply) : ValueNotBelow s (exec vault s op) := by
  cases op with
  | donate x => exact (valueNotBelow_iff _ _).2 (Shares.donate_value (pool s) x)
  | call c =>
    simp only [exec]
    cases e : vault s c with
    | none => exact Shares.valueNotBelow_refl (pool s)
    | some s' =>
      rw [Option.getD_some, valueNotBelow_iff]
      cases c with
      | deposit who x =>
        obtain ⟨t, ht⟩ := hDE s s' who x e
        rw [pool_minted ht]
        exact Shares.add_value (pool s) ((hDR s s' who x t e ht).2 hs).1
      | redeem who t =>
        obtain ⟨y, hy⟩ := hRE s s' who t e
        rw [pool_burned hy]
        exact Shares.sub_value (pool s) ((hRR s s' who t y e hy).2 hs).1
      | withdraw who x =>
        obtain ⟨t, ht⟩ := hWE s s' who x e
        rw [pool_burned ht]
        exact Shares.sub_value (pool s) (hWR s s' who x t e ht).2.1

/-- REQ-SHARE-VALUE for every implementation that meets the effect and rounding requirements of
the three calls (from any start, not only the histories from `empty`). -/
theorem share_value : ShareValueNeverFalls vault := by
  intro history ops h
  simp only [run_eq, trace_eq] at h ⊢
  exact Seq.run_rel_of_trace (C := fun v => 0 < v.supply) (R := ValueNotBelow)
    (fun v => Shares.valueNotBelow_refl (pool v))
    (fun x y z h1 h2 hq => Shares.valueNotBelow_trans (p := pool x) (q := pool y) (r := pool z)
      h1 h2 hq)
    (fun v op hv => exec_value hDE hDR hRE hRR hWE hWR v op hv) _ ops h

end Requirements

end ProofForgeFinDemo.DeFi.Hundred
