import ProofForgeFin.Rounding
import ProofForgeFin.Shares
import ProofForgeFin.Seq
/-!
# ERC-4626 vaults with virtual shares and assets

OpenZeppelin's `ERC4626` (v4.9 and later) prices every conversion from the books plus a virtual
offset: `assets * (totalSupply + 10 ** decimalsOffset) / (totalAssets + 1)` for shares and
`shares * (totalAssets + 1) / (totalSupply + 10 ** decimalsOffset)` for assets, each rounded in
the vault's favour. This module reads a vault's books as a `Shares.Pool` and an offset (`Offset`:
virtual assets and virtual shares); every conversion is the `Shares` conversion of the virtual
pool `virt o p`, so the `Shares` lemmas apply to it unchanged.

* The four previews and their rounding directions per EIP-4626 (`previewDeposit` and
  `previewRedeem` round down, `previewMint` and `previewWithdraw` round up): exact bounds,
  `previewDeposit_le_previewWithdraw`, `previewRedeem_le_previewMint`, and `convertToShares`,
  `convertToAssets` (rounded down); `previewDeposit_oz` states the OpenZeppelin formula.
* `maxWithdraw` and `maxRedeem` (from the owner's balance): withdrawing `maxWithdraw` burns at most
  the balance (`previewWithdraw_maxWithdraw_le`), and with virtual assets at most 1 and positive
  virtual shares it never exceeds the assets held (`maxWithdraw_le_assets`); minting the shares a
  deposit would give costs at most the deposit (`previewMint_previewDeposit_le`).
* The inflation attack. A deposit of `x` mints at least one share exactly when
  `assets + virtual assets ≤ x * (supply + virtual shares)` (`previewDeposit_pos_iff`); with
  OpenZeppelin's offset `10 ** d`, a donation `D` cannot make a later deposit of `x` mint nothing
  unless `assets + D ≥ x * 10 ** d` (`no_zero_shares`, `donation_needed`), and this holds for every
  offset at least `d` (`no_zero_shares_of_le`); the holders of `S` shares capture at most the
  fraction `S / (S + virtual shares)` of a donation (`donate_redeem_le`).
* A vault model (`step`: deposit, mint, redeem, withdraw, donate) priced from the virtual pool.
  With positive virtual assets and shares the value of a share never falls over any sequence of
  operations (`run_value`): unlike `Shares.run_value`, no condition on the shares outstanding is
  needed, because the virtual pool always has shares.
-/

namespace ProofForgeFin.DeFi.Vault

open ProofForgeFin ProofForgeFin.Shares

/-- Virtual assets and shares added to the books before every conversion. -/
structure Offset where
  /-- Virtual assets (OpenZeppelin: 1). -/
  assets : Nat
  /-- Virtual shares (OpenZeppelin: `10 ** _decimalsOffset()`). -/
  shares : Nat
  deriving DecidableEq, Repr

/-- OpenZeppelin's offset for `_decimalsOffset() = d`. -/
def ozOffset (d : Nat) : Offset := ⟨1, 10 ^ d⟩

/-- No offset: the conversions of `Shares` (and of vaults before OpenZeppelin v4.9). -/
def noOffset : Offset := ⟨0, 0⟩

/-- The virtual pool: the books plus the offset. -/
def virt (o : Offset) (p : Pool) : Pool := ⟨p.assets + o.assets, p.supply + o.shares⟩

/-- Without an offset the virtual pool is the pool. -/
@[simp] theorem virt_noOffset (p : Pool) : virt noOffset p = p := rfl

/-- Assets in and shares issued commute with the offset. -/
theorem virt_add (o : Offset) (p : Pool) (x t : Nat) : virt o (p.add x t) = (virt o p).add x t := by
  simp only [virt, Pool.add]; congr 1 <;> omega

/-- Assets out and shares burned commute with the offset when they are within the books. -/
theorem virt_sub (o : Offset) {p : Pool} {y t : Nat} (hy : y ≤ p.assets) (ht : t ≤ p.supply) :
    virt o (p.sub y t) = (virt o p).sub y t := by
  simp only [virt, Pool.sub]; congr 1 <;> omega

/-! ## Previews -/

section Previews

variable (o : Offset) (p : Pool)

/-- `previewDeposit`: shares for `x` assets, rounded down. -/
def previewDeposit (x : Nat) : Nat := Shares.previewDeposit (virt o p) x

/-- `previewMint`: assets for `t` shares, rounded up. -/
def previewMint (t : Nat) : Nat := Shares.previewMint (virt o p) t

/-- `previewRedeem`: assets for `t` shares, rounded down. -/
def previewRedeem (t : Nat) : Nat := Shares.previewRedeem (virt o p) t

/-- `previewWithdraw`: shares for `x` assets, rounded up. -/
def previewWithdraw (x : Nat) : Nat := Shares.previewWithdraw (virt o p) x

/-- `convertToShares`: rounded down, as `previewDeposit` without fees. -/
def convertToShares (x : Nat) : Nat := previewDeposit o p x

/-- `convertToAssets`: rounded down, as `previewRedeem` without fees. -/
def convertToAssets (t : Nat) : Nat := previewRedeem o p t

/-- `maxWithdraw(owner)`: the assets the owner's balance redeems for, rounded down. -/
def maxWithdraw (bal : Nat) : Nat := previewRedeem o p bal

/-- `maxRedeem(owner)`: the owner's balance. -/
def maxRedeem (bal : Nat) : Nat := bal

/-- OpenZeppelin's `_convertToShares(assets, Floor)`:
`assets * (totalSupply + 10 ** d) / (totalAssets + 1)`. -/
theorem previewDeposit_oz (d x : Nat) :
    previewDeposit (ozOffset d) p x = x * (p.supply + 10 ^ d) / (p.assets + 1) := rfl

/-- OpenZeppelin's `_convertToAssets(shares, Floor)`:
`shares * (totalAssets + 1) / (totalSupply + 10 ** d)`. -/
theorem previewRedeem_oz (d t : Nat) :
    previewRedeem (ozOffset d) p t = t * (p.assets + 1) / (p.supply + 10 ^ d) := rfl

/-- Without an offset the previews are those of `Shares`. -/
theorem previewDeposit_noOffset (x : Nat) : previewDeposit noOffset p x = Shares.previewDeposit p x :=
  rfl

/-- `previewDeposit` is no more than the exact share amount and within one share of it. -/
theorem previewDeposit_spec (x : Nat) (h : 0 < p.assets + o.assets) :
    previewDeposit o p x * (p.assets + o.assets) ≤ x * (p.supply + o.shares) ∧
      x * (p.supply + o.shares) < (previewDeposit o p x + 1) * (p.assets + o.assets) :=
  Shares.previewDeposit_spec (virt o p) x h

/-- `previewMint` is no less than the exact asset amount and within one unit of it. -/
theorem previewMint_spec (t : Nat) (h : 0 < p.supply + o.shares) :
    t * (p.assets + o.assets) ≤ previewMint o p t * (p.supply + o.shares) ∧
      previewMint o p t * (p.supply + o.shares) < t * (p.assets + o.assets) + (p.supply + o.shares) :=
  Shares.previewMint_spec (virt o p) t h

/-- `previewRedeem` is no more than the exact asset amount and within one unit of it. -/
theorem previewRedeem_spec (t : Nat) (h : 0 < p.supply + o.shares) :
    previewRedeem o p t * (p.supply + o.shares) ≤ t * (p.assets + o.assets) ∧
      t * (p.assets + o.assets) < (previewRedeem o p t + 1) * (p.supply + o.shares) :=
  Shares.previewRedeem_spec (virt o p) t h

/-- `previewWithdraw` is no less than the exact share amount and within one share of it. -/
theorem previewWithdraw_spec (x : Nat) (h : 0 < p.assets + o.assets) :
    x * (p.supply + o.shares) ≤ previewWithdraw o p x * (p.assets + o.assets) ∧
      previewWithdraw o p x * (p.assets + o.assets) < x * (p.supply + o.shares) + (p.assets + o.assets) :=
  Shares.previewWithdraw_spec (virt o p) x h

/-- The shares a deposit mints never exceed the shares a withdrawal of the same assets burns. -/
theorem previewDeposit_le_previewWithdraw (x : Nat) : previewDeposit o p x ≤ previewWithdraw o p x :=
  Shares.previewDeposit_le_previewWithdraw _ _

/-- The assets a redemption pays never exceed the assets a mint of the same shares charges. -/
theorem previewRedeem_le_previewMint (t : Nat) : previewRedeem o p t ≤ previewMint o p t :=
  Shares.previewRedeem_le_previewMint _ _

/-- Minting the shares a deposit of `x` would give costs at most `x`. -/
theorem previewMint_previewDeposit_le (x : Nat) (h : 0 < p.supply + o.shares) :
    previewMint o p (previewDeposit o p x) ≤ x := by
  have := Nat.div_mul_le_self (x * (p.supply + o.shares)) (p.assets + o.assets)
  apply (ceilDiv_le_iff h).2
  exact this

/-- Withdrawing `maxWithdraw` burns at most the balance. -/
theorem previewWithdraw_maxWithdraw_le (bal : Nat) (h : 0 < p.assets + o.assets) :
    previewWithdraw o p (maxWithdraw o p bal) ≤ bal := by
  have := Nat.div_mul_le_self (bal * (p.assets + o.assets)) (p.supply + o.shares)
  apply (ceilDiv_le_iff h).2
  exact this

/-- Redeeming `maxRedeem` pays `maxWithdraw`. -/
theorem previewRedeem_maxRedeem (bal : Nat) :
    previewRedeem o p (maxRedeem bal) = maxWithdraw o p bal := rfl

/-- With virtual assets at most 1 and positive virtual shares, a holder of at most the supply can
withdraw at most the assets held: the virtual assets are never paid out. -/
theorem maxWithdraw_le_assets {bal : Nat} (hva : o.assets ≤ 1) (hvs : 0 < o.shares)
    (hb : bal ≤ p.supply) : maxWithdraw o p bal ≤ p.assets := by
  unfold maxWithdraw previewRedeem Shares.previewRedeem virt
  dsimp only
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega)).2
  have h1 : bal * (p.assets + o.assets) ≤ p.supply * (p.assets + o.assets) := Nat.mul_le_mul_right _ hb
  have h2 : p.supply * o.assets ≤ p.supply := by
    have := Nat.mul_le_mul_left p.supply hva; simpa using this
  have e1 : p.supply * (p.assets + o.assets) = p.supply * p.assets + p.supply * o.assets := Nat.mul_add _ _ _
  have e2 : (p.assets + 1) * (p.supply + o.shares) =
      p.supply * p.assets + p.assets * o.shares + p.supply + o.shares := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_comm p.assets p.supply]; omega
  rw [Nat.succ_eq_add_one, e2]
  omega

end Previews

/-! ## The inflation attack -/

/-- A deposit of `x` mints at least one share exactly when the virtual assets are at most `x` times
the virtual supply. -/
theorem previewDeposit_pos_iff (o : Offset) (p : Pool) (x : Nat) (h : 0 < p.assets + o.assets) :
    0 < previewDeposit o p x ↔ p.assets + o.assets ≤ x * (p.supply + o.shares) := by
  unfold previewDeposit Shares.previewDeposit virt
  dsimp only
  rw [Nat.pos_iff_ne_zero, ne_eq, Nat.div_eq_zero_iff_lt h]
  omega

/-- With OpenZeppelin's offset `10 ** d`, a donation `D` cannot make a later deposit of `x` mint
nothing while the assets after the donation stay below `x * 10 ** d`: an attacker must donate at
least `10 ** d` times the victim's deposit (less the assets already held). -/
theorem no_zero_shares (d : Nat) (p : Pool) {D x : Nat} (h : p.assets + D < x * 10 ^ d) :
    0 < previewDeposit (ozOffset d) (p.add D 0) x := by
  apply (previewDeposit_pos_iff _ _ _ (by simp [ozOffset, Pool.add])).2
  simp only [ozOffset, Pool.add, Nat.add_zero]
  have : x * 10 ^ d ≤ x * (p.supply + 10 ^ d) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  omega

/-- The contrapositive: if a deposit of `x` mints nothing after a donation `D`, the vault holds at
least `x * 10 ** d` assets after the donation. -/
theorem donation_needed (d : Nat) (p : Pool) {D x : Nat}
    (h : previewDeposit (ozOffset d) (p.add D 0) x = 0) : x * 10 ^ d ≤ p.assets + D := by
  apply Nat.le_of_not_lt
  intro hlt
  have := no_zero_shares d p hlt
  omega

/-- The protection holds for every offset at least `d`. -/
theorem no_zero_shares_of_le {d e : Nat} (hde : d ≤ e) (p : Pool) {D x : Nat}
    (h : p.assets + D < x * 10 ^ d) : 0 < previewDeposit (ozOffset e) (p.add D 0) x :=
  no_zero_shares e p (Nat.lt_of_lt_of_le h
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hde)))

/-- The holders of `S` shares capture at most the fraction `S / (S + virtual shares)` of a
donation: what their shares redeem for after a donation `D`, scaled by the virtual supply, is at
most `S` times the virtual assets before plus `S` times the donation. The rest of the donation
stays with the virtual shares, so a donation costs the donor `D * shares / (S + shares)` at least. -/
theorem donate_redeem_le (o : Offset) (p : Pool) (D S : Nat) :
    previewRedeem o (p.add D 0) S * (p.supply + o.shares) ≤ S * (p.assets + o.assets) + S * D := by
  have := Nat.div_mul_le_self (S * (p.assets + D + o.assets)) (p.supply + 0 + o.shares)
  unfold previewRedeem Shares.previewRedeem virt Pool.add
  dsimp only
  rw [Nat.add_zero] at this ⊢
  have e : S * (p.assets + D + o.assets) = S * (p.assets + o.assets) + S * D := by
    rw [← Nat.mul_add]; congr 1; omega
  omega

/-! ## A vault and its operations -/

/-- Operations on a vault. -/
inductive Op where
  /-- Deposit `x` assets for `previewDeposit` shares. -/
  | deposit (x : Nat)
  /-- Mint `t` shares for `previewMint` assets. -/
  | mint (t : Nat)
  /-- Redeem `t` shares for `previewRedeem` assets; refused beyond the books. -/
  | redeem (t : Nat)
  /-- Withdraw `x` assets for `previewWithdraw` shares; refused beyond the books. -/
  | withdraw (x : Nat)
  /-- Send `x` assets to the vault without calling it. -/
  | donate (x : Nat)
  deriving DecidableEq, Repr

/-- One operation priced from the virtual pool; a refused operation changes nothing. -/
def step (o : Offset) (p : Pool) : Op → Pool
  | .deposit x => p.add x (previewDeposit o p x)
  | .mint t => p.add (previewMint o p t) t
  | .redeem t =>
    if t ≤ p.supply ∧ previewRedeem o p t ≤ p.assets then p.sub (previewRedeem o p t) t else p
  | .withdraw x =>
    if x ≤ p.assets ∧ previewWithdraw o p x ≤ p.supply then p.sub x (previewWithdraw o p x) else p
  | .donate x => p.add x 0

/-- With positive virtual assets and shares, no operation lowers the value of a share, read from
the virtual pool. -/
theorem step_value {o : Offset} (hva : 0 < o.assets) (hvs : 0 < o.shares) (p : Pool) (op : Op) :
    ValueNotBelow (virt o p) (virt o (step o p op)) := by
  cases op with
  | deposit x => simp only [step]; rw [virt_add]; exact deposit_value _ x
  | mint t =>
    simp only [step]; rw [virt_add]
    exact mint_value _ t (by simp only [virt]; omega)
  | redeem t =>
    simp only [step]; split
    · rename_i h; rw [virt_sub o h.2 h.1]; exact redeem_value _ t
    · exact valueNotBelow_refl _
  | withdraw x =>
    simp only [step]; split
    · rename_i h; rw [virt_sub o h.1 h.2]
      exact withdraw_value _ x (by simp only [virt]; omega)
    · exact valueNotBelow_refl _
  | donate x => simp only [step]; rw [virt_add]; exact donate_value _ x

/-- With positive virtual assets and shares, the value of a share never falls over any sequence of
operations, with no condition on the shares outstanding. -/
theorem run_value {o : Offset} (hva : 0 < o.assets) (hvs : 0 < o.shares) (p : Pool) (ops : List Op) :
    ValueNotBelow (virt o p) (virt o (Seq.run (step o) p ops)) := by
  induction ops generalizing p with
  | nil => exact valueNotBelow_refl _
  | cons op ops ih =>
    exact valueNotBelow_trans (step_value hva hvs p op) (ih _)
      (by simp only [virt]; omega)

/-- OpenZeppelin's offset satisfies the conditions of `run_value` for every `d`. -/
theorem run_value_oz (d : Nat) (p : Pool) (ops : List Op) :
    ValueNotBelow (virt (ozOffset d) p) (virt (ozOffset d) (Seq.run (step (ozOffset d)) p ops)) :=
  run_value Nat.one_pos (Nat.pow_pos (by decide : 0 < 10)) p ops

/-- The vault never pays out more than it holds: redeeming at most the supply never pays beyond
the assets with OpenZeppelin's offset. -/
theorem previewRedeem_le_assets_oz (d : Nat) (p : Pool) {t : Nat} (ht : t ≤ p.supply) :
    previewRedeem (ozOffset d) p t ≤ p.assets :=
  maxWithdraw_le_assets (ozOffset d) p (Nat.le_refl _) (Nat.pow_pos (by decide : 0 < 10)) ht

end ProofForgeFin.DeFi.Vault
