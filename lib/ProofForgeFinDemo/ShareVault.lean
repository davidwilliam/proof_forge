import ProofForgeFin
/-!
# Demonstration: REQ-SHARE-VALUE of `rw-hundred-vault` with the library

The definitions below are copied without change from `realworld/tasks/rw-hundred-vault`:
the state, calls, operations, `exec`, `run`, `trace`, `ValueNotBelow` and the requirement
`ShareValueNeverFalls` from `spec/ShareVault/Spec.lean`, and the implementation `vault` with its
helpers and its three shape lemmas from `reference/SolutionA.lean`. The task files are not
imported or modified.

The reference solution proves the requirement with its own floor and ceiling bounds, a
transitivity lemma for cross-multiplied values, a 40-line case analysis (`exec_value`) and an
induction over the trace (`run_value`). Here the case analysis reduces each successful call to a
library lemma (`Shares.deposit_value`, `Shares.redeem_value`, `Shares.withdraw_value`,
`Shares.donate_value`), and the induction is `Seq.run_rel_of_trace` with
`Shares.valueNotBelow_trans`. The only task-specific facts are that the task's `run` and `trace`
are the library's and that the task's state maps onto `Shares.Pool`.
-/

namespace ProofForgeFinDemo.ShareVault

open ProofForgeFin

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

/-! ## Copied from `reference/SolutionA.lean` -/

/-- `s` after `who` paid in `x` and received `t` new shares. -/
def mintTo (s : Vault) (who : Actor) (x t : Nat) : Vault :=
  { assets := s.assets + x, supply := s.supply + t,
    balance := fun b => if b = who then s.balance b + t else s.balance b }

/-- `s` after `who` gave back `t` shares and received `y`. -/
def burnFrom (s : Vault) (who : Actor) (t y : Nat) : Vault :=
  { assets := s.assets - y, supply := s.supply - t,
    balance := fun b => if b = who then s.balance b - t else s.balance b }

/-- Shares burned for a withdrawal of `x`: `x * supply / assets` rounded up. -/
def sharesUp (s : Vault) (x : Nat) : Nat :=
  (x * s.supply + s.assets - 1) / s.assets

def vault : Impl := fun s c =>
  match c with
  | .deposit who x =>
    if s.supply = 0 then some (mintTo s who x (initialSharesPerUnit * x))
    else if s.assets = 0 then none
    else some (mintTo s who x (x * s.supply / s.assets))
  | .redeem who t =>
    if t ≤ s.balance who ∧ t ≤ s.supply then
      some (burnFrom s who t (t * s.assets / s.supply))
    else none
  | .withdraw who x =>
    if 0 < s.supply ∧ 0 < s.assets ∧ sharesUp s x ≤ s.balance who ∧ sharesUp s x ≤ s.supply ∧
        x ≤ s.assets then
      some (burnFrom s who (sharesUp s x) x)
    else none

theorem deposit_some {s s' : Vault} {who x : Nat} (h : vault s (.deposit who x) = some s') :
    (s.supply = 0 ∧ s' = mintTo s who x (initialSharesPerUnit * x)) ∨
    (0 < s.supply ∧ 0 < s.assets ∧ s' = mintTo s who x (x * s.supply / s.assets)) := by
  simp only [vault] at h
  split at h
  · exact Or.inl ⟨by assumption, (Option.some.inj h).symm⟩
  · split at h
    · contradiction
    · exact Or.inr ⟨by omega, by omega, (Option.some.inj h).symm⟩

theorem redeem_some {s s' : Vault} {who t : Nat} (h : vault s (.redeem who t) = some s') :
    t ≤ s.balance who ∧ t ≤ s.supply ∧ s' = burnFrom s who t (t * s.assets / s.supply) := by
  simp only [vault] at h
  split at h
  · exact ⟨by omega, by omega, (Option.some.inj h).symm⟩
  · contradiction

theorem withdraw_some {s s' : Vault} {who x : Nat} (h : vault s (.withdraw who x) = some s') :
    0 < s.supply ∧ 0 < s.assets ∧ sharesUp s x ≤ s.balance who ∧ sharesUp s x ≤ s.supply ∧
      x ≤ s.assets ∧ s' = burnFrom s who (sharesUp s x) x := by
  simp only [vault] at h
  split at h
  · rename_i hc
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, (Option.some.inj h).symm⟩
  · contradiction

/-! ## Re-proved with the library -/

/-- The books of a vault state, as the library sees them. -/
def books (s : Vault) : Shares.Pool := ⟨s.assets, s.supply⟩

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

/-- The task's share value comparison is the library's on the books. -/
theorem value_iff (s s' : Vault) : ValueNotBelow s s' ↔ Shares.ValueNotBelow (books s) (books s') :=
  Iff.rfl

/-- Share value comparison is reflexive. -/
theorem value_refl (s : Vault) : ValueNotBelow s s := Shares.valueNotBelow_refl (books s)

/-- Share value comparisons chain through a state with outstanding shares. -/
theorem value_trans {s t u : Vault} (h1 : ValueNotBelow s t) (h2 : ValueNotBelow t u)
    (ht : 0 < t.supply) : ValueNotBelow s u :=
  Shares.valueNotBelow_trans (p := books s) (q := books t) (r := books u) h1 h2 ht

/-- Each operation keeps share value while shares are outstanding: every successful call is a
library conversion rounded in the vault's favour, and a donation is a library donation. -/
theorem exec_value (s : Vault) (op : Op) (hs : 0 < s.supply) : ValueNotBelow s (exec vault s op) := by
  cases op with
  | donate x => exact Shares.donate_value (books s) x
  | call c =>
    simp only [exec]
    cases h : vault s c with
    | none => exact value_refl s
    | some s' =>
      cases c with
      | deposit who x =>
        rcases deposit_some h with ⟨h0, _⟩ | ⟨_, _, rfl⟩
        · omega
        · exact Shares.deposit_value (books s) x
      | redeem who t =>
        obtain ⟨_, _, rfl⟩ := redeem_some h
        exact Shares.redeem_value (books s) t
      | withdraw who x =>
        obtain ⟨_, ha, _, _, _, rfl⟩ := withdraw_some h
        exact Shares.withdraw_value (books s) x ha

/-- REQ-SHARE-VALUE for the reference implementation. -/
theorem req_share_value : ShareValueNeverFalls vault := by
  intro history ops h
  rw [trace_eq] at h
  rw [run_eq vault (run vault empty history) ops]
  exact Seq.run_rel_of_trace (R := ValueNotBelow) (C := fun v => 0 < v.supply) value_refl
    (fun _ _ _ h1 h2 hq => value_trans h1 h2 hq) exec_value _ ops h

end ProofForgeFinDemo.ShareVault
