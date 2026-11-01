import ProofForgeFin.Accumulator.Index
import ProofForgeFin.Ledger
/-!
# Potentials of index-based reward accumulators

The bound "rewards credited never exceed what was owed at the start plus what was emitted since"
is proved with a potential: for every account, the rewards credited to it (accrued and not yet
paid, plus paid) at the index scale `one`, plus what it is owed (`units * (index - start)` on each
side it holds), summed over the accounts, plus `one` times the emission not yet in any index. No
interaction raises the potential; time passing raises it by exactly `one` times the emission.

This module proves those steps once, for any account type and any term an account contributes.
A term is a function `t i a` of the index `i` and the account `a`; the only facts used about it
are local ones a proof establishes by unfolding its own definition:

* the index step: `t i' a ≤ t i a + units a * (i' - i)` (an account is owed at most its units
  times the increase; `owed_le_add` proves it for a start that moves up with the index);
* the settlement: crediting an account its owed amount rounded down and moving its checkpoint
  to the index does not raise its term (`settle_scaled_le`).

From these:

* `pot_accrue_le`: an update covered by the emission it indexes does not raise
  `Σ t + one * unindexed`, and `pot_accrue_settle_le`: nor does an update followed by the
  settlement of one account (the shape of every interaction); `accrue_budget` and
  `accrue_budget'` give its budget hypothesis from a `Covered` update of one of two sides;
* `acct_accrue_le`: the same for the potential of one account, which counts the unindexed
  emission of a side only while the account holds units there (`unindexed_ite_eq`: an account
  settled right after an update can change its units without changing it), and
  `getD_modify_le`: a change of one account that does not raise its potential raises no
  account's;
* `sum_scaled_add`, `sum_scaled_le`, `sum_mul_le_sum_scaled`: the potential split into the
  credited amount at scale `one` and the owed amounts, for the bound at the start of a run and
  the passage from the potential to the credited amount at its end;
* `sum_owed_index_eq`: exactly, the owed amounts at a later index are those at the earlier index
  plus the total units times the increase, when no account starts after the earlier index
  (accrued equals balance times index difference).
-/

namespace ProofForgeFin.Accumulator

universe u

variable {α : Type u}

/-! ## One account -/

/-- Raising the index from `i` to `i'` and the start from `s` to `s' ≥ s` raises an owed amount
`u * (i - s)` by at most `u * (i' - i)`. With `s' = s` this is a fixed checkpoint; with a start
that moves up with the index (`firstStart_mono`) it covers accounts with no checkpoint. -/
theorem owed_le_add {u i i' s s' : Nat} (hs : s ≤ s') :
    u * (i' - s') ≤ u * (i - s) + u * (i' - i) := by
  rw [← Nat.mul_add]
  exact Nat.mul_le_mul_left _ (by omega)

/-- Exactly: from a start at or below `i`, the owed amount at `i' ≥ i` is the owed amount at `i`
plus the units times the increase. -/
theorem owed_add_eq {u i i' s : Nat} (hs : s ≤ i) (hi : i ≤ i') :
    u * (i' - s) = u * (i - s) + u * (i' - i) := by
  rw [← Nat.mul_add]
  congr 1
  omega

/-- Settling an account at index `i`: it is credited `u * (i - q) / one` (its owed amount from
the start `q`, rounded down) on top of `c`, and restarts at `q' ≥ i`, where it owes nothing.
Its scaled credited amount plus what it is owed does not grow. -/
theorem settle_scaled_le {one c u i q q' : Nat} (hq' : i ≤ q') :
    (c + u * (i - q) / one) * one + u * (i - q') ≤ c * one + u * (i - q) := by
  have h1 : u * (i - q) / one * one ≤ u * (i - q) := Nat.div_mul_le_self _ _
  have h2 : i - q' = 0 := by omega
  rw [h2, Nat.mul_zero, Nat.add_zero, Nat.add_mul]
  omega

/-- Settling from the protocol's start `q`, at or after the start `p` the potential counts the
account from: the scaled credited amount plus what is owed does not grow. An account credited
from before `p` would be paid rewards the potential never counted. -/
theorem settle_scaled_le_of_le {one c u i p q q' : Nat} (hpq : p ≤ q) (hq' : i ≤ q') :
    (c + u * (i - q) / one) * one + u * (i - q') ≤ c * one + u * (i - p) := by
  have := settle_scaled_le (one := one) (c := c) (u := u) (q := q) hq'
  have h2 : u * (i - q) ≤ u * (i - p) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Settling exactly: when `one` divides the owed amount, crediting it keeps the scaled credited
amount plus the owed amount unchanged. -/
theorem settle_scaled_eq {one c u i q q' : Nat} (hq' : i ≤ q') (hd : one ∣ u * (i - q)) :
    (c + u * (i - q) / one) * one + u * (i - q') = c * one + u * (i - q) := by
  have h2 : i - q' = 0 := by omega
  rw [h2, Nat.mul_zero, Nat.add_zero, Nat.add_mul, Nat.div_mul_cancel hd]

/-! ## Sums over the accounts -/

/-- An index increase over the accounts of a list raises the total of the terms by at most the
total units times the increase, when it raises each term by at most its units times it. -/
theorem sum_index_le (l : List α) (t : Nat → α → Nat) (units : α → Nat) {i i' : Nat}
    (ht : ∀ a ∈ l, t i' a ≤ t i a + units a * (i' - i)) :
    (l.map (t i')).sum ≤ (l.map (t i)).sum + (l.map units).sum * (i' - i) := by
  have h := Ledger.sum_map_le_add l (t i) (t i') (fun a => units a * (i' - i)) ht
  rw [Ledger.sum_map_mul_right] at h
  exact h

/-- The owed amounts over the accounts of a list at a later index are those at the earlier index
plus the total units times the increase, when no account starts after the earlier index. -/
theorem sum_owed_index_eq (l : List α) (units start : α → Nat) {i i' : Nat}
    (hs : ∀ a ∈ l, start a ≤ i) (hi : i ≤ i') :
    (l.map fun a => units a * (i' - start a)).sum =
      (l.map fun a => units a * (i - start a)).sum + (l.map units).sum * (i' - i) := by
  rw [← Ledger.sum_map_mul_right, ← ProofForgeFin.DeFi.Rewards.sum_map_add]
  exact Ledger.sum_map_congr l (fun a ha => owed_add_eq (hs a ha) hi)

/-- An update of an index does not raise the potential `Σ t + one * U`: each term grows by at
most its units times the increase, and the total units times the increase plus what is left
unindexed (`U'`, at scale `one`) is at most what was unindexed before (`U`). -/
theorem pot_accrue_le (l : List α) (t : Nat → α → Nat) (units : α → Nat) {one i i' U U' : Nat}
    (ht : ∀ a ∈ l, t i' a ≤ t i a + units a * (i' - i))
    (hU : (l.map units).sum * (i' - i) + one * U' ≤ one * U) :
    (l.map (t i')).sum + one * U' ≤ (l.map (t i)).sum + one * U := by
  have := sum_index_le l t units ht
  omega

/-- An update of an index followed by a change of the account at position `w` that does not
raise its term at the new index (a settlement) does not raise the potential. This is the shape
of every interaction of an index-based reward accumulator. -/
theorem pot_accrue_settle_le (l : List α) (w : Nat) (f : α → α) (d : α) (t : Nat → α → Nat)
    (units : α → Nat) {one i i' U U' : Nat}
    (ht : ∀ a ∈ l, t i' a ≤ t i a + units a * (i' - i))
    (hU : (l.map units).sum * (i' - i) + one * U' ≤ one * U)
    (hf : w < l.length → t i' (f (l.getD w d)) ≤ t i' (l.getD w d)) :
    ((l.modify w f).map (t i')).sum + one * U' ≤ (l.map (t i)).sum + one * U := by
  have h1 := Ledger.sum_map_modify_le l w f (t i') d hf
  have h2 := pot_accrue_le l t units ht hU
  omega

/-- An update covered by the emission it indexes: the hypothesis `hU` of `pot_accrue_le` from a
`Covered` movement, when the unindexed emission of the updated side drops from `E` to 0 and
the other sides' unindexed emission `V` is unchanged. -/
theorem accrue_budget {one T i i' E V : Nat} (h : Covered T (one * E) i i') :
    T * (i' - i) + one * (0 + V) ≤ one * (E + V) := by
  have := h.2
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_zero]
  omega

/-- `accrue_budget` with the updated side second. -/
theorem accrue_budget' {one T i i' E V : Nat} (h : Covered T (one * E) i i') :
    T * (i' - i) + one * (V + 0) ≤ one * (V + E) := by
  have := accrue_budget (V := V) h
  rw [Nat.add_comm V 0, Nat.add_comm V E]
  exact this

/-! ## The potential of one account -/

/-- The potential of one account across an update of one side: its term grows from `x` to at
most `x + u * d` (its units `u` times the increase `d`), and it is owed the unindexed emission of
that side only while it holds units. When the total units times the increase plus what is left
unindexed (`U'`) is covered by what was unindexed (`U`), its potential does not grow. -/
theorem acct_accrue_le {one u T d U U' x x' : Nat} (hx : x' ≤ x + u * d) (hu : u ≤ T)
    (hU : T * d + one * U' ≤ one * U) :
    x' + one * (if 0 < u then U' else 0) ≤ x + one * (if 0 < u then U else 0) := by
  have h1 : u * d ≤ T * d := Nat.mul_le_mul_right _ hu
  split
  · omega
  · have : u = 0 := by omega
    subst this
    simp only [Nat.zero_mul, Nat.add_zero] at hx
    omega

/-- The potential of one account read after a change of the account at position `w`: when the
change does not raise the value `g` of the changed account, no account's value is raised (the
others are unchanged). -/
theorem getD_modify_le (l : List α) (w v : Nat) (f : α → α) (d : α) (g : α → Nat)
    (h : w < l.length → g (f (l.getD w d)) ≤ g (l.getD w d)) :
    g ((l.modify w f).getD v d) ≤ g (l.getD v d) := by
  rw [Ledger.getD_modify]
  split
  · rename_i hv
    obtain ⟨rfl, hw⟩ := hv
    exact h hw
  · exact Nat.le_refl _

/-- An account with nothing unindexed on a side (right after an update) can change its units
there without changing the unindexed emission its potential counts. -/
theorem unindexed_ite_eq {U : Nat} (u u' : Nat) (h : U = 0) :
    (if 0 < u' then U else 0) = (if 0 < u then U else 0) := by
  subst h; simp

/-! ## Credited amounts and owed amounts -/

/-- A potential split into the credited amounts at scale `one` and the owed amounts. -/
theorem sum_scaled_add (l : List α) (c p : α → Nat) (one : Nat) :
    (l.map fun a => c a * one + p a).sum = (l.map c).sum * one + (l.map p).sum := by
  rw [ProofForgeFin.DeFi.Rewards.sum_map_add, Ledger.sum_map_mul_right]

/-- The potential at the start of a run is at most the credited amount at scale `one` plus a
bound on every account's owed amount. -/
theorem sum_scaled_le (l : List α) (c p q : α → Nat) (one : Nat) (h : ∀ a ∈ l, p a ≤ q a) :
    (l.map fun a => c a * one + p a).sum ≤ (l.map c).sum * one + (l.map q).sum := by
  rw [sum_scaled_add]
  have := Ledger.sum_map_le_sum_map l h
  omega

/-- The credited amount at scale `one` is at most the potential. -/
theorem sum_mul_le_sum_scaled (l : List α) (c p : α → Nat) (one : Nat) :
    (l.map c).sum * one ≤ (l.map fun a => c a * one + p a).sum := by
  rw [sum_scaled_add]
  exact Nat.le_add_right _ _

end ProofForgeFin.Accumulator
