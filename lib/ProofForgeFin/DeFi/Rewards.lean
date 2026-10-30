import ProofForgeFin.Rounding
import ProofForgeFin.FixedPoint
import ProofForgeFin.Seq
import ProofForgeFin.Ledger
/-!
# Index-based reward accrual

The reward pattern of Compound's Comptroller (`compSupplyState`, `compSupplierIndex`),
SushiSwap's MasterChef (`accSushiPerShare`, `rewardDebt`) and Synthetix's `StakingRewards`
(`rewardPerTokenStored`, `userRewardPerTokenPaid`): a global index, at a fixed-point scale `one`,
grows by the rewards emitted per unit of stake; each account records the index at its last
interaction (its checkpoint) and, when it interacts again, is credited its units times the index
gained since, rounded down.

The safety statement is a bound: rewards credited (accrued and not yet paid, plus paid) never
exceed what was owed at the start plus what was emitted since, in total and per account. The
proof goes through a potential, the scaled rewards credited plus every account's pending rewards
plus the scaled emission not yet in the index, which no settlement raises and which an emission
raises by exactly `one` times the amount. This module proves the arithmetic of each step once:

* `pending units start index = units * (index - start)` (scaled rewards owed) and
  `credit one units start index = pending / one` (rewards credited, rounded down);
* `indexDelta one emission total = emission * one / total`, the increment of the index, with
  `total * indexDelta ≤ emission * one` (the index never distributes more than was emitted);
* `settle_le`: crediting an account from any start at or after the start the potential counts
  from, and moving its checkpoint to the index, never raises `credited * one + pending`;
* `effStart` and `firstStart`: the start of an account with no recorded checkpoint, for an
  index that began at a value `init` (Compound's `compInitialIndex`), and `effStart_le_firstStart`,
  the condition the Proposal 62 code broke (`p62Start`, `p62_overcredit`);
* sums over the accounts of a list: an index increase raises the total pending by at most the
  total units times the increase (`sum_le_of_index_le`), and accruing then settling one account
  (`sum_modify_index_le`), the shape of every interaction;
* the `rewardDebt` accounting of MasterChef (`debtOf`, `harvest`), whose settlements are exact
  for the potential and whose stake changes each add less than one unit of rounding.

Every lemma is stated for any scale `one`; most need no positivity.
-/

namespace ProofForgeFin.DeFi.Rewards

open ProofForgeFin

universe u

/-! ## Rewards owed between two index values -/

/-- Rewards owed on `units` of stake from index `start` to index `index`, at the index scale:
`units * (index - start)`. A start at or above the index owes nothing. -/
def pending (units start index : Nat) : Nat := units * (index - start)

/-- Rewards credited for `units` from index `start` to index `index`, rounded down at scale
`one`: Compound's `mul_(units, Double(index - start))`, Synthetix's
`balance * (rewardPerToken - userRewardPerTokenPaid) / 1e18`. -/
def credit (one units start index : Nat) : Nat := units * (index - start) / one

/-- The credit is the pending amount rounded down. -/
theorem credit_eq_div (one units start index : Nat) :
    credit one units start index = pending units start index / one := rfl

/-- The credit, at scale `one`, never exceeds the pending amount. -/
theorem credit_mul_le (one units start index : Nat) :
    credit one units start index * one ≤ pending units start index :=
  Nat.div_mul_le_self _ _

/-- The credit loses less than one unit to rounding. -/
theorem pending_lt_credit_add_one_mul {one : Nat} (units start index : Nat) (h : 0 < one) :
    pending units start index < (credit one units start index + 1) * one :=
  lt_div_add_one_mul _ _ h

/-- Nothing is pending from the index itself. -/
@[simp] theorem pending_self (units index : Nat) : pending units index index = 0 := by
  simp [pending]

/-- Nothing is pending from a start at or above the index. -/
theorem pending_of_le {units start index : Nat} (h : index ≤ start) :
    pending units start index = 0 := by
  simp [pending, Nat.sub_eq_zero_of_le h]

/-- No units, nothing pending. -/
@[simp] theorem pending_zero_units (start index : Nat) : pending 0 start index = 0 := by
  simp [pending]

/-- No units, no credit. -/
@[simp] theorem credit_zero_units (one start index : Nat) : credit one 0 start index = 0 := by
  simp [credit]

/-- Nothing is credited from the index itself. -/
@[simp] theorem credit_self (one units index : Nat) : credit one units index index = 0 := by
  simp [credit]

/-- A later start owes less. -/
theorem pending_anti_start (units : Nat) {start start' : Nat} (index : Nat) (h : start ≤ start') :
    pending units start' index ≤ pending units start index :=
  Nat.mul_le_mul_left _ (by omega)

/-- A higher index owes more. -/
theorem pending_mono_index (units start : Nat) {index index' : Nat} (h : index ≤ index') :
    pending units start index ≤ pending units start index' :=
  Nat.mul_le_mul_left _ (by omega)

/-- More units owe more. -/
theorem pending_mono_units {units units' : Nat} (start index : Nat) (h : units ≤ units') :
    pending units start index ≤ pending units' start index :=
  Nat.mul_le_mul_right _ h

/-- An index increase from `index` to `index'` raises the pending amount by at most the units
times the increase. -/
theorem pending_le_add (units start : Nat) {index index' : Nat} (h : index ≤ index') :
    pending units start index' ≤ pending units start index + units * (index' - index) := by
  unfold pending
  rw [← Nat.mul_add]
  exact Nat.mul_le_mul_left _ (by omega)

/-- From a start at or below the index, an increase raises the pending amount by exactly the
units times the increase. -/
theorem pending_add_eq (units : Nat) {start index index' : Nat} (hs : start ≤ index)
    (h : index ≤ index') :
    pending units start index' = pending units start index + units * (index' - index) := by
  unfold pending
  rw [← Nat.mul_add]
  congr 1
  omega

/-- Pending amounts add up along the index. -/
theorem pending_trans (units : Nat) {start mid index : Nat} (h1 : start ≤ mid) (h2 : mid ≤ index) :
    pending units start index = pending units start mid + pending units mid index := by
  unfold pending
  rw [← Nat.mul_add]
  congr 1
  omega

/-- A later start is credited less. -/
theorem credit_anti_start (one units : Nat) {start start' : Nat} (index : Nat) (h : start ≤ start') :
    credit one units start' index ≤ credit one units start index :=
  Nat.div_le_div_right (pending_anti_start units index h)

/-- A higher index is credited more. -/
theorem credit_mono_index (one units start : Nat) {index index' : Nat} (h : index ≤ index') :
    credit one units start index ≤ credit one units start index' :=
  Nat.div_le_div_right (pending_mono_index units start h)

/-- The credit is `mulDiv units (index - start) one`. -/
theorem credit_eq_mulDiv (one units start index : Nat) :
    credit one units start index = mulDiv units (index - start) one := rfl

/-! ## Settling an account -/

/-- Settling an account. The potential counts the account as owed from `p`; the protocol credits
it from `q` and moves its checkpoint to `p'`. When the protocol's start is at or after the
potential's (`p ≤ q`) and the new checkpoint is at or above the index (`index ≤ p'`), the
credited amount `r` (scaled by `one`) plus the pending amount does not grow. This is the step
Compound's `distributeSupplierComp`, Synthetix's `updateReward` and MasterChef's harvest perform,
and the condition `p ≤ q` is what Compound Proposal 62 broke. -/
theorem settle_le {one units p q p' index r r' : Nat} (hr : r' = r + credit one units q index)
    (hpq : p ≤ q) (hp' : index ≤ p') :
    r' * one + pending units p' index ≤ r * one + pending units p index := by
  have h1 := credit_mul_le one units q index
  have h2 := pending_anti_start units index hpq
  rw [pending_of_le hp', hr, Nat.add_mul]
  omega

/-- `settle_le` with the checkpoint moved to the index. -/
theorem settle_le_self {one units p q index r r' : Nat} (hr : r' = r + credit one units q index)
    (hpq : p ≤ q) : r' * one ≤ r * one + pending units p index := by
  have := settle_le (p' := index) hr hpq (Nat.le_refl _)
  simpa using this

/-- While an account is settled at the index (its checkpoint at or above it), its units can
change without changing what it is owed: nothing is pending either way. -/
theorem pending_units_change {start index : Nat} (units units' : Nat) (h : index ≤ start) :
    pending units' start index = pending units start index := by
  rw [pending_of_le h, pending_of_le h]

/-! ## Accounts without a recorded checkpoint -/

/-- The index from which an account is owed when its recorded checkpoint is `recorded` and 0
means that none is recorded: the recorded checkpoint, or for an account with none, the value
`init` the index started from (an account that held a position before rewards started is owed
from the start of rewards, not from 0). -/
def effStart (init recorded : Nat) : Nat := if recorded = 0 then init else recorded

/-- The start Compound uses after Proposal 64 (`supplierIndex == 0 && supplyIndex >=
compInitialIndex`): the recorded checkpoint; for an account with none, `init` once the index has
reached it, and 0 for an index still below it (an index that grew from 0). -/
def firstStart (init recorded index : Nat) : Nat :=
  if recorded = 0 then (if init ≤ index then init else 0) else recorded

/-- The start of the Proposal 62 code (`supplierIndex == 0 && supplyIndex > compInitialIndex`):
it differs from `firstStart` only for an index exactly at `init`. -/
def p62Start (init recorded index : Nat) : Nat :=
  if recorded = 0 ∧ init < index then init else recorded

/-- An account settled at the index owes nothing at that index, whatever the index started from:
recording the index (even an index of 0, which reads as "none recorded") settles the account. -/
@[simp] theorem pending_effStart_self (init units index : Nat) :
    pending units (effStart init index) index = 0 := by
  apply pending_of_le
  unfold effStart
  split <;> omega

/-- A recorded index is never above its effective start. -/
theorem le_effStart_self (init index : Nat) : index ≤ effStart init index := by
  unfold effStart
  split <;> omega

/-- `effStart` of a recorded checkpoint is that checkpoint. -/
theorem effStart_of_ne_zero {init recorded : Nat} (h : recorded ≠ 0) :
    effStart init recorded = recorded := by
  simp [effStart, h]

/-- `effStart` of no recorded checkpoint is the start of the index. -/
@[simp] theorem effStart_zero (init : Nat) : effStart init 0 = init := rfl

/-- The Proposal 64 start is safe: for an index that started from 0 or from `init` and has not
fallen below its start, `firstStart` is at or after the start the potential counts from. -/
theorem effStart_le_firstStart {g init index : Nat} (recorded : Nat) (hg : g = 0 ∨ g = init)
    (hgi : g ≤ index) : effStart g recorded ≤ firstStart init recorded index := by
  unfold effStart firstStart
  split
  · split <;> omega
  · exact Nat.le_refl _

/-- `firstStart` never lies above the index when the recorded checkpoint does not. -/
theorem firstStart_le_index (init : Nat) {recorded index : Nat} (h : recorded ≤ index) :
    firstStart init recorded index ≤ index := by
  unfold firstStart
  split
  · split <;> omega
  · exact h

/-- The Proposal 62 start agrees with the safe one except for an index exactly at `init`. -/
theorem p62Start_eq_firstStart {init recorded index : Nat} (h : index ≠ init ∨ recorded ≠ 0) :
    p62Start init recorded index = firstStart init recorded index := by
  unfold p62Start firstStart
  by_cases hr : recorded = 0
  · subst hr
    have : index ≠ init := by omega
    by_cases hi : init < index
    · simp [hi, Nat.le_of_lt hi]
    · have : ¬ init ≤ index := by omega
      simp [hi, this]
  · simp [hr]

/-- The Proposal 62 overcredit: an account with `units` and no recorded checkpoint, in a market
whose index the upgrade set to exactly `init = one` (`compInitialIndex = doubleScale = 1e36`), is
credited from 0, which is `units` (one reward unit per unit held) although nothing was emitted;
the safe start credits 0. -/
theorem p62_overcredit {one : Nat} (units : Nat) (h : 0 < one) :
    credit one units (p62Start one 0 one) one = units ∧
    credit one units (firstStart one 0 one) one = 0 := by
  unfold p62Start firstStart credit
  simp [Nat.mul_div_cancel _ h]

/-! ## Index increments -/

/-- The increment of the index for `emission` rewards over `total` units at scale `one`, rounded
down: Compound's `fraction(compAccrued, supplyTokens)`, Synthetix's
`(lastTimeRewardApplicable() - lastUpdateTime) * rewardRate * 1e18 / _totalSupply` (with
`emission = elapsed * rate`), MasterChef's `sushiReward * 1e12 / lpSupply`. Zero over zero units. -/
def indexDelta (one emission total : Nat) : Nat := emission * one / total

/-- The index never distributes more than was emitted: the total units times the increment is
at most the emission, at scale `one`. -/
theorem total_mul_indexDelta_le (one emission total : Nat) :
    total * indexDelta one emission total ≤ emission * one := by
  unfold indexDelta
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self _ _

/-- The increment loses less than one index unit per unit of stake: the emission, at scale `one`,
is below the total units times the increment plus one. -/
theorem lt_total_mul_indexDelta_add_one (one emission : Nat) {total : Nat} (h : 0 < total) :
    emission * one < total * (indexDelta one emission total + 1) := by
  have := lt_div_add_one_mul (emission * one) total h
  unfold indexDelta
  rwa [Nat.mul_comm (emission * one / total + 1) total] at this

/-- Over zero units the index does not move. -/
@[simp] theorem indexDelta_zero_total (one emission : Nat) : indexDelta one emission 0 = 0 := by
  simp [indexDelta]

/-- No emission, no increment. -/
@[simp] theorem indexDelta_zero_emission (one total : Nat) : indexDelta one 0 total = 0 := by
  simp [indexDelta]

/-- The increment is monotone in the emission. -/
theorem indexDelta_mono {one emission emission' : Nat} (total : Nat) (h : emission ≤ emission') :
    indexDelta one emission total ≤ indexDelta one emission' total :=
  Nat.div_le_div_right (Nat.mul_le_mul_right _ h)

/-- One account's share of an index increment is covered by the emission. -/
theorem units_mul_le_of_le_total {units total d E : Nat} (hu : units ≤ total) (h : total * d ≤ E) :
    units * d ≤ E :=
  Nat.le_trans (Nat.mul_le_mul_right _ hu) h

/-- One account's share of an index increment is covered by the emission while it holds units,
and is zero otherwise. This is the form a per-account potential uses: an account is owed the
emission not yet in the index only while it holds a position. -/
theorem units_mul_le_ite {units total d E : Nat} (hu : units ≤ total) (h : total * d ≤ E) :
    units * d ≤ if 0 < units then E else 0 := by
  split
  · exact units_mul_le_of_le_total hu h
  · have : units = 0 := by omega
    simp [this]

/-- Rewards emitted at `rate` per block (or per second) over the time from `last` to `now + k`
are those up to `now` plus `k * rate`, when `last ≤ now`: the emission not yet in an index grows
linearly while time passes (Compound's `deltaBlocks * speed`, Synthetix's
`(lastTimeRewardApplicable() - lastUpdateTime) * rewardRate`). -/
theorem elapsed_add_mul {last now : Nat} (k rate : Nat) (h : last ≤ now) :
    (now + k - last) * rate = (now - last) * rate + k * rate := by
  rw [Nat.sub_add_comm h, Nat.add_mul]

/-- The per-account form of an accrual. An account holds `units ≤ total`; the index grows by `d`
with `total * d` covered by the emission `un` net of what is left unindexed (`un'`), at scale `c`;
afterwards the account holds `units'`, equal to `units` or with nothing left unindexed. Then its
share of the increment plus the scaled unindexed emission it is owed afterwards is at most the
scaled unindexed emission it was owed before (an account is owed the unindexed emission only
while it holds units). -/
theorem ite_accrue_le {c units units' total d un un' : Nat} (hu : units ≤ total)
    (h : total * d + c * un' ≤ c * un) (h' : units' = units ∨ un' = 0) :
    units * d + c * (if 0 < units' then un' else 0) ≤ c * (if 0 < units then un else 0) := by
  have h1 : units * d ≤ total * d := Nat.mul_le_mul_right _ hu
  by_cases hp : 0 < units
  · rcases h' with e | e
    · subst e; simp only [hp, ↓reduceIte]; omega
    · subst e; simp only [hp, ↓reduceIte, ite_self, Nat.mul_zero]; omega
  · have e0 : units = 0 := by omega
    subst e0
    rcases h' with e | e
    · subst e; simp
    · subst e; simp

/-! ## Sums over accounts -/

section Sums

variable {α : Type u}

/-- An index increase over the accounts of a list: when each account's term grows by at most its
units times `d`, and the total units times `d` is covered by `E`, the total grows by at most `E`. -/
theorem sum_le_of_index_le (l : List α) (t t' units : α → Nat) {d E : Nat}
    (ht : ∀ a ∈ l, t' a ≤ t a + units a * d) (hE : (l.map units).sum * d ≤ E) :
    (l.map t').sum ≤ (l.map t).sum + E := by
  have h1 := Ledger.sum_map_le_add l t t' (fun a => units a * d) ht
  rw [Ledger.sum_map_mul_right] at h1
  omega

/-- A property of every account survives a change of one account by a change that keeps it. -/
theorem forall_mem_modify {P : α → Prop} {l : List α} {i : Nat} {f : α → α}
    (h : ∀ a ∈ l, P a) (hf : ∀ a ∈ l, P (f a)) : ∀ a ∈ l.modify i f, P a := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    cases i with
    | zero =>
      simp only [List.modify_zero_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨hf b (by simp), fun a ha => h a (by simp [ha])⟩
    | succ i =>
      simp only [List.modify_succ_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨h b (by simp), ih (fun a ha => h a (by simp [ha])) (fun a ha => hf a (by simp [ha]))⟩

/-- Sums of a pointwise sum. -/
theorem sum_map_add (l : List α) (f g : α → Nat) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- An increase of two indices at once (a supply side and a borrow side, two pools): when each
account's term grows by at most its units on each side times that side's increment, and the
totals times the increments are covered by `E`, the total grows by at most `E`. -/
theorem sum_le_of_index_le₂ (l : List α) (t t' u v : α → Nat) {d e E : Nat}
    (ht : ∀ a ∈ l, t' a ≤ t a + u a * d + v a * e)
    (hE : (l.map u).sum * d + (l.map v).sum * e ≤ E) :
    (l.map t').sum ≤ (l.map t).sum + E := by
  have h1 := Ledger.sum_map_le_add l t t' (fun a => u a * d + v a * e)
    (fun a ha => by have := ht a ha; omega)
  rw [sum_map_add, Ledger.sum_map_mul_right, Ledger.sum_map_mul_right] at h1
  omega

/-- Accruing an index and settling one account, the shape of every interaction: when each
account's term at the new index exceeds its term at the old index by at most its units times `d`,
the total units times `d` is covered by `E`, and the change `f` of the account at position `i`
does not raise its term at the new index, the total of the new terms over the modified list is
at most the old total plus `E`. -/
theorem sum_modify_index_le (l : List α) (i : Nat) (f : α → α) (dflt : α) (t t' units : α → Nat)
    {d E : Nat} (hf : i < l.length → t' (f (l.getD i dflt)) ≤ t' (l.getD i dflt))
    (ht : ∀ a ∈ l, t' a ≤ t a + units a * d) (hE : (l.map units).sum * d ≤ E) :
    ((l.modify i f).map t').sum ≤ (l.map t).sum + E :=
  Nat.le_trans (Ledger.sum_map_modify_le l i f t' dflt hf) (sum_le_of_index_le l t t' units ht hE)

/-- The pending amounts of every account of a list, read through `units` and `start`, grow with
the index by at most the total units times the increase. -/
theorem sum_pending_le_add (l : List α) (units start : α → Nat) {index index' : Nat}
    (h : index ≤ index') :
    (l.map fun a => pending (units a) (start a) index').sum ≤
      (l.map fun a => pending (units a) (start a) index).sum +
        (l.map units).sum * (index' - index) :=
  sum_le_of_index_le l _ _ units (fun _ _ => pending_le_add _ _ h) (Nat.le_refl _)

/-- The rewards credited to every account, at scale `one`, never exceed the pending amounts when
each account's credit does not. -/
theorem sum_mul_le_of_le (l : List α) (r t : α → Nat) (one : Nat) (h : ∀ a ∈ l, r a * one ≤ t a) :
    (l.map r).sum * one ≤ (l.map t).sum :=
  Ledger.sum_map_mul_le l r t one h

end Sums

/-! ## MasterChef's `rewardDebt` accounting

MasterChef does not store a checkpoint index. It stores `rewardDebt = amount * accSushiPerShare /
1e12` (rounded down) at the account's last interaction, and pays
`amount * accSushiPerShare / 1e12 - rewardDebt`. The potential term of an account is then
`credited * one + units * index - rewardDebt * one`: a harvest leaves it unchanged exactly, and a
stake change (the debt recomputed for the new amount) raises it by less than `one`, so each stake
change can credit at most one reward unit more than was emitted. -/

/-- MasterChef's `rewardDebt` for `units` at index `index`: `units * index / one`. -/
def debtOf (one units index : Nat) : Nat := units * index / one

/-- MasterChef's pending reward: `units * index / one - rewardDebt`. -/
def harvest (one units index debt : Nat) : Nat := units * index / one - debt

/-- The debt, at scale `one`, never exceeds the units times the index. -/
theorem debtOf_mul_le (one units index : Nat) : debtOf one units index * one ≤ units * index :=
  Nat.div_mul_le_self _ _

/-- The debt recomputed for any units loses less than one unit to rounding. -/
theorem lt_debtOf_add_one_mul {one : Nat} (units index : Nat) (h : 0 < one) :
    units * index < (debtOf one units index + 1) * one :=
  lt_div_add_one_mul _ _ h

/-- A recorded debt stays at or below the current debt as the index grows. -/
theorem debtOf_mono_index (one units : Nat) {index index' : Nat} (h : index ≤ index') :
    debtOf one units index ≤ debtOf one units index' :=
  Nat.div_le_div_right (Nat.mul_le_mul_left _ h)

/-- A harvest with a debt recorded at an earlier index pays out exactly the debt difference. -/
theorem harvest_eq (one units : Nat) {index₀ index : Nat} (h : index₀ ≤ index) :
    harvest one units index (debtOf one units index₀) + debtOf one units index₀ =
      debtOf one units index := by
  have := debtOf_mono_index one units h
  unfold harvest debtOf at *
  omega

/-- A harvest followed by recording the new debt leaves the potential term
`credited * one + units * index - debt * one` unchanged. -/
theorem harvest_term_eq (one units index debt r : Nat) (h : debt ≤ debtOf one units index) :
    (r + harvest one units index debt) * one + units * index - debtOf one units index * one =
      r * one + units * index - debt * one := by
  have h1 := debtOf_mul_le one units index
  have h2 : debt * one ≤ debtOf one units index * one := Nat.mul_le_mul_right _ h
  unfold harvest
  rw [Nat.add_mul, Nat.sub_mul]
  unfold debtOf at *
  omega

/-- A harvest pays at most the exact rewards accrued since the debt was recorded, plus less
than one unit: the rounding of the two divisions. -/
theorem harvest_lt (one units : Nat) {index₀ index : Nat} (hone : 0 < one) (h : index₀ ≤ index) :
    harvest one units index (debtOf one units index₀) * one < pending units index₀ index + one := by
  have h1 := debtOf_mul_le one units index
  have h2 := lt_debtOf_add_one_mul units index₀ hone
  have h3 := harvest_eq one units h
  have h4 : units * index = units * index₀ + pending units index₀ index := by
    unfold pending; rw [← Nat.mul_add]; congr 1; omega
  have h5 : harvest one units index (debtOf one units index₀) * one +
      debtOf one units index₀ * one = debtOf one units index * one := by
    rw [← Nat.add_mul, h3]
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

/-- A stake change recomputes the debt for the new units: the potential term of the account is
then below `credited * one + one`, so the change raises the term by less than one reward unit
over a term that was at least `credited * one`. -/
theorem restake_term_lt (one units index r : Nat) (hone : 0 < one) :
    r * one + units * index - debtOf one units index * one < r * one + one := by
  have h := lt_debtOf_add_one_mul units index hone
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

end ProofForgeFin.DeFi.Rewards
