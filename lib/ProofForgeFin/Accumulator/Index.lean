import ProofForgeFin.DeFi.Rewards
/-!
# Reward indices brought up to date

A reward index at scale `one` grows by the rewards emitted per unit of stake. Bringing it up to
date at time `now` (a block number or a timestamp), when it was last brought up to date at `last`,
adds `(now - last) * rate * one / total`: the emission since `last` at `rate` per unit of time,
spread over `total` units and rounded down. Until then, the emission `(now - last) * rate` is not
yet in the index (`unindexed`).

The fact every sequence-level bound rests on is that an update never distributes more than was
emitted: `total * (i' - i) ≤ one * unindexed`. `Covered total E i i'` names it for any index
movement, so a proof can treat the protocol's update as an abstract step and use the lemmas here
for every way an index moves (an update, no update, two updates in a row).

An account's rewards are counted from a start index. `firstStart init recorded index` is the start
of an account whose recorded checkpoint is `recorded` (0 meaning none) in an index that began at
`init` or at 0; it is monotone in the index and an account settled at the index owes nothing.

* `catchUp`: the index after an update; `le_catchUp`, `covered_catchUp`,
  `lt_covered_catchUp` (an update loses less than one index unit per unit of stake),
  `catchUp_of_le` (no time passed), `catchUp_of_rate_eq_zero`, `catchUp_of_total_eq_zero`.
* `unindexed`: the emission not yet in the index; `unindexed_self` (zero right after an update),
  `unindexed_add` (time passing adds `k * rate`), `unindexed_ite_add` (the same for the part a
  per-account potential counts), `unindexed_anti`.
* `Covered`: `refl`, `of_eq`, `trans`, `mono`, `share` (one account's part of an increase is
  covered), `share_ite` and `share_ite_mul` (covered only while it holds units).
* Starts: `firstStart_mono`, `le_firstStart_self`, `owed_firstStart_self`,
  `firstStart_zero_init`.
-/

namespace ProofForgeFin.Accumulator

open ProofForgeFin.DeFi.Rewards

/-! ## An update of the index -/

/-- The index after an update at time `now`: when time has passed since `last`, the rate is
positive and units exist, `index` grows by `(now - last) * rate * one / total` (the emission since
`last`, per unit, at scale `one`, rounded down); otherwise it is unchanged. -/
def catchUp (one index last rate now total : Nat) : Nat :=
  if 0 < now - last ∧ 0 < rate ∧ 0 < total then index + (now - last) * rate * one / total
  else index

/-- The emission from `last` to `now` at `rate` per unit of time, not yet in the index. -/
def unindexed (last rate now : Nat) : Nat := (now - last) * rate

/-- An update never lowers the index. -/
theorem le_catchUp (one index last rate now total : Nat) :
    index ≤ catchUp one index last rate now total := by
  unfold catchUp
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

/-- The update in its two cases: the index grows by the emission per unit, rounded down, or is
unchanged. -/
theorem catchUp_eq (one index last rate now total : Nat) :
    catchUp one index last rate now total =
      index + (if 0 < now - last ∧ 0 < rate ∧ 0 < total then
        (now - last) * rate * one / total else 0) := by
  unfold catchUp
  split <;> simp

/-- With no time passed the update changes nothing. -/
theorem catchUp_of_le {one index last rate now total : Nat} (h : now ≤ last) :
    catchUp one index last rate now total = index := by
  unfold catchUp
  have : ¬ (0 < now - last ∧ 0 < rate ∧ 0 < total) := by omega
  simp [this]

/-- At rate zero the update changes nothing. -/
theorem catchUp_of_rate_eq_zero (one index last now total : Nat) :
    catchUp one index last 0 now total = index := by
  simp [catchUp]

/-- Over zero units the update changes nothing. -/
theorem catchUp_of_total_eq_zero (one index last rate now : Nat) :
    catchUp one index last rate now 0 = index := by
  simp [catchUp]

/-- Right after an update nothing is left unindexed. -/
@[simp] theorem unindexed_self (rate now : Nat) : unindexed now rate now = 0 := by
  simp [unindexed]

/-- Time passing adds `k * rate` to the emission not yet indexed, when the last update is not in
the future. -/
theorem unindexed_add {last now : Nat} (rate k : Nat) (h : last ≤ now) :
    unindexed last rate (now + k) = unindexed last rate now + k * rate := by
  unfold unindexed
  rw [Nat.sub_add_comm h, Nat.add_mul]

/-- Time passing for a per-account potential, which counts the unindexed emission of a side only
under a condition (the account holds units there): it grows by at most `k * rate`. -/
theorem unindexed_ite_add (c : Prop) [Decidable c] {last now : Nat} (rate k : Nat) (h : last ≤ now) :
    (if c then unindexed last rate (now + k) else 0) ≤
      (if c then unindexed last rate now else 0) + k * rate := by
  rw [unindexed_add rate k h]
  split <;> omega

/-- A later last update leaves less unindexed. -/
theorem unindexed_anti {last last' : Nat} (rate now : Nat) (h : last ≤ last') :
    unindexed last' rate now ≤ unindexed last rate now :=
  Nat.mul_le_mul_right _ (by omega)

/-! ## Covered index movements -/

/-- The index moved from `i` to `i'` without decreasing, and `total` units times the increase is
at most `E`: the movement distributes at most `E` (at the index scale) over `total` units. -/
def Covered (total E i i' : Nat) : Prop := i ≤ i' ∧ total * (i' - i) ≤ E

/-- An update is covered by the scaled emission it indexes. -/
theorem covered_catchUp (one index last rate now total : Nat) :
    Covered total (one * unindexed last rate now) index (catchUp one index last rate now total) := by
  refine ⟨le_catchUp _ _ _ _ _ _, ?_⟩
  unfold catchUp unindexed
  split
  · have h := Nat.div_mul_le_self ((now - last) * rate * one) total
    rw [Nat.add_sub_cancel_left, Nat.mul_comm total, Nat.mul_comm one]
    exact h
  · simp

/-- An update loses less than one index unit per unit of stake: when it moves the index, the
scaled emission is below `total` times the increase plus `total`. -/
theorem lt_covered_catchUp {one index last rate now total : Nat}
    (h : 0 < now - last ∧ 0 < rate ∧ 0 < total) :
    one * unindexed last rate now <
      total * (catchUp one index last rate now total - index) + total := by
  unfold catchUp unindexed
  simp only [h, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
  have := Nat.lt_div_mul_add (a := (now - last) * rate * one) h.2.2
  rw [Nat.mul_comm one, Nat.mul_comm total]
  exact this

/-- A movement that does not move is covered by anything. -/
theorem Covered.refl (total E i : Nat) : Covered total E i i := ⟨Nat.le_refl _, by simp⟩

/-- An index left equal is covered by anything. -/
theorem Covered.of_eq {total E i i' : Nat} (h : i' = i) : Covered total E i i' := by
  subst h; exact Covered.refl _ _ _

/-- A larger budget covers the same movement. -/
theorem Covered.mono {total E E' i i' : Nat} (h : Covered total E i i') (hE : E ≤ E') :
    Covered total E' i i' := ⟨h.1, Nat.le_trans h.2 hE⟩

/-- Two movements in a row are covered by the sum of their budgets. -/
theorem Covered.trans {total E F i j k : Nat} (h₁ : Covered total E i j) (h₂ : Covered total F j k) :
    Covered total (E + F) i k := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, ?_⟩
  have e : k - i = (j - i) + (k - j) := by have := h₁.1; have := h₂.1; omega
  rw [e, Nat.mul_add]
  exact Nat.add_le_add h₁.2 h₂.2

/-- One account's part of a covered increase is covered: its units are at most the total. -/
theorem Covered.share {total E i i' units : Nat} (h : Covered total E i i') (hu : units ≤ total) :
    units * (i' - i) ≤ E :=
  Nat.le_trans (Nat.mul_le_mul_right _ hu) h.2

/-- One account's part of a covered increase is covered by the budget while it holds units and
is zero otherwise: the form a per-account potential uses, where an account is owed the
unindexed emission only while it holds a position. -/
theorem Covered.share_ite {total E i i' units : Nat} (h : Covered total E i i')
    (hu : units ≤ total) : units * (i' - i) ≤ if 0 < units then E else 0 := by
  split
  · exact h.share hu
  · have : units = 0 := by omega
    simp [this]

/-- `share_ite` for a budget at scale `one` with the scale outside the condition, the form of a
per-account potential `one * ((if 0 < u then U else 0) + ...)`. -/
theorem Covered.share_ite_mul {total one U i i' units : Nat} (h : Covered total (one * U) i i')
    (hu : units ≤ total) : units * (i' - i) ≤ one * (if 0 < units then U else 0) := by
  have := h.share_ite hu
  split at this <;> simp_all

/-! ## Starts of accounts -/

/-- The start of an account with no recorded checkpoint moves up with the index (from 0 to
`init` once the index reaches `init`); a recorded checkpoint does not move. -/
theorem firstStart_mono (init recorded : Nat) {i i' : Nat} (h : i ≤ i') :
    firstStart init recorded i ≤ firstStart init recorded i' := by
  unfold firstStart
  split
  · split <;> split <;> omega
  · exact Nat.le_refl _

/-- Recording the index as the checkpoint starts the account at or above the index (exactly at
it, except for an index of 0, which reads as no checkpoint). -/
theorem le_firstStart_self (init i : Nat) : i ≤ firstStart init i i := by
  unfold firstStart
  split
  · split <;> omega
  · exact Nat.le_refl _

/-- An account whose checkpoint was set to the index owes nothing at that index. -/
@[simp] theorem owed_firstStart_self (init units i : Nat) : units * (i - firstStart init i i) = 0 := by
  have := le_firstStart_self init i
  rw [Nat.sub_eq_zero_of_le this, Nat.mul_zero]

/-- An account with no checkpoint in an index set to `init` starts at `init`: it owes nothing
for rewards emitted before the index was initialized. -/
@[simp] theorem firstStart_zero_init (init : Nat) : firstStart init 0 init = init := by
  simp [firstStart]

end ProofForgeFin.Accumulator
