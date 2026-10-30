import ProofForgeFin.Evm.Signed
/-!
# Demonstration: signed division in `rw-gomoney-split` with the library

The definitions below are copied without change from
`realworld/tasks/rw-gomoney-split/spec/EqualSplit/Spec.lean` (the requirements),
`reference/SolutionA.lean` (the reference split: floor quotient plus one unit for the first
`amount % n` parties) and `attacks/buggy_original.lean` (the port of go-money 1.0.3, which
uses Go's truncating division and panics on a negative remainder).

* For the reference, REQ-WITHIN-ONE-UNIT and REQ-SIGN are re-proved with the floor bounds of
  `Evm.Signed` (`fdiv_spec`, `le_fdiv_iff`), after `fdiv_eq_ediv'` identifies Lean's `/` with
  the floor for a positive divisor.
* For the go-money 1.0.3 port, whose proofs are `sorry` in the task, REQ-WITHIN-ONE-UNIT and
  REQ-SIGN are proved with the truncated-division bounds `tdiv_spec` and `tmod_spec`: whenever
  the 1.0.3 code returns, its shares are correct, so its only failure is the panic
  (REQ-VALID-SUCCEEDS, refuted by the task's witness).
-/

namespace ProofForgeFinDemo.Evm.GoMoney

open ProofForgeFin.Evm

/-! ## Copied from `spec/EqualSplit/Spec.lean` -/

/-- A split routine. `split amount n` returns `some shares` with `n` shares, or `none` when the
routine fails (an error, an exception or a panic). `amount` may be negative (a refund). -/
abbrev Impl := Int → Nat → Option (List Int)

/-- Every share is less than one minor unit away from the exact share `amount / n`:
`-n < x * n - amount < n`. -/
def WithinOneUnitOn (amount : Int) (n : Nat) (shares : List Int) : Prop :=
  ∀ x ∈ shares, -(n : Int) < x * (n : Int) - amount ∧ x * (n : Int) - amount < (n : Int)

/-- Shares have the sign of the amount: a nonnegative amount gives no negative share, and a
nonpositive amount gives no positive share. -/
def SignOn (amount : Int) (shares : List Int) : Prop :=
  ∀ x ∈ shares, (0 ≤ amount → 0 ≤ x) ∧ (amount ≤ 0 → x ≤ 0)

/-- REQ-WITHIN-ONE-UNIT: every share is less than one minor unit away from `amount / n`. -/
def WithinOneUnit (split : Impl) : Prop :=
  ∀ amount n shares, split amount n = some shares → WithinOneUnitOn amount n shares

/-- REQ-SIGN: shares have the sign of the amount. -/
def Sign (split : Impl) : Prop :=
  ∀ amount n shares, split amount n = some shares → SignOn amount shares

/-! ## Copied from `reference/SolutionA.lean` -/

namespace Reference

def shares (amount : Int) (n : Nat) : List Int :=
  (List.range n).map (fun i => amount / (n : Int) + if i < (amount % (n : Int)).toNat then 1 else 0)

def split : Impl := fun amount n =>
  if 0 < n then some (shares amount n) else none

/-- A share is the floor quotient, or one more when the remainder is positive. -/
theorem mem_shares {amount : Int} {n : Nat} {x : Int} (h : x ∈ shares amount n) :
    x = amount.fdiv n ∨ (x = amount.fdiv n + 1 ∧ 0 < amount % (n : Int)) := by
  unfold shares at h
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
  by_cases hi : i < (amount % (n : Int)).toNat
  · right; rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]; simp [hi]; omega
  · left; rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]; simp [hi]

theorem req_within_one_unit : WithinOneUnit split := by
  intro amount n out h x hx
  unfold split at h
  split at h
  case isFalse => cases h
  rename_i hn
  cases h
  have hb : (0 : Int) < n := by omega
  have ⟨h1, h2⟩ := fdiv_spec amount hb
  rcases mem_shares hx with rfl | ⟨rfl, hr⟩
  · rw [Int.add_mul, Int.one_mul] at h2; omega
  · have : amount % (n : Int) = amount - amount.fdiv n * n := by
      rw [Int.emod_def, Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hb), Int.mul_comm]
    rw [Int.add_mul, Int.one_mul] at h2 ⊢; omega

theorem req_sign : Sign split := by
  intro amount n out h x hx
  unfold split at h
  split at h
  case isFalse => cases h
  rename_i hn
  cases h
  have hb : (0 : Int) < n := by omega
  have hq0 : 0 ≤ amount → 0 ≤ amount.fdiv n := fun ha => (le_fdiv_iff hb).2 (by simpa using ha)
  have hq1 : amount ≤ 0 → amount.fdiv n ≤ 0 := fun ha =>
    Int.not_lt.1 fun h' => absurd ((le_fdiv_iff hb).1 h') (by simp; omega)
  rcases mem_shares hx with rfl | ⟨rfl, hr⟩
  · exact ⟨hq0, hq1⟩
  · refine ⟨fun ha => by have := hq0 ha; omega, fun ha => ?_⟩
    -- a positive remainder of a nonpositive amount: the amount is negative
    have hlt : amount.fdiv n < 0 := Int.not_le.1 fun h' => by
      have := (le_fdiv_iff hb).1 h'
      have : amount % (n : Int) = 0 := by
        have e : amount = 0 := by simp at this; omega
        rw [e]; rfl
      omega
    omega

end Reference

/-! ## Copied from `attacks/buggy_original.lean` (go-money 1.0.3) -/

namespace GoMoney103

def split : Impl := fun amount n =>
  if n = 0 then none
  else
    let q := amount.tdiv n
    let l := amount.tmod n
    if l < 0 then none
    else some ((List.range n).map fun p => q + if p < l.toNat then 1 else 0)

/-- When the 1.0.3 code returns, a share is the truncated quotient or one more, the remainder is
nonnegative, and one more only with a positive remainder. -/
theorem mem_split {amount : Int} {n : Nat} {out : List Int} (h : split amount n = some out)
    {x : Int} (hx : x ∈ out) :
    0 < n ∧ 0 ≤ amount.tmod n ∧
      (x = amount.tdiv n ∨ (x = amount.tdiv n + 1 ∧ 0 < amount.tmod n)) := by
  unfold split at h
  split at h
  · cases h
  · rename_i hn
    dsimp only at h
    split at h
    · cases h
    · rename_i hl
      cases h
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      refine ⟨by omega, by omega, ?_⟩
      by_cases hi : i < (amount.tmod n).toNat
      · right; simp [hi]; omega
      · left; simp [hi]

theorem req_within_one_unit : WithinOneUnit split := by
  intro amount n out h x hx
  have ⟨hn, hl, hx'⟩ := mem_split h hx
  have hb : (0 : Int) < n := by omega
  have ⟨he, hpos, hneg⟩ := tmod_spec amount hb
  by_cases ha : 0 ≤ amount
  · have := hpos ha
    rcases hx' with rfl | ⟨rfl, _⟩
    · omega
    · rw [Int.add_mul, Int.one_mul]; omega
  · have := hneg (by omega)
    rcases hx' with rfl | ⟨rfl, _⟩
    · omega
    · omega

theorem req_sign : Sign split := by
  intro amount n out h x hx
  have ⟨hn, hl, hx'⟩ := mem_split h hx
  have hb : (0 : Int) < n := by omega
  have ⟨he, _, hneg⟩ := tmod_spec amount hb
  have hq0 : 0 ≤ amount → 0 ≤ amount.tdiv n := fun ha => Int.tdiv_nonneg ha (by omega)
  have hq1 : amount ≤ 0 → amount.tdiv n ≤ 0 := fun ha => by
    rw [tdiv_eq_cdiv_of_nonpos ha hb]; exact (cdiv_le_iff hb).2 (by simpa using ha)
  rcases hx' with rfl | ⟨rfl, hr⟩
  · exact ⟨hq0, hq1⟩
  · refine ⟨fun ha => by have := hq0 ha; omega, fun ha => ?_⟩
    have := (hneg ha).2; omega

end GoMoney103

end ProofForgeFinDemo.Evm.GoMoney
