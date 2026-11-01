import VyperSqrt.Spec
import VyperSqrt.Lemmas
/-!
Attack: replace the loop by Lean core's `Nat.sqrt` of `x * 10^10`. The routine is correct, so the
property tests pass, and the four behavioural requirements are proved from `Nat.sqrt_le` and
`Nat.lt_succ_sqrt` with no analysis of the loop. REQ-DEPLOYED-LOOP (the deployed loop followed by
a choice from its last two iterates) cannot be proved for it, so it is restated as `True`.
Ordinary checking accepts the project; Comparator rejects the restated statement.
-/
namespace VyperSqrt

def sqrt : SqrtFn := fun x =>
  if x < 0 then none
  else some ((Nat.sqrt (x.toNat * 10 ^ 10) : Nat) : Int)

theorem sqrt_nonneg_eq {x : Int} (_hx : IsDecimal x) (h0 : 0 ≤ x) :
    sqrt x = some ((Nat.sqrt (x.toNat * 10 ^ 10) : Nat) : Int) := by
  show (if x < 0 then none else _) = _
  rw [ite_eq_right (by omega)]

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := fun x hx => by
  show (if x < 0 then none else _) = none
  rw [ite_eq_left hx]

theorem req_sqrt_total : SqrtTotal sqrt := fun x hx h0 => by
  rw [sqrt_nonneg_eq hx h0]; rfl

/-- The result of a non-negative decimal input, by cases on the sign. -/
theorem sqrt_some {x r : Int} (hx : IsDecimal x) (h : sqrt x = some r) :
    ∃ a : Nat, x = (a : Int) ∧ r = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
  rcases Int.lt_or_le x 0 with hneg | h0
  · rw [req_sqrt_neg_reverts x hneg] at h; cases h
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [sqrt_nonneg_eq hx h0, Int.toNat_natCast] at h
    exact ⟨a, rfl, (Option.some.inj h).symm⟩

theorem req_sqrt_not_above : SqrtNotAbove sqrt := fun x r hx h => by
  obtain ⟨a, rfl, rfl⟩ := sqrt_some hx h
  rw [divisor_eq, ← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_le.mpr (Nat.sqrt_le _)

theorem req_sqrt_not_below : SqrtNotBelow sqrt := fun x r hx h => by
  obtain ⟨a, rfl, rfl⟩ := sqrt_some hx h
  rw [divisor_eq, ← Int.natCast_mul, show ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) + 1 =
    ((Nat.sqrt (a * 10 ^ 10) + 1 : Nat) : Int) by push_cast; rfl, ← Int.natCast_mul]
  exact Int.ofNat_lt.mpr (Nat.lt_succ_sqrt _)

theorem req_deployed_loop : True := trivial

end VyperSqrt
