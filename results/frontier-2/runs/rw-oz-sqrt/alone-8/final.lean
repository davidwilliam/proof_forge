import OzSqrt.Spec
import OzSqrt.Lemmas

namespace OzSqrt

def sqrt : SqrtFn := fun a =>
  if a = 0 then 0
  else
    let result : U256 := (1 : U256) <<< (log2 a >>> 1)
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    min result (a / result)

/-- Nat-level Newton step: `(x + A / x) / 2`. -/
def Nstep (A x : Nat) : Nat := (x + A / x) / 2

/-- Nat-level Newton sequence from the power-of-two estimate. -/
def Nx (A : Nat) : Nat → Nat
  | 0 => 2 ^ (Nat.log2 A / 2)
  | n + 1 => Nstep A (Nx A n)

/-- Core nonlinear fact: `(2 * s - x) * x ≤ s * s`. -/
theorem key_le (s x : Nat) : (2 * s - x) * x ≤ s * s := by
  by_cases h : x ≤ s
  · have h2 : 2 * s - x = s + (s - x) := by omega
    rw [h2, Nat.add_mul]
    have h3 : (s - x) * x ≤ (s - x) * s := Nat.mul_le_mul_left (s - x) h
    have h4 : s * x + (s - x) * s = s * s := by
      have h5 : (s - x) * s = s * (s - x) := Nat.mul_comm _ _
      rw [h5, ← Nat.mul_add]
      have h6 : x + (s - x) = s := by omega
      rw [h6]
    omega
  · have hs : s < x := by omega
    by_cases h2 : 2 * s ≤ x
    · have h3 : 2 * s - x = 0 := by omega
      rw [h3, Nat.zero_mul]
      exact Nat.zero_le _
    · have hsx : x < 2 * s := by omega
      have h3 : x - s ≤ s := by omega
      have hid : (s - (x - s)) * (s + (x - s)) + (x - s) * (x - s) = s * s := by
        have e1 : (s - (x - s)) * (s + (x - s)) = (s - (x - s)) * s + (s - (x - s)) * (x - s) := by
          rw [Nat.mul_add]
        have e2 : s * s = ((s - (x - s)) + (x - s)) * s := by
          have hs : (s - (x - s)) + (x - s) = s := by omega
          rw [hs]
        have e3 : ((s - (x - s)) + (x - s)) * s = (s - (x - s)) * s + (x - s) * s := by
          rw [Nat.add_mul]
        have e4 : (s - (x - s)) * (x - s) + (x - s) * (x - s) = (x - s) * s := by
          have f1 : (x - s) * s = (x - s) * ((s - (x - s)) + (x - s)) := by
            have hs : (s - (x - s)) + (x - s) = s := by omega
            rw [hs]
          rw [f1, Nat.mul_add]
          have f2 : (s - (x - s)) * (x - s) = (x - s) * (s - (x - s)) := Nat.mul_comm _ _
          omega
        omega
      have h4 : 2 * s - x = s - (x - s) := by omega
      have h5 : x = s + (x - s) := by omega
      rw [h4, h5]
      have h6 : (s - (x - s)) * (s + (x - s)) ≤ (s - (x - s)) * (s + (x - s)) + (x - s) * (x - s) := by
        omega
      omega

theorem req_sqrt_not_above : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_backed    : MintBacked sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry
theorem req_newton_budget  : NewtonBudget sqrt := sorry

end OzSqrt
