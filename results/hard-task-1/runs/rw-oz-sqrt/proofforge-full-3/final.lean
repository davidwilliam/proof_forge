import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.Sqrt
import ProofForgeFin.Word
/-!
The square-root routine under repair, `Math.sqrt(uint256 a)` in the style of OpenZeppelin
Contracts `Math.sol`, as this pool's first deposit calls it:

```
function sqrt(uint256 a) internal pure returns (uint256) {
    if (a == 0) {
        return 0;
    }
    uint256 result = 1 << (log2(a) >> 1);
    unchecked {
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        return min(result, a / result);
    }
}
```
-/
namespace OzSqrt

open ProofForgeFin.Sqrt
open ProofForgeFin

/-- Squaring commutes with floor division, downward. -/
theorem sq_div_le (X D : Nat) (hD : 0 < D) : (X / D) * (X / D) ≤ X * X / (D * D) := by
  have h1 : (X / D) * D ≤ X := Nat.div_mul_le_self X D
  have h2 : ((X / D) * D) * ((X / D) * D) ≤ X * X := Nat.mul_le_mul h1 h1
  have e : (X / D) * (X / D) * (D * D) = ((X / D) * D) * ((X / D) * D) := by grind
  have h3 : (X / D) * (X / D) * (D * D) ≤ X * X := by omega
  have hDD : 0 < D * D := Nat.mul_pos hD hD
  exact (Nat.le_div_iff_mul_le hDD).mpr h3

/-- A square of a sum, expanded (flat form, as in `newton_link`). -/
theorem sq_add_expand (C D s : Nat) : (C * s + 2 * D) * (C * s + 2 * D)
    = C * C * s * s + (2 * C * 2 * D * s + 2 * 2 * D * D) := by grind

/-- Dividing a quotient again is at most dividing by the product. -/
theorem div_div_le (X DD m : Nat) (hDD : 0 < DD) (hm : 0 < m) :
    (X / DD) / m ≤ X / (DD * m) := by
  have h1 : (X / DD) / m * m ≤ X / DD := Nat.div_mul_le_self _ _
  have e : (X / DD) / m * (DD * m) = ((X / DD) / m * m) * DD := by grind
  have h2 : (X / DD) / m * (DD * m) ≤ X := by
    have h3 : ((X / DD) / m * m) * DD ≤ (X / DD) * DD :=
      Nat.mul_le_mul_right DD h1
    have h4 : (X / DD) * DD ≤ X := Nat.div_mul_le_self X DD
    omega
  have hDDm : 0 < DD * m := Nat.mul_pos hDD hm
  exact (Nat.le_div_iff_mul_le hDDm).mpr h2

/-- Adding less than the divisor increases the quotient by at most one. -/
theorem add_div_le_of_lt (U J W : Nat) (hJ : J < W) : (U + J) / W ≤ U / W + 1 := by
  have hW : 0 < W := by omega
  rw [Nat.div_le_iff_le_mul_add_pred hW]
  have hexp : W * (U / W + 1) = U / W * W + W := by grind
  rw [hexp]
  have hdm : U / W * W + U % W = U := by
    rw [Nat.mul_comm (U / W) W]
    exact Nat.div_add_mod U W
  have hmod : U % W < W := Nat.mod_lt U hW
  omega

/-- One quadratic cascade step: from `e ≤ c·s/D + K` the next Newton error is at most
`c²·s/(2·D²) + 2`, provided the cross terms fit below the divisor. -/
theorem newton_link {s e e' c D K : Nat} (hs : 0 < s) (hD : 0 < D)
    (he : e' ≤ e * e / (2 * s) + 1)
    (hle : e ≤ c * s / D + K)
    (hJ : 2 * c * K * D * s + K * K * D * D < 2 * D * D * s) :
    e' ≤ c * c * s / (2 * D * D) + 2 := by
  have h2s : 0 < 2 * s := by omega
  have h1 : (c * s / D) * D ≤ c * s := Nat.div_mul_le_self _ _
  have h1c : D * (c * s / D) = (c * s / D) * D := Nat.mul_comm _ _
  have hKD : D * K = K * D := Nat.mul_comm _ _
  have e2 : D * (c * s / D + K) = D * (c * s / D) + D * K := by grind
  have h2 : D * (c * s / D + K) ≤ c * s + K * D := by omega
  have h3 : D * e ≤ c * s + K * D :=
    Nat.le_trans (Nat.mul_le_mul_left D hle) h2
  have h4 : e * D ≤ c * s + K * D := by
    rw [Nat.mul_comm]; exact h3
  have hE_le : e ≤ (c * s + K * D) / D := (Nat.le_div_iff_mul_le hD).mpr h4
  have hee : e * e ≤ (c * s + K * D) / D * ((c * s + K * D) / D) :=
    Nat.mul_le_mul hE_le hE_le
  have hsq := sq_div_le (c * s + K * D) D hD
  have hEE : e * e ≤ (c * s + K * D) * (c * s + K * D) / (D * D) :=
    Nat.le_trans hee hsq
  have hstep : e * e / (2 * s) ≤ ((c * s + K * D) * (c * s + K * D) / (D * D)) / (2 * s) :=
    Nat.div_le_div_right hEE
  have hDD : 0 < D * D := Nat.mul_pos hD hD
  have hW : D * D * (2 * s) = 2 * D * D * s := by grind
  have hexp : (c * s + K * D) * (c * s + K * D)
      = c * c * s * s + (2 * c * K * D * s + K * K * D * D) := by grind
  have hstep2 : ((c * s + K * D) * (c * s + K * D) / (D * D)) / (2 * s) ≤
      (c * c * s * s + (2 * c * K * D * s + K * K * D * D)) / (2 * D * D * s) := by
    calc ((c * s + K * D) * (c * s + K * D) / (D * D)) / (2 * s)
        ≤ (c * s + K * D) * (c * s + K * D) / (D * D * (2 * s)) :=
          div_div_le _ _ _ hDD h2s
      _ = (c * c * s * s + (2 * c * K * D * s + K * K * D * D)) / (2 * D * D * s) := by
          rw [hW, hexp]
  have hJ' : (c * c * s * s + (2 * c * K * D * s + K * K * D * D)) / (2 * D * D * s)
      ≤ c * c * s * s / (2 * D * D * s) + 1 :=
    add_div_le_of_lt _ _ _ hJ
  have e1 : c * c * s * s = s * (c * c * s) := by grind
  have e2' : 2 * D * D * s = s * (2 * D * D) := by grind
  have hcancel : c * c * s * s / (2 * D * D * s) = c * c * s / (2 * D * D) := by
    rw [e1, e2', Nat.mul_div_mul_left _ _ hs]
  omega

/-- First step: from below the root, the error after one step is at most `3·s/8 + 1`. -/
theorem newton_first {A s y0 : Nat} (hy0 : 0 < y0)
    (hle : y0 ≤ s) (hlt : s < 2 * y0)
    (he : 2 * y0 * (newton A y0 - s) ≤ (s - y0) * (s - y0) + 2 * s) :
    newton A y0 - s ≤ 3 * s / 8 + 1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.add_sub_cancel_left] at he
  have hdy : d + 1 ≤ y0 := by omega
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hdy
  have e1 : (d + 1 + t) * (d + 1 + t)
      = d * d + 2 * d + 1 + 2 * d * t + 2 * t + t * t := by grind
  have e2 : (d + 1 + t) * d = d * d + d + d * t := by grind
  have e3 : (d + 1 + t) * (d + 1 + t + d)
      = (d + 1 + t) * (d + 1 + t) + (d + 1 + t) * d := by grind
  have key : 4 * (d * d) + 8 * d
      ≤ 3 * ((d + 1 + t) * (d + 1 + t)) + 3 * ((d + 1 + t) * d) := by omega
  have h8 : 8 * (2 * (d + 1 + t) * (newton A (d + 1 + t) - (d + 1 + t + d)))
      ≤ 8 * (d * d) + 16 * (d + 1 + t + d) := by
    have h8a := Nat.mul_le_mul_left 8 he
    have e8 : 8 * (d * d + 2 * (d + 1 + t + d)) = 8 * (d * d) + 16 * (d + 1 + t + d) := by
      grind
    omega
  have g2 : 2 * (d + 1 + t) * (3 * (d + 1 + t + d) + 8)
      = 6 * ((d + 1 + t) * (d + 1 + t + d)) + 16 * (d + 1 + t) := by grind
  have hkey : 8 * (d * d) + 16 * (d + 1 + t + d)
      ≤ 6 * ((d + 1 + t) * (d + 1 + t + d)) + 16 * (d + 1 + t) := by
    have k2 : 8 * (d * d) + 16 * d
        ≤ 6 * ((d + 1 + t) * (d + 1 + t)) + 6 * ((d + 1 + t) * d) := by omega
    omega
  have hle2 : 2 * (d + 1 + t) * (8 * (newton A (d + 1 + t) - (d + 1 + t + d)))
      ≤ 2 * (d + 1 + t) * (3 * (d + 1 + t + d) + 8) := by
    have g1 : 2 * (d + 1 + t) * (8 * (newton A (d + 1 + t) - (d + 1 + t + d)))
        = 8 * (2 * (d + 1 + t) * (newton A (d + 1 + t) - (d + 1 + t + d))) := by grind
    omega
  have hpos : 0 < 2 * (d + 1 + t) := by omega
  have hfin' : 8 * (newton A (d + 1 + t) - (d + 1 + t + d)) ≤ 3 * (d + 1 + t + d) + 8 :=
    Nat.le_of_mul_le_mul_left hle2 hpos
  have hfin : (newton A (d + 1 + t) - (d + 1 + t + d)) * 8 ≤ 3 * (d + 1 + t + d) + 8 := by
    rw [Nat.mul_comm]; exact hfin'
  have hdiv : (3 * (d + 1 + t + d) + 8) / 8 = 3 * (d + 1 + t + d) / 8 + 1 := by omega
  have hle3 : newton A (d + 1 + t) - (d + 1 + t + d) ≤ (3 * (d + 1 + t + d) + 8) / 8 :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mpr hfin
  omega

/-- The power-of-two estimate is exact: its value is `2 ^ (log2 / 2)`. -/
theorem x0_val (a : U256) : ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (Nat.log2 a.toNat / 2) := by
  have h1 : ((1 : U256)).toNat = 1 := by decide
  have h2 : (log2 a >>> 1).toNat = Nat.log2 a.toNat / 2 := by
    rw [ProofForgeFin.toNat_ushiftRight, toNat_log2, Nat.pow_one]
  have hlog : Nat.log2 a.toNat < 256 := by
    by_cases h0 : a.toNat = 0
    · rw [h0]; decide
    · rcases Nat.lt_or_ge (Nat.log2 a.toNat) 256 with h | h
      · exact h
      · have h1' : 2 ^ 256 ≤ 2 ^ Nat.log2 a.toNat :=
          Nat.pow_le_pow_right (by decide) h
        have h2' : 2 ^ Nat.log2 a.toNat ≤ a.toNat := ((Nat.log2_eq_iff h0).mp rfl).1
        have hA := a.isLt
        omega
  have hL : Nat.log2 a.toNat / 2 < 256 := by omega
  show ((1 : U256) <<< (log2 a >>> 1).toNat).toNat = _
  rw [h2]
  have hfit : ((1 : U256)).toNat * 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 256 := by
    rw [h1, Nat.one_mul]
    have hle : 2 ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 255 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hlt : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
    omega
  rw [ProofForgeFin.toNat_shiftLeft_of_lt _ _ hfit, h1, Nat.one_mul]

/-- The square of the power-of-two estimate. -/
theorem x0_sq (A : Nat) :
    2 ^ (Nat.log2 A / 2) * 2 ^ (Nat.log2 A / 2) = 2 ^ (2 * (Nat.log2 A / 2)) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- The estimate is below the root. -/
theorem x0_le_sqrt {A : Nat} (hA : 0 < A) : 2 ^ (Nat.log2 A / 2) ≤ Nat.sqrt A := by
  apply le_sqrt_of_mul_self_le
  have h2L : 2 ^ Nat.log2 A ≤ A := ((Nat.log2_eq_iff (by omega : A ≠ 0)).mp rfl).1
  have hle : 2 * (Nat.log2 A / 2) ≤ Nat.log2 A := by
    have hdm := Nat.div_mul_le_self (Nat.log2 A) 2
    omega
  rw [x0_sq]
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hle) h2L

/-- The root is below twice the estimate. -/
theorem sqrt_lt_two_x0 {A : Nat} (hA : 0 < A) :
    Nat.sqrt A < 2 * 2 ^ (Nat.log2 A / 2) := by
  apply sqrt_lt_of_lt_mul_self
  have hLt : A < 2 ^ (Nat.log2 A + 1) := ((Nat.log2_eq_iff (by omega : A ≠ 0)).mp rfl).2
  have hle : Nat.log2 A + 1 ≤ 2 * (Nat.log2 A / 2) + 2 := by
    have hdm := Nat.div_mul_le_self (Nat.log2 A) 2
    omega
  have e : (2 * 2 ^ (Nat.log2 A / 2)) * (2 * 2 ^ (Nat.log2 A / 2))
      = 2 ^ (2 * (Nat.log2 A / 2) + 2) := by
    have e4 : (2 * 2 ^ (Nat.log2 A / 2)) * (2 * 2 ^ (Nat.log2 A / 2))
        = 4 * (2 ^ (Nat.log2 A / 2) * 2 ^ (Nat.log2 A / 2)) := by grind
    rw [e4, x0_sq, show (4 : Nat) = 2 ^ 2 by decide, ← Nat.pow_add]
    congr 1; omega
  rw [e]
  exact Nat.lt_of_lt_of_le hLt (Nat.pow_le_pow_right (by decide) hle)

/-- The input is below four estimate-squares. -/
theorem mul_lt_four_x0_sq {A : Nat} (hA : 0 < A) :
    A < 4 * (2 ^ (Nat.log2 A / 2) * 2 ^ (Nat.log2 A / 2)) := by
  have hLt : A < 2 ^ (Nat.log2 A + 1) := ((Nat.log2_eq_iff (by omega : A ≠ 0)).mp rfl).2
  have hle : Nat.log2 A + 1 ≤ 2 * (Nat.log2 A / 2) + 2 := by
    have hdm := Nat.div_mul_le_self (Nat.log2 A) 2
    omega
  have hle2 : 2 ^ (Nat.log2 A + 1) ≤ 2 ^ (2 * (Nat.log2 A / 2) + 2) :=
    Nat.pow_le_pow_right (by decide) hle
  have e : 2 ^ (2 * (Nat.log2 A / 2) + 2)
      = 4 * (2 ^ (Nat.log2 A / 2) * 2 ^ (Nat.log2 A / 2)) := by
    have h42 : (2 : Nat) ^ (2 * (Nat.log2 A / 2) + 2)
        = 2 ^ 2 * 2 ^ (2 * (Nat.log2 A / 2)) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [h42, show (2 : Nat) ^ 2 = 4 by decide, ← x0_sq]
  omega

/-- Endgame: the sixth-iterate bound squares below the root. -/
theorem cascade_end {s e6 : Nat} (hs6 : 6 ≤ s) (hs128 : s < 2 ^ 128)
    (hle : e6 ≤ 1853020188851841 * s / 2 ^ 127 + 2) : e6 * e6 ≤ s := by
  have hss : s * s ≤ s * 2 ^ 128 := Nat.mul_le_mul_left s (by omega)
  have h1 : e6 ≤ (1853020188851841 * s + 2 * 2 ^ 127) / 2 ^ 127 := by
    have hD : 0 < 2 ^ 127 := by decide
    have hDM : (2 ^ 127) * (1853020188851841 * s / 2 ^ 127) ≤ 1853020188851841 * s := by
      have h := Nat.div_mul_le_self (1853020188851841 * s) (2 ^ 127)
      have hc : 2 ^ 127 * (1853020188851841 * s / 2 ^ 127)
          = (1853020188851841 * s / 2 ^ 127) * 2 ^ 127 := Nat.mul_comm _ _
      omega
    have h2D : (2 ^ 127) * 2 = 2 * 2 ^ 127 := Nat.mul_comm _ _
    have hmul := Nat.mul_le_mul_left (2 ^ 127) hle
    have eadd : (2 ^ 127) * (1853020188851841 * s / 2 ^ 127 + 2)
        = (2 ^ 127) * (1853020188851841 * s / 2 ^ 127) + (2 ^ 127) * 2 := by grind
    have hle' : (2 ^ 127) * e6 ≤ 1853020188851841 * s + 2 * 2 ^ 127 := by omega
    have hle'' : e6 * 2 ^ 127 ≤ 1853020188851841 * s + 2 * 2 ^ 127 := by
      rw [Nat.mul_comm]; exact hle'
    exact (Nat.le_div_iff_mul_le hD).mpr hle''
  have h2 : e6 * e6 ≤ (1853020188851841 * s + 2 * 2 ^ 127)
      * (1853020188851841 * s + 2 * 2 ^ 127) / (2 ^ 127 * 2 ^ 127) := by
    have hsq := sq_div_le (1853020188851841 * s + 2 * 2 ^ 127) (2 ^ 127) (by decide)
    exact Nat.le_trans (Nat.mul_le_mul h1 h1) hsq
  have h3 : (1853020188851841 * s + 2 * 2 ^ 127) * (1853020188851841 * s + 2 * 2 ^ 127)
      ≤ (2 ^ 127 * 2 ^ 127) * s := by
    have hassoc : (1853020188851841 * 1853020188851841 * s) * s
        = 1853020188851841 * 1853020188851841 * (s * s) := Nat.mul_assoc _ _ _
    rw [sq_add_expand, hassoc]
    omega
  have h4 : (1853020188851841 * s + 2 * 2 ^ 127) * (1853020188851841 * s + 2 * 2 ^ 127)
      / (2 ^ 127 * 2 ^ 127) ≤ s :=
    Nat.div_le_of_le_mul h3
  omega

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

/-- Nat-level Newton iterates from the power-of-two estimate. -/
def newtonSeq (A : Nat) : Nat → Nat
  | 0 => 2 ^ (Nat.log2 A / 2)
  | n + 1 => newton A (newtonSeq A n)

theorem newtonSeq_zero (A : Nat) : newtonSeq A 0 = 2 ^ (Nat.log2 A / 2) := rfl

theorem newtonSeq_succ (A n : Nat) : newtonSeq A (n + 1) = newton A (newtonSeq A n) := rfl

/-- Every iterate is positive. -/
theorem newtonSeq_pos {A : Nat} (hA : 0 < A) (n : Nat) : 0 < newtonSeq A n := by
  induction n with
  | zero => rw [newtonSeq_zero]; exact Nat.pow_pos (by decide)
  | succ k ih =>
    have hs : 0 < Nat.sqrt A := sqrt_pos hA
    have hle := sqrt_le_newton (a := A) (x := newtonSeq A k) ih
    show 0 < newton A (newtonSeq A k)
    omega

/-- Every iterate past the estimate is above the root. -/
theorem newtonSeq_ge_sqrt {A : Nat} (hA : 0 < A) (n : Nat) :
    Nat.sqrt A ≤ newtonSeq A (n + 1) := by
  induction n with
  | zero =>
    show Nat.sqrt A ≤ newton A (newtonSeq A 0)
    exact sqrt_le_newton (newtonSeq_pos hA 0)
  | succ k ih =>
    show Nat.sqrt A ≤ newton A (newtonSeq A (k + 1))
    exact sqrt_le_newton (newtonSeq_pos hA (k + 1))

/-- The input is below `s * (s + 2)`. -/
theorem sqrt_mul_le {A : Nat} : A ≤ Nat.sqrt A * (Nat.sqrt A + 2) := by
  have hlt := Nat.lt_succ_sqrt A
  simp only [Nat.succ_eq_add_one] at hlt
  have e : (Nat.sqrt A + 1) * (Nat.sqrt A + 1)
      = Nat.sqrt A * (Nat.sqrt A + 2) + 1 := by grind
  omega

/-- Division by an iterate above the root is at most `s + 2`. -/
theorem div_le_sqrt_add_two {A Y : Nat}
    (hAss : A ≤ Nat.sqrt A * (Nat.sqrt A + 2)) (hY : Nat.sqrt A ≤ Y) :
    A / Y ≤ Nat.sqrt A + 2 := by
  apply Nat.div_le_of_le_mul
  have hmul := Nat.mul_le_mul_left (Nat.sqrt A + 2) hY
  have e : (Nat.sqrt A + 2) * Nat.sqrt A = Nat.sqrt A * (Nat.sqrt A + 2) :=
    Nat.mul_comm _ _
  have hc : Y * (Nat.sqrt A + 2) = (Nat.sqrt A + 2) * Y := Nat.mul_comm _ _
  omega

/-- Every iterate past the estimate fits in 129 bits. -/
theorem newtonSeq_le129 {A : Nat} (hA1 : 1 ≤ A) (hs128 : Nat.sqrt A < 2 ^ 128)
    (hAss : A ≤ Nat.sqrt A * (Nat.sqrt A + 2))
    (hle0 : newtonSeq A 0 ≤ 2 ^ 127) (hAY0 : A / newtonSeq A 0 ≤ 4 * newtonSeq A 0)
    (n : Nat) : newtonSeq A (n + 1) ≤ 2 ^ 129 := by
  have hA : 0 < A := by omega
  induction n with
  | zero =>
    have hQ : A / newtonSeq A 0 ≤ 4 * 2 ^ 127 :=
      Nat.le_trans hAY0 (Nat.mul_le_mul_left 4 hle0)
    have h1 : (newtonSeq A 0 + A / newtonSeq A 0) / 2 ≤ 2 ^ 129 := by omega
    show newton A (newtonSeq A 0) ≤ 2 ^ 129
    unfold newton
    exact h1
  | succ k ih =>
    have hY : newtonSeq A (k + 1) ≤ 2 ^ 129 := ih
    have hge : Nat.sqrt A ≤ newtonSeq A (k + 1) := newtonSeq_ge_sqrt hA k
    have hAY : A / newtonSeq A (k + 1) ≤ Nat.sqrt A + 2 :=
      div_le_sqrt_add_two hAss hge
    have hs : Nat.sqrt A + 2 ≤ 2 ^ 128 + 1 := by omega
    have h2 : (newtonSeq A (k + 1) + A / newtonSeq A (k + 1)) / 2 ≤ 2 ^ 129 := by omega
    show newton A (newtonSeq A (k + 1)) ≤ 2 ^ 129
    unfold newton
    exact h2

/-- One word-level Newton step mirrors the Nat step. -/
theorem wstep {a : U256} {n : Nat} {r : U256}
    (hr : r.toNat = newtonSeq a.toNat n)
    (hno : r.toNat + a.toNat / r.toNat < 2 ^ 256) :
    (newtonStep a r).toNat = newtonSeq a.toNat (n + 1) := by
  rw [toNat_newtonStep _ _ hno, hr]

/-- The Nat-level cascade: seven Newton steps then `min` give the floor. -/
theorem newtonSeq_floor {A : Nat} (hA1 : 1 ≤ A) (hs6 : 6 ≤ Nat.sqrt A)
    (hs128 : Nat.sqrt A < 2 ^ 128)
    (hle : 2 ^ (Nat.log2 A / 2) ≤ Nat.sqrt A)
    (hlt : Nat.sqrt A < 2 * 2 ^ (Nat.log2 A / 2)) :
    Nat.min (newtonSeq A 7) (A / newtonSeq A 7) = Nat.sqrt A := by
  have hA : 0 < A := by omega
  have hspos : 0 < Nat.sqrt A := sqrt_pos hA
  have hY0le : newtonSeq A 0 ≤ Nat.sqrt A := by
    rw [newtonSeq_zero]; exact hle
  have hY0lt : Nat.sqrt A < 2 * newtonSeq A 0 := by
    rw [newtonSeq_zero]; exact hlt
  have hYpos : ∀ n, 0 < newtonSeq A n := newtonSeq_pos hA
  have hYge : ∀ n, Nat.sqrt A ≤ newtonSeq A (n + 1) := newtonSeq_ge_sqrt hA
  have he0 := newton_err_below (x := newtonSeq A 0) (hYpos 0) hY0le
  have q1 : newtonSeq A 1 - Nat.sqrt A ≤ 3 * Nat.sqrt A / 8 + 1 :=
    newton_first (hYpos 0) hY0le hY0lt he0
  have he1 := newton_sub_sqrt_le_sq_div hspos (hYge 0)
  have hJ1 : 2 * 3 * 1 * 8 * Nat.sqrt A + 1 * 1 * 8 * 8 < 2 * 8 * 8 * Nat.sqrt A := by
    omega
  have q2 : newtonSeq A 2 - Nat.sqrt A ≤ 9 * Nat.sqrt A / 128 + 2 :=
    newton_link hspos (by decide) he1 q1 hJ1
  have he2 := newton_sub_sqrt_le_sq_div hspos (hYge 1)
  have hJ2 : 2 * 9 * 2 * 128 * Nat.sqrt A + 2 * 2 * 128 * 128
      < 2 * 128 * 128 * Nat.sqrt A := by omega
  have q3 : newtonSeq A 3 - Nat.sqrt A ≤ 81 * Nat.sqrt A / 32768 + 2 :=
    newton_link hspos (by decide) he2 q2 hJ2
  have he3 := newton_sub_sqrt_le_sq_div hspos (hYge 2)
  have hJ3 : 2 * 81 * 2 * 32768 * Nat.sqrt A + 2 * 2 * 32768 * 32768
      < 2 * 32768 * 32768 * Nat.sqrt A := by omega
  have q4 : newtonSeq A 4 - Nat.sqrt A ≤ 6561 * Nat.sqrt A / 2 ^ 31 + 2 :=
    newton_link hspos (by decide) he3 q3 hJ3
  have he4 := newton_sub_sqrt_le_sq_div hspos (hYge 3)
  have hJ4 : 2 * 6561 * 2 * 2 ^ 31 * Nat.sqrt A + 2 * 2 * 2 ^ 31 * 2 ^ 31
      < 2 * 2 ^ 31 * 2 ^ 31 * Nat.sqrt A := by omega
  have q5 : newtonSeq A 5 - Nat.sqrt A ≤ 43046721 * Nat.sqrt A / 2 ^ 63 + 2 :=
    newton_link hspos (by decide) he4 q4 hJ4
  have he5 := newton_sub_sqrt_le_sq_div hspos (hYge 4)
  have hJ5 : 2 * 43046721 * 2 * 2 ^ 63 * Nat.sqrt A + 2 * 2 * 2 ^ 63 * 2 ^ 63
      < 2 * 2 ^ 63 * 2 ^ 63 * Nat.sqrt A := by omega
  have q6 : newtonSeq A 6 - Nat.sqrt A ≤ 1853020188851841 * Nat.sqrt A / 2 ^ 127 + 2 :=
    newton_link hspos (by decide) he5 q5 hJ5
  have hend : (newtonSeq A 6 - Nat.sqrt A) * (newtonSeq A 6 - Nat.sqrt A) ≤ Nat.sqrt A :=
    cascade_end hs6 hs128 q6
  have hfinal := newton_eq_or_succ (x := newtonSeq A 6) (hYpos 6) (hYge 5) hend
  exact min_div_eq_sqrt (hYpos 7) hfinal

/-- Tiny inputs never overstate: checked by evaluation. -/
theorem tiny_bound1 : ∀ i : Fin 36,
    (sqrt (BitVec.ofNat 256 i.val)).toNat * (sqrt (BitVec.ofNat 256 i.val)).toNat ≤ i.val := by
  decide

/-- Tiny inputs never understate: checked by evaluation. -/
theorem tiny_bound2 : ∀ i : Fin 36,
    i.val < ((sqrt (BitVec.ofNat 256 i.val)).toNat + 1) * ((sqrt (BitVec.ofNat 256 i.val)).toNat + 1) := by
  decide

/-- The master fact on tiny inputs. -/
theorem sqrt_eq_tiny (a : U256) (h : a.toNat ≤ 35) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  have ha : a = BitVec.ofNat 256 a.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have h256 : a.toNat < 2 ^ 256 := Nat.lt_of_le_of_lt h (by decide)
    rw [Nat.mod_eq_of_lt h256]
  have hOA : (BitVec.ofNat 256 a.toNat).toNat = a.toNat := by
    rw [BitVec.toNat_ofNat]
    have h256 : a.toNat < 2 ^ 256 := Nat.lt_of_le_of_lt h (by decide)
    rw [Nat.mod_eq_of_lt h256]
  have h1 := tiny_bound1 ⟨a.toNat, by omega⟩
  have h2 := tiny_bound2 ⟨a.toNat, by omega⟩
  rw [ha, hOA]
  exact (sqrt_eq_of_bounds h1 h2).symm

theorem req_sqrt_not_above : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_backed    : MintBacked sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry
theorem req_newton_budget  : NewtonBudget sqrt :=
  ⟨7, by omega, fun a => rfl⟩

end OzSqrt
