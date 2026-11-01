import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.Sqrt
import ProofForgeFin.Evm.Bits
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

def sqrt : SqrtFn := newtonSqrt 7

/-- The initial Newton iterate on naturals: `2 ^ (log2 n / 2)`. -/
def X0 (n : Nat) : Nat := 2 ^ (Nat.log2 n / 2)

/-- Newton iterates on naturals from `X0`. -/
def XA (n : Nat) : Nat → Nat
  | 0 => X0 n
  | i + 1 => ProofForgeFin.Sqrt.newton n (XA n i)

/-- Square of a halved division: `(X/k)^2 ≤ (X*X)/(k*k)`. -/
theorem divsq_le (X k : Nat) (hk : 0 < k) : (X / k) * (X / k) ≤ (X * X) / (k * k) := by
  have h1 : ((X / k) * k) * ((X / k) * k) ≤ X * X :=
    Nat.mul_le_mul (Nat.div_mul_le_self X k) (Nat.div_mul_le_self X k)
  have e : ((X / k) * k) * ((X / k) * k) = ((X / k) * (X / k)) * (k * k) := by
    ac_rfl
  rw [e] at h1
  have hk2 : 0 < k * k := Nat.mul_pos hk hk
  exact (Nat.le_div_iff_mul_le hk2).mpr h1

/-- `(X/j)*X ≤ (X*X)/j`. -/
theorem upper_mul_le (X j : Nat) (hj : 0 < j) : (X / j) * X ≤ (X * X) / j := by
  have h1 : ((X / j) * X) * j ≤ X * X := by
    have e : ((X / j) * X) * j = ((X / j) * j) * X := by ac_rfl
    rw [e]
    exact Nat.mul_le_mul_right X (Nat.div_mul_le_self X j)
  exact (Nat.le_div_iff_mul_le hj).mpr h1

/-- `(X*X)/j - X ≤ (X/j)*X`. -/
theorem lower_mul_ge (X j : Nat) (hj : 0 < j) : (X * X) / j - X ≤ (X / j) * X := by
  have hdm : j * (X / j) + X % j = X := Nat.div_add_mod X j
  have hlt : X % j < j := Nat.mod_lt X hj
  have ecomm : (X / j) * j = j * (X / j) := Nat.mul_comm _ _
  have h1 : X + 1 ≤ (X / j) * j + j := by omega
  have ex : ((X / j) + 1) * X = (X / j) * X + X := by
    rw [Nat.add_mul, Nat.one_mul]
  have eX1 : (X + 1) * X = X * X + X := by
    rw [Nat.add_mul, Nat.one_mul]
  have eac : ((X / j) * X) * j = ((X / j) * j) * X := by ac_rfl
  have h3 : X * X ≤ (((X / j) + 1) * X) * j := by
    rw [ex, Nat.add_mul, eac]
    by_cases hc : X + 1 ≤ j
    · have g1 : X * X ≤ X * j := Nat.mul_le_mul_left X (by omega)
      have g2 : X * j ≤ ((X / j) * j) * X + X * j := Nat.le_add_left _ _
      omega
    · have hs : (X + 1 - j) * X + j * X = (X + 1) * X := by
        rw [Nat.sub_mul]
        have ec : j * X = X * j := Nat.mul_comm _ _
        have hCX : j * X ≤ (X + 1) * X := Nat.mul_le_mul_right X (by omega)
        omega
      have hm : (X + 1 - j) * X ≤ ((X / j) * j) * X :=
        Nat.mul_le_mul_right X (by omega)
      have ec : j * X = X * j := Nat.mul_comm _ _
      have hGX : j * X ≤ X * X := Nat.mul_le_mul_right X (by omega)
      omega
  have eassoc : (((X / j) + 1) * X) * j = j * (((X / j) + 1) * X) := Nat.mul_comm _ _
  have h4 : (X * X) / j ≤ ((X / j) + 1) * X :=
    (Nat.div_le_iff_le_mul_add_pred hj).mpr (by omega)
  omega

/-- `(X*X)/(X*M) ≤ X/M`. -/
theorem upper_cancel_le (X M : Nat) (hX : 0 < X) (hM : 0 < M) :
    (X * X) / (X * M) ≤ X / M := by
  have hpos : 0 < X * M := Nat.mul_pos hX hM
  have hdm := Nat.div_add_mod X M
  have hlt := Nat.mod_lt X hM
  have h1 : (X / M) * M + X % M = X := by
    have ec : M * (X / M) = (X / M) * M := Nat.mul_comm _ _
    omega
  have g1 : (X / M) * (X * M) = X * ((X / M) * M) := by ac_rfl
  have eC : (X / M) * (X * M) = X * X - X * (X % M) := by
    rw [g1, show (X / M) * M = X - X % M from by omega, Nat.mul_sub]
  have m1 : X * (X % M) ≤ X * (M - 1) :=
    Nat.mul_le_mul_left X (by omega)
  have e2 : X * (M - 1) = X * M - X := by
    rw [Nat.mul_sub, Nat.mul_one]
  have hXm : X * M - X ≤ X * M - 1 := by omega
  have hR : X * (X % M) ≤ X * M - 1 := by omega
  have ecomm2 : (X * M) * (X / M) = (X / M) * (X * M) := Nat.mul_comm _ _
  rw [Nat.div_le_iff_le_mul_add_pred hpos]
  omega

/-- Main quadratic-step estimate: `(X/k)^2/(2*X) ≤ X/(2*(k*k))`. -/
theorem main_term_le (X k : Nat) (hX : 0 < X) (hk : 0 < k) :
    (X / k) * (X / k) / (2 * X) ≤ X / (2 * (k * k)) := by
  have d : (X / k) * (X / k) ≤ (X * X) / (k * k) := divsq_le X k hk
  have step : ((X * X) / (k * k)) / (2 * X) ≤ X / (2 * (k * k)) := by
    rw [Nat.div_div_eq_div_mul]
    have e : (k * k) * (2 * X) = X * (2 * (k * k)) := by ac_rfl
    rw [e]
    exact upper_cancel_le X (2 * (k * k)) hX (by have hkk : 0 < k * k := Nat.mul_pos hk hk; omega)
  exact Nat.le_trans (Nat.div_le_div_right d) step

/-- One quadratic Newton-step error bound. -/
theorem step_le (a x E LB : Nat) (hs : 0 < Nat.sqrt a) (hx : Nat.sqrt a ≤ x)
    (he : x - Nat.sqrt a ≤ E) (hLB : LB ≤ Nat.sqrt a) (hLBpos : 0 < LB) :
    newton a x - Nat.sqrt a ≤ E * E / (2 * LB) + 1 := by
  have hqs := newton_sub_sqrt_le_sq_div hs hx
  have hsq : (x - Nat.sqrt a) * (x - Nat.sqrt a) ≤ E * E := Nat.mul_le_mul he he
  have hd1 : (x - Nat.sqrt a) * (x - Nat.sqrt a) / (2 * Nat.sqrt a) ≤ E * E / (2 * Nat.sqrt a) :=
    Nat.div_le_div_right hsq
  have h2 : 2 * LB ≤ 2 * Nat.sqrt a := by omega
  have hp2 : 0 < 2 * LB := by omega
  have hd2 : E * E / (2 * Nat.sqrt a) ≤ E * E / (2 * LB) :=
    Nat.div_le_div_left h2 hp2
  omega

theorem X0pos (n : Nat) (hn : 0 < n) : 0 < X0 n := by
  unfold X0
  exact Nat.pow_pos (by decide)

theorem X0le (n : Nat) (hn : 0 < n) : X0 n ≤ Nat.sqrt n := by
  unfold X0
  apply le_sqrt_of_mul_self_le
  have h1 : 2 ^ Nat.log2 n ≤ n := (ProofForgeFin.Evm.log2_spec (Nat.pos_iff_ne_zero.mp hn)).1
  have h2 : 2 * (Nat.log2 n / 2) ≤ Nat.log2 n := Nat.mul_div_le _ _
  have h3 : 2 ^ (2 * (Nat.log2 n / 2)) ≤ 2 ^ Nat.log2 n := Nat.pow_le_pow_right (by decide) h2
  have h4 : 2 ^ (Nat.log2 n / 2) * 2 ^ (Nat.log2 n / 2) = 2 ^ (2 * (Nat.log2 n / 2)) := by
    rw [← Nat.pow_add]; congr 1; omega
  omega

theorem slt2 (n : Nat) (hn : 0 < n) : Nat.sqrt n < 2 * X0 n := by
  unfold X0
  apply sqrt_lt_of_lt_mul_self
  have h1 : n < 2 ^ (Nat.log2 n + 1) := (ProofForgeFin.Evm.log2_spec (Nat.pos_iff_ne_zero.mp hn)).2
  have f2 : 2 * 2 ^ (Nat.log2 n / 2) = 2 ^ (Nat.log2 n / 2 + 1) := by
    rw [Nat.pow_succ]; exact Nat.mul_comm _ _
  have e : (2 * 2 ^ (Nat.log2 n / 2)) * (2 * 2 ^ (Nat.log2 n / 2)) = 2 ^ (2 * (Nat.log2 n / 2) + 2) := by
    rw [f2, ← Nat.pow_add]; congr 1; omega
  rw [e]
  exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega))

/-- First Newton step from any iterate below the root: error at most half plus two. -/
theorem e1bound_gen (n x0 : Nat) (hx0 : 0 < x0) (hxs : x0 ≤ Nat.sqrt n)
    (hs2 : Nat.sqrt n < 2 * x0) :
    newton n x0 - Nat.sqrt n ≤ x0 / 2 + 2 := by
  have hs2' : Nat.sqrt n ≤ 2 * x0 - 1 := by omega
  have hd : Nat.sqrt n - x0 ≤ x0 - 1 := by omega
  have herr := newton_err_below hx0 hxs
  have f1 : (Nat.sqrt n - x0) * (Nat.sqrt n - x0) ≤ (x0 - 1) * (x0 - 1) :=
    Nat.mul_le_mul hd hd
  have f2 : (x0 - 1) * (x0 - 1) ≤ (x0 - 1) * x0 :=
    Nat.mul_le_mul_left (x0 - 1) (by omega)
  have f3 : (x0 - 1) * x0 = x0 * x0 - x0 := by
    rw [Nat.sub_mul, Nat.one_mul]
  have f4 : 2 * Nat.sqrt n ≤ 4 * x0 - 2 := by omega
  have f6 : (x0 - 1) * x0 ≤ ((x0 / 2) * 2) * x0 :=
    Nat.mul_le_mul_right x0 (by omega)
  have f7 : (x0 / 2) * (2 * x0) = ((x0 / 2) * 2) * x0 := by
    rw [Nat.mul_assoc]
  have f8 : (x0 / 2 + 2) * (2 * x0) = (x0 / 2) * (2 * x0) + 2 * (2 * x0) :=
    Nat.add_mul _ _ _
  have hpos : 0 < 2 * x0 := by omega
  have g : (newton n x0 - Nat.sqrt n) * (2 * x0) = 2 * x0 * (newton n x0 - Nat.sqrt n) :=
    Nat.mul_comm _ _
  have main : (newton n x0 - Nat.sqrt n) * (2 * x0) ≤ (x0 / 2 + 2) * (2 * x0) := by
    rw [g, f8, f7]
    omega
  exact Nat.le_of_mul_le_mul_right main hpos

/-- Even `log2`: the start is within half of itself below the root. -/
theorem even_d (n m : Nat) (hn : 0 < n) (hm : Nat.log2 n = m + m) (hm3 : 3 ≤ m) :
    Nat.sqrt n - X0 n ≤ X0 n / 2 := by
  have hX : X0 n = 2 ^ m := by
    unfold X0; rw [hm]; congr 1; omega
  have ep : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [Nat.mul_comm 2 (2 ^ (m - 1)), ← Nat.pow_succ]
    show 2 ^ m = 2 ^ ((m - 1) + 1)
    congr 1; omega
  have eq : X0 n / 2 = 2 ^ (m - 1) := by
    have e22 : (2 ^ m) / 2 = 2 ^ (m - 1) := by rw [ep]; omega
    rw [hX, e22]
  have ePQ : (2 ^ m + 2 ^ (m - 1)) * (2 ^ m + 2 ^ (m - 1))
      = (2 ^ (m + m) + 2 ^ (m + (m - 1))) + (2 ^ (m + (m - 1)) + 2 ^ ((m - 1) + (m - 1))) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm (2 ^ (m - 1)) (2 ^ m),
      ← Nat.pow_add (2) m m, ← Nat.pow_add (2) m (m - 1), ← Nat.pow_add (2) (m - 1) (m - 1)]
  have emid : 2 ^ (m + (m - 1)) + 2 ^ (m + (m - 1)) = 2 ^ (m + m) := by
    have h2 : 2 ^ (m + (m - 1)) + 2 ^ (m + (m - 1)) = 2 * 2 ^ (m + (m - 1)) := by omega
    rw [h2, Nat.mul_comm, ← Nat.pow_succ]
    congr 1; omega
  have h2m : 2 ^ (m + m) + 2 ^ (m + m) = 2 ^ (m + m + 1) := by
    have h2 : 2 ^ (m + m) + 2 ^ (m + m) = 2 * 2 ^ (m + m) := by omega
    rw [h2, Nat.mul_comm, ← Nat.pow_succ]
  have hbig : 2 ^ (m + m + 1) ≤ (X0 n + X0 n / 2 + 1) * (X0 n + X0 n / 2 + 1) := by
    have hge : 2 ^ m + 2 ^ (m - 1) + 1 ≤ X0 n + X0 n / 2 + 1 := by
      have e22 : (2 ^ m) / 2 = 2 ^ (m - 1) := by rw [ep]; omega
      have eX : X0 n + X0 n / 2 + 1 = 2 ^ m + 2 ^ (m - 1) + 1 := by rw [hX, e22]
      omega
    have hsq0 : (2 ^ m + 2 ^ (m - 1)) * (2 ^ m + 2 ^ (m - 1))
        ≤ (2 ^ m + 2 ^ (m - 1) + 1) * (2 ^ m + 2 ^ (m - 1) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hsq1 : (2 ^ m + 2 ^ (m - 1)) * (2 ^ m + 2 ^ (m - 1))
        ≤ (X0 n + X0 n / 2 + 1) * (X0 n + X0 n / 2 + 1) :=
      Nat.le_trans hsq0 (Nat.mul_le_mul hge hge)
    have hexp : 2 ^ (m + m) + 2 ^ (m + m)
        ≤ (2 ^ (m + m) + 2 ^ (m + (m - 1))) + (2 ^ (m + (m - 1)) + 2 ^ ((m - 1) + (m - 1))) := by
      have eac : (2 ^ (m + m) + 2 ^ (m + (m - 1))) + (2 ^ (m + (m - 1)) + 2 ^ ((m - 1) + (m - 1)))
          = (2 ^ (m + m) + (2 ^ (m + (m - 1)) + 2 ^ (m + (m - 1)))) + 2 ^ ((m - 1) + (m - 1)) := by
        ac_rfl
      rw [eac, emid]
      exact Nat.le_add_right _ _
    have htot : (2 ^ (m + m) + 2 ^ (m + (m - 1))) + (2 ^ (m + (m - 1)) + 2 ^ ((m - 1) + (m - 1)))
        ≤ (X0 n + X0 n / 2 + 1) * (X0 n + X0 n / 2 + 1) := by
      rw [← ePQ]; exact hsq1
    rw [← h2m]
    exact Nat.le_trans hexp htot
  have h1 : n < 2 ^ (Nat.log2 n + 1) :=
    (ProofForgeFin.Evm.log2_spec (Nat.pos_iff_ne_zero.mp hn)).2
  have h2 : 2 ^ (Nat.log2 n + 1) ≤ (X0 n + X0 n / 2 + 1) * (X0 n + X0 n / 2 + 1) := by
    rw [hm]; exact hbig
  have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hlt : Nat.sqrt n * Nat.sqrt n < (X0 n + X0 n / 2 + 1) * (X0 n + X0 n / 2 + 1) := by
    omega
  have hlt2 : Nat.sqrt n < X0 n + X0 n / 2 + 1 :=
    lt_of_mul_self_lt_mul_self hlt
  omega

theorem X0eq (n m : Nat) (hm : Nat.log2 n = m + m) : X0 n = 2 ^ m := by
  unfold X0; rw [hm]; congr 1; omega

/-- Even `log2`: first Newton error at most an eighth plus three. -/
theorem e1even (n m : Nat) (hn : 0 < n) (hm : Nat.log2 n = m + m) (hm3 : 3 ≤ m) :
    newton n (X0 n) - Nat.sqrt n ≤ X0 n / 8 + 3 := by
  have hX : X0 n = 2 ^ m := X0eq n m hm
  have hx0 : 0 < X0 n := X0pos n hn
  have hxs : X0 n ≤ Nat.sqrt n := X0le n hn
  have hs2 : Nat.sqrt n < 2 * X0 n := slt2 n hn
  have hd : Nat.sqrt n - X0 n ≤ X0 n / 2 := even_d n m hn hm hm3
  have herr := newton_err_below hx0 hxs
  have f1 : (Nat.sqrt n - X0 n) * (Nat.sqrt n - X0 n) ≤ (X0 n / 2) * (X0 n / 2) :=
    Nat.mul_le_mul hd hd
  have f1b : (X0 n / 2) * (X0 n / 2) ≤ (X0 n * X0 n) / 4 := by
    have d := divsq_le (X0 n) 2 (by decide)
    rw [show (2 * 2 : Nat) = 4 from rfl] at d
    exact d
  have hs2' : Nat.sqrt n ≤ 2 * X0 n - 1 := by omega
  have f4 : 2 * Nat.sqrt n ≤ 4 * X0 n - 2 := by omega
  have h_a : X0 n / 4 - 1 ≤ 2 * (X0 n / 8) := by omega
  have e_ac : (X0 n / 8) * (2 * X0 n) = X0 n * (2 * (X0 n / 8)) := by ac_rfl
  have h_b : X0 n * (X0 n / 4 - 1) ≤ X0 n * (2 * (X0 n / 8)) :=
    Nat.mul_le_mul_left (X0 n) h_a
  have h_c : X0 n * (X0 n / 4 - 1) = X0 n * (X0 n / 4) - X0 n := by
    rw [Nat.mul_sub, Nat.mul_one]
  have h_d : (X0 n * X0 n) / 4 - X0 n ≤ (X0 n / 4) * X0 n :=
    lower_mul_ge (X0 n) 4 (by decide)
  have h_d' : X0 n * (X0 n / 4) ≥ (X0 n * X0 n) / 4 - X0 n := by
    have ec : X0 n * (X0 n / 4) = (X0 n / 4) * X0 n := Nat.mul_comm _ _
    omega
  have hpos : 0 < 2 * X0 n := by omega
  have g : (newton n (X0 n) - Nat.sqrt n) * (2 * X0 n)
      = 2 * X0 n * (newton n (X0 n) - Nat.sqrt n) := Nat.mul_comm _ _
  have f8 : (X0 n / 8 + 3) * (2 * X0 n) = (X0 n / 8) * (2 * X0 n) + 3 * (2 * X0 n) :=
    Nat.add_mul _ _ _
  have main : (newton n (X0 n) - Nat.sqrt n) * (2 * X0 n) ≤ (X0 n / 8 + 3) * (2 * X0 n) := by
    rw [g, f8, e_ac]
    omega
  exact Nat.le_of_mul_le_mul_right main hpos

/-- Even chain, second step. -/
theorem stepF2_even (n x X : Nat) (hs : 0 < Nat.sqrt n) (hx : Nat.sqrt n ≤ x)
    (he : x - Nat.sqrt n ≤ X / 8 + 3) (hLB : X ≤ Nat.sqrt n) (hXpos : 0 < X) (hX8 : 8 ≤ X) :
    newton n x - Nat.sqrt n ≤ X / 64 + 2 := by
  have h1 := step_le n x (X / 8 + 3) X hs hx he hLB hXpos
  have e_exp : (X / 8 + 3) * (X / 8 + 3)
      = (X / 8) * (X / 8) + (X / 8) * 3 + (3 * (X / 8) + 3 * 3) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  have d1 : (X / 8) * (X / 8) ≤ (X * X) / 64 := by
    have d := divsq_le X 8 (by omega)
    rw [show (8 * 8 : Nat) = 64 from rfl] at d
    exact d
  have m1 : 1 ≤ (X * X) / 64 := by
    have h64 : 64 ≤ X * X := by
      have h4 := Nat.mul_le_mul hX8 hX8
      omega
    have h : 64 / 64 ≤ (X * X) / 64 := Nat.div_le_div_right h64
    omega
  have e_rhs : (X / 64 + 1) * (2 * X) = (X / 64) * (2 * X) + 2 * X := by
    rw [Nat.add_mul, Nat.one_mul]
  have ecomm : (2 * X) * (X / 64 + 1) = (X / 64 + 1) * (2 * X) := Nat.mul_comm _ _
  have e_ac : (X / 64) * (2 * X) = 2 * ((X / 64) * X) := by ac_rfl
  have h_lo : 2 * (((X * X) / 64) - X) ≤ 2 * ((X / 64) * X) :=
    Nat.mul_le_mul_left 2 (lower_mul_ge X 64 (by decide))
  have hpos : 0 < 2 * X := by omega
  have step : (X / 8 + 3) * (X / 8 + 3) / (2 * X) ≤ X / 64 + 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hpos]
    omega
  omega

/-- Even chain, third step. -/
theorem stepF3_even (n x X : Nat) (hs : 0 < Nat.sqrt n) (hx : Nat.sqrt n ≤ x)
    (he : x - Nat.sqrt n ≤ X / 64 + 2) (hLB : X ≤ Nat.sqrt n) (hXpos : 0 < X) (hX8 : 8 ≤ X) :
    newton n x - Nat.sqrt n ≤ X / 8192 + 2 := by
  have h1 := step_le n x (X / 64 + 2) X hs hx he hLB hXpos
  have e_exp : (X / 64 + 2) * (X / 64 + 2)
      = (X / 64) * (X / 64) + (X / 64) * 2 + (2 * (X / 64) + 2 * 2) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  have d1 : (X / 64) * (X / 64) ≤ (X * X) / 4096 := by
    have d := divsq_le X 64 (by omega)
    rw [show (64 * 64 : Nat) = 4096 from rfl] at d
    exact d
  have m2 : (X * X) / 4096 ≤ 2 * ((X * X) / 8192) + 1 := by omega
  have e_rhs : (X / 8192 + 1) * (2 * X) = (X / 8192) * (2 * X) + 2 * X := by
    rw [Nat.add_mul, Nat.one_mul]
  have ecomm : (2 * X) * (X / 8192 + 1) = (X / 8192 + 1) * (2 * X) := Nat.mul_comm _ _
  have e_ac : (X / 8192) * (2 * X) = 2 * ((X / 8192) * X) := by ac_rfl
  have h_lo : 2 * (((X * X) / 8192) - X) ≤ 2 * ((X / 8192) * X) :=
    Nat.mul_le_mul_left 2 (lower_mul_ge X 8192 (by decide))
  have hpos : 0 < 2 * X := by omega
  have step : (X / 64 + 2) * (X / 64 + 2) / (2 * X) ≤ X / 8192 + 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hpos]
    omega
  omega

/-- Even chain, fourth step. -/
theorem stepF4_even (n x X : Nat) (hs : 0 < Nat.sqrt n) (hx : Nat.sqrt n ≤ x)
    (he : x - Nat.sqrt n ≤ X / 8192 + 2) (hLB : X ≤ Nat.sqrt n) (hXpos : 0 < X) (hX8 : 8 ≤ X) :
    newton n x - Nat.sqrt n ≤ X / 2 ^ 27 + 2 := by
  have h1 := step_le n x (X / 8192 + 2) X hs hx he hLB hXpos
  have e_exp : (X / 8192 + 2) * (X / 8192 + 2)
      = (X / 8192) * (X / 8192) + (X / 8192) * 2 + (2 * (X / 8192) + 2 * 2) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  have d1 : (X / 8192) * (X / 8192) ≤ (X * X) / 2 ^ 26 := by
    have d := divsq_le X 8192 (by omega)
    rw [show (8192 * 8192 : Nat) = 2 ^ 26 from by decide] at d
    exact d
  have m2 : (X * X) / 2 ^ 26 ≤ 2 * ((X * X) / 2 ^ 27) + 1 := by omega
  have e_rhs : (X / 2 ^ 27 + 1) * (2 * X) = (X / 2 ^ 27) * (2 * X) + 2 * X := by
    rw [Nat.add_mul, Nat.one_mul]
  have ecomm : (2 * X) * (X / 2 ^ 27 + 1) = (X / 2 ^ 27 + 1) * (2 * X) := Nat.mul_comm _ _
  have e_ac : (X / 2 ^ 27) * (2 * X) = 2 * ((X / 2 ^ 27) * X) := by ac_rfl
  have h_lo : 2 * (((X * X) / 2 ^ 27) - X) ≤ 2 * ((X / 2 ^ 27) * X) :=
    Nat.mul_le_mul_left 2 (lower_mul_ge X (2 ^ 27) (by decide))
  have hpos : 0 < 2 * X := by omega
  have step : (X / 8192 + 2) * (X / 8192 + 2) / (2 * X) ≤ X / 2 ^ 27 + 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hpos]
    omega
  omega

/-- Even chain, fifth step. -/
theorem stepF5_even (n x X : Nat) (hs : 0 < Nat.sqrt n) (hx : Nat.sqrt n ≤ x)
    (he : x - Nat.sqrt n ≤ X / 2 ^ 27 + 2) (hLB : X ≤ Nat.sqrt n) (hXpos : 0 < X) (hX8 : 8 ≤ X) :
    newton n x - Nat.sqrt n ≤ X / 2 ^ 55 + 2 := by
  have h1 := step_le n x (X / 2 ^ 27 + 2) X hs hx he hLB hXpos
  have e_exp : (X / 2 ^ 27 + 2) * (X / 2 ^ 27 + 2)
      = (X / 2 ^ 27) * (X / 2 ^ 27) + (X / 2 ^ 27) * 2 + (2 * (X / 2 ^ 27) + 2 * 2) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  have d1 : (X / 2 ^ 27) * (X / 2 ^ 27) ≤ (X * X) / 2 ^ 54 := by
    have d := divsq_le X (2 ^ 27) (Nat.pow_pos (by decide))
    rw [show ((2 ^ 27) * (2 ^ 27) : Nat) = 2 ^ 54 from by decide] at d
    exact d
  have m2 : (X * X) / 2 ^ 54 ≤ 2 * ((X * X) / 2 ^ 55) + 1 := by omega
  have e_rhs : (X / 2 ^ 55 + 1) * (2 * X) = (X / 2 ^ 55) * (2 * X) + 2 * X := by
    rw [Nat.add_mul, Nat.one_mul]
  have ecomm : (2 * X) * (X / 2 ^ 55 + 1) = (X / 2 ^ 55 + 1) * (2 * X) := Nat.mul_comm _ _
  have e_ac : (X / 2 ^ 55) * (2 * X) = 2 * ((X / 2 ^ 55) * X) := by ac_rfl
  have h_lo : 2 * (((X * X) / 2 ^ 55) - X) ≤ 2 * ((X / 2 ^ 55) * X) :=
    Nat.mul_le_mul_left 2 (lower_mul_ge X (2 ^ 55) (by decide))
  have hpos : 0 < 2 * X := by omega
  have step : (X / 2 ^ 27 + 2) * (X / 2 ^ 27 + 2) / (2 * X) ≤ X / 2 ^ 55 + 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hpos]
    omega
  omega

/-- Odd `log2`: `X + X/4 + X/8` is below the root. -/
theorem oddLB (n m : Nat) (hn : 0 < n) (hm : Nat.log2 n = 2 * m + 1) (hm3 : 3 ≤ m) :
    X0 n + X0 n / 4 + X0 n / 8 ≤ Nat.sqrt n := by
  have hX : X0 n = 2 ^ m := by
    unfold X0; rw [hm]
    have : (2 * m + 1) / 2 = m := by omega
    rw [this]
  have hX4 : X0 n / 4 = 2 ^ (m - 2) := by
    have ep : 2 ^ m = 4 * 2 ^ (m - 2) := by
      have e4 : (4 : Nat) = 2 ^ 2 := rfl
      rw [e4, ← Nat.pow_add]
      congr 1; omega
    have e22 : (2 ^ m) / 4 = 2 ^ (m - 2) := by rw [ep]; omega
    rw [hX, e22]
  have hX8 : X0 n / 8 = 2 ^ (m - 3) := by
    have ep : 2 ^ m = 8 * 2 ^ (m - 3) := by
      have e8 : (8 : Nat) = 2 ^ 3 := rfl
      rw [e8, ← Nat.pow_add]
      congr 1; omega
    have e22 : (2 ^ m) / 8 = 2 ^ (m - 3) := by rw [ep]; omega
    rw [hX, e22]
  have hP : (8 : Nat) * 2 ^ (m - 3) = 2 ^ m := by
    have e8 : (8 : Nat) = 2 ^ 3 := rfl
    rw [e8, ← Nat.pow_add]
    congr 1; omega
  have hQ : (2 : Nat) * 2 ^ (m - 3) = 2 ^ (m - 2) := by
    rw [Nat.mul_comm, ← Nat.pow_succ]
    congr 1; omega
  have hLB : X0 n + X0 n / 4 + X0 n / 8 = 11 * 2 ^ (m - 3) := by
    rw [hX4, hX8, hX, ← hP, ← hQ]
    omega
  have e11 : (11 * 2 ^ (m - 3)) * (11 * 2 ^ (m - 3)) = 121 * (2 ^ (m - 3) * 2 ^ (m - 3)) := by
    have e : (11 * 2 ^ (m - 3)) * (11 * 2 ^ (m - 3)) = (11 * 11) * (2 ^ (m - 3) * 2 ^ (m - 3)) := by
      ac_rfl
    rw [e]
  have eYY : 2 ^ (m - 3) * 2 ^ (m - 3) = 2 ^ (2 * (m - 3)) := by
    rw [← Nat.pow_add]
    congr 1; omega
  have h121 : (121 : Nat) * 2 ^ (2 * (m - 3)) ≤ 128 * 2 ^ (2 * (m - 3)) := by
    apply Nat.mul_le_mul_right
    decide
  have e128 : (128 : Nat) * 2 ^ (2 * (m - 3)) = 2 ^ (2 * m + 1) := by
    have e7 : (128 : Nat) = 2 ^ 7 := rfl
    rw [e7, ← Nat.pow_add]
    congr 1; omega
  have h1 : 2 ^ (2 * m + 1) ≤ n := by
    have h := (ProofForgeFin.Evm.log2_spec (Nat.pos_iff_ne_zero.mp hn)).1
    rw [hm] at h
    exact h
  have h2 : (X0 n + X0 n / 4 + X0 n / 8) * (X0 n + X0 n / 4 + X0 n / 8) ≤ n := by
    have h3 : (X0 n + X0 n / 4 + X0 n / 8) * (X0 n + X0 n / 4 + X0 n / 8)
        ≤ 128 * 2 ^ (2 * (m - 3)) := by
      rw [hLB, e11, eYY]
      exact h121
    exact Nat.le_trans h3 (by rw [e128]; exact h1)
  exact le_sqrt_of_mul_self_le h2

/-- Even chain, sixth step. -/
theorem stepF6_even (n x X : Nat) (hs : 0 < Nat.sqrt n) (hx : Nat.sqrt n ≤ x)
    (he : x - Nat.sqrt n ≤ X / 2 ^ 55 + 2) (hLB : X ≤ Nat.sqrt n) (hXpos : 0 < X) (hX8 : 8 ≤ X) :
    newton n x - Nat.sqrt n ≤ X / 2 ^ 111 + 2 := by
  have h1 := step_le n x (X / 2 ^ 55 + 2) X hs hx he hLB hXpos
  have e_exp : (X / 2 ^ 55 + 2) * (X / 2 ^ 55 + 2)
      = (X / 2 ^ 55) * (X / 2 ^ 55) + (X / 2 ^ 55) * 2 + (2 * (X / 2 ^ 55) + 2 * 2) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  have d1 : (X / 2 ^ 55) * (X / 2 ^ 55) ≤ (X * X) / 2 ^ 110 := by
    have d := divsq_le X (2 ^ 55) (Nat.pow_pos (by decide))
    rw [show ((2 ^ 55) * (2 ^ 55) : Nat) = 2 ^ 110 from by decide] at d
    exact d
  have m2 : (X * X) / 2 ^ 110 ≤ 2 * ((X * X) / 2 ^ 111) + 1 := by omega
  have e_rhs : (X / 2 ^ 111 + 1) * (2 * X) = (X / 2 ^ 111) * (2 * X) + 2 * X := by
    rw [Nat.add_mul, Nat.one_mul]
  have ecomm : (2 * X) * (X / 2 ^ 111 + 1) = (X / 2 ^ 111 + 1) * (2 * X) := Nat.mul_comm _ _
  have e_ac : (X / 2 ^ 111) * (2 * X) = 2 * ((X / 2 ^ 111) * X) := by ac_rfl
  have h_lo : 2 * (((X * X) / 2 ^ 111) - X) ≤ 2 * ((X / 2 ^ 111) * X) :=
    Nat.mul_le_mul_left 2 (lower_mul_ge X (2 ^ 111) (by decide))
  have hpos : 0 < 2 * X := by omega
  have step : (X / 2 ^ 55 + 2) * (X / 2 ^ 55 + 2) / (2 * X) ≤ X / 2 ^ 111 + 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hpos]
    omega
  omega

/-- A Newton step from a positive point stays positive. -/
theorem newton_pos (a x : Nat) (ha : 0 < a) (hx : 0 < x) : 0 < newton a x := by
  unfold newton
  have hdx : 0 ≤ a / x := Nat.zero_le _
  have h1 : 1 ≤ x + a / x := by omega
  have hne : x + a / x ≠ 1 := by
    intro hc
    have hx1 : x = 1 := by omega
    subst hx1
    rw [Nat.div_one] at hc
    omega
  omega

/-- Odd chain, second step: from `X/2+2` to `X/8+2`. -/
theorem stepF2_odd (n x X : Nat) (hs : 0 < Nat.sqrt n) (hx : Nat.sqrt n ≤ x)
    (he : x - Nat.sqrt n ≤ X / 2 + 2) (hLB : X ≤ Nat.sqrt n) (hXpos : 0 < X) (hX8 : 8 ≤ X) :
    newton n x - Nat.sqrt n ≤ X / 8 + 3 := by
  have h1 := step_le n x (X / 2 + 2) X hs hx he hLB hXpos
  have e_exp : (X / 2 + 2) * (X / 2 + 2)
      = (X / 2) * (X / 2) + (X / 2) * 2 + (2 * (X / 2) + 2 * 2) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  have d1 : (X / 2) * (X / 2) ≤ (X * X) / 4 := by
    have d := divsq_le X 2 (by omega)
    rw [show (2 * 2 : Nat) = 4 from rfl] at d
    exact d
  have m1 : 1 ≤ (X * X) / 4 := by
    have h16 : 16 ≤ X * X := by
      have h4 := Nat.mul_le_mul hX8 hX8
      omega
    have h : 16 / 4 ≤ (X * X) / 4 := Nat.div_le_div_right h16
    omega
  have m2 : (X * X) / 4 ≤ 2 * ((X * X) / 8) + 1 := by omega
  have e_rhs : (X / 8 + 2) * (2 * X) = (X / 8) * (2 * X) + 2 * (2 * X) := by
    rw [Nat.add_mul]
  have ecomm : (2 * X) * (X / 8 + 2) = (X / 8 + 2) * (2 * X) := Nat.mul_comm _ _
  have e_ac : (X / 8) * (2 * X) = 2 * ((X / 8) * X) := by ac_rfl
  have h_lo : 2 * (((X * X) / 8) - X) ≤ 2 * ((X / 8) * X) :=
    Nat.mul_le_mul_left 2 (lower_mul_ge X 8 (by decide))
  have h_nt : X ≤ (X * X) / 8 := by
    have h8x : 8 * X ≤ X * X := Nat.mul_le_mul_right X hX8
    have h : 8 * X / 8 ≤ (X * X) / 8 := Nat.div_le_div_right h8x
    omega
  have hpos : 0 < 2 * X := by omega
  have step : (X / 2 + 2) * (X / 2 + 2) / (2 * X) ≤ X / 8 + 2 := by
    rw [Nat.div_le_iff_le_mul_add_pred hpos]
    omega
  omega

/-- Final Newton step: from error `X/2^111+2`, the squared error is below the root. -/
theorem stepFinal (n x X : Nat) (hs : 0 < Nat.sqrt n) (hx : Nat.sqrt n ≤ x)
    (he : x - Nat.sqrt n ≤ X / 2 ^ 111 + 2) (hLB : X ≤ Nat.sqrt n)
    (hX8 : 8 ≤ X) (hXcap : X ≤ 2 ^ 127) :
    (x - Nat.sqrt n) * (x - Nat.sqrt n) ≤ Nat.sqrt n := by
  have hE2 : (x - Nat.sqrt n) * (x - Nat.sqrt n) ≤ (X / 2 ^ 111 + 2) * (X / 2 ^ 111 + 2) :=
    Nat.mul_le_mul he he
  have hEX : (X / 2 ^ 111 + 2) * (X / 2 ^ 111 + 2) ≤ X := by
    by_cases hA : X < 2 ^ 111
    · have hz : X / 2 ^ 111 = 0 := Nat.div_eq_of_lt hA
      rw [hz]
      omega
    · have hA' : 2 ^ 111 ≤ X := by omega
      by_cases hB : X < 2 ^ 112
      · have h1 : X / 2 ^ 111 ≤ 1 := by omega
        have h9 : (X / 2 ^ 111 + 2) * (X / 2 ^ 111 + 2) ≤ 9 := by
          have hle : X / 2 ^ 111 + 2 ≤ 3 := by omega
          have hle2 := Nat.mul_le_mul hle hle
          omega
        omega
      · have hB' : 2 ^ 112 ≤ X := by omega
        have h2 : 2 ≤ X / 2 ^ 111 := by omega
        have hE1 : X / 2 ^ 111 + 2 ≤ 2 * (X / 2 ^ 111) := by omega
        have hE2 : 2 * (X / 2 ^ 111) ≤ X / 2 ^ 110 := by omega
        have hE3 : X / 2 ^ 110 ≤ 2 ^ 17 := by omega
        have hE4 : (X / 2 ^ 111 + 2) * (X / 2 ^ 111 + 2) ≤ 2 ^ 34 := by
          have hle : X / 2 ^ 111 + 2 ≤ 2 ^ 17 := by omega
          have hle2 := Nat.mul_le_mul hle hle
          rwa [show (2 ^ 17) * (2 ^ 17) = 2 ^ 34 from by rw [← Nat.pow_add]] at hle2
        omega
  omega

/-- Small inputs: the bound form of the conclusion, proved by kernel computation. -/
theorem smallBound : ∀ m, m < 64 →
    (Nat.min (XA m 7) (m / XA m 7)) * (Nat.min (XA m 7) (m / XA m 7)) ≤ m ∧
    m < (Nat.min (XA m 7) (m / XA m 7) + 1) * (Nat.min (XA m 7) (m / XA m 7) + 1) := by
  decide

/-- The natural-number iteration reaches the floor square root. -/
theorem natMain (n : Nat) (hn : 0 < n) (hcap : n < 2 ^ 256) :
    Nat.min (XA n 7) (n / XA n 7) = Nat.sqrt n := by
  have hs : 0 < Nat.sqrt n := sqrt_pos hn
  have hXpos : 0 < X0 n := X0pos n hn
  have hXle : X0 n ≤ Nat.sqrt n := X0le n hn
  have hs2 : Nat.sqrt n < 2 * X0 n := slt2 n hn
  have hL : Nat.log2 n < 256 := by
    by_contra hcon
    have h256 : 256 ≤ Nat.log2 n := by omega
    have h2L : 2 ^ 256 ≤ 2 ^ Nat.log2 n := Nat.pow_le_pow_right (by decide) h256
    have h1 := (ProofForgeFin.Evm.log2_spec (Nat.pos_iff_ne_zero.mp hn)).1
    omega
  have XApos : ∀ i, 0 < XA n i := by
    intro i
    induction i with
    | zero => exact X0pos n hn
    | succ i ih => exact newton_pos n (XA n i) hn ih
  have XAabove : ∀ i, Nat.sqrt n ≤ XA n (i + 1) := fun i => sqrt_le_newton (XApos i)
  by_cases hsmall : Nat.log2 n ≤ 5
  · have hn64 : n < 64 := by
      have h1 := (ProofForgeFin.Evm.log2_spec (Nat.pos_iff_ne_zero.mp hn)).2
      have h2 : 2 ^ (Nat.log2 n + 1) ≤ 64 := by
        have hle : Nat.log2 n + 1 ≤ 6 := by omega
        calc 2 ^ (Nat.log2 n + 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hle
          _ = 64 := rfl
      omega
    have hb := smallBound n hn64
    rw [eq_sqrt_iff]
    exact hb
  · have h6 : 6 ≤ Nat.log2 n := by omega
    have hX8 : 8 ≤ X0 n := by
      have hm3 : 3 ≤ Nat.log2 n / 2 := by omega
      have h8 : 2 ^ 3 ≤ 2 ^ (Nat.log2 n / 2) := Nat.pow_le_pow_right (by decide) hm3
      have hXe : X0 n = 2 ^ (Nat.log2 n / 2) := by unfold X0; rfl
      omega
    have hXcap : X0 n ≤ 2 ^ 127 := by
      have hmcap : Nat.log2 n / 2 ≤ 127 := by omega
      have h8 : 2 ^ (Nat.log2 n / 2) ≤ 2 ^ 127 := Nat.pow_le_pow_right (by decide) hmcap
      have hXe : X0 n = 2 ^ (Nat.log2 n / 2) := by unfold X0; rfl
      omega
    by_cases hpar : Nat.log2 n % 2 = 0
    · obtain ⟨m, hm⟩ : ∃ m, Nat.log2 n = m + m := ⟨Nat.log2 n / 2, by omega⟩
      have hm3 : 3 ≤ m := by omega
      have e1 : newton n (X0 n) - Nat.sqrt n ≤ X0 n / 8 + 3 := e1even n m hn hm hm3
      have e2 := stepF2_even n (XA n 1) (X0 n) hs (XAabove 0) e1 hXle hXpos hX8
      have e3 := stepF3_even n (XA n 2) (X0 n) hs (XAabove 1) e2 hXle hXpos hX8
      have e4 := stepF4_even n (XA n 3) (X0 n) hs (XAabove 2) e3 hXle hXpos hX8
      have e5 := stepF5_even n (XA n 4) (X0 n) hs (XAabove 3) e4 hXle hXpos hX8
      have e6 := stepF6_even n (XA n 5) (X0 n) hs (XAabove 4) e5 hXle hXpos hX8
      have ef := stepFinal n (XA n 6) (X0 n) hs (XAabove 5) e6 hXle hX8 hXcap
      have hdisj := newton_eq_or_succ (XApos 6) (XAabove 5) ef
      have h7 : XA n 7 = Nat.sqrt n ∨
          (XA n 7 = Nat.sqrt n + 1 ∧ Nat.sqrt n * (Nat.sqrt n + 1) ≤ n) := hdisj
      exact min_div_eq_sqrt (XApos 7) h7
    · have hodd : Nat.log2 n % 2 = 1 := by omega
      obtain ⟨m, hm⟩ : ∃ m, Nat.log2 n = 2 * m + 1 := ⟨Nat.log2 n / 2, by omega⟩
      have hm3 : 3 ≤ m := by omega
      have e1 : newton n (X0 n) - Nat.sqrt n ≤ X0 n / 2 + 2 :=
        e1bound_gen n (X0 n) hXpos hXle hs2
      have e2 := stepF2_odd n (XA n 1) (X0 n) hs (XAabove 0) e1 hXle hXpos hX8
      have e3 := stepF2_even n (XA n 2) (X0 n) hs (XAabove 1) e2 hXle hXpos hX8
      have e4 := stepF3_even n (XA n 3) (X0 n) hs (XAabove 2) e3 hXle hXpos hX8
      have e5 := stepF4_even n (XA n 4) (X0 n) hs (XAabove 3) e4 hXle hXpos hX8
      have e6 := stepF5_even n (XA n 5) (X0 n) hs (XAabove 4) e5 hXle hXpos hX8
      have e7 := stepF6_even n (XA n 6) (X0 n) hs (XAabove 5) e6 hXle hXpos hX8
      have ef := stepFinal n (XA n 7) (X0 n) hs (XAabove 6) e7 hXle hX8 hXcap
      have hdisj := newton_eq_or_succ (XApos 7) (XAabove 6) ef
      have h8 : XA n 8 = Nat.sqrt n ∨
          (XA n 8 = Nat.sqrt n + 1 ∧ Nat.sqrt n * (Nat.sqrt n + 1) ≤ n) := hdisj
      exact min_div_eq_sqrt (XApos 8) h8

theorem req_sqrt_not_above : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_backed    : MintBacked sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry
theorem req_newton_budget  : NewtonBudget sqrt := sorry

end OzSqrt
