import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.Sqrt
import ProofForgeFin.Word
import ProofForgeFin.Evm.Bits
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
        return min(result, a / result);
    }
}
```
-/
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

theorem x0_eq (a : U256) : ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (Nat.log2 a.toNat / 2) := by
  have hbb : ((1 : U256) <<< (log2 a >>> 1)) = ((1 : U256) <<< (log2 a >>> 1).toNat) := by simp
  rw [hbb]
  have hlog : (log2 a).toNat = Nat.log2 a.toNat := toNat_log2 a
  have hlt : Nat.log2 a.toNat < 256 := by
    by_cases h : a.toNat = 0
    · simp [h]
    · exact (ProofForgeFin.Evm.log2_lt_iff (hn := h)).mpr (a.isLt)
  have hshr : (log2 a >>> 1).toNat = (log2 a).toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hk : (log2 a >>> 1).toNat ≤ 127 := by omega
  have hexp : (1 : U256).toNat * 2 ^ (log2 a >>> 1).toNat < 2 ^ 256 := by
    have h1 : (1 : U256).toNat = 1 := by decide
    rw [h1]
    simp
    calc 2 ^ (log2 a >>> 1).toNat ≤ 2 ^ 127 := Nat.pow_le_pow_right (by decide) hk
    _ < 2 ^ 256 := by decide
  have hsh := ProofForgeFin.toNat_shiftLeft_of_lt (1 : U256) ((log2 a >>> 1).toNat) hexp
  have h1 : (1 : U256).toNat = 1 := by decide
  rw [hsh, h1] at ⊢
  simp at ⊢
  rw [hlog]
  simp [Nat.shiftRight_eq_div_pow]

theorem x0_sq_le (a : U256) (ha : 0 < a.toNat) : (2 ^ (Nat.log2 a.toNat / 2)) * (2 ^ (Nat.log2 a.toNat / 2)) ≤ a.toNat := by
  have hspec := ProofForgeFin.Evm.log2_spec (hn := (by omega : a.toNat ≠ 0))
  have hle : 2 * (Nat.log2 a.toNat / 2) ≤ Nat.log2 a.toNat := Nat.mul_div_le _ _
  calc (2 ^ (Nat.log2 a.toNat / 2)) * (2 ^ (Nat.log2 a.toNat / 2))
      = 2 ^ (Nat.log2 a.toNat / 2 + Nat.log2 a.toNat / 2) := by rw [← Nat.pow_add]
    _ = 2 ^ (2 * (Nat.log2 a.toNat / 2)) := by congr 1; omega
    _ ≤ 2 ^ Nat.log2 a.toNat := Nat.pow_le_pow_right (by decide) hle
    _ ≤ a.toNat := hspec.1

theorem a_lt_four_x0 (a : U256) (ha : 0 < a.toNat) :
    a.toNat < 4 * ((2 ^ (Nat.log2 a.toNat / 2)) * (2 ^ (Nat.log2 a.toNat / 2))) := by
  have hspec := ProofForgeFin.Evm.log2_spec (hn := (by omega : a.toNat ≠ 0))
  have h2 : Nat.log2 a.toNat + 1 ≤ 2 * (Nat.log2 a.toNat / 2) + 2 := by omega
  have h3 : (2 : Nat) ^ (Nat.log2 a.toNat + 1) ≤ 2 ^ (2 * (Nat.log2 a.toNat / 2) + 2) :=
    Nat.pow_le_pow_right (by decide) h2
  have h4 : (2 : Nat) ^ (2 * (Nat.log2 a.toNat / 2) + 2) = 4 * ((2 ^ (Nat.log2 a.toNat / 2)) * (2 ^ (Nat.log2 a.toNat / 2))) := by
    have e : 2 * (Nat.log2 a.toNat / 2) + 2 = (Nat.log2 a.toNat / 2 + Nat.log2 a.toNat / 2) + 2 := by omega
    rw [e, Nat.pow_add, Nat.pow_add]
    simp [Nat.mul_comm]
  omega

theorem dbl (n : Nat) : 2 * 2 ^ n = 2 ^ (n + 1) := by
  rw [Nat.pow_succ]; exact Nat.mul_comm _ _

theorem step_above (a x B B' : Nat) (hx : 0 < x)
    (hle : Nat.sqrt a ≤ x) (he : x - Nat.sqrt a ≤ B)
    (hBs : B * B + 2 * Nat.sqrt a < (B' + 1) * (2 * Nat.sqrt a)) :
    ProofForgeFin.Sqrt.newton a x - Nat.sqrt a ≤ B' := by
  have herr := ProofForgeFin.Sqrt.newton_err_above (a := a) (x := x) hx hle
  have hsq := ProofForgeFin.Sqrt.mul_self_le_mul_self he
  have h2sx : 2 * Nat.sqrt a ≤ 2 * x := by omega
  have e1 : 2 * Nat.sqrt a * (ProofForgeFin.Sqrt.newton a x - Nat.sqrt a)
      ≤ 2 * x * (ProofForgeFin.Sqrt.newton a x - Nat.sqrt a) :=
    Nat.mul_le_mul h2sx (Nat.le_refl _)
  have hcomb : 2 * Nat.sqrt a * (ProofForgeFin.Sqrt.newton a x - Nat.sqrt a)
      < (B' + 1) * (2 * Nat.sqrt a) := by omega
  have heq : (B' + 1) * (2 * Nat.sqrt a) = 2 * Nat.sqrt a * (B' + 1) := Nat.mul_comm _ _
  rw [heq] at hcomb
  have hlt : ProofForgeFin.Sqrt.newton a x - Nat.sqrt a < B' + 1 :=
    Nat.lt_of_mul_lt_mul_left hcomb
  omega

theorem step_below (a x E B1 : Nat) (hx : 0 < x)
    (hle : x ≤ Nat.sqrt a) (he : Nat.sqrt a - x ≤ E)
    (hE : E * E + 2 * Nat.sqrt a < (B1 + 1) * (2 * x)) :
    ProofForgeFin.Sqrt.newton a x - Nat.sqrt a ≤ B1 := by
  have herr := ProofForgeFin.Sqrt.newton_err_below (a := a) (x := x) hx hle
  have hsq := ProofForgeFin.Sqrt.mul_self_le_mul_self he
  have hcomb : 2 * x * (ProofForgeFin.Sqrt.newton a x - Nat.sqrt a)
      < (B1 + 1) * (2 * x) := by omega
  have heq : (B1 + 1) * (2 * x) = 2 * x * (B1 + 1) := Nat.mul_comm _ _
  rw [heq] at hcomb
  have hlt : ProofForgeFin.Sqrt.newton a x - Nat.sqrt a < B1 + 1 :=
    Nat.lt_of_mul_lt_mul_left hcomb
  omega

theorem s_bounds (a k : Nat) (hlo : 2 ^ (2 * k) ≤ a) (hhi : a < 2 ^ (2 * k + 2)) :
    2 ^ k ≤ Nat.sqrt a ∧ Nat.sqrt a < 2 ^ (k + 1) := by
  have e1 : k + k = 2 * k := by omega
  have e2 : 2 * k + 2 = 2 * (k + 1) := by omega
  constructor
  · apply ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le
    calc (2 ^ k) * (2 ^ k) = 2 ^ (k + k) := by rw [← Nat.pow_add]
    _ = 2 ^ (2 * k) := by rw [e1]
    _ ≤ a := hlo
  · apply ProofForgeFin.Sqrt.sqrt_lt_two_pow
    calc a < 2 ^ (2 * k + 2) := hhi
    _ = 2 ^ (2 * (k + 1)) := by rw [e2]

theorem endgame (a X6 : Nat) (ha : 1 ≤ a) (hX6 : 0 < X6) (hle : Nat.sqrt a ≤ X6)
    (hdsq : (X6 - Nat.sqrt a) * (X6 - Nat.sqrt a) ≤ Nat.sqrt a) :
    Nat.min (ProofForgeFin.Sqrt.newton a X6) (a / ProofForgeFin.Sqrt.newton a X6) = Nat.sqrt a := by
  have h7 := ProofForgeFin.Sqrt.newton_eq_or_succ (a := a) (x := X6) hX6 hle hdsq
  have hpos7 : 0 < ProofForgeFin.Sqrt.newton a X6 := by
    have hge := ProofForgeFin.Sqrt.sqrt_le_newton (a := a) (x := X6) hX6
    have hs1 : 0 < Nat.sqrt a := ProofForgeFin.Sqrt.sqrt_pos (by omega)
    omega
  exact ProofForgeFin.Sqrt.min_div_eq_sqrt hpos7 h7

theorem sq_add_one (t : Nat) : (t + 1) * (t + 1) = t * t + 2 * t + 1 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem expand_sq (m : Nat) : (2 ^ m + 1) * (2 ^ m + 1) = 2 ^ (2 * m) + 2 ^ (m + 1) + 1 := by
  have e1 : (2 ^ m) * (2 ^ m) = 2 ^ (2 * m) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [sq_add_one, e1, dbl m]

theorem expand_rhs (m' s : Nat) : ((2 ^ m' + 1) + 1) * (2 * s) = 2 ^ m' * (2 * s) + 2 * (2 * s) := by
  have h : ((2 ^ m' + 1) + 1) = (2 ^ m' + 2) := by omega
  rw [h, Nat.add_mul]

theorem main_le (s k m m' : Nat) (hsge : 2 ^ k ≤ s) (hme : 2 * m ≤ m' + 1 + k) :
    2 ^ (2 * m) ≤ 2 ^ m' * (2 * s) := by
  have h1 : 2 ^ (2 * m) ≤ 2 ^ ((m' + 1) + k) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ ((m' + 1) + k) = 2 ^ (m' + 1) * 2 ^ k := by rw [Nat.pow_add]
  have e1 : (2 : Nat) ^ (m' + 1) * 2 ^ k = 2 ^ m' * (2 * 2 ^ k) := by
    rw [Nat.pow_succ, Nat.mul_assoc]
  have e2 : (2 : Nat) * 2 ^ k ≤ 2 * s := Nat.mul_le_mul (Nat.le_refl 2) hsge
  have e3 := Nat.mul_le_mul (Nat.le_refl (2 ^ m')) e2
  omega

theorem remain_lt (s k m : Nat) (hsge : 2 ^ k ≤ s) (hmk : m + 1 ≤ k) (hk1 : 1 ≤ k) :
    2 ^ (m + 1) + 1 < 2 * s := by
  have p1 : 2 ^ (m + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hmk
  have h2k : (2 : Nat) ≤ 2 ^ k := by
    have e : (2 : Nat) = 2 ^ 1 := by decide
    rw [e]; exact Nat.pow_le_pow_right (by decide) hk1
  have hmul : 2 * 2 ^ k ≤ 2 * s := Nat.mul_le_mul (Nat.le_refl 2) hsge
  omega

theorem chain_uniform (a k : Nat) (ha : 1 ≤ a)
    (hlo : 2 ^ (2 * k) ≤ a) (hhi : a < 2 ^ (2 * k + 2))
    (hk2 : 2 ≤ k) (hk127 : k ≤ 127) :
    Nat.min (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))))) (a / ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))))) = Nat.sqrt a := by
  have hsb := s_bounds a k hlo hhi
  have hsge : 2 ^ k ≤ Nat.sqrt a := hsb.1
  have hslt : Nat.sqrt a < 2 ^ (k + 1) := hsb.2
  have h1k : (1 : Nat) ≤ 2 ^ k := Nat.one_le_two_pow
  have hspos : 1 ≤ Nat.sqrt a := by omega
  have hX0pos : 0 < 2 ^ k := by omega
  have h2s : 2 ^ (k + 1) ≤ 2 * Nat.sqrt a := by
    have hle := Nat.mul_le_mul (Nat.le_refl 2) hsge
    rw [dbl k] at hle
    omega
  have hX0lt2 : Nat.sqrt a < 2 * 2 ^ k := by
    rw [dbl k]; exact hslt
  have hX0le : 2 ^ k ≤ Nat.sqrt a := hsge
  -- X1 lower bound
  have l1 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (2 ^ k) :=
    ProofForgeFin.Sqrt.sqrt_le_newton hX0pos
  have hX1pos : 0 < ProofForgeFin.Sqrt.newton a (2 ^ k) := by omega
  -- e1 via step_below, E = X0, B1 = 2^(k-1)+1
  have eX0 : (2 ^ k) * (2 ^ k) = 2 ^ (2 * k) := by
    rw [← Nat.pow_add]; congr 1; omega
  have he0 : Nat.sqrt a - 2 ^ k ≤ 2 ^ k := by omega
  have e1 : ProofForgeFin.Sqrt.newton a (2 ^ k) - Nat.sqrt a ≤ 2 ^ (k - 1) + 1 := by
    apply step_below _ _ _ _ hX0pos hX0le he0 ?_
    have eR : ((2 ^ (k - 1) + 1) + 1) * (2 * 2 ^ k) = 2 ^ (2 * k) + 2 ^ (k + 2) := by
      have eA : 2 ^ (k - 1) * (2 * 2 ^ k) = 2 ^ (2 * k) := by
        rw [dbl k, ← Nat.pow_add]; congr 1; omega
      have eB : 2 * (2 * 2 ^ k) = 2 ^ (k + 2) := by
        have e1 : k + 2 = (k + 1) + 1 := by omega
        rw [e1, Nat.pow_succ, dbl k]
        exact Nat.mul_comm _ _
      have hexp : ((2 ^ (k - 1) + 1) + 1) * (2 * 2 ^ k)
          = 2 ^ (k - 1) * (2 * 2 ^ k) + 2 * (2 * 2 ^ k) := by
        have h1 : ((2 ^ (k - 1) + 1) + 1) = (2 ^ (k - 1) + 2) := by omega
        rw [h1, Nat.add_mul]
      rw [hexp, eA, eB]
    rw [eX0]
    have hs2 : 2 * Nat.sqrt a < 2 ^ (k + 2) := by
      have h1 : Nat.sqrt a + 1 ≤ 2 ^ (k + 1) := by omega
      have h2 := Nat.mul_le_mul (Nat.le_refl 2) h1
      have e2 : 2 * 2 ^ (k + 1) = 2 ^ (k + 2) := by
        have e1 : k + 2 = (k + 1) + 1 := by omega
        rw [e1, Nat.pow_succ]
        exact Nat.mul_comm _ _
      omega
    omega
  -- X2
  have l2 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)) :=
    ProofForgeFin.Sqrt.sqrt_le_newton hX1pos
  have hX2pos : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)) := by omega
  have hBs2 : (2 ^ (k - 1) + 1) * (2 ^ (k - 1) + 1) + 2 * Nat.sqrt a
      < ((2 ^ (k - 3) + 1) + 1) * (2 * Nat.sqrt a) := by
    have eB := expand_sq (k - 1)
    have eR := expand_rhs (k - 3) (Nat.sqrt a)
    have hM := main_le (Nat.sqrt a) k (k - 1) (k - 3) hsge (by omega)
    have hR := remain_lt (Nat.sqrt a) k (k - 1) hsge (by omega) (by omega)
    omega
  have e2 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)) - Nat.sqrt a
      ≤ 2 ^ (k - 3) + 1 :=
    step_above _ _ _ _ hX1pos l1 e1 hBs2
  -- X3
  have l3 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))) :=
    ProofForgeFin.Sqrt.sqrt_le_newton hX2pos
  have hX3pos : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))) := by omega
  have hBs3 : (2 ^ (k - 3) + 1) * (2 ^ (k - 3) + 1) + 2 * Nat.sqrt a
      < ((2 ^ (k - 7) + 1) + 1) * (2 * Nat.sqrt a) := by
    have eB := expand_sq (k - 3)
    have eR := expand_rhs (k - 7) (Nat.sqrt a)
    have hM := main_le (Nat.sqrt a) k (k - 3) (k - 7) hsge (by omega)
    have hR := remain_lt (Nat.sqrt a) k (k - 3) hsge (by omega) (by omega)
    omega
  have e3 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))) - Nat.sqrt a
      ≤ 2 ^ (k - 7) + 1 :=
    step_above _ _ _ _ hX2pos l2 e2 hBs3
  -- X4
  have l4 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))) :=
    ProofForgeFin.Sqrt.sqrt_le_newton hX3pos
  have hX4pos : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))) := by omega
  have hBs4 : (2 ^ (k - 7) + 1) * (2 ^ (k - 7) + 1) + 2 * Nat.sqrt a
      < ((2 ^ (k - 15) + 1) + 1) * (2 * Nat.sqrt a) := by
    have eB := expand_sq (k - 7)
    have eR := expand_rhs (k - 15) (Nat.sqrt a)
    have hM := main_le (Nat.sqrt a) k (k - 7) (k - 15) hsge (by omega)
    have hR := remain_lt (Nat.sqrt a) k (k - 7) hsge (by omega) (by omega)
    omega
  have e4 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))) - Nat.sqrt a
      ≤ 2 ^ (k - 15) + 1 :=
    step_above _ _ _ _ hX3pos l3 e3 hBs4
  -- X5
  have l5 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))))) :=
    ProofForgeFin.Sqrt.sqrt_le_newton hX4pos
  have hX5pos : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))))) := by omega
  have hBs5 : (2 ^ (k - 15) + 1) * (2 ^ (k - 15) + 1) + 2 * Nat.sqrt a
      < ((2 ^ (k - 31) + 1) + 1) * (2 * Nat.sqrt a) := by
    have eB := expand_sq (k - 15)
    have eR := expand_rhs (k - 31) (Nat.sqrt a)
    have hM := main_le (Nat.sqrt a) k (k - 15) (k - 31) hsge (by omega)
    have hR := remain_lt (Nat.sqrt a) k (k - 15) hsge (by omega) (by omega)
    omega
  have e5 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))))) - Nat.sqrt a
      ≤ 2 ^ (k - 31) + 1 :=
    step_above _ _ _ _ hX4pos l4 e4 hBs5
  -- X6
  have l6 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))) :=
    ProofForgeFin.Sqrt.sqrt_le_newton hX5pos
  have hX6pos : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))) := by omega
  have hBs6 : (2 ^ (k - 31) + 1) * (2 ^ (k - 31) + 1) + 2 * Nat.sqrt a
      < ((2 ^ (k - 63) + 1) + 1) * (2 * Nat.sqrt a) := by
    have eB := expand_sq (k - 31)
    have eR := expand_rhs (k - 63) (Nat.sqrt a)
    have hM := main_le (Nat.sqrt a) k (k - 31) (k - 63) hsge (by omega)
    have hR := remain_lt (Nat.sqrt a) k (k - 31) hsge (by omega) (by omega)
    omega
  have e6 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))) - Nat.sqrt a
      ≤ 2 ^ (k - 63) + 1 :=
    step_above _ _ _ _ hX5pos l5 e5 hBs6
  -- final: e6^2 <= s
  have hsq6 := ProofForgeFin.Sqrt.mul_self_le_mul_self e6
  have hB6sq : (2 ^ (k - 63) + 1) * (2 ^ (k - 63) + 1) ≤ 2 ^ k := by
    by_cases hk64 : k < 64
    · have hz : k - 63 = 0 := by omega
      have h1 : (2 : Nat) ^ (k - 63) = 1 := by rw [hz]
      have h4 : (4 : Nat) ≤ 2 ^ k := by
        have e : (4 : Nat) = 2 ^ 2 := by decide
        rw [e]; exact Nat.pow_le_pow_right (by decide) (by omega)
      rw [h1]
      omega
    · have eB6 := expand_sq (k - 63)
      have hA : 2 ^ (2 * (k - 63)) ≤ 2 ^ (k - 1) := by
        apply Nat.pow_le_pow_right (by decide)
        omega
      have hC : 2 ^ ((k - 63) + 1) + 1 ≤ 2 ^ (k - 1) := by
        have p1 : 2 ^ ((k - 63) + 1) ≤ 2 ^ (k - 2) := by
          apply Nat.pow_le_pow_right (by decide)
          omega
        have p2 : (2 : Nat) ^ (k - 2) + 1 ≤ 2 ^ (k - 1) := by
          have q1 : (1 : Nat) ≤ 2 ^ (k - 2) := by
            have e : (1 : Nat) = 2 ^ 0 := by decide
            rw [e]; exact Nat.pow_le_pow_right (by decide) (by omega)
          have q2 : 2 ^ (k - 2) + 2 ^ (k - 2) = 2 ^ (k - 1) := by
            have e : (k - 1) = (k - 2) + 1 := by omega
            rw [e, ← dbl (k - 2)]
            omega
          omega
        omega
      have h2k : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
        have e : (k - 1) + 1 = k := by omega
        have h := dbl (k - 1)
        rw [e] at h
        omega
      omega
  have e6sq : _ ≤ Nat.sqrt a := Nat.le_trans (Nat.le_trans hsq6 hB6sq) hsge
  exact endgame a _ ha hX6pos l6 e6sq

theorem chain_tiny (a k : Nat) (ha : 1 ≤ a)
    (hlo : 2 ^ (2 * k) ≤ a) (hhi : a < 2 ^ (2 * k + 2)) (hk1 : k ≤ 1) :
    Nat.min (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))))) (a / ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))))) = Nat.sqrt a := by
  have hsb := s_bounds a k hlo hhi
  have hsge : 2 ^ k ≤ Nat.sqrt a := hsb.1
  have hslt : Nat.sqrt a < 2 ^ (k + 1) := hsb.2
  have h1k : (1 : Nat) ≤ 2 ^ k := Nat.one_le_two_pow
  have hspos : 1 ≤ Nat.sqrt a := by omega
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have hX0 : (2 : Nat) ^ k = 1 := by rw [hk0]
    have htwo : (2 : Nat) ^ (k + 1) = 2 := by rw [hk0]
    have hpos0 : 0 < (2 : Nat) ^ k := by omega
    have hl0 : (2 : Nat) ^ k ≤ Nat.sqrt a := by omega
    have he0 : Nat.sqrt a - (2 : Nat) ^ k ≤ 0 := by omega
    have l1 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (2 ^ k) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos0
    have hpos1 : 0 < ProofForgeFin.Sqrt.newton a (2 ^ k) := by omega
    have e1 : ProofForgeFin.Sqrt.newton a (2 ^ k) - Nat.sqrt a ≤ 1 := by
      apply step_below _ _ _ _ hpos0 hl0 he0 ?_; omega
    have l2 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos1
    have hpos2 : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)) := by omega
    have e2 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)) - Nat.sqrt a ≤ 1 :=
      step_above _ _ _ _ hpos1 l1 e1 (by omega)
    have l3 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos2
    have hpos3 : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))) := by omega
    have e3 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))) - Nat.sqrt a ≤ 1 :=
      step_above _ _ _ _ hpos2 l2 e2 (by omega)
    have l4 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos3
    have hpos4 : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))) := by omega
    have e4 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))) - Nat.sqrt a ≤ 1 :=
      step_above _ _ _ _ hpos3 l3 e3 (by omega)
    have l5 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos4
    have hpos5 : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))))) := by omega
    have e5 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))))) - Nat.sqrt a ≤ 1 :=
      step_above _ _ _ _ hpos4 l4 e4 (by omega)
    have l6 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos5
    have hpos6 : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))) := by omega
    have e6 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))) - Nat.sqrt a ≤ 1 :=
      step_above _ _ _ _ hpos5 l5 e5 (by omega)
    have hsq6 := ProofForgeFin.Sqrt.mul_self_le_mul_self e6
    have hs1b : 1 * 1 ≤ Nat.sqrt a := by omega
    have e6sq : _ ≤ Nat.sqrt a := Nat.le_trans hsq6 hs1b
    exact endgame a _ ha hpos6 l6 e6sq
  · have hk1' : k = 1 := by omega
    have hX0 : (2 : Nat) ^ k = 2 := by rw [hk1']
    have htwo : (2 : Nat) ^ (k + 1) = 4 := by rw [hk1']
    have hpos0 : 0 < (2 : Nat) ^ k := by omega
    have hl0 : (2 : Nat) ^ k ≤ Nat.sqrt a := by omega
    have he0 : Nat.sqrt a - (2 : Nat) ^ k ≤ 1 := by omega
    have l1 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (2 ^ k) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos0
    have hpos1 : 0 < ProofForgeFin.Sqrt.newton a (2 ^ k) := by omega
    have e1 : ProofForgeFin.Sqrt.newton a (2 ^ k) - Nat.sqrt a ≤ 1 := by
      apply step_below _ _ _ _ hpos0 hl0 he0 ?_; omega
    have l2 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos1
    have hpos2 : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)) := by omega
    have e2 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)) - Nat.sqrt a ≤ 1 :=
      step_above _ _ _ _ hpos1 l1 e1 (by omega)
    have l3 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos2
    have hpos3 : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))) := by omega
    have e3 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))) - Nat.sqrt a ≤ 1 :=
      step_above _ _ _ _ hpos2 l2 e2 (by omega)
    have l4 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos3
    have hpos4 : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))) := by omega
    have e4 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))) - Nat.sqrt a ≤ 1 :=
      step_above _ _ _ _ hpos3 l3 e3 (by omega)
    have l5 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos4
    have hpos5 : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))))) := by omega
    have e5 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k))))) - Nat.sqrt a ≤ 1 :=
      step_above _ _ _ _ hpos4 l4 e4 (by omega)
    have l6 : Nat.sqrt a ≤ ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos5
    have hpos6 : 0 < ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))) := by omega
    have e6 : ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (ProofForgeFin.Sqrt.newton a (2 ^ k)))))) - Nat.sqrt a ≤ 1 :=
      step_above _ _ _ _ hpos5 l5 e5 (by omega)
    have hsq6 := ProofForgeFin.Sqrt.mul_self_le_mul_self e6
    have hs1b : 1 * 1 ≤ Nat.sqrt a := by omega
    have e6sq : _ ≤ Nat.sqrt a := Nat.le_trans hsq6 hs1b
    exact endgame a _ ha hpos6 l6 e6sq

theorem nowrap (n k X : Nat) (hk : k ≤ 127) (hhi : n < 2 ^ (2 * k + 2))
    (hXlo : 2 ^ k ≤ X) (hXhi : X < 2 ^ (k + 2)) : X + n / X < 2 ^ 256 := by
  have hXpos : 0 < X := by
    have h1k : (1 : Nat) ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have hmul : 2 ^ (2 * k + 2) ≤ 2 ^ (k + 2) * X := by
    have e : 2 ^ (k + 2) * 2 ^ k = 2 ^ (2 * k + 2) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [← e]
    exact Nat.mul_le_mul (Nat.le_refl _) hXlo
  have hdiv : n / X < 2 ^ (k + 2) := by
    rw [Nat.div_lt_iff_lt_mul hXpos]
    exact Nat.lt_of_lt_of_le hhi hmul
  have h256 : 2 ^ (k + 2) + 2 ^ (k + 2) ≤ 2 ^ 256 := by
    have h1 : k + 2 + 1 = k + 3 := by omega
    have h := dbl (k + 2)
    rw [h1] at h
    have h2 : 2 ^ (k + 2) + 2 ^ (k + 2) = 2 ^ (k + 3) := by omega
    rw [h2]
    calc 2 ^ (k + 3) ≤ 2 ^ 130 := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ 2 ^ 256 := by decide
  omega

def natIter (g : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => natIter g n (g x)

theorem newton_step_hi (n X : Nat) (k : Nat)
    (hslt : Nat.sqrt n < 2 ^ (k + 1)) (hk12 : 2 ^ (k + 1) < 2 ^ (k + 2))
    (hXlo : Nat.sqrt n ≤ X) (hXhi : X < 2 ^ (k + 2)) (hXpos : 0 < X) :
    ProofForgeFin.Sqrt.newton n X < 2 ^ (k + 2) := by
  by_cases hlt : Nat.sqrt n < X
  · have h := ProofForgeFin.Sqrt.newton_lt_self hlt
    omega
  · have heq : X = Nat.sqrt n := by omega
    have hmem := ProofForgeFin.Sqrt.newton_of_mem hXpos (by omega) (by omega)
    have hs1 : Nat.sqrt n + 1 ≤ 2 ^ (k + 1) := by omega
    rcases hmem with h | ⟨-, h, -⟩
    · omega
    · omega

theorem iter_all (a : U256) (j : Nat) (n k : Nat) (X : U256) (Xv : Nat)
    (ha : a.toNat = n) (hk : k ≤ 127) (hlo : 2 ^ (2 * k) ≤ n) (hhi : n < 2 ^ (2 * k + 2))
    (hsge : 2 ^ k ≤ Nat.sqrt n) (hslt : Nat.sqrt n < 2 ^ (k + 1)) (hk12 : 2 ^ (k + 1) < 2 ^ (k + 2))
    (hX : X.toNat = Xv) (hsX : Nat.sqrt n ≤ Xv) (hbX : Xv < 2 ^ (k + 2)) (hXpos : 0 < Xv) :
    (OzSqrt.iterate (newtonStep a) j X).toNat = natIter (ProofForgeFin.Sqrt.newton n) j Xv ∧
    Nat.sqrt n ≤ natIter (ProofForgeFin.Sqrt.newton n) j Xv ∧
    natIter (ProofForgeFin.Sqrt.newton n) j Xv < 2 ^ (k + 2) ∧
    0 < natIter (ProofForgeFin.Sqrt.newton n) j Xv := by
  induction j generalizing X Xv with
  | zero => exact ⟨hX, hsX, hbX, hXpos⟩
  | succ j ih =>
    have hXlo : 2 ^ k ≤ Xv := Nat.le_trans hsge hsX
    have w : X.toNat + a.toNat / X.toNat < 2 ^ 256 := by
      rw [hX, ha]
      exact nowrap n k Xv hk hhi hXlo hbX
    have hX1 : (newtonStep a X).toNat = ProofForgeFin.Sqrt.newton n Xv := by
      have h := toNat_newtonStep a X w
      rw [hX, ha] at h
      exact h
    have hs1 : Nat.sqrt n ≤ ProofForgeFin.Sqrt.newton n Xv :=
      ProofForgeFin.Sqrt.sqrt_le_newton hXpos
    have hb1 : ProofForgeFin.Sqrt.newton n Xv < 2 ^ (k + 2) :=
      newton_step_hi n Xv k hslt hk12 hsX hbX hXpos
    have hspos : 1 ≤ Nat.sqrt n := by
      have h1n : 1 ≤ n := by
        have h12k : (1 : Nat) ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
        omega
      have hsp := ProofForgeFin.Sqrt.sqrt_pos h1n
      omega
    have hp1 : 0 < ProofForgeFin.Sqrt.newton n Xv := by omega
    have ih' := ih (newtonStep a X) (ProofForgeFin.Sqrt.newton n Xv) hX1 hs1 hb1 hp1
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih'
    have e1 : OzSqrt.iterate (newtonStep a) (j + 1) X =
        OzSqrt.iterate (newtonStep a) j (newtonStep a X) := rfl
    have e2 : natIter (ProofForgeFin.Sqrt.newton n) (j + 1) Xv =
        natIter (ProofForgeFin.Sqrt.newton n) j (ProofForgeFin.Sqrt.newton n Xv) := rfl
    rw [e1, e2]
    exact ⟨ih1, ih2, ih3, ih4⟩

theorem sqrt_eq_of_log (a : U256) (k : Nat) (hkdef : k = Nat.log2 a.toNat / 2) (h0 : a.toNat ≠ 0) :
    (sqrt a).toNat = Nat.sqrt a.toNat := by
  have hane : ¬ a = 0 := fun c => h0 (by rw [c]; decide)
  have hlog256 : Nat.log2 a.toNat < 256 :=
    (ProofForgeFin.Evm.log2_lt_iff (hn := h0)).mpr (a.isLt)
  have hk127 : k ≤ 127 := by omega
  have h2k : 2 * k ≤ Nat.log2 a.toNat := by omega
  have hm : Nat.log2 a.toNat ≤ 2 * k + 1 := by omega
  have hlog := ProofForgeFin.Evm.log2_spec (hn := h0)
  obtain ⟨hlo2, hhi2⟩ := hlog
  have hlo : 2 ^ (2 * k) ≤ a.toNat := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) h2k
    omega
  have hhi : a.toNat < 2 ^ (2 * k + 2) := by
    have hm2 : Nat.log2 a.toNat + 1 ≤ 2 * k + 1 + 1 := by omega
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm2
    have e : 2 * k + 1 + 1 = 2 * k + 2 := by omega
    rw [e] at h
    omega
  have hsb := s_bounds a.toNat k hlo hhi
  have hsge : 2 ^ k ≤ Nat.sqrt a.toNat := hsb.1
  have hslt : Nat.sqrt a.toNat < 2 ^ (k + 1) := hsb.2
  have hk12 : 2 ^ (k + 1) < 2 ^ (k + 2) := by
    have hpos : (0 : Nat) < 2 ^ (k + 1) := by
      have h1k : (1 : Nat) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      omega
    have e : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
      have h1 : (k + 1) + 1 = k + 2 := by omega
      have h := dbl (k + 1)
      rw [h1] at h
      exact h.symm
    omega
  have hX0 : ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ k := by
    have h := x0_eq a
    rw [← hkdef] at h
    exact h
  have hX0pos : 0 < (2 : Nat) ^ k := by
    have h1k : (1 : Nat) ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have hX0hi : (2 : Nat) ^ k < 2 ^ (k + 2) := by
    have h1 : (2 : Nat) ^ k ≤ 2 ^ (k + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hX1lt : ProofForgeFin.Sqrt.newton a.toNat (2 ^ k) < 2 ^ (k + 2) := by
    have hQ : 2 ^ k ≤ 2 ^ (k + 2) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hdiv : a.toNat / 2 ^ k < 2 ^ (k + 2) := by
      rw [Nat.div_lt_iff_lt_mul hX0pos]
      have e : 2 ^ (k + 2) * 2 ^ k = 2 ^ (2 * k + 2) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [e]
      exact hhi
    unfold ProofForgeFin.Sqrt.newton
    omega
  have hslo1 : Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newton a.toNat (2 ^ k) :=
    ProofForgeFin.Sqrt.sqrt_le_newton hX0pos
  have hX1pos : 0 < ProofForgeFin.Sqrt.newton a.toNat (2 ^ k) := by
    have hs1 : 1 ≤ Nat.sqrt a.toNat := by
      have h1n : 1 ≤ a.toNat := by
        have h12k : (1 : Nat) ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
        omega
      have hsp := ProofForgeFin.Sqrt.sqrt_pos h1n
      omega
    omega
  have w0 : ((1 : U256) <<< (log2 a >>> 1)).toNat +
      a.toNat / ((1 : U256) <<< (log2 a >>> 1)).toNat < 2 ^ 256 := by
    rw [hX0]
    exact nowrap a.toNat k (2 ^ k) hk127 hhi (Nat.le_refl _) hX0hi
  have eStep1 : (newtonStep a ((1 : U256) <<< (log2 a >>> 1))).toNat =
      ProofForgeFin.Sqrt.newton a.toNat (2 ^ k) := by
    have h := toNat_newtonStep a ((1 : U256) <<< (log2 a >>> 1)) w0
    rw [hX0] at h
    exact h
  have hall := iter_all a 6 a.toNat k
    (newtonStep a ((1 : U256) <<< (log2 a >>> 1)))
    (ProofForgeFin.Sqrt.newton a.toNat (2 ^ k))
    rfl hk127 hlo hhi hsge hslt hk12 eStep1 hslo1 hX1lt hX1pos
  have hshape : sqrt a = newtonSqrt 7 a := rfl
  rw [hshape]
  have hif : newtonSqrt 7 a = min
      (OzSqrt.iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
      (a / OzSqrt.iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))) := by
    unfold newtonSqrt
    rw [if_neg hane]
  rw [hif, toNat_min]
  have eIter7 : (OzSqrt.iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat =
      natIter (ProofForgeFin.Sqrt.newton a.toNat) 7 (2 ^ k) := by
    have e7 : OzSqrt.iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)) =
        OzSqrt.iterate (newtonStep a) 6 (newtonStep a ((1 : U256) <<< (log2 a >>> 1))) := rfl
    have e7n : natIter (ProofForgeFin.Sqrt.newton a.toNat) 7 (2 ^ k) =
        natIter (ProofForgeFin.Sqrt.newton a.toNat) 6
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ k)) := rfl
    rw [e7, e7n]
    exact hall.1
  rw [eIter7, ProofForgeFin.toNat_udiv', eIter7]
  have h1a : 1 ≤ a.toNat := by omega
  by_cases hk1 : k ≤ 1
  · exact chain_tiny a.toNat k h1a hlo hhi hk1
  · have hk2 : 2 ≤ k := by omega
    exact chain_uniform a.toNat k h1a hlo hhi hk2 hk127

theorem toNat_sqrt_eq : ∀ a : U256, (sqrt a).toNat = Nat.sqrt a.toNat := by
  intro a
  by_cases h0 : a.toNat = 0
  · have ha0 : a = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
    subst ha0
    decide
  · exact sqrt_eq_of_log a (Nat.log2 a.toNat / 2) rfl h0

theorem sqrtUp_toNat' (a : U256) :
    (sqrtUp sqrt a).toNat = Nat.sqrt a.toNat + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  unfold sqrtUp
  dsimp only
  have hr : (sqrt a).toNat = Nat.sqrt a.toNat := toNat_sqrt_eq a
  have hfit : (sqrt a).toNat * (sqrt a).toNat < 2 ^ 256 := by
    rw [hr]
    have h1 := Nat.sqrt_le a.toNat
    have h2 := a.isLt
    omega
  have hmul : (sqrt a * sqrt a).toNat = (sqrt a).toNat * (sqrt a).toNat :=
    ProofForgeFin.toNat_mul_of_lt _ _ hfit
  have hiff : (sqrt a * sqrt a < a) ↔ (Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat) := by
    constructor
    · intro c
      have c2 := BitVec.lt_def.mp c
      rw [hmul, hr] at c2
      exact c2
    · intro c
      have c2 : (sqrt a * sqrt a).toNat < a.toNat := by rw [hmul, hr]; exact c
      exact BitVec.lt_def.mpr c2
  have hs128 : Nat.sqrt a.toNat < 2 ^ 128 := by
    have h1 := Nat.sqrt_le a.toNat
    have h4 := a.isLt
    by_cases hc : Nat.sqrt a.toNat < 2 ^ 128
    · exact hc
    · have hc' : 2 ^ 128 ≤ Nat.sqrt a.toNat := by omega
      have h2 := Nat.mul_le_mul hc' hc'
      have h3 : (2 ^ 128) * (2 ^ 128) = 2 ^ 256 := by rw [← Nat.pow_add]
      omega
  have hsmall : (sqrt a).toNat + 1 < 2 ^ 256 := by
    rw [hr]
    calc Nat.sqrt a.toNat + 1 ≤ 2 ^ 128 := by omega
    _ < 2 ^ 256 := by decide
  by_cases hc : sqrt a * sqrt a < a
  · rw [if_pos hc, if_pos (hiff.mp hc)]
    have h1 : ((1 : U256)).toNat = 1 := by decide
    have hh := ProofForgeFin.toNat_add_of_lt (sqrt a) (1 : U256) (by rw [h1]; exact hsmall)
    rw [hh, h1, hr]
  · rw [if_neg hc, if_neg (fun c => hc (hiff.mpr c))]
    have h1 : ((0 : U256)).toNat = 0 := by decide
    have hh := ProofForgeFin.toNat_add_of_lt (sqrt a) (0 : U256) (by rw [h1]; omega)
    rw [hh, h1, hr]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  rw [toNat_sqrt_eq a]
  exact Nat.sqrt_le _

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro a
  rw [toNat_sqrt_eq a]
  exact Nat.lt_succ_sqrt _

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  intro a
  rw [sqrtUp_toNat' a]
  by_cases hc : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat
  · rw [if_pos hc]
    have h1 := Nat.lt_succ_sqrt a.toNat
    rw [Nat.succ_eq_add_one] at h1
    exact Nat.le_of_lt h1
  · rw [if_neg hc]
    simp
    omega

theorem req_sqrt_up_tight : SqrtUpTight sqrt := by
  intro a hu
  rw [sqrtUp_toNat' a] at hu ⊢
  by_cases hc : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat
  · rw [if_pos hc]
    have hsub : Nat.sqrt a.toNat + 1 - 1 = Nat.sqrt a.toNat := by omega
    rw [hsub]
    exact hc
  · rw [if_neg hc] at hu ⊢
    simp at hu ⊢
    have h1 := Nat.sqrt_le a.toNat
    have hs : 0 < Nat.sqrt a.toNat := by omega
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Nat.sqrt a.toNat ≠ 0)
    rw [ht] at h1 ⊢
    simp only [Nat.succ_eq_add_one] at h1 ⊢
    simp at ⊢
    have h2 : t * t < (t + 1) * (t + 1) := Nat.mul_self_lt_mul_self (Nat.lt_succ_self t)
    omega

theorem req_mint_backed : MintBacked sqrt := by
  intro a0 a1 l hl
  obtain ⟨hprod, hroot, hliq⟩ := firstMint_eq_some hl
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have hr : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [toNat_sqrt_eq (a0 * a1), hmul]
  rw [hliq, hr]
  exact Nat.sqrt_le _

theorem req_mint_full : MintFull sqrt := by
  intro a0 a1 l hl
  obtain ⟨hprod, hroot, hliq⟩ := firstMint_eq_some hl
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have hr : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [toNat_sqrt_eq (a0 * a1), hmul]
  have hlt := Nat.lt_succ_sqrt (a0.toNat * a1.toNat)
  have h1001 : l.toNat + 1001 = Nat.sqrt (a0.toNat * a1.toNat) + 1 := by omega
  rw [h1001]
  exact hlt

theorem req_mint_live : MintLive sqrt := by
  intro a0 a1 hprod hbig
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have hr : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [toNat_sqrt_eq (a0 * a1), hmul]
  apply firstMint_isSome hprod
  rw [hr]
  have hle : Nat.sqrt (1001 * 1001) ≤ Nat.sqrt (a0.toNat * a1.toNat) :=
    ProofForgeFin.Sqrt.sqrt_le_sqrt hbig
  have h1001 : Nat.sqrt (1001 * 1001) = 1001 := ProofForgeFin.Sqrt.sqrt_mul_self 1001
  omega

theorem req_newton_budget : NewtonBudget sqrt := by
  exact ⟨7, by decide, fun a => rfl⟩

end OzSqrt
