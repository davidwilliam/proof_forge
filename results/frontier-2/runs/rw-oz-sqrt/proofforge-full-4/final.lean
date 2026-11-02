import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.Sqrt
import ProofForgeFin.SqrtIter
import ProofForgeFin.WordBridge
import ProofForgeFin.NatSqrt
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

/-- Initial estimate `1 << (log2(a) >> 1)`, named. -/
def w0 (a : U256) : U256 := (1 : U256) <<< (log2 a >>> 1)

/-- One Newton line `(result + a / result) >> 1`, named. -/
def wstep (a w : U256) : U256 := (w + a / w) >>> 1

/-- The routine is seven named steps and the final `min`. -/
theorem sqrt_eq_min7 (a : U256) (ha : ¬ a = 0) :
    sqrt a = min (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (w0 a))))))))
      (a / wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (w0 a)))))))) := by
  unfold sqrt w0 wstep
  rw [ite_eq_right ha]

/-- The routine returns the floor of the square root on values. -/
theorem sqrt_toNat (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  by_cases ha : a = 0
  · subst ha
    have hs : sqrt 0 = 0 := by simp [sqrt]
    rw [hs, ProofForgeFin.WordBridge.toNat_zero']
    rfl
  · have hpos : 0 < a.toNat :=
      (ProofForgeFin.WordBridge.ne_zero_iff_toNat_pos).mp ha
    have ha256 : a.toNat < 2 ^ 256 := a.isLt
    have hlog : (log2 a).toNat = Nat.log2 a.toNat := toNat_log2 a
    have hshr : (log2 a >>> 1).toNat = Nat.log2 a.toNat / 2 := by
      have h := ProofForgeFin.WordBridge.toNat_shiftRight (log2 a) 1
      rw [hlog] at h
      simpa using h
    have hL256 : Nat.log2 a.toNat < 256 :=
      ProofForgeFin.WordBridge.log2_toNat_lt (by decide) a
    have hltInit : (log2 a >>> 1).toNat < 256 := by rw [hshr]; omega
    have hx0 : (w0 a).toNat = 2 ^ (Nat.log2 a.toNat / 2) := by
      unfold w0
      rw [ProofForgeFin.WordBridge.toNat_one_shiftLeft_bv hltInit, hshr]
    have hx0pos : 0 < 2 ^ (Nat.log2 a.toNat / 2) := Nat.pow_pos (by decide)
    have hle : 2 ^ (Nat.log2 a.toNat / 2) ≤ Nat.sqrt a.toNat :=
      ProofForgeFin.Sqrt.two_pow_half_log2_le_sqrt hpos
    have hlt2 : Nat.sqrt a.toNat < 2 * 2 ^ (Nat.log2 a.toNat / 2) :=
      ProofForgeFin.Sqrt.sqrt_lt_two_mul_two_pow_half_log2 _
    have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
      ProofForgeFin.Sqrt.sqrt_lt_two_pow_of_lt ha256 (by decide)
    have hsPos : 0 < Nat.sqrt a.toNat :=
      ProofForgeFin.Sqrt.sqrt_pos hpos
    have hx0le129 : 2 ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 129 := by
      apply Nat.pow_le_pow_right (by decide)
      omega
    have e130lt : (2 : Nat) ^ 130 < 2 ^ 256 :=
      Nat.pow_lt_pow_right (by decide) (by decide)
    have h2B129 : 2 * (2 : Nat) ^ 129 < 2 ^ 256 := by
      have e2x129 : 2 * (2 : Nat) ^ 129 = 2 ^ (129 + 1) := by
        rw [Nat.pow_succ]
      have e130 : (2 : Nat) ^ (129 + 1) < 2 ^ 256 :=
        Nat.pow_lt_pow_right (by decide) (by decide)
      omega
    have hdiv : a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 4 * 2 ^ (Nat.log2 a.toNat / 2) := by
      have h := ProofForgeFin.Sqrt.div_lt_of_sqrt_lt_mul (a := a.toNat)
        (x := 2 ^ (Nat.log2 a.toNat / 2)) (c := 2) hx0pos hlt2
      have h22 : (2 : Nat) * 2 * 2 ^ (Nat.log2 a.toNat / 2) = 4 * 2 ^ (Nat.log2 a.toNat / 2) := by
        omega
      rw [h22] at h
      exact h
    have h4x0 : 4 * 2 ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 129 := by
      have e2 : (4 : Nat) = 2 ^ 2 := by decide
      rw [e2, ← Nat.pow_add]
      apply Nat.pow_le_pow_right (by decide)
      omega
    have hsum0 : 2 ^ (Nat.log2 a.toNat / 2) + a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 256 := by
      omega
    have hm1ge : Nat.sqrt a.toNat ≤
        ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) :=
      ProofForgeFin.Sqrt.sqrt_le_newton (a := a.toNat) hx0pos
    have hm1lt : ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) < 2 ^ 129 := by
      unfold ProofForgeFin.Sqrt.newton
      omega
    have p129_130 : (2 : Nat) ^ 129 ≤ 2 ^ 130 :=
      Nat.pow_le_pow_right (by decide) (by decide)
    have p128_130 : (2 : Nat) ^ 128 ≤ 2 ^ 130 :=
      Nat.pow_le_pow_right (by decide) (by decide)
    have p131_256 : (2 : Nat) ^ (130 + 1) ≤ 2 ^ 256 :=
      Nat.pow_le_pow_right (by decide) (by decide)
    have e131 : 2 * (2 : Nat) ^ 130 = 2 ^ (130 + 1) := by
      rw [Nat.pow_succ]
    have hbig : (2 : Nat) ^ 130 + 2 ^ 128 + 2 < 2 ^ 256 := by omega
    have hM130 : max (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))
        (Nat.sqrt a.toNat + 1) < 2 ^ 130 := by
      omega
    have hsum0w : (w0 a).toNat + a.toNat / (w0 a).toNat < 2 ^ 256 := by
      rw [hx0]
      exact hsum0
    have eW1 : (wstep a (w0 a)).toNat =
        ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) := by
      unfold wstep
      rw [← hx0]
      exact ProofForgeFin.Sqrt.toNat_newton_word a (w0 a) hsum0w
    -- From here every iterate is at or above the root.
    have stepAbove : ∀ y : U256, Nat.sqrt a.toNat ≤ y.toNat →
        y.toNat + Nat.sqrt a.toNat + 2 < 2 ^ 256 →
        ((wstep a y)).toNat = ProofForgeFin.Sqrt.newton a.toNat y.toNat := by
      intro y hleY hwY
      unfold wstep
      exact ProofForgeFin.Sqrt.toNat_newton_word_of_sqrt_le hsPos hleY hwY
    have eW2 : (wstep a (wstep a (w0 a))).toNat = ProofForgeFin.Sqrt.newton a.toNat
        (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) := by
      rw [stepAbove _ (by rw [eW1]; exact hm1ge) (by rw [eW1]; omega), eW1]
    have hm2ge : Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newton a.toNat
        (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton_of_le (a := a.toNat) hm1ge
    have hm2le : ProofForgeFin.Sqrt.newton a.toNat
        (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) ≤
        max (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))
          (Nat.sqrt a.toNat + 1) :=
      ProofForgeFin.Sqrt.newton_le_max (a := a.toNat) hm1ge
    have eW3 : (wstep a (wstep a (wstep a (w0 a)))).toNat = ProofForgeFin.Sqrt.newton a.toNat
        (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))) := by
      rw [stepAbove _ (by rw [eW2]; exact hm2ge) (by rw [eW2]; omega), eW2]
    have hm3ge : Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newton a.toNat
        (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton_of_le (a := a.toNat) hm2ge
    have hm3le : ProofForgeFin.Sqrt.newton a.toNat
        (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))) ≤
        max (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))
          (Nat.sqrt a.toNat + 1) := by
      have h := ProofForgeFin.Sqrt.newtonIter_le_max (a := a.toNat)
        (x := ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) 2 hm1ge
      have e2 : ProofForgeFin.Sqrt.newtonIter a.toNat 2
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) =
        ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))) := by
        rw [ProofForgeFin.Sqrt.newtonIter_succ', ProofForgeFin.Sqrt.newtonIter_succ']
        rfl
      rw [← e2]; exact h
    have eW4 : (wstep a (wstep a (wstep a (wstep a (w0 a))))).toNat =
        ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat
            (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))))) := by
      rw [stepAbove _ (by rw [eW3]; exact hm3ge) (by rw [eW3]; omega), eW3]
    have hm4ge : Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newton a.toNat
        (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton_of_le (a := a.toNat) hm3ge
    have hm4le : ProofForgeFin.Sqrt.newton a.toNat
        (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))))) ≤
        max (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))
          (Nat.sqrt a.toNat + 1) := by
      have h := ProofForgeFin.Sqrt.newtonIter_le_max (a := a.toNat)
        (x := ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) 3 hm1ge
      have e3 : ProofForgeFin.Sqrt.newtonIter a.toNat 3
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) =
        ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
            (2 ^ (Nat.log2 a.toNat / 2))))) := by
        rw [ProofForgeFin.Sqrt.newtonIter_succ', ProofForgeFin.Sqrt.newtonIter_succ',
          ProofForgeFin.Sqrt.newtonIter_succ']
        rfl
      rw [← e3]; exact h
    have eW5 : (wstep a (wstep a (wstep a (wstep a (wstep a (w0 a)))))).toNat =
        ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
            (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))))) := by
      rw [stepAbove _ (by rw [eW4]; exact hm4ge) (by rw [eW4]; omega), eW4]
    have hm5ge : Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newton a.toNat
        (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat
            (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton_of_le (a := a.toNat) hm4ge
    have hm5le : ProofForgeFin.Sqrt.newton a.toNat
        (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat
            (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))))) ≤
        max (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))
          (Nat.sqrt a.toNat + 1) := by
      have h := ProofForgeFin.Sqrt.newtonIter_le_max (a := a.toNat)
        (x := ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) 4 hm1ge
      have e4 : ProofForgeFin.Sqrt.newtonIter a.toNat 4
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) =
        ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
            (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))))) := by
        rw [ProofForgeFin.Sqrt.newtonIter_succ', ProofForgeFin.Sqrt.newtonIter_succ',
          ProofForgeFin.Sqrt.newtonIter_succ', ProofForgeFin.Sqrt.newtonIter_succ']
        rfl
      rw [← e4]; exact h
    have eW6 : (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (w0 a))))))).toNat =
        ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
            (ProofForgeFin.Sqrt.newton a.toNat
              (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))))))) := by
      rw [stepAbove _ (by rw [eW5]; exact hm5ge) (by rw [eW5]; omega), eW5]
    have hm6ge : Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newton a.toNat
        (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
            (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))))))) :=
      ProofForgeFin.Sqrt.sqrt_le_newton_of_le (a := a.toNat) hm5ge
    have hm6le : ProofForgeFin.Sqrt.newton a.toNat
        (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
            (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))))))) ≤
        max (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))
          (Nat.sqrt a.toNat + 1) := by
      have h := ProofForgeFin.Sqrt.newtonIter_le_max (a := a.toNat)
        (x := ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) 5 hm1ge
      have e5 : ProofForgeFin.Sqrt.newtonIter a.toNat 5
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) =
        ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
            (ProofForgeFin.Sqrt.newton a.toNat
              (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))))))) := by
        rw [ProofForgeFin.Sqrt.newtonIter_succ', ProofForgeFin.Sqrt.newtonIter_succ',
          ProofForgeFin.Sqrt.newtonIter_succ', ProofForgeFin.Sqrt.newtonIter_succ',
          ProofForgeFin.Sqrt.newtonIter_succ']
        rfl
      rw [← e5]; exact h
    have eW7 : (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (w0 a)))))))).toNat =
        ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
            (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
              (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))))))) := by
      rw [stepAbove _ (by rw [eW6]; exact hm6ge) (by rw [eW6]; omega), eW6]
    have hW7ge : Nat.sqrt a.toNat ≤
        (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (w0 a)))))))).toNat := by
      rw [eW7]
      exact ProofForgeFin.Sqrt.sqrt_le_newton_of_le (a := a.toNat) hm6ge
    -- Convergence on values after seven steps.
    have hconv := ProofForgeFin.Sqrt.newtonIter_eq_or_succ_of_lt_two_mul (a := a.toNat)
      (x := 2 ^ (Nat.log2 a.toNat / 2)) (b := 128) (k := 5) hx0pos hle hlt2 hs128
      (by decide) (by decide)
    have hiter7 : ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) =
        ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
            (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
              (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))))))) := by
      have h6 : ProofForgeFin.Sqrt.newtonIter a.toNat 6 (2 ^ (Nat.log2 a.toNat / 2)) =
        ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
          (ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newton a.toNat
            (ProofForgeFin.Sqrt.newton a.toNat
              (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))))))) := by
        rw [ProofForgeFin.Sqrt.newtonIter_succ', ProofForgeFin.Sqrt.newtonIter_succ',
          ProofForgeFin.Sqrt.newtonIter_succ', ProofForgeFin.Sqrt.newtonIter_succ',
          ProofForgeFin.Sqrt.newtonIter_succ', ProofForgeFin.Sqrt.newtonIter_succ']
        rfl
      rw [show (7 : Nat) = 6 + 1 from rfl,
        ProofForgeFin.Sqrt.newtonIter_succ', h6]
    rw [show (5 : Nat) + 2 = 7 from rfl] at hconv
    rw [hiter7] at hconv
    have hconv' : (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a
      (w0 a)))))))).toNat = Nat.sqrt a.toNat ∨
      ((wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a
        (w0 a)))))))).toNat = Nat.sqrt a.toNat + 1 ∧
        Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 1) ≤ a.toNat) := by
      rw [eW7]; exact hconv
    have hW7pos : 0 < (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a
      (w0 a)))))))).toNat :=
      Nat.lt_of_lt_of_le hsPos hW7ge
    have hminNat : Nat.min (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a
      (w0 a)))))))).toNat
        (a.toNat / (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a
          (w0 a)))))))).toNat) = Nat.sqrt a.toNat :=
      ProofForgeFin.Sqrt.min_div_eq_sqrt hW7pos hconv'
    have hminW : (min (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a
      (w0 a)))))))) (a / wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a
        (w0 a))))))))).toNat = Nat.min (wstep a (wstep a (wstep a (wstep a (wstep a
          (wstep a (wstep a (w0 a)))))))).toNat
        (a.toNat / (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a (wstep a
          (w0 a)))))))).toNat) := by
      rw [toNat_min, ProofForgeFin.WordBridge.toNat_div]
    rw [sqrt_eq_min7 a ha, hminW, hminNat]

/-- The rounded-up root on values. -/
theorem sqrtUp_toNat (a : U256) : (sqrtUp sqrt a).toNat =
    Nat.sqrt a.toNat + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  have hrr : (sqrt a).toNat = Nat.sqrt a.toNat := sqrt_toNat a
  have hbound : (sqrt a).toNat * (sqrt a).toNat < 2 ^ 256 := by
    rw [sqrt_toNat]
    exact Nat.lt_of_le_of_lt (Nat.sqrt_le _) a.isLt
  have hsq : (sqrt a * sqrt a).toNat = Nat.sqrt a.toNat * Nat.sqrt a.toNat := by
    rw [ProofForgeFin.WordBridge.toNat_mul_of_lt' hbound, sqrt_toNat]
  have hlt128 : Nat.sqrt a.toNat < 2 ^ 128 :=
    ProofForgeFin.Sqrt.sqrt_lt_two_pow_of_lt a.isLt (by decide)
  have hp128 : (2 : Nat) ^ 128 < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) (by decide)
  have hadd : (sqrt a + (if sqrt a * sqrt a < a then 1 else 0)).toNat =
      Nat.sqrt a.toNat + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
    by_cases hc : sqrt a * sqrt a < a
    · have hcN : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
        have h := BitVec.lt_def.mp hc
        rw [hsq] at h
        exact h
      have h1 : ((1 : U256)).toNat = 1 := ProofForgeFin.WordBridge.toNat_one' (by decide)
      have hbd : (sqrt a).toNat + ((1 : U256)).toNat < 2 ^ 256 := by rw [hrr, h1]; omega
      rw [if_pos hc, if_pos hcN, ProofForgeFin.WordBridge.toNat_add_of_lt' hbd, hrr, h1]
    · have hcN : ¬ Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
        intro h
        exact hc (BitVec.lt_def.mpr (by rw [hsq]; exact h))
      have h0 : ((0 : U256)).toNat = 0 := ProofForgeFin.WordBridge.toNat_zero'
      have hbd : (sqrt a).toNat + ((0 : U256)).toNat < 2 ^ 256 := by rw [hrr, h0]; omega
      rw [if_neg hc, if_neg hcN, ProofForgeFin.WordBridge.toNat_add_of_lt' hbd, hrr, h0]
  unfold sqrtUp
  exact hadd

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  unfold SqrtNotAbove
  intro a
  rw [sqrt_toNat]
  exact Nat.sqrt_le _

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  unfold SqrtNotBelow
  intro a
  rw [sqrt_toNat]
  exact Nat.lt_succ_sqrt _

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  unfold SqrtUpCovers
  intro a
  rw [sqrtUp_toNat]
  exact ProofForgeFin.Sqrt.le_mul_self_sqrt_add_ite _

theorem req_sqrt_up_tight  : SqrtUpTight sqrt := by
  unfold SqrtUpTight
  intro a h
  rw [sqrtUp_toNat] at h ⊢
  exact ProofForgeFin.Sqrt.sqrt_add_ite_sub_one_mul_self_lt h

theorem req_mint_backed    : MintBacked sqrt := by
  unfold MintBacked
  intro a0 a1 l h
  obtain ⟨hprod, hroot, hliq⟩ := firstMint_eq_some h
  have hprodEq : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have h1 : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_toNat, hprodEq]
  have hliq2 : l.toNat + 1000 = Nat.sqrt (a0.toNat * a1.toNat) := by rw [hliq, h1]
  calc (l.toNat + 1000) * (l.toNat + 1000)
      = Nat.sqrt (a0.toNat * a1.toNat) * Nat.sqrt (a0.toNat * a1.toNat) := by rw [hliq2]
    _ ≤ a0.toNat * a1.toNat := Nat.sqrt_le _

theorem req_mint_full      : MintFull sqrt := by
  unfold MintFull
  intro a0 a1 l h
  obtain ⟨hprod, hroot, hliq⟩ := firstMint_eq_some h
  have hprodEq : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have h1 : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_toNat, hprodEq]
  have hliq2 : l.toNat + 1000 = Nat.sqrt (a0.toNat * a1.toNat) := by rw [hliq, h1]
  have e : l.toNat + 1001 = Nat.sqrt (a0.toNat * a1.toNat) + 1 := by omega
  rw [e]
  exact Nat.lt_succ_sqrt _

theorem req_mint_live      : MintLive sqrt := by
  unfold MintLive
  intro a0 a1 hprod hbig
  have hprodEq : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have h1 : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_toNat, hprodEq]
  apply firstMint_isSome hprod
  rw [h1]
  have h1001 : 1001 ≤ Nat.sqrt (a0.toNat * a1.toNat) :=
    ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le (m := 1001) hbig
  omega

theorem req_newton_budget  : NewtonBudget sqrt := by
  refine ⟨7, by decide, fun a => ?_⟩
  simp only [sqrt, newtonSqrt, iterate, newtonStep]
