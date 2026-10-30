import ProofForgeFin.FixedPoint
/-!
# Fixed-point exponentiation by squaring

DSMath `rpow(x, n)` (MakerDAO), Solmate `FixedPointMathLib.rpow(x, n, scalar)` and MakerDAO
`Jug`'s assembly `rpow` raise a fixed-point number `x` (value `x / s` for the scale `s`) to an
integer power `n` by repeated squaring, rounding after every product:

```
z = n % 2 != 0 ? x : s;
for (n /= 2; n != 0; n /= 2) {
    x = mul(x, x);
    if (n % 2 != 0) { z = mul(z, x); }
}
```

`rpowWith mul s x n` is this loop for any product `mul`; `rpowDown`, `rpowUp` and `rpowHalf`
use the product rounded down, rounded up, and rounded half up (`(a * b + s / 2) / s`, DSMath's
`rmul` and Solmate's rounding). The exact value is `x^n / s^(n - 1)`, which in fixed point is
`s * (x / s)^n`; a result `r` is compared with it by cross-multiplication: `r * s^n ≤ x^n * s`
reads "`r` is at most the exact value".

* `rpowWith_invariant`: a property of (value, exponent) pairs that holds for `s` (exponent 0)
  and `x` (exponent 1) and is preserved by `mul` holds for the result with exponent `n`.
  Every bound below is an instance.
* `rpowDown_le` and `le_rpowUp`: rounding down never exceeds the exact value, rounding up never
  falls below it (for every base).
* `rpowDown_ge` and `rpowDown_ge_bernoulli`: for a base at least one (`s ≤ x`, interest
  accrual), rounding down loses at most a factor `(1 - 1/s)^(n-1)`, hence at most the relative
  amount `(n - 1) / s`: `x^n * (s - (n - 1)) ≤ rpowDown s x n * s^n`.
* `rpowUp_le`: for `s ≤ x`, rounding up gains at most a factor `(1 + 1/s)^(n-1)`.
* `rpowDown_le_rpowHalf`, `rpowHalf_le_rpowUp`: the half-up result lies between the two, so it
  inherits both error bounds.

Overflow is not modeled: the EVM functions revert when an intermediate product does not fit in
256 bits, and the statements here are about the natural-number computation they perform when
they do not revert.
-/

namespace ProofForgeFin.Evm

/-! ## The loop -/

/-- The loop of `rpow`: `for (n /= 2; n != 0; n /= 2) { x = mul(x, x); if (n % 2 != 0) z =
mul(z, x); }`, started with the halved exponent `m`. -/
def rpowLoop (mul : Nat → Nat → Nat) (x z m : Nat) : Nat :=
  if m = 0 then z
  else rpowLoop mul (mul x x) (if m % 2 = 1 then mul z (mul x x) else z) (m / 2)
termination_by m
decreasing_by omega

/-- `rpow` with the product `mul` and the scale `s`: `z = n % 2 != 0 ? x : s`, then the loop. -/
def rpowWith (mul : Nat → Nat → Nat) (s x n : Nat) : Nat :=
  rpowLoop mul x (if n % 2 = 1 then x else s) (n / 2)

/-- The fixed-point product rounded half up: `(a * b + s / 2) / s` (DSMath `rmul`). -/
def mulHalf (s a b : Nat) : Nat := (a * b + s / 2) / s

/-- `rpow` with products rounded down. -/
def rpowDown (s x n : Nat) : Nat := rpowWith (mulDown s) s x n

/-- `rpow` with products rounded up. -/
def rpowUp (s x n : Nat) : Nat := rpowWith (mulUp s) s x n

/-- `rpow` with products rounded half up: DSMath `rpow`, Solmate `rpow`, MakerDAO `Jug.rpow`. -/
def rpowHalf (s x n : Nat) : Nat := rpowWith (mulHalf s) s x n

/-- The loop with a zero halved exponent returns the accumulator. -/
theorem rpowLoop_zero (mul : Nat → Nat → Nat) (x z : Nat) : rpowLoop mul x z 0 = z := by
  rw [rpowLoop]; simp

/-- One iteration of the loop. -/
theorem rpowLoop_succ (mul : Nat → Nat → Nat) (x z : Nat) {m : Nat} (hm : m ≠ 0) :
    rpowLoop mul x z m =
      rpowLoop mul (mul x x) (if m % 2 = 1 then mul z (mul x x) else z) (m / 2) := by
  rw [rpowLoop]; simp [hm]

/-- The loop invariant: if `R` holds for `x` with exponent `px` and for `z` with exponent `pz`
and is preserved by `mul` (exponents add), it holds for the result with exponent
`pz + 2 * px * m`. -/
theorem rpowLoop_invariant (mul : Nat → Nat → Nat) (R : Nat → Nat → Prop)
    (hmul : ∀ a b p q, R a p → R b q → R (mul a b) (p + q)) :
    ∀ m x z px pz, R x px → R z pz → R (rpowLoop mul x z m) (pz + 2 * px * m) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro x z px pz hx hz
    by_cases hm : m = 0
    · subst hm; rw [rpowLoop_zero]; simpa using hz
    · rw [rpowLoop_succ mul x z hm]
      have hxx := hmul x x px px hx hx
      have hm2 : m / 2 < m := by omega
      by_cases ho : m % 2 = 1
      · rw [ite_eq_left ho]
        have hz' := hmul z (mul x x) pz (px + px) hz hxx
        have := ih (m / 2) hm2 (mul x x) (mul z (mul x x)) (px + px) (pz + (px + px)) hxx hz'
        have e : pz + (px + px) + 2 * (px + px) * (m / 2) = pz + 2 * px * m := by
          have : m = 2 * (m / 2) + 1 := by omega
          generalize m / 2 = k at this ⊢
          subst this
          grind
        rwa [e] at this
      · rw [ite_eq_right ho]
        have := ih (m / 2) hm2 (mul x x) z (px + px) pz hxx hz
        have e : pz + 2 * (px + px) * (m / 2) = pz + 2 * px * m := by
          have : m = 2 * (m / 2) := by omega
          generalize m / 2 = k at this ⊢
          subst this
          grind
        rwa [e] at this

/-- The invariant principle for `rpow`: a property of (value, exponent) pairs that holds for the
scale `s` with exponent 0 and for the base `x` with exponent 1 and that `mul` preserves holds for
`rpowWith mul s x n` with exponent `n`. -/
theorem rpowWith_invariant (mul : Nat → Nat → Nat) (R : Nat → Nat → Prop)
    (hmul : ∀ a b p q, R a p → R b q → R (mul a b) (p + q)) {s x : Nat} (hs : R s 0) (hx : R x 1)
    (n : Nat) : R (rpowWith mul s x n) n := by
  unfold rpowWith
  have hz : R (if n % 2 = 1 then x else s) (n % 2) := by
    by_cases h : n % 2 = 1
    · rw [ite_eq_left h, h]; exact hx
    · rw [ite_eq_right h, show n % 2 = 0 by omega]; exact hs
  have := rpowLoop_invariant mul R hmul (n / 2) x _ 1 (n % 2) hx hz
  rwa [show n % 2 + 2 * 1 * (n / 2) = n by omega] at this

/-- Comparison of two loops: with pointwise ordered, monotone products, ordered inputs give
ordered results. -/
theorem rpowLoop_le (mul₁ mul₂ : Nat → Nat → Nat)
    (hmul : ∀ a a' b b', a ≤ a' → b ≤ b' → mul₁ a b ≤ mul₂ a' b') :
    ∀ m x x' z z', x ≤ x' → z ≤ z' → rpowLoop mul₁ x z m ≤ rpowLoop mul₂ x' z' m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro x x' z z' hx hz
    by_cases hm : m = 0
    · subst hm; rw [rpowLoop_zero, rpowLoop_zero]; exact hz
    · rw [rpowLoop_succ mul₁ x z hm, rpowLoop_succ mul₂ x' z' hm]
      have hxx := hmul x x' x x' hx hx
      apply ih (m / 2) (by omega) _ _ _ _ hxx
      split
      · exact hmul _ _ _ _ hz hxx
      · exact hz

/-- `rpowWith` is monotone in the product: pointwise ordered, monotone products give ordered
results. -/
theorem rpowWith_le (mul₁ mul₂ : Nat → Nat → Nat)
    (hmul : ∀ a a' b b', a ≤ a' → b ≤ b' → mul₁ a b ≤ mul₂ a' b') (s x n : Nat) :
    rpowWith mul₁ s x n ≤ rpowWith mul₂ s x n := by
  unfold rpowWith
  exact rpowLoop_le mul₁ mul₂ hmul _ _ _ _ _ (Nat.le_refl _) (Nat.le_refl _)

/-! ## One-sided bounds for every base -/

/-- Rounding down never exceeds the exact value: `rpowDown s x n * s^n ≤ x^n * s`. -/
theorem rpowDown_le {s : Nat} (hs : 0 < s) (x n : Nat) : rpowDown s x n * s ^ n ≤ x ^ n * s := by
  unfold rpowDown
  apply rpowWith_invariant (mulDown s) (fun a p => a * s ^ p ≤ x ^ p * s)
  · intro a b p q ha hb
    show mulDown s a b * s ^ (p + q) ≤ x ^ (p + q) * s
    have h1 := mulDown_mul_le s a b
    have h2 : a * s ^ p * (b * s ^ q) ≤ x ^ p * s * (x ^ q * s) := Nat.mul_le_mul ha hb
    apply Nat.le_of_mul_le_mul_right _ hs
    calc mulDown s a b * s ^ (p + q) * s = mulDown s a b * s * s ^ (p + q) := by
          rw [Nat.mul_right_comm]
      _ ≤ a * b * s ^ (p + q) := Nat.mul_le_mul_right _ h1
      _ = a * s ^ p * (b * s ^ q) := by rw [Nat.pow_add]; grind
      _ ≤ x ^ p * s * (x ^ q * s) := h2
      _ = x ^ (p + q) * s * s := by rw [Nat.pow_add]; grind
  · show s * s ^ 0 ≤ x ^ 0 * s; simp
  · show x * s ^ 1 ≤ x ^ 1 * s; simp

/-- Rounding up never falls below the exact value: `x^n * s ≤ rpowUp s x n * s^n`. -/
theorem le_rpowUp {s : Nat} (hs : 0 < s) (x n : Nat) : x ^ n * s ≤ rpowUp s x n * s ^ n := by
  unfold rpowUp
  apply rpowWith_invariant (mulUp s) (fun a p => x ^ p * s ≤ a * s ^ p)
  · intro a b p q ha hb
    show x ^ (p + q) * s ≤ mulUp s a b * s ^ (p + q)
    have h1 := le_mulUp_mul s a b hs
    have h2 : x ^ p * s * (x ^ q * s) ≤ a * s ^ p * (b * s ^ q) := Nat.mul_le_mul ha hb
    apply Nat.le_of_mul_le_mul_right _ hs
    calc x ^ (p + q) * s * s = x ^ p * s * (x ^ q * s) := by rw [Nat.pow_add]; grind
      _ ≤ a * s ^ p * (b * s ^ q) := h2
      _ = a * b * s ^ (p + q) := by rw [Nat.pow_add]; grind
      _ ≤ mulUp s a b * s * s ^ (p + q) := Nat.mul_le_mul_right _ h1
      _ = mulUp s a b * s ^ (p + q) * s := by rw [Nat.mul_right_comm]
  · show s ^ 0 * s ≤ s * s ^ 0; simp [Nat.mul_comm]
  · show x ^ 1 * s ≤ x * s ^ 1; simp

/-! ## Error bounds for a base at least one -/

/-- One rounded-down product of two numbers at least `s` loses at most a factor `(s - 1) / s`:
`a * b * (s - 1) ≤ mulDown s a b * s * s`. -/
theorem mul_pred_le_mulDown {s a b : Nat} (hs : 0 < s) (ha : s ≤ a) (hb : s ≤ b) :
    a * b * (s - 1) ≤ mulDown s a b * s * s := by
  have ⟨_, h2⟩ := mulDown_spec s a b hs
  have hab : s * s ≤ a * b := Nat.mul_le_mul ha hb
  rw [Nat.add_mul, Nat.one_mul] at h2
  -- `mulDown * s ≥ a * b - s + 1`, and `a * b ≥ s * s`
  have hss : s ≤ s * s := Nat.le_mul_of_pos_left s hs
  have h3 : (a * b - s + 1) * s ≤ mulDown s a b * s * s := Nat.mul_le_mul_right _ (by omega)
  have h4 : a * b * (s - 1) ≤ (a * b - s + 1) * s := by
    have e1 : a * b * (s - 1) = a * b * s - a * b := by rw [Nat.mul_sub, Nat.mul_one]
    have e2 : (a * b - s + 1) * s = a * b * s - s * s + s := by
      rw [Nat.add_mul, Nat.one_mul, Nat.sub_mul]
    have h5 : a * b ≤ a * b * s := Nat.le_mul_of_pos_right _ hs
    have h6 : s * s ≤ a * b * s := Nat.le_trans hab h5
    rw [e1, e2]
    omega
  exact Nat.le_trans h4 h3

/-- One rounded-up product of two numbers at least `s` gains at most a factor `(s + 1) / s`:
`mulUp s a b * s * s ≤ a * b * (s + 1)`. -/
theorem mulUp_le_mul_succ {s a b : Nat} (hs : 0 < s) (ha : s ≤ a) (hb : s ≤ b) :
    mulUp s a b * s * s ≤ a * b * (s + 1) := by
  have ⟨_, h2⟩ := mulUp_spec s a b hs
  have hab : s * s ≤ a * b := Nat.mul_le_mul ha hb
  have h3 : mulUp s a b * s * s ≤ (a * b + s) * s := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_one] at *
  omega

/-- Rounding down twice the same way is monotone in the left factor once it is at least `s`. -/
theorem le_mulDown_of_le {s a b : Nat} (hs : 0 < s) (ha : s ≤ a) : b ≤ mulDown s a b := by
  unfold mulDown mulDiv
  rw [Nat.le_div_iff_mul_le hs]
  rw [Nat.mul_comm a b]; exact Nat.mul_le_mul_left _ ha

/-- For a base at least one, rounding down loses at most a factor `(1 - 1/s)^(n-1)`:
`x^n * (s - 1)^(n-1) * s ≤ rpowDown s x n * s^n * s^(n-1)`. -/
theorem rpowDown_ge {s x : Nat} (hs : 0 < s) (hx : s ≤ x) (n : Nat) :
    x ^ n * (s - 1) ^ (n - 1) * s ≤ rpowDown s x n * s ^ n * s ^ (n - 1) := by
  have key := rpowWith_invariant (mulDown s)
    (fun a p => s ≤ a ∧ x ^ p * (s - 1) ^ (p - 1) * s ≤ a * s ^ p * s ^ (p - 1))
    (s := s) (x := x) ?_ ?_ ?_ n
  · exact key.2
  · intro a b p q ⟨ha, hpa⟩ ⟨hb, hpb⟩
    refine ⟨Nat.le_trans hb (le_mulDown_of_le hs ha), ?_⟩
    by_cases hp : p = 0
    · subst hp
      rw [Nat.zero_add]
      exact Nat.le_trans hpb (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_mulDown_of_le hs ha)))
    by_cases hq : q = 0
    · subst hq
      rw [Nat.add_zero]
      rw [mulDown_comm]
      exact Nat.le_trans hpa (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_mulDown_of_le hs hb)))
    have e : p + q - 1 = (p - 1) + (q - 1) + 1 := by omega
    rw [e]
    have h1 := mul_pred_le_mulDown hs ha hb
    have h2 := Nat.mul_le_mul hpa hpb
    have h3 : x ^ p * (s - 1) ^ (p - 1) * s * (x ^ q * (s - 1) ^ (q - 1) * s) * (s - 1) ≤
        a * s ^ p * s ^ (p - 1) * (b * s ^ q * s ^ (q - 1)) * (s - 1) := Nat.mul_le_mul_right _ h2
    apply Nat.le_of_mul_le_mul_right _ hs
    calc x ^ (p + q) * (s - 1) ^ (p - 1 + (q - 1) + 1) * s * s
        = x ^ p * (s - 1) ^ (p - 1) * s * (x ^ q * (s - 1) ^ (q - 1) * s) * (s - 1) := by
          rw [Nat.pow_add, Nat.pow_succ, Nat.pow_add]; grind
      _ ≤ a * s ^ p * s ^ (p - 1) * (b * s ^ q * s ^ (q - 1)) * (s - 1) := h3
      _ = a * b * (s - 1) * (s ^ p * s ^ q * s ^ (p - 1) * s ^ (q - 1)) := by grind
      _ ≤ mulDown s a b * s * s * (s ^ p * s ^ q * s ^ (p - 1) * s ^ (q - 1)) :=
          Nat.mul_le_mul_right _ h1
      _ = mulDown s a b * s ^ (p + q) * s ^ (p - 1 + (q - 1) + 1) * s := by
          rw [Nat.pow_add, Nat.pow_succ, Nat.pow_add]; grind
  · exact ⟨Nat.le_refl _, by simp⟩
  · exact ⟨hx, by simp⟩

/-- Bernoulli's inequality in cross-multiplied form: `s^k * (s - k) ≤ (s - 1)^k * s`, that is
`(1 - 1/s)^k ≥ 1 - k/s`. -/
theorem bernoulli (s k : Nat) : s ^ k * (s - k) ≤ (s - 1) ^ k * s := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : s ≤ k
    · rw [show s - (k + 1) = 0 by omega, Nat.mul_zero]; exact Nat.zero_le _
    · calc s ^ (k + 1) * (s - (k + 1)) = s ^ k * (s * (s - (k + 1))) := by
            rw [Nat.pow_succ, Nat.mul_assoc]
        _ ≤ s ^ k * ((s - k) * (s - 1)) := by
            apply Nat.mul_le_mul_left
            have e1 : s * (s - (k + 1)) = s * s - s * (k + 1) := Nat.mul_sub _ _ _
            have e2 : (s - k) * (s - 1) = (s - k) * s - (s - k) := by
              rw [Nat.mul_sub, Nat.mul_one]
            rw [e1, e2, Nat.sub_mul, Nat.mul_add, Nat.mul_one]
            have : k * s ≤ s * s := Nat.mul_le_mul_right _ (by omega)
            have : s * k + s ≤ s * s := by
              rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
            rw [Nat.mul_comm k s] at *
            omega
        _ = s ^ k * (s - k) * (s - 1) := by rw [Nat.mul_assoc]
        _ ≤ (s - 1) ^ k * s * (s - 1) := Nat.mul_le_mul_right _ ih
        _ = (s - 1) ^ (k + 1) * s := by rw [Nat.pow_succ]; grind

/-- For a base at least one, rounding down loses at most the relative amount `(n - 1) / s`:
`x^n * (s - (n - 1)) ≤ rpowDown s x n * s^n`, that is
`rpowDown s x n ≥ exact * (1 - (n - 1) / s)` with `exact = x^n / s^(n-1)`. -/
theorem rpowDown_ge_bernoulli {s x : Nat} (hs : 0 < s) (hx : s ≤ x) (n : Nat) :
    x ^ n * (s - (n - 1)) ≤ rpowDown s x n * s ^ n := by
  have h1 := rpowDown_ge hs hx n
  have h2 := bernoulli s (n - 1)
  have hp : 0 < s ^ (n - 1) := Nat.pow_pos hs
  apply Nat.le_of_mul_le_mul_right _ hp
  calc x ^ n * (s - (n - 1)) * s ^ (n - 1) = x ^ n * (s ^ (n - 1) * (s - (n - 1))) := by grind
    _ ≤ x ^ n * ((s - 1) ^ (n - 1) * s) := Nat.mul_le_mul_left _ h2
    _ = x ^ n * (s - 1) ^ (n - 1) * s := by grind
    _ ≤ rpowDown s x n * s ^ n * s ^ (n - 1) := h1

/-- For a base at least one, rounding up gains at most a factor `(1 + 1/s)^(n-1)`:
`rpowUp s x n * s^n * s^(n-1) ≤ x^n * (s + 1)^(n-1) * s`. -/
theorem rpowUp_le {s x : Nat} (hs : 0 < s) (hx : s ≤ x) (n : Nat) :
    rpowUp s x n * s ^ n * s ^ (n - 1) ≤ x ^ n * (s + 1) ^ (n - 1) * s := by
  have key := rpowWith_invariant (mulUp s)
    (fun a p => s ≤ a ∧ a * s ^ p * s ^ (p - 1) ≤ x ^ p * (s + 1) ^ (p - 1) * s)
    (s := s) (x := x) ?_ ?_ ?_ n
  · exact key.2
  · intro a b p q ⟨ha, hpa⟩ ⟨hb, hpb⟩
    have hm : s ≤ mulUp s a b := Nat.le_trans hb (Nat.le_trans (le_mulDown_of_le hs ha)
      (mulDown_le_mulUp s a b))
    refine ⟨hm, ?_⟩
    by_cases hp : p = 0
    · subst hp
      have has : a = s := by simp at hpa; omega
      rw [has, Nat.zero_add, mulUp_comm, mulUp_one s b hs]; exact hpb
    by_cases hq : q = 0
    · subst hq
      have hbs : b = s := by simp at hpb; omega
      rw [hbs, Nat.add_zero, mulUp_one s a hs]; exact hpa
    have e : p + q - 1 = (p - 1) + (q - 1) + 1 := by omega
    rw [e]
    have h1 := mulUp_le_mul_succ hs ha hb
    have h2 := Nat.mul_le_mul hpa hpb
    have h3 : a * s ^ p * s ^ (p - 1) * (b * s ^ q * s ^ (q - 1)) * (s + 1) ≤
        x ^ p * (s + 1) ^ (p - 1) * s * (x ^ q * (s + 1) ^ (q - 1) * s) * (s + 1) :=
      Nat.mul_le_mul_right _ h2
    apply Nat.le_of_mul_le_mul_right _ hs
    calc mulUp s a b * s ^ (p + q) * s ^ (p - 1 + (q - 1) + 1) * s
        = mulUp s a b * s * s * (s ^ p * s ^ q * s ^ (p - 1) * s ^ (q - 1)) := by
          rw [Nat.pow_add, Nat.pow_succ, Nat.pow_add]; grind
      _ ≤ a * b * (s + 1) * (s ^ p * s ^ q * s ^ (p - 1) * s ^ (q - 1)) :=
          Nat.mul_le_mul_right _ h1
      _ = a * s ^ p * s ^ (p - 1) * (b * s ^ q * s ^ (q - 1)) * (s + 1) := by grind
      _ ≤ x ^ p * (s + 1) ^ (p - 1) * s * (x ^ q * (s + 1) ^ (q - 1) * s) * (s + 1) := h3
      _ = x ^ (p + q) * (s + 1) ^ (p - 1 + (q - 1) + 1) * s * s := by
          rw [Nat.pow_add, Nat.pow_succ, Nat.pow_add]; grind
  · exact ⟨Nat.le_refl _, by simp⟩
  · exact ⟨hx, by simp⟩

/-! ## Rounding half up -/

/-- The product rounded half up lies between the two directed roundings. -/
theorem mulDown_le_mulHalf_le_mulUp {s : Nat} (hs : 0 < s) (a b : Nat) :
    mulDown s a b ≤ mulHalf s a b ∧ mulHalf s a b ≤ mulUp s a b := by
  unfold mulDown mulHalf mulUp mulDiv mulDivUp ceilDiv
  constructor
  · exact Nat.div_le_div_right (Nat.le_add_right _ _)
  · exact Nat.div_le_div_right (by omega)

/-- `mulHalf` is monotone in both factors. -/
theorem mulHalf_mono (s : Nat) {a a' b b' : Nat} (ha : a ≤ a') (hb : b ≤ b') :
    mulHalf s a b ≤ mulHalf s a' b' := by
  unfold mulHalf
  exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul ha hb) _)

/-- The half-up result is at least the rounded-down one. -/
theorem rpowDown_le_rpowHalf {s : Nat} (hs : 0 < s) (x n : Nat) : rpowDown s x n ≤ rpowHalf s x n :=
  rpowWith_le _ _ (fun _ _ _ _ ha hb => Nat.le_trans (mulDown_mono s ha hb)
    (mulDown_le_mulHalf_le_mulUp hs _ _).1) s x n

/-- The half-up result is at most the rounded-up one. -/
theorem rpowHalf_le_rpowUp {s : Nat} (hs : 0 < s) (x n : Nat) : rpowHalf s x n ≤ rpowUp s x n :=
  rpowWith_le _ _ (fun _ _ _ _ ha hb => Nat.le_trans (mulHalf_mono s ha hb)
    (mulDown_le_mulHalf_le_mulUp hs _ _).2) s x n

/-- The error bound of DSMath and Solmate `rpow` (rounding half up) for a base at least one:
`x^n * (s - (n - 1)) ≤ rpowHalf s x n * s^n` and
`rpowHalf s x n * s^n * s^(n-1) ≤ x^n * (s + 1)^(n-1) * s`. -/
theorem rpowHalf_bounds {s x : Nat} (hs : 0 < s) (hx : s ≤ x) (n : Nat) :
    x ^ n * (s - (n - 1)) ≤ rpowHalf s x n * s ^ n ∧
      rpowHalf s x n * s ^ n * s ^ (n - 1) ≤ x ^ n * (s + 1) ^ (n - 1) * s := by
  constructor
  · exact Nat.le_trans (rpowDown_ge_bernoulli hs hx n)
      (Nat.mul_le_mul_right _ (rpowDown_le_rpowHalf hs x n))
  · exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (rpowHalf_le_rpowUp hs x n)))
      (rpowUp_le hs hx n)

/-- With exact products (`mul a b = a * b / s` where `s` divides every product, for example
`s = 1`), `rpow` is the power: `rpowWith (mulDown 1) 1 x n = x^n`. -/
theorem rpowDown_one (x n : Nat) : rpowDown 1 x n = x ^ n := by
  have := rpowWith_invariant (mulDown 1) (fun a p => a = x ^ p)
    (fun a b p q ha hb => by
      show mulDown 1 a b = x ^ (p + q)
      rw [mulDown, mulDiv, Nat.div_one, ha, hb, Nat.pow_add])
    (s := 1) (x := x) (by simp) (by simp) n
  exact this

end ProofForgeFin.Evm
