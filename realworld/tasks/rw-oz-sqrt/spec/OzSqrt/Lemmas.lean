import OzSqrt.Spec
/-!
# Helper lemmas and sanity theorems (protected, agent-visible)

Proved facts about the protected definitions `log2`, `newtonStep`, `iterate`, `min` and
`firstMint`. They say nothing about the definition hole; a candidate may use them.

* `toNat_log2`: the port of `Math.log2` is Lean core's `Nat.log2` on every `uint256`.
* `toNat_newtonStep`: a Newton line of `Math.sqrt` is the step on natural numbers
  `(r + a / r) / 2` when `r + a / r` does not wrap.
* `firstMint_eq_some`: when the first deposit succeeds, its liquidity is the root minus the
  minimum liquidity.

The sanity theorems at the end show that the requirements are not vacuous:

* `floor_unique`: a routine that meets REQ-SQRT-NOT-ABOVE and REQ-SQRT-NOT-BELOW returns
  `2^102 - 1` at `2^204 - 1`;
* `mint_example`: with such a routine the first deposit of `2^102 + 1` and `2^102 - 1` mints
  `2^102 - 1001`, so the deposit requirements constrain a real output.
-/

namespace OzSqrt

/-- `log2Step` on values: if `v` is the input divided by `2^r` and below `2^(2k)`, then after the
step the value is the input divided by `2^r'`, below `2^k`, still positive if it was. -/
theorem log2Step_spec (k A : Nat) (_hk : 0 < k) (p : U256 × U256) (hv : p.1.toNat = A / 2 ^ p.2.toNat)
    (hlt : p.1.toNat < 2 ^ (2 * k)) (hr : p.2.toNat + k < 2 ^ 256) (hpos : 0 < p.1.toNat) :
    (log2Step k p).1.toNat = A / 2 ^ (log2Step k p).2.toNat ∧ (log2Step k p).1.toNat < 2 ^ k ∧
      0 < (log2Step k p).1.toNat ∧ (log2Step k p).2.toNat ≤ p.2.toNat + k := by
  obtain ⟨v, r⟩ := p
  simp only at hv hlt hr hpos ⊢
  unfold log2Step
  simp only
  have hsh : (v >>> k).toNat = v.toNat / 2 ^ k := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases h : v >>> k > 0
  · rw [ite_eq_left h]
    simp only
    have h' : 0 < v.toNat / 2 ^ k := by
      have := BitVec.lt_def.mp h; simpa [hsh] using this
    have hk256 : k < 2 ^ 256 := by omega
    have hadd : (r + BitVec.ofNat 256 k).toNat = r.toNat + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk256, Nat.mod_eq_of_lt hr]
    rw [hsh, hadd]
    refine ⟨?_, ?_, h', Nat.le_refl _⟩
    · rw [hv, Nat.div_div_eq_div_mul, Nat.pow_add]
    · apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr
      rw [← Nat.pow_add, show k + k = 2 * k by omega]; exact hlt
  · rw [ite_eq_right h]
    simp only
    have h' : v.toNat / 2 ^ k = 0 := by
      have : ¬ 0 < (v >>> k).toNat := fun c => h (BitVec.lt_def.mpr (by simpa using c))
      omega
    refine ⟨hv, ?_, hpos, Nat.le_add_right _ _⟩
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)).mp h'

/-- The port of `Math.log2` is the floor of the base-2 logarithm, `Nat.log2`, on every `uint256`
(both are 0 at 0). -/
theorem toNat_log2 (a : U256) : (log2 a).toNat = Nat.log2 a.toNat := by
  by_cases h0 : a.toNat = 0
  · have : a = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
    subst this
    rw [h0]; decide
  have hpos : 0 < a.toNat := Nat.pos_of_ne_zero h0
  have ha := a.isLt
  unfold log2
  have s128 := log2Step_spec 128 a.toNat (by decide) (a, 0) (by simp) (by simpa using ha) (by simp) hpos
  have hz : ((a, (0 : U256)) : U256 × U256).2.toNat = 0 := rfl
  rw [hz] at s128
  generalize log2Step 128 (a, 0) = p1 at s128 ⊢
  have s64 := log2Step_spec 64 a.toNat (by decide) p1 s128.1 s128.2.1 (by omega) s128.2.2.1
  generalize log2Step 64 p1 = p2 at s64 ⊢
  have s32 := log2Step_spec 32 a.toNat (by decide) p2 s64.1 s64.2.1 (by omega) s64.2.2.1
  generalize log2Step 32 p2 = p3 at s32 ⊢
  have s16 := log2Step_spec 16 a.toNat (by decide) p3 s32.1 s32.2.1 (by omega) s32.2.2.1
  generalize log2Step 16 p3 = p4 at s16 ⊢
  have s8 := log2Step_spec 8 a.toNat (by decide) p4 s16.1 s16.2.1 (by omega) s16.2.2.1
  generalize log2Step 8 p4 = p5 at s8 ⊢
  have s4 := log2Step_spec 4 a.toNat (by decide) p5 s8.1 s8.2.1 (by omega) s8.2.2.1
  generalize log2Step 4 p5 = p6 at s4 ⊢
  have s2 := log2Step_spec 2 a.toNat (by decide) p6 s4.1 s4.2.1 (by omega) s4.2.2.1
  generalize log2Step 2 p6 = p7 at s2 ⊢
  have s1 := log2Step_spec 1 a.toNat (by decide) p7 s2.1 s2.2.1 (by omega) s2.2.2.1
  generalize log2Step 1 p7 = q at s1 ⊢
  obtain ⟨hq, hq1, hq0, -⟩ := s1
  have hq' : (q.1).toNat = 1 := by omega
  rw [hq'] at hq
  symm
  apply (Nat.log2_eq_iff h0).mpr
  have hp := Nat.two_pow_pos q.2.toNat
  constructor
  · have := (Nat.le_div_iff_mul_le hp).mp (Nat.le_of_eq hq); omega
  · have := Nat.lt_succ_of_le (Nat.le_of_eq hq.symm)
    have := (Nat.div_lt_iff_lt_mul hp).mp this
    rw [Nat.pow_succ]; omega

/-- `Math.min` on values is `Nat.min`. -/
theorem toNat_min (a b : U256) : (min a b).toNat = Nat.min a.toNat b.toNat := by
  unfold min Nat.min
  by_cases h : a < b
  · rw [ite_eq_left h]; have := BitVec.lt_def.mp h; omega
  · rw [ite_eq_right h]; have : ¬ a.toNat < b.toNat := fun c => h (BitVec.lt_def.mpr c); omega

/-- A Newton line `(r + a / r) >> 1` of `Math.sqrt` is `(r + a / r) / 2` on values when
`r + a / r` does not wrap. -/
theorem toNat_newtonStep (a r : U256) (h : r.toNat + a.toNat / r.toNat < 2 ^ 256) :
    (newtonStep a r).toNat = (r.toNat + a.toNat / r.toNat) / 2 := by
  unfold newtonStep
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_udiv,
    Nat.mod_eq_of_lt h]

/-- The product of the deposit when it does not overflow. -/
theorem toNat_mul_of_lt {a b : U256} (h : a.toNat * b.toNat < 2 ^ 256) : (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

/-- When the first deposit succeeds, the product did not overflow, the root of the product is
above `MINIMUM_LIQUIDITY`, and the liquidity is the root minus `MINIMUM_LIQUIDITY`. -/
theorem firstMint_eq_some {sqrt : SqrtFn} {a0 a1 l : U256} (h : firstMint sqrt a0 a1 = some l) :
    a0.toNat * a1.toNat < 2 ^ 256 ∧ 1000 < (sqrt (a0 * a1)).toNat ∧
      l.toNat + 1000 = (sqrt (a0 * a1)).toNat := by
  unfold firstMint at h
  by_cases h1 : 2 ^ 256 ≤ a0.toNat * a1.toNat
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  simp only at h
  by_cases h2 : sqrt (a0 * a1) < MINIMUM_LIQUIDITY
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h
  have h2' : 1000 ≤ (sqrt (a0 * a1)).toNat := by
    have : ¬ (sqrt (a0 * a1)).toNat < 1000 := fun c => h2 (BitVec.lt_def.mpr (by simpa [MINIMUM_LIQUIDITY] using c))
    omega
  have hsub : (sqrt (a0 * a1) - MINIMUM_LIQUIDITY).toNat = (sqrt (a0 * a1)).toNat - 1000 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simpa [MINIMUM_LIQUIDITY] using h2'))]; rfl
  split at h
  · cases h
  · rename_i h3
    cases h
    have : (sqrt (a0 * a1) - MINIMUM_LIQUIDITY).toNat ≠ 0 := fun c => h3 (BitVec.eq_of_toNat_eq (by simpa using c))
    refine ⟨by omega, by omega, by omega⟩

/-- The first deposit succeeds when the product does not overflow and its root, as computed by
the routine, is above `MINIMUM_LIQUIDITY`. -/
theorem firstMint_isSome {sqrt : SqrtFn} {a0 a1 : U256} (h1 : a0.toNat * a1.toNat < 2 ^ 256)
    (h2 : 1000 < (sqrt (a0 * a1)).toNat) : (firstMint sqrt a0 a1).isSome := by
  unfold firstMint
  rw [ite_eq_right (by omega)]
  simp only
  have h2' : ¬ sqrt (a0 * a1) < MINIMUM_LIQUIDITY := fun c => by
    have := BitVec.lt_def.mp c; simp [MINIMUM_LIQUIDITY] at this; omega
  rw [ite_eq_right h2']
  have hsub : (sqrt (a0 * a1) - MINIMUM_LIQUIDITY).toNat = (sqrt (a0 * a1)).toNat - 1000 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simp [MINIMUM_LIQUIDITY]; omega))]; rfl
  have h3 : ¬ sqrt (a0 * a1) - MINIMUM_LIQUIDITY = 0 := fun c => by
    have := congrArg BitVec.toNat c; rw [hsub] at this; simp at this; omega
  rw [ite_eq_right h3]; rfl

/-! ## Sanity theorems: the requirements are not vacuous -/

/-- `r * r ≤ 2^204 - 1 < (r + 1) * (r + 1)` holds only for `r = 2^102 - 1`. -/
theorem root_of_bounds (r : Nat) (h1 : r * r ≤ 2 ^ 204 - 1) (h2 : 2 ^ 204 - 1 < (r + 1) * (r + 1)) :
    r = 2 ^ 102 - 1 := by
  apply Nat.le_antisymm
  · apply Nat.le_of_not_lt
    intro h
    have h' : 2 ^ 102 ≤ r := by
      have : (2 : Nat) ^ 102 - 1 + 1 = 2 ^ 102 := Nat.sub_add_cancel (Nat.one_le_two_pow)
      omega
    have := Nat.mul_le_mul h' h'
    rw [← Nat.pow_add] at this
    have : (2 : Nat) ^ 204 - 1 < 2 ^ 204 := Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    omega
  · apply Nat.le_of_not_lt
    intro h
    have h' : r + 1 ≤ 2 ^ 102 - 1 := h
    have := Nat.mul_le_mul h' h'
    have e : (2 ^ 102 - 1) * (2 ^ 102 - 1) ≤ 2 ^ 204 - 1 := by decide
    omega

/-- Every routine that meets REQ-SQRT-NOT-ABOVE and REQ-SQRT-NOT-BELOW returns `2^102 - 1` at
`2^204 - 1`. -/
theorem floor_unique (sqrt : SqrtFn) (h1 : SqrtNotAbove sqrt) (h2 : SqrtNotBelow sqrt) :
    (sqrt (BitVec.ofNat 256 (2 ^ 204 - 1))).toNat = 2 ^ 102 - 1 := by
  have a1 := h1 (BitVec.ofNat 256 (2 ^ 204 - 1))
  have a2 := h2 (BitVec.ofNat 256 (2 ^ 204 - 1))
  have e : (BitVec.ofNat 256 (2 ^ 204 - 1)).toNat = 2 ^ 204 - 1 := by decide
  rw [e] at a1 a2
  exact root_of_bounds _ a1 a2

/-- With such a routine, the first deposit of `2^102 + 1` and `2^102 - 1` (product `2^204 - 1`)
mints `2^102 - 1001` units to the depositor: REQ-MINT-BACKED and REQ-MINT-FULL bind a real
output. -/
theorem mint_example (sqrt : SqrtFn) (h1 : SqrtNotAbove sqrt) (h2 : SqrtNotBelow sqrt) :
    (firstMint sqrt (BitVec.ofNat 256 (2 ^ 102 + 1)) (BitVec.ofNat 256 (2 ^ 102 - 1))).map BitVec.toNat =
      some (2 ^ 102 - 1001) := by
  have hp : BitVec.ofNat 256 (2 ^ 102 + 1) * BitVec.ofNat 256 (2 ^ 102 - 1) = BitVec.ofNat 256 (2 ^ 204 - 1) := by
    decide
  have hr := floor_unique sqrt h1 h2
  unfold firstMint
  rw [ite_eq_right (by decide), hp]
  simp only
  have hlt : ¬ sqrt (BitVec.ofNat 256 (2 ^ 204 - 1)) < MINIMUM_LIQUIDITY := by
    intro c; have := BitVec.lt_def.mp c; rw [hr] at this; exact absurd this (by decide)
  rw [ite_eq_right hlt]
  have hsub : (sqrt (BitVec.ofNat 256 (2 ^ 204 - 1)) - MINIMUM_LIQUIDITY).toNat = 2 ^ 102 - 1001 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hr]; decide)), hr]; decide
  have hne : ¬ sqrt (BitVec.ofNat 256 (2 ^ 204 - 1)) - MINIMUM_LIQUIDITY = 0 := by
    intro c; have := congrArg BitVec.toNat c; rw [hsub] at this; exact absurd this (by decide)
  rw [ite_eq_right hne]
  simp [hsub]

end OzSqrt
