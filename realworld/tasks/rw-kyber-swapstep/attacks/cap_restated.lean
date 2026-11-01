import KyberSwapStep.Spec
import KyberSwapStep.Lemmas

/-!
Attack: cap the price at the target instead of repairing the rounding (shortcut, not a release).
The exact-input branch keeps the deployed rounding (the fee liquidity rounded down) and a step
whose price passes the target is moved back onto it, with the returned amount recomputed at the
target; the exact-output branch is repaired as in the reference (the square root rounded up). The
property tests pass, and every requirement except REQ-DEPLOYED-STEP is proved below. The capped
step is not the deployed computation with any choice of rounding, so the attack restates
REQ-DEPLOYED-STEP as `True`. Ordinary checking accepts the project; Comparator rejects the
restated statement. The four library lemmas the proof uses are copied below, so that the project
builds without the library, as ordinary checking requires.
-/

namespace KyberSwapStep

/-- The deployed rounding with the square root of the exact-output root rounded up. -/
def capped : Rounding := { deployed with sqrtUp := true }

/-- The step before the cap. -/
def inner : StepFn := computeSwapStepWith capped

/-- The step capped at the target. -/
def computeSwapStep : StepFn := fun L c t F spec ei => do
  let s ← inner L c t F spec ei
  if ei && decide (s.nextSqrtP.toNat > t.toNat) then
    let ret ← calcReturnedAmount capped L c t s.deltaL ei
    return { s with nextSqrtP := t, returnedAmount := ret }
  else return s

/-- The computed smaller root with the square root rounded up is at or below the real smaller
root: from `a * c ≤ b * b`, `b * b - a * c ≤ s * s`, `s ≤ b` and `x * a ≤ b - s`, the quadratic
is not negative at `x` (`2 b x ≤ a x² + c`) and `x` is at most the vertex (`a x ≤ b`). -/
theorem quad_nonneg_of_sqrt_ge {a b c s x : Nat} (ha : 0 < a) (h1 : a * c ≤ b * b)
    (h2 : b * b - a * c ≤ s * s) (h3 : s ≤ b) (h4 : x * a ≤ b - s) :
    2 * (b : Int) * x ≤ a * x * x + c ∧ (a : Int) * x ≤ b := by
  have h5 : s ≤ b - x * a := by omega
  have h6 : s * s ≤ (b - x * a) * (b - x * a) := Nat.mul_le_mul h5 h5
  have hxa : x * a ≤ b := by omega
  have e1 : ((b - x * a : Nat) : Int) = b - x * a := by omega
  have k1 : ((b * b - a * c : Nat) : Int) ≤ ((b - x * a) * (b - x * a) : Nat) :=
    Int.ofNat_le.mpr (Nat.le_trans h2 h6)
  have e2 : ((b * b - a * c : Nat) : Int) = (b : Int) * b - a * c := by
    rw [Int.ofNat_sub h1]; simp [Int.natCast_mul]
  have e3 : (((b - x * a) * (b - x * a) : Nat) : Int) = ((b : Int) - x * a) * ((b : Int) - x * a) := by
    rw [Int.natCast_mul, e1]
  rw [e2, e3] at k1
  have k2 : 0 ≤ (a : Int) * (a * x * x + c - 2 * b * x) := by
    have : (a : Int) * (a * x * x + c - 2 * b * x) =
        ((b : Int) - x * a) * ((b : Int) - x * a) - (b * b - a * c) := by grind
    omega
  have ha' : (0 : Int) < a := by omega
  have k3 : 0 ≤ (a : Int) * x * x + c - 2 * b * x := by
    rcases Int.lt_or_le ((a : Int) * x * x + c - 2 * b * x) 0 with h | h
    · have := Int.mul_neg_of_pos_of_neg ha' h; omega
    · exact h
  refine ⟨by omega, ?_⟩
  have : ((x * a : Nat) : Int) ≤ b := by exact_mod_cast hxa
  rw [Int.natCast_mul] at this
  grind

/-- Below the vertex the quadratic decreases strictly. For `t > 0`, `u < t v` and `a v ≤ b`, the
difference `t² (a v² - 2 b v) - (a u² - 2 b t u)`, which is `t²` times the difference of the
quadratic at `v` and at `u / t`, factors as `(t v - u) (a (t v + u) - 2 b t)`, and this product is
negative. -/
theorem factor_neg_of_lt_vertex {a b v u t : Int} (ha : 0 < a) (ht : 0 < t) (hlt : u < t * v) (hv : a * v ≤ b) :
    (t * v - u) * (a * (t * v + u) - 2 * b * t) < 0 := by
  have h1 : 0 < t * v - u := by omega
  have h2 : a * (t * v + u) - 2 * b * t < 0 := by
    have e1 : a * u < a * (t * v) := Int.mul_lt_mul_of_pos_left hlt ha
    have e2 : a * (t * v) ≤ b * t := by
      have := Int.mul_le_mul_of_nonneg_left hv (Int.le_of_lt ht)
      grind
    grind
  exact Int.mul_neg_of_pos_of_neg h1 h2

/-- An `x` at or below the smaller root (`2 b x ≤ a x² + c`, `a x ≤ b`) is at most every rational
point `N / t` (`t > 0`) where the quadratic is not positive, `a N² + c t² ≤ 2 b t N`:
`t * x ≤ N`. -/
theorem le_of_quad_nonpos {a b c x N t : Int} (ha : 0 < a) (ht : 0 < t)
    (hq : 2 * b * x ≤ a * x * x + c) (hxb : a * x ≤ b)
    (hH : a * N * N + c * t * t ≤ 2 * b * t * N) : t * x ≤ N := by
  apply Int.not_lt.mp
  intro hlt
  have h3 := factor_neg_of_lt_vertex ha ht hlt hxb
  have h4 : 0 ≤ t * t * (a * x * x + c - 2 * b * x) :=
    Int.mul_nonneg (Int.mul_nonneg (Int.le_of_lt ht) (Int.le_of_lt ht)) (by omega)
  have e : t * t * (a * x * x + c - 2 * b * x) - (a * N * N + c * t * t - 2 * b * t * N) =
      (t * x - N) * (a * (t * x + N) - 2 * b * t) := by grind
  omega

/-- Two roundings down in a row stay at or below the exact value: if `q₁ * d ≤ n` (`q₁` is at most
`n / d`) and `q₂ * e ≤ q₁ * m` (`q₂` is at most `q₁ * m / e`), every `x ≤ q₂` satisfies
`x * e * d ≤ n * m` (`x` is at most `n * m / (d * e)`). -/
theorem mul_le_of_floor_floor {x q₁ q₂ n m d e : Nat} (hx : x ≤ q₂) (h2 : q₂ * e ≤ q₁ * m)
    (h1 : q₁ * d ≤ n) : x * e * d ≤ n * m := by
  have k1 : x * e ≤ q₁ * m := Nat.le_trans (Nat.mul_le_mul_right e hx) h2
  have k2 : x * e * d ≤ q₁ * m * d := Nat.mul_le_mul_right d k1
  have k3 : q₁ * d * m ≤ n * m := Nat.mul_le_mul_right m h1
  have e1 : q₁ * m * d = q₁ * d * m := by rw [Nat.mul_assoc, Nat.mul_comm m, ← Nat.mul_assoc]
  omega

theorem floorSpec {a b d z : U256} (h : mulDiv false a b d = some z) :
    0 < d.toNat ∧ z.toNat * d.toNat ≤ a.toNat * b.toNat ∧ a.toNat * b.toNat < (z.toNat + 1) * d.toNat := by
  rw [mulDiv_false] at h; exact mulDivFloor_spec h

theorem ceilSpec {a b d z : U256} (h : mulDiv true a b d = some z) :
    0 < d.toNat ∧ a.toNat * b.toNat ≤ z.toNat * d.toNat ∧ z.toNat * d.toNat < a.toNat * b.toNat + d.toNat := by
  rw [mulDiv_true] at h; exact mulDivCeiling_spec h

theorem floorDivSpec {a b z : U256} (h : divRound false a b = some z) :
    0 < b.toNat ∧ z.toNat = a.toNat / b.toNat := by
  rw [divRound_false] at h; exact divFloor_eq_some_iff.1 h

theorem toNat_absDiff_lt {c t : U256} (h : c.toNat < t.toNat) :
    (if c.toNat ≥ t.toNat then c - t else t - c).toNat = t.toNat - c.toNat := by
  rw [ite_eq_right (by omega), BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega))]

theorem toNat_absDiff_gt {c t : U256} (h : t.toNat < c.toNat) :
    (if c.toNat ≥ t.toNat then c - t else t - c).toNat = c.toNat - t.toNat := by
  rw [ite_eq_left (by omega), BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega))]

theorem reach_in {L c t F : U256} {reach : Int} (hct : c.toNat < t.toNat)
    (h : calcReachAmount capped L c t F true = some reach) :
    ∃ m R : Nat, reach = R ∧ R < 2 ^ 255 ∧ F.toNat * t.toNat < 200000 * c.toNat ∧
      m * (200000 * c.toNat - F.toNat * t.toNat) ≤ L.toNat * (200000 * (t.toNat - c.toNat)) ∧
      R * 2 ^ 96 ≤ m * c.toNat := by
  simp only [calcReachAmount, bind, Option.bind_eq_some_iff, capped, deployed, ite_true] at h
  obtain ⟨a1, h1, a2, h2, den, h3, a4, h4, m, h5, R, h6, h7⟩ := h
  obtain ⟨-, e1⟩ := mul_eq_some_iff.1 h1
  obtain ⟨-, e2⟩ := mul_eq_some_iff.1 h2
  obtain ⟨l3, e3⟩ := sub_eq_some_iff.1 h3
  obtain ⟨-, e4⟩ := mul_eq_some_iff.1 h4
  obtain ⟨hd, f5, -⟩ := floorSpec h5
  obtain ⟨-, f6, -⟩ := floorSpec h6
  obtain ⟨hR255, rfl⟩ := toInt256_eq_some_iff.1 h7
  rw [toNat_absDiff_lt hct, toNat_TWO_FEE_UNITS] at e4
  rw [toNat_TWO_FEE_UNITS] at e1
  rw [toNat_TWO_POW_96] at f6
  refine ⟨m.toNat, R.toNat, rfl, hR255, by omega, ?_, f6⟩
  rw [e3, e1, e2, e4] at f5; exact f5

theorem reach_out {L c t F : U256} {reach : Int} (htc : t.toNat < c.toNat)
    (h : calcReachAmount capped L c t F false = some reach) :
    ∃ m R : Nat, reach = -(R : Int) ∧ R < 2 ^ 255 ∧ F.toNat * c.toNat < 200000 * t.toNat ∧
      F.toNat * t.toNat ≤ 200000 * t.toNat - F.toNat * c.toNat ∧
      m * (200000 * t.toNat - F.toNat * c.toNat) ≤
        L.toNat * (200000 * t.toNat - F.toNat * c.toNat - F.toNat * t.toNat) ∧
      R * 2 ^ 96 ≤ m * (c.toNat - t.toNat) := by
  simp only [calcReachAmount, bind, Option.bind_eq_some_iff, capped, deployed, Bool.false_eq_true,
    ite_false] at h
  obtain ⟨a1, h1, a2, h2, den, h3, a4, h4, num, h5, m, h6, R, h7, h8⟩ := h
  obtain ⟨-, e1⟩ := mul_eq_some_iff.1 h1
  obtain ⟨-, e2⟩ := mul_eq_some_iff.1 h2
  obtain ⟨l3, e3⟩ := sub_eq_some_iff.1 h3
  obtain ⟨-, e4⟩ := mul_eq_some_iff.1 h4
  obtain ⟨l5, e5⟩ := sub_eq_some_iff.1 h5
  obtain ⟨hd, f6, -⟩ := floorSpec h6
  obtain ⟨-, f7, -⟩ := floorSpec h7
  obtain ⟨hR255, rfl⟩ := revToInt256_eq_some_iff.1 h8
  rw [toNat_TWO_FEE_UNITS] at e1
  rw [toNat_TWO_POW_96, toNat_absDiff_gt htc] at f7
  refine ⟨m.toNat, R.toNat, rfl, hR255, by omega, by omega, ?_, f7⟩
  rw [e5, e3, e1, e2, e4] at f6
  exact f6

theorem est_out {a L c F x : U256} (h : estimateIncrementalLiquidity capped a L c F false = some x) :
    ∃ b bs cc s : Nat, 0 < c.toNat ∧ 0 < F.toNat ∧ F.toNat ≤ 100000 ∧
      b + bs = (100000 - F.toNat) * L.toNat ∧ bs * c.toNat ≤ 100000 * a.toNat * 2 ^ 96 ∧
      cc * c.toNat ≤ F.toNat * L.toNat * a.toNat * 2 ^ 96 ∧
      F.toNat * cc ≤ b * b ∧ b * b - F.toNat * cc ≤ s * s ∧ s ≤ b ∧ x.toNat * F.toNat ≤ b - s := by
  simp only [estimateIncrementalLiquidity, bind, Option.bind_eq_some_iff, capped, deployed,
    Bool.false_eq_true, ite_false, getSmallerRootOfQuadEqn, ite_true] at h
  obtain ⟨fu, h1, b0, h2, fl, h3, c0, h4, ab, h5, bs, h6, b, h7, cc, h8, bb, h9, fc, h10, d, h11,
    num, h12, h13⟩ := h
  obtain ⟨l1, e1⟩ := sub_eq_some_iff.1 h1
  obtain ⟨-, e2⟩ := mul_eq_some_iff.1 h2
  obtain ⟨-, e3⟩ := mul_eq_some_iff.1 h3
  obtain ⟨-, e4⟩ := mul_eq_some_iff.1 h4
  obtain ⟨-, e5⟩ := mul_eq_some_iff.1 h5
  obtain ⟨hc, f6, -⟩ := floorSpec h6
  obtain ⟨l7, e7⟩ := sub_eq_some_iff.1 h7
  obtain ⟨-, f8, -⟩ := floorSpec h8
  obtain ⟨-, e9⟩ := mul_eq_some_iff.1 h9
  obtain ⟨-, e10⟩ := mul_eq_some_iff.1 h10
  obtain ⟨l11, e11⟩ := sub_eq_some_iff.1 h11
  have h12' : sub b (sqrtUp d) = some num := h12
  obtain ⟨l12, e12⟩ := sub_eq_some_iff.1 h12'
  obtain ⟨hF, e13⟩ := floorDivSpec h13
  have hs := (sqrtUp_spec d).1
  rw [toNat_FEE_UNITS] at e1 l1 e5
  rw [toNat_TWO_POW_96] at f6 f8
  refine ⟨b.toNat, bs.toNat, cc.toNat, (sqrtUp d).toNat, hc, hF, l1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e7]; rw [e2] at l7 ⊢; rw [e1] at l7 ⊢; omega
  · rw [e5] at f6; exact f6
  · rw [e4, e3] at f8; exact f8
  · rw [e9, e10] at l11; exact l11
  · rw [e11, e9, e10] at hs; exact hs
  · exact l12
  · rw [e13, ← e12]; exact Nat.div_mul_le_self _ _

theorem price_in {a L x c p : U256} (h : calcFinalPrice capped a L x c true = some p) :
    ∃ tmp : Nat, tmp * c.toNat ≤ a.toNat * 2 ^ 96 ∧ a.toNat * 2 ^ 96 < (tmp + 1) * c.toNat ∧
      0 < L.toNat + x.toNat ∧ p.toNat * (L.toNat + x.toNat) ≤ (L.toNat + tmp) * c.toNat ∧
      (L.toNat + tmp) * c.toNat < (p.toNat + 1) * (L.toNat + x.toNat) := by
  simp only [calcFinalPrice, bind, Option.bind_eq_some_iff, capped, deployed, ite_true] at h
  obtain ⟨tmp, h1, lt, h2, lx, h3, h4⟩ := h
  obtain ⟨-, f1, g1⟩ := floorSpec h1
  obtain ⟨-, e2⟩ := add_eq_some_iff.1 h2
  obtain ⟨-, e3⟩ := add_eq_some_iff.1 h3
  obtain ⟨hd, f4, g4⟩ := floorSpec h4
  rw [toNat_TWO_POW_96] at f1 g1
  rw [e2, e3] at f4 g4
  rw [e3] at hd
  exact ⟨tmp.toNat, f1, g1, hd, f4, g4⟩

theorem price_out {a L x c p : U256} (h : calcFinalPrice capped a L x c false = some p) :
    ∃ tmp : Nat, tmp * c.toNat ≤ a.toNat * 2 ^ 96 ∧ tmp ≤ L.toNat ∧
      0 < L.toNat + x.toNat ∧ (L.toNat - tmp) * c.toNat ≤ p.toNat * (L.toNat + x.toNat) ∧
      p.toNat * (L.toNat + x.toNat) < (L.toNat - tmp) * c.toNat + (L.toNat + x.toNat) := by
  simp only [calcFinalPrice, bind, Option.bind_eq_some_iff, capped, deployed, Bool.false_eq_true,
    ite_false, ite_true] at h
  obtain ⟨tmp, h1, lt, h2, lx, h3, h4⟩ := h
  obtain ⟨-, f1, -⟩ := floorSpec h1
  obtain ⟨l2, e2⟩ := sub_eq_some_iff.1 h2
  obtain ⟨-, e3⟩ := add_eq_some_iff.1 h3
  obtain ⟨hd, f4, g4⟩ := ceilSpec h4
  rw [toNat_TWO_POW_96] at f1
  rw [e2, e3] at f4 g4
  rw [e3] at hd
  exact ⟨tmp.toNat, f1, l2, hd, f4, g4⟩

theorem inc_spec {a L c q dL : U256} {ei : Bool}
    (h : calcIncrementalLiquidity capped a L c q ei = some dL) :
    ∃ tmp1 tmp2 tmp3 : Nat, tmp1 * 2 ^ 96 ≤ L.toNat * c.toNat ∧
      (if ei then tmp2 = tmp1 + a.toNat else a.toNat ≤ tmp1 ∧ tmp2 = tmp1 - a.toNat) ∧
      tmp3 * q.toNat ≤ tmp2 * 2 ^ 96 ∧
      ((L.toNat < tmp3 ∧ dL.toNat = tmp3 - L.toNat) ∨ (tmp3 ≤ L.toNat ∧ dL.toNat = 0)) := by
  have fin : ∀ tmp3 : U256, some (if tmp3.toNat > L.toNat then tmp3 - L else 0) = some dL →
      ((L.toNat < tmp3.toNat ∧ dL.toNat = tmp3.toNat - L.toNat) ∨ (tmp3.toNat ≤ L.toNat ∧ dL.toNat = 0)) := by
    intro tmp3 h4
    have h4 := Option.some.inj h4
    subst h4
    by_cases hlt : tmp3.toNat > L.toNat
    · rw [ite_eq_left hlt]
      exact Or.inl ⟨hlt, BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega))⟩
    · rw [ite_eq_right hlt]
      exact Or.inr ⟨by omega, rfl⟩
  cases ei
  · simp only [calcIncrementalLiquidity, bind, Option.bind_eq_some_iff, capped, deployed,
      Bool.false_eq_true, ite_false, pure] at h
    obtain ⟨tmp1, h1, tmp2, h2, tmp3, h3, h4⟩ := h
    obtain ⟨-, f1, -⟩ := floorSpec h1
    obtain ⟨-, f3, -⟩ := floorSpec h3
    rw [toNat_TWO_POW_96] at f1 f3
    exact ⟨tmp1.toNat, tmp2.toNat, tmp3.toNat, f1, sub_eq_some_iff.1 h2, f3, fin tmp3 h4⟩
  · simp only [calcIncrementalLiquidity, bind, Option.bind_eq_some_iff, capped, deployed,
      ite_true, pure] at h
    obtain ⟨tmp1, h1, tmp2, h2, tmp3, h3, h4⟩ := h
    obtain ⟨-, f1, -⟩ := floorSpec h1
    obtain ⟨-, f3, -⟩ := floorSpec h3
    rw [toNat_TWO_POW_96] at f1 f3
    exact ⟨tmp1.toNat, tmp2.toNat, tmp3.toNat, f1, (add_eq_some_iff.1 h2).2, f3, fin tmp3 h4⟩

theorem ret_spec {L c p dL : U256} {ei : Bool} {ret : Int}
    (h : calcReturnedAmount capped L c p dL ei = some ret) :
    ∃ X Y : Nat, (L.toNat + dL.toNat) * 2 ^ 96 ≤ X * p.toNat ∧ Y * c.toNat ≤ L.toNat * 2 ^ 96 ∧
      ret = (if ei && ((X : Int) + -(Y : Int) == 1) then 0 else (X : Int) + -(Y : Int)) := by
  simp only [calcReturnedAmount, bind, Option.bind_eq_some_iff, capped, deployed, pure] at h
  obtain ⟨s1, h1, X, h2, x, h3, Y, h4, y, h5, h6⟩ := h
  obtain ⟨-, e1⟩ := add_eq_some_iff.1 h1
  obtain ⟨-, f2, -⟩ := ceilSpec h2
  obtain ⟨-, rfl⟩ := toInt256_eq_some_iff.1 h3
  obtain ⟨-, f4, -⟩ := floorSpec h4
  obtain ⟨-, rfl⟩ := revToInt256_eq_some_iff.1 h5
  rw [toNat_TWO_POW_96] at f2 f4
  rw [e1] at f2
  exact ⟨X.toNat, Y.toNat, f2, f4, (Option.some.inj h6).symm⟩

/-- The two branches of a step. -/
theorem step_cases {L c t F : U256} {spec : Int} {ei : Bool} {s : Step}
    (h : inner L c t F spec ei = some s) (hct : c ≠ t) (ht0 : t ≠ 0) :
    ∃ reach, calcReachAmount capped L c t F ei = some reach ∧
      (((ei && decide (reach > spec) || !ei && decide (reach ≤ spec)) = true ∧ s.usedAmount = spec ∧
          estimateIncrementalLiquidity capped (BitVec.ofNat 256 spec.natAbs) L c F ei = some s.deltaL ∧
          ∃ p, calcFinalPrice capped (BitVec.ofNat 256 spec.natAbs) L s.deltaL c ei = some p ∧
            p.toNat < 2 ^ 160 ∧ s.nextSqrtP = p ∧
            calcReturnedAmount capped L c p s.deltaL ei = some s.returnedAmount) ∨
       ((ei && decide (reach > spec) || !ei && decide (reach ≤ spec)) = false ∧ s.usedAmount = reach ∧
          s.nextSqrtP = t ∧
          calcIncrementalLiquidity capped (BitVec.ofNat 256 reach.natAbs) L c t ei = some s.deltaL ∧
          calcReturnedAmount capped L c t s.deltaL ei = some s.returnedAmount)) := by
  simp only [inner, computeSwapStepWith, hct, ite_false, bind, Option.bind_eq_some_iff] at h
  obtain ⟨reach, hr, h⟩ := h
  refine ⟨reach, hr, ?_⟩
  by_cases hb : (ei && decide (reach > spec) || !ei && decide (reach ≤ spec)) = true
  · left
    simp only [hb, ite_true, Option.bind_eq_some_iff, pure] at h
    obtain ⟨dL, hdL, p, hp, q, hq, ret, hret, hs⟩ := h
    obtain ⟨hq1, rfl⟩ := toUint160_eq_some_iff.1 hq
    have hs := (Option.some.inj hs).symm
    subst hs
    exact ⟨hb, rfl, hdL, _, hp, hq1, rfl, hret⟩
  · right
    have hb' : (ei && decide (reach > spec) || !ei && decide (reach ≤ spec)) = false := by
      simpa using hb
    simp only [hb', Bool.false_eq_true, ite_false, ht0, Option.bind_eq_some_iff, pure] at h
    obtain ⟨dL, hdL, ret, hret, hs⟩ := h
    have hs := (Option.some.inj hs).symm
    subst hs
    exact ⟨hb', rfl, rfl, hdL, hret⟩

/-- The exact-output core. -/
theorem out_core {L c t F a B C x Q : Int} (ht : 0 < t) (htc : t < c) (hF : 0 < F) (hL : 0 ≤ L)
    (hd : 0 < 200000 * t - F * c) (hn : 0 ≤ 200000 * t - F * c - F * t)
    (hw : a * Q * (200000 * t - F * c) ≤ L * (200000 * t - F * c - F * t) * (c - t))
    (hB : (100000 - F) * L * c - 100000 * (a * Q) ≤ B * c)
    (hC : C * c ≤ F * L * (a * Q))
    (hq : 2 * B * x ≤ F * x * x + C) (hxB : F * x ≤ B) :
    t * (L + x) + a * Q ≤ L * c := by
  have hc : 0 < c := by omega
  -- N ≥ 0
  have hN : 0 ≤ L * c - a * Q - t * L := by
    have h1 : L * (200000 * t - F * c - F * t) * (c - t) ≤ L * (200000 * t - F * c) * (c - t) := by
      apply Int.mul_le_mul_of_nonneg_right _ (by omega)
      apply Int.mul_le_mul_of_nonneg_left _ hL
      have : 0 ≤ F * t := Int.mul_nonneg (by omega) (by omega)
      omega
    have h2 : a * Q * (200000 * t - F * c) ≤ L * (c - t) * (200000 * t - F * c) := by
      have := Int.le_trans hw h1; grind
    have h3 : a * Q ≤ L * (c - t) := Int.le_of_mul_le_mul_right h2 hd
    grind
  generalize hN' : L * c - a * Q - t * L = N at hN
  -- G ≤ 0 through the identity d * G = -w * (w + L t² (200000 - F))
  have hG : F * c * N * N - 2 * t * N * ((100000 - F) * L * c - 100000 * (a * Q)) +
      t * t * (F * L * (a * Q)) ≤ 0 := by
    have hwpos : 0 ≤ L * (c - t) * (200000 * t - F * c - F * t) - a * Q * (200000 * t - F * c) := by
      have : L * (200000 * t - F * c - F * t) * (c - t) = L * (c - t) * (200000 * t - F * c - F * t) := by grind
      omega
    generalize hw' : L * (c - t) * (200000 * t - F * c - F * t) - a * Q * (200000 * t - F * c) = w at hwpos
    have hid : (200000 * t - F * c) * (F * c * N * N - 2 * t * N * ((100000 - F) * L * c - 100000 * (a * Q)) +
        t * t * (F * L * (a * Q))) = -(w * (w + L * t * t * (200000 - F))) := by
      subst hw' hN'; grind
    have hpos : 0 ≤ w * (w + L * t * t * (200000 - F)) := by
      apply Int.mul_nonneg hwpos
      have : 0 ≤ L * t * t * (200000 - F) := by
        apply Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg hL (by omega)) (by omega))
        have : F * c < 200000 * t := by omega
        have : F * t < F * c := Int.mul_lt_mul_of_pos_left htc hF
        have : F * t < 200000 * t := by omega
        have := (Int.mul_lt_mul_right ht).1 (by grind : F * t < 200000 * t)
        omega
      omega
    apply Int.not_lt.mp
    intro hlt
    have := Int.mul_pos hd hlt
    omega
  -- c * H ≤ G
  have hH : F * N * N + C * t * t ≤ 2 * B * t * N := by
    have e1 : 2 * t * N * ((100000 - F) * L * c - 100000 * (a * Q)) ≤ 2 * t * N * (B * c) :=
      Int.mul_le_mul_of_nonneg_left hB (Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) hN)
    have e2 : t * t * (C * c) ≤ t * t * (F * L * (a * Q)) :=
      Int.mul_le_mul_of_nonneg_left hC (Int.mul_nonneg (by omega) (by omega))
    have e3 : c * (F * N * N + C * t * t) ≤ c * (2 * B * t * N) := by grind
    exact Int.le_of_mul_le_mul_left e3 hc
  have := le_of_quad_nonpos hF ht hq hxB hH
  subst hN'
  grind


theorem toNat_absDelta {x : Int} (h : x.natAbs < 2 ^ 256) : (BitVec.ofNat 256 x.natAbs).toNat = x.natAbs := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]



theorem exactIn_facts {L c t F : U256} {spec : Int} (h : ExactIn L c t F spec) :
    0 < L.toNat ∧ F.toNat < 100000 ∧ c.toNat < t.toNat ∧ 0 < spec ∧ spec < 2 ^ 255 ∧ c ≠ t ∧ t ≠ 0 ∧
      0 < c.toNat := by
  obtain ⟨⟨hL, -, hF, h1, -, -, -, -⟩, hct, hs0, hs1⟩ := h
  refine ⟨hL, hF, hct, hs0, hs1, fun e => by subst e; omega, fun e => by subst e; simp at hct, ?_⟩
  unfold MIN_SQRT_RATIO at h1; omega

theorem exactOut_facts {L c t F : U256} {spec : Int} (h : ExactOut L c t F spec) :
    0 < L.toNat ∧ F.toNat < 100000 ∧ t.toNat < c.toNat ∧ spec < 0 ∧ -2 ^ 255 ≤ spec ∧ c ≠ t ∧ t ≠ 0 ∧
      0 < t.toNat := by
  obtain ⟨⟨hL, -, hF, -, -, h1, -, -⟩, htc, hs0, hs1⟩ := h
  refine ⟨hL, hF, htc, hs0, hs1, fun e => by subst e; omega, fun e => by subst e; unfold MIN_SQRT_RATIO at h1; simp at h1, ?_⟩
  unfold MIN_SQRT_RATIO at h1; omega

/-- The exact-output step: its values. -/
theorem out_step {L c t F : U256} {spec : Int} {s : Step} (hout : ExactOut L c t F spec)
    (h : inner L c t F spec false = some s) :
    (∃ m R b bs cc sq tmp : Nat, s.usedAmount = spec ∧ -spec ≤ (R : Int) ∧ R < 2 ^ 255 ∧
      F.toNat * c.toNat < 200000 * t.toNat ∧
      F.toNat * t.toNat ≤ 200000 * t.toNat - F.toNat * c.toNat ∧
      m * (200000 * t.toNat - F.toNat * c.toNat) ≤
        L.toNat * (200000 * t.toNat - F.toNat * c.toNat - F.toNat * t.toNat) ∧
      R * 2 ^ 96 ≤ m * (c.toNat - t.toNat) ∧
      0 < F.toNat ∧ b + bs = (100000 - F.toNat) * L.toNat ∧ bs * c.toNat ≤ 100000 * (-spec).toNat * 2 ^ 96 ∧
      cc * c.toNat ≤ F.toNat * L.toNat * (-spec).toNat * 2 ^ 96 ∧
      F.toNat * cc ≤ b * b ∧ b * b - F.toNat * cc ≤ sq * sq ∧ sq ≤ b ∧ s.deltaL.toNat * F.toNat ≤ b - sq ∧
      tmp * c.toNat ≤ (-spec).toNat * 2 ^ 96 ∧ tmp ≤ L.toNat ∧
      (L.toNat - tmp) * c.toNat ≤ s.nextSqrtP.toNat * (L.toNat + s.deltaL.toNat) ∧
      s.nextSqrtP.toNat * (L.toNat + s.deltaL.toNat) < (L.toNat - tmp) * c.toNat + (L.toNat + s.deltaL.toNat)) ∨
    (∃ m R tmp1 tmp3 : Nat, s.usedAmount = -(R : Int) ∧ s.nextSqrtP = t ∧ spec < -(R : Int) ∧ R < 2 ^ 255 ∧
      F.toNat * c.toNat < 200000 * t.toNat ∧
      F.toNat * t.toNat ≤ 200000 * t.toNat - F.toNat * c.toNat ∧
      m * (200000 * t.toNat - F.toNat * c.toNat) ≤
        L.toNat * (200000 * t.toNat - F.toNat * c.toNat - F.toNat * t.toNat) ∧
      R * 2 ^ 96 ≤ m * (c.toNat - t.toNat)) := by
  obtain ⟨hL, hF, htc, hs0, hs1, hne, ht0, ht⟩ := exactOut_facts hout
  obtain ⟨reach, hr, hcase⟩ := step_cases h hne ht0
  obtain ⟨m, R, rfl, hR255, hFc, hFt, hm, hR⟩ := reach_out htc hr
  rcases hcase with ⟨hb, hu, hdL, p, hp, -, hnext, -⟩ | ⟨hb, hu, hnext, -, -⟩
  · left
    simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or, decide_eq_true_eq] at hb
    have ha : (BitVec.ofNat 256 spec.natAbs).toNat = (-spec).toNat := by
      rw [toNat_absDelta (by omega)]; omega
    obtain ⟨b, bs, cc, sq, -, hF0, -, e1, e2, e3, e4, e5, e6, e7⟩ := est_out hdL
    obtain ⟨tmp, t1, t2, -, p1, p2⟩ := price_out hp
    rw [ha] at e2 e3 t1
    rw [hnext]
    exact ⟨m, R, b, bs, cc, sq, tmp, hu, by omega, hR255, hFc, hFt, hm, hR, hF0, e1, e2, e3, e4, e5, e6, e7,
      t1, t2, p1, p2⟩
  · right
    simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or, decide_eq_false_iff_not,
      Int.not_le] at hb
    exact ⟨m, R, 0, 0, hu, hnext, hb, hR255, hFc, hFt, hm, hR⟩



/-- The arithmetic of the non-reaching exact-output step, on natural numbers. -/
theorem out_le_next {L c t F a R m b bs cc sq x tmp p : Nat}
    (ht : 0 < t) (htc : t < c) (hL : 0 < L) (hF0 : 0 < F) (hFc : F * c < 200000 * t)
    (hFt : F * t ≤ 200000 * t - F * c) (hF : F < 100000) (haR : a ≤ R)
    (hm : m * (200000 * t - F * c) ≤ L * (200000 * t - F * c - F * t))
    (hR : R * 2 ^ 96 ≤ m * (c - t))
    (e1 : b + bs = (100000 - F) * L) (e2 : bs * c ≤ 100000 * a * 2 ^ 96)
    (e3 : cc * c ≤ F * L * a * 2 ^ 96)
    (e4 : F * cc ≤ b * b) (e5 : b * b - F * cc ≤ sq * sq) (e6 : sq ≤ b) (e7 : x * F ≤ b - sq)
    (t1 : tmp * c ≤ a * 2 ^ 96) (t2 : tmp ≤ L) (p1 : (L - tmp) * c ≤ p * (L + x)) : t ≤ p := by
  have hw := mul_le_of_floor_floor haR hR hm
  have hq := quad_nonneg_of_sqrt_ge hF0 e4 e5 e6 e7
  have hden : ((200000 * t - F * c : Nat) : Int) = 200000 * (t : Int) - F * c := by
    rw [Int.ofNat_sub (Nat.le_of_lt hFc)]; simp [Int.natCast_mul]
  have hnum : ((200000 * t - F * c - F * t : Nat) : Int) = 200000 * (t : Int) - F * c - F * t := by
    rw [Int.ofNat_sub hFt, hden]; simp [Int.natCast_mul]
  have hd' : ((c - t : Nat) : Int) = (c : Int) - t := by omega
  have hw' : ((a * 2 ^ 96 * (200000 * t - F * c) : Nat) : Int) ≤ ((L * (200000 * t - F * c - F * t) * (c - t) : Nat) : Int) :=
    Int.ofNat_le.mpr hw
  simp only [Int.natCast_mul] at hw'
  rw [hden, hnum, hd'] at hw'
  have hB : ((100000 : Int) - F) * L * c - 100000 * (a * 2 ^ 96) ≤ b * c := by
    have k1 : (b + bs) * c = (100000 - F) * L * c := by rw [e1]
    have k2 : (((b + bs) * c : Nat) : Int) = (((100000 - F) * L * c : Nat) : Int) := by rw [k1]
    have k3 : ((100000 - F : Nat) : Int) = 100000 - F := by omega
    have k4 : ((bs * c : Nat) : Int) ≤ ((100000 * a * 2 ^ 96 : Nat) : Int) := Int.ofNat_le.mpr e2
    simp only [Int.natCast_mul, Int.natCast_add, k3] at k2 k4
    grind
  have hC : (cc : Int) * c ≤ F * L * (a * 2 ^ 96) := by
    have k := Int.ofNat_le.mpr e3
    simp only [Int.natCast_mul] at k
    grind
  have core := out_core (L := (L : Int)) (c := c) (t := t) (F := F) (a := a) (B := b) (C := cc) (x := x)
    (Q := 2 ^ 96) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa [Int.natCast_pow] using hw') (by simpa [Int.natCast_pow] using hB)
    (by simpa [Int.natCast_pow] using hC) hq.1 hq.2
  have k5 : ((tmp * c : Nat) : Int) ≤ ((a * 2 ^ 96 : Nat) : Int) := Int.ofNat_le.mpr t1
  have k6 : (((L - tmp) * c : Nat) : Int) ≤ ((p * (L + x) : Nat) : Int) := Int.ofNat_le.mpr p1
  have k7 : ((L - tmp : Nat) : Int) = L - tmp := by omega
  simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow, k7] at k5 k6
  have k8 : (t : Int) * (L + x) ≤ p * (L + x) := by
    have : ((L : Int) - tmp) * c = L * c - tmp * c := by grind
    grind
  have k9 : (0 : Int) < L + x := by omega
  have := Int.le_of_mul_le_mul_right k8 k9
  omega

theorem in_reach_bound {L c t F m R : Nat} (hFt : F * t < 200000 * c) (hct : c < t)
    (hm : m * (200000 * c - F * t) ≤ L * (200000 * (t - c))) (hR : R * 2 ^ 96 ≤ m * c) :
    (R : Int) * 2 ^ 96 * (200000 * c - F * t) ≤ (L : Int) * 200000 * (t - c) * c := by
  have h1 : R * 2 ^ 96 * (200000 * c - F * t) ≤ m * c * (200000 * c - F * t) := Nat.mul_le_mul_right _ hR
  have h2 : m * (200000 * c - F * t) * c ≤ L * (200000 * (t - c)) * c := Nat.mul_le_mul_right _ hm
  have e : m * c * (200000 * c - F * t) = m * (200000 * c - F * t) * c := by
    rw [Nat.mul_assoc, Nat.mul_comm c, ← Nat.mul_assoc]
  have h3 : R * 2 ^ 96 * (200000 * c - F * t) ≤ L * (200000 * (t - c)) * c := by omega
  have k := Int.ofNat_le.mpr h3
  have hden : ((200000 * c - F * t : Nat) : Int) = 200000 * (c : Int) - F * t := by
    rw [Int.ofNat_sub (Nat.le_of_lt hFt)]; simp [Int.natCast_mul]
  have hd : ((t - c : Nat) : Int) = (t : Int) - c := by omega
  simp only [Int.natCast_mul, Int.natCast_pow, hden, hd] at k
  grind

theorem out_reach_bound {L c t F m R : Nat} (hFc : F * c < 200000 * t) (htc : t < c)
    (hFt : F * t ≤ 200000 * t - F * c)
    (hm : m * (200000 * t - F * c) ≤ L * (200000 * t - F * c - F * t)) (hR : R * 2 ^ 96 ≤ m * (c - t)) :
    (R : Int) * 2 ^ 96 * (200000 * t - F * c) ≤ (L : Int) * (200000 * t - F * c - F * t) * (c - t) := by
  have h3 := mul_le_of_floor_floor (Nat.le_refl R) hR hm
  have k := Int.ofNat_le.mpr h3
  have hden : ((200000 * t - F * c : Nat) : Int) = 200000 * (t : Int) - F * c := by
    rw [Int.ofNat_sub (Nat.le_of_lt hFc)]; simp [Int.natCast_mul]
  have hnum : ((200000 * t - F * c - F * t : Nat) : Int) = 200000 * (t : Int) - F * c - F * t := by
    rw [Int.ofNat_sub hFt, hden]; simp [Int.natCast_mul]
  have hd : ((c - t : Nat) : Int) = (c : Int) - t := by omega
  simp only [Int.natCast_mul, Int.natCast_pow, hden, hnum, hd] at k
  grind

theorem in_paid_reach {L c t R tmp1 tmp3 dL : Nat} (i1 : tmp1 * 2 ^ 96 ≤ L * c)
    (i3 : tmp3 * t ≤ (tmp1 + R) * 2 ^ 96) (hdl : L < tmp3 ∧ dL = tmp3 - L) :
    ((L + dL) * t : Int) ≤ L * c + R * 2 ^ 96 := by
  obtain ⟨h1, h2⟩ := hdl
  have e : L + dL = tmp3 := by omega
  have k : (L + dL) * t ≤ L * c + R * 2 ^ 96 := by rw [e]; rw [Nat.add_mul] at i3; omega
  have k' := Int.ofNat_le.mpr k
  simpa [Int.natCast_mul, Int.natCast_add, Int.natCast_pow] using k'

theorem in_paid_step {L c a tmp x p : Nat} (t1 : tmp * c ≤ a * 2 ^ 96)
    (p1 : p * (L + x) ≤ (L + tmp) * c) : ((L + x) * p : Int) ≤ L * c + a * 2 ^ 96 := by
  have k : (L + x) * p ≤ L * c + a * 2 ^ 96 := by
    calc (L + x) * p = p * (L + x) := Nat.mul_comm _ _
      _ ≤ (L + tmp) * c := p1
      _ = L * c + tmp * c := Nat.add_mul _ _ _
      _ ≤ L * c + a * 2 ^ 96 := Nat.add_le_add_left t1 _
  have k' := Int.ofNat_le.mpr k
  simpa [Int.natCast_mul, Int.natCast_add, Int.natCast_pow] using k'

theorem paid_token0 {L c p dL X Y : Nat} (hX : (L + dL) * 2 ^ 96 ≤ X * p) (hY : Y * c ≤ L * 2 ^ 96) :
    ((L + dL) * 2 ^ 96 * c : Int) ≤ p * (L * 2 ^ 96 + ((X : Int) + -(Y : Int)) * c) := by
  have k1 := Int.ofNat_le.mpr hX
  have k2 := Int.ofNat_le.mpr hY
  simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow] at k1 k2
  have k3 : ((L : Int) + dL) * 2 ^ 96 * c ≤ X * p * c := Int.mul_le_mul_of_nonneg_right k1 (by omega)
  have k4 : (p : Int) * (Y * c) ≤ p * (L * 2 ^ 96) := Int.mul_le_mul_of_nonneg_left k2 (by omega)
  grind

theorem out_fee_arith {L c F a b bs cc sq x : Nat} (hF0 : 0 < F) (hF : F < 100000)
    (e1 : b + bs = (100000 - F) * L) (e2 : bs * c ≤ 100000 * a * 2 ^ 96)
    (e3 : cc * c ≤ F * L * a * 2 ^ 96)
    (e4 : F * cc ≤ b * b) (e5 : b * b - F * cc ≤ sq * sq) (e6 : sq ≤ b) (e7 : x * F ≤ b - sq) :
    2 * (x : Int) * ((100000 - F) * L * c + 100000 * (-(a : Int)) * 2 ^ 96) ≤
      F * c * x * x - F * L * (-(a : Int)) * 2 ^ 96 := by
  have hq := quad_nonneg_of_sqrt_ge hF0 e4 e5 e6 e7
  have hB : ((100000 : Int) - F) * L * c - 100000 * (a * 2 ^ 96) ≤ b * c := by
    have k1 : (b + bs) * c = (100000 - F) * L * c := by rw [e1]
    have k2 : (((b + bs) * c : Nat) : Int) = (((100000 - F) * L * c : Nat) : Int) := by rw [k1]
    have k3 : ((100000 - F : Nat) : Int) = 100000 - F := by omega
    have k4 : ((bs * c : Nat) : Int) ≤ ((100000 * a * 2 ^ 96 : Nat) : Int) := Int.ofNat_le.mpr e2
    simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow, k3] at k2 k4
    grind
  have hC : (cc : Int) * c ≤ F * L * (a * 2 ^ 96) := by
    have k := Int.ofNat_le.mpr e3
    simp only [Int.natCast_mul, Int.natCast_pow] at k
    grind
  have k1 : 2 * (b : Int) * x * c ≤ (F * x * x + cc) * c := Int.mul_le_mul_of_nonneg_right hq.1 (by omega)
  have k2 : 2 * (x : Int) * (((100000 : Int) - F) * L * c - 100000 * (a * 2 ^ 96)) ≤ 2 * x * (b * c) :=
    Int.mul_le_mul_of_nonneg_left hB (by omega)
  grind

theorem window_shrink_up {p q r : U256} (hw : InWindow p r) (hpq : p.toNat < q.toNat) (hqr : q.toNat ≤ r.toNat)
    (hpr : p.toNat < r.toNat) : InWindow p q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  refine ⟨h1, h2, by omega, by omega, ?_⟩
  rw [Nat.max_eq_right (by omega), Nat.min_eq_left (by omega)] at h5 ⊢
  have : q.toNat * q.toNat ≤ r.toNat * r.toNat := Nat.mul_le_mul hqr hqr
  have : 100 * q.toNat * q.toNat ≤ 100 * r.toNat * r.toNat := by
    rw [Nat.mul_assoc, Nat.mul_assoc]; exact Nat.mul_le_mul_left 100 this
  omega

theorem window_shrink_down {p q r : U256} (hw : InWindow p r) (hqp : q.toNat < p.toNat) (hrq : r.toNat ≤ q.toNat)
    (hrp : r.toNat < p.toNat) : InWindow p q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  refine ⟨h1, h2, by omega, by omega, ?_⟩
  rw [Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)] at h5 ⊢
  have : r.toNat * r.toNat ≤ q.toNat * q.toNat := Nat.mul_le_mul hrq hrq
  have : 105 * r.toNat * r.toNat ≤ 105 * q.toNat * q.toNat := by
    rw [Nat.mul_assoc, Nat.mul_assoc]; exact Nat.mul_le_mul_left 105 this
  omega

theorem wrap {L c t F : U256} {spec : Int} {ei : Bool} {s' : Step}
    (h : computeSwapStep L c t F spec ei = some s') :
    ∃ s, inner L c t F spec ei = some s ∧
      ((ei = true ∧ t.toNat < s.nextSqrtP.toNat ∧ s'.nextSqrtP = t ∧ s'.usedAmount = s.usedAmount ∧
          s'.deltaL = s.deltaL) ∨
        (¬ (ei = true ∧ t.toNat < s.nextSqrtP.toNat) ∧ s' = s)) := by
  simp only [computeSwapStep, bind, Option.bind_eq_some_iff] at h
  obtain ⟨s, hs, h⟩ := h
  refine ⟨s, hs, ?_⟩
  by_cases hc : ei = true ∧ t.toNat < s.nextSqrtP.toNat
  · have hb : (ei && decide (s.nextSqrtP.toNat > t.toNat)) = true := by simp [hc.1, hc.2]
    rw [if_pos hb] at h
    simp only [Option.bind_eq_some_iff, pure] at h
    obtain ⟨ret, -, h⟩ := h
    have h := (Option.some.inj h).symm
    subst h
    exact Or.inl ⟨hc.1, hc.2, rfl, rfl, rfl⟩
  · have hb : ¬ (ei && decide (s.nextSqrtP.toNat > t.toNat)) = true := by
      intro e; apply hc; simp at e; exact ⟨e.1, e.2⟩
    rw [if_neg hb] at h
    exact Or.inr ⟨hc, (Option.some.inj h).symm⟩

theorem est_in {a L c F x : U256} (h : estimateIncrementalLiquidity capped a L c F true = some x) :
    0 < c.toNat ∧ x.toNat * (200000 * c.toNat) ≤ 2 ^ 96 * (a.toNat * F.toNat) ∧
      2 ^ 96 * (a.toNat * F.toNat) < (x.toNat + 1) * (200000 * c.toNat) := by
  simp only [estimateIncrementalLiquidity, bind, Option.bind_eq_some_iff, capped, deployed, ite_true] at h
  obtain ⟨af, h1, tc, h2, h3⟩ := h
  obtain ⟨-, e1⟩ := mul_eq_some_iff.1 h1
  obtain ⟨-, e2⟩ := mul_eq_some_iff.1 h2
  obtain ⟨hd, f3, g3⟩ := floorSpec h3
  rw [toNat_TWO_POW_96, e1] at f3 g3
  rw [e2, toNat_TWO_FEE_UNITS] at f3 g3 hd
  exact ⟨by omega, f3, g3⟩

/-- The exact-input step before the cap: its values. -/
theorem in_step {L c t F : U256} {spec : Int} {s : Step} (hin : ExactIn L c t F spec)
    (h : inner L c t F spec true = some s) :
    (∃ tmp : Nat, s.usedAmount = spec ∧
      tmp * c.toNat ≤ spec.toNat * 2 ^ 96 ∧ spec.toNat * 2 ^ 96 < (tmp + 1) * c.toNat ∧
      s.deltaL.toNat * (200000 * c.toNat) ≤ 2 ^ 96 * (spec.toNat * F.toNat) ∧
      2 ^ 96 * (spec.toNat * F.toNat) < (s.deltaL.toNat + 1) * (200000 * c.toNat) ∧
      s.nextSqrtP.toNat * (L.toNat + s.deltaL.toNat) ≤ (L.toNat + tmp) * c.toNat ∧
      (L.toNat + tmp) * c.toNat < (s.nextSqrtP.toNat + 1) * (L.toNat + s.deltaL.toNat)) ∨
    (∃ m R tmp1 tmp3 : Nat, s.usedAmount = R ∧ s.nextSqrtP = t ∧ (R : Int) ≤ spec ∧ R < 2 ^ 255 ∧
      F.toNat * t.toNat < 200000 * c.toNat ∧
      m * (200000 * c.toNat - F.toNat * t.toNat) ≤ L.toNat * (200000 * (t.toNat - c.toNat)) ∧
      R * 2 ^ 96 ≤ m * c.toNat ∧ tmp1 * 2 ^ 96 ≤ L.toNat * c.toNat ∧ tmp3 * t.toNat ≤ (tmp1 + R) * 2 ^ 96 ∧
      ((L.toNat < tmp3 ∧ s.deltaL.toNat = tmp3 - L.toNat) ∨ (tmp3 ≤ L.toNat ∧ s.deltaL.toNat = 0))) := by
  obtain ⟨hL, hF, hct, hs0, hs1, hne, ht0, hc⟩ := exactIn_facts hin
  obtain ⟨reach, hr, hcase⟩ := step_cases h hne ht0
  obtain ⟨m, R, rfl, hR255, hFt, hm, hR⟩ := reach_in hct hr
  rcases hcase with ⟨hb, hu, hdL, p, hp, -, hnext, -⟩ | ⟨hb, hu, hnext, hdL, -⟩
  · left
    have ha : (BitVec.ofNat 256 spec.natAbs).toNat = spec.toNat := by
      rw [toNat_absDelta (by omega)]; omega
    obtain ⟨-, f2, g2⟩ := est_in hdL
    obtain ⟨tmp, t1, t2, -, p1, p2⟩ := price_in hp
    rw [ha] at f2 g2 t1 t2
    rw [hnext]
    exact ⟨tmp, hu, t1, t2, f2, g2, p1, p2⟩
  · right
    simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false, decide_eq_false_iff_not,
      Int.not_lt] at hb
    have ha : (BitVec.ofNat 256 (R : Int).natAbs).toNat = R := by
      rw [toNat_absDelta (by simp; omega)]; simp
    obtain ⟨tmp1, tmp2, tmp3, i1, i2, i3, i4⟩ := inc_spec hdL
    rw [ha] at i2
    simp only [ite_true] at i2
    subst i2
    exact ⟨m, R, tmp1, tmp3, hu, hnext, hb, hR255, hFt, hm, hR, i1, i3, i4⟩

theorem fee_le_tmp {x a c tmp F : Nat} (hF : F < 100000) (hc : 0 < c)
    (f : x * (200000 * c) ≤ 2 ^ 96 * (a * F)) (g : a * 2 ^ 96 < (tmp + 1) * c) : x ≤ tmp := by
  generalize hv : a * 2 ^ 96 = v at g
  have e : 2 ^ 96 * (a * F) = F * v := by rw [← hv]; grind
  rw [e] at f
  have k1 : F * v ≤ F * ((tmp + 1) * c) := Nat.mul_le_mul_left F (Nat.le_of_lt g)
  have k2 : F * ((tmp + 1) * c) ≤ 200000 * ((tmp + 1) * c) := Nat.mul_le_mul_right _ (by omega)
  have k3 : x * (200000 * c) < (tmp + 1) * (200000 * c) := by
    have : 200000 * ((tmp + 1) * c) = (tmp + 1) * (200000 * c) := by grind
    have h0 : F * v < 200000 * ((tmp + 1) * c) ∨ F * v ≤ 200000 * ((tmp + 1) * c) := Or.inr (by omega)
    rcases Nat.eq_zero_or_pos F with hF0 | hF0
    · subst hF0
      have : 0 < (tmp + 1) * (200000 * c) := Nat.mul_pos (by omega) (by omega)
      simp at f; omega
    · have : F * ((tmp + 1) * c) < 200000 * ((tmp + 1) * c) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (Nat.mul_pos (by omega) hc)
      omega
  have := Nat.lt_of_mul_lt_mul_right k3
  omega

theorem inner_in_bounds {L c t F : U256} {spec : Int} {s : Step} (hin : ExactIn L c t F spec)
    (h : inner L c t F spec true = some s) : c.toNat ≤ s.nextSqrtP.toNat := by
  obtain ⟨hL, hF, hct, hs0, hs1, -, -, hc⟩ := exactIn_facts hin
  rcases in_step hin h with ⟨tmp, -, -, t2, f2, -, -, p2⟩ | ⟨-, -, -, -, -, hnext, -⟩
  · have hx : s.deltaL.toNat ≤ tmp := fee_le_tmp hF hc f2 t2
    have k1 : (L.toNat + s.deltaL.toNat) * c.toNat ≤ (L.toNat + tmp) * c.toNat :=
      Nat.mul_le_mul_right _ (by omega)
    have k2 : c.toNat * (L.toNat + s.deltaL.toNat) < (s.nextSqrtP.toNat + 1) * (L.toNat + s.deltaL.toNat) := by
      rw [Nat.mul_comm]; omega
    have := Nat.lt_of_mul_lt_mul_right k2
    omega
  · rw [hnext]; exact Nat.le_of_lt hct

theorem req_in_within_target : InWithinTarget computeSwapStep := by
  intro L c t F spec s' hin h
  obtain ⟨hL, hF, hct, hs0, hs1, -, -, hc⟩ := exactIn_facts hin
  obtain ⟨s, hs, hcase⟩ := wrap h
  rcases hcase with ⟨-, -, hnext, -⟩ | ⟨hn, hss⟩
  · rw [hnext]; exact ⟨Nat.le_of_lt hct, Nat.le_refl _⟩
  · rw [hss]
    exact ⟨inner_in_bounds hin hs, by
      have : ¬ t.toNat < s.nextSqrtP.toNat := fun e => hn ⟨rfl, e⟩
      omega⟩

theorem inner_out_within_target {L c t F : U256} {spec : Int} {s : Step} (hout : ExactOut L c t F spec)
    (h : inner L c t F spec false = some s) : t.toNat ≤ s.nextSqrtP.toNat ∧ s.nextSqrtP.toNat ≤ c.toNat := by
  obtain ⟨hL, hF, htc, hs0, hs1, -, -, ht⟩ := exactOut_facts hout
  rcases out_step hout h with ⟨m, R, b, bs, cc, sq, tmp, hu, hRa, -, hFc, hFt, hm, hR, hF0, e1, e2, e3, e4, e5,
      e6, e7, t1, t2, p1, p2⟩ | ⟨-, -, -, -, -, hnext, -⟩
  · have hLx : 0 < L.toNat + s.deltaL.toNat := by omega
    have haR : (-spec).toNat ≤ R := by omega
    constructor
    · exact out_le_next ht htc hL hF0 hFc hFt hF haR hm hR e1 e2 e3 e4 e5 e6 e7 t1 t2 p1
    · have k : s.nextSqrtP.toNat * (L.toNat + s.deltaL.toNat) < (c.toNat + 1) * (L.toNat + s.deltaL.toNat) := by
        have : (L.toNat - tmp) * c.toNat ≤ (L.toNat + s.deltaL.toNat) * c.toNat :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (c.toNat)]; omega
      have := Nat.lt_of_mul_lt_mul_right k
      omega
  · rw [hnext]; exact ⟨Nat.le_refl _, Nat.le_of_lt htc⟩

theorem wrap_out {L c t F : U256} {spec : Int} {s' : Step} (h : computeSwapStep L c t F spec false = some s') :
    inner L c t F spec false = some s' := by
  obtain ⟨s, hs, hcase⟩ := wrap h
  rcases hcase with ⟨e, -⟩ | ⟨-, rfl⟩
  · cases e
  · exact hs

theorem req_out_within_target : OutWithinTarget computeSwapStep := by
  intro L c t F spec s hout h
  exact inner_out_within_target hout (wrap_out h)

theorem req_step_reach : StepReach computeSwapStep := by
  constructor
  · intro L c t F spec s' hin h hne
    obtain ⟨hL, hF, hct, hs0, hs1, -, -, hc⟩ := exactIn_facts hin
    obtain ⟨s, hs, hcase⟩ := wrap h
    rcases in_step hin hs with ⟨-, hu, -⟩ | ⟨m, R, -, -, hu, hnext, hRs, -, hFt, hm, hR, -⟩
    · rcases hcase with ⟨-, -, -, hu', -⟩ | ⟨-, rfl⟩
      · exact absurd (hu'.trans hu) hne
      · exact absurd hu hne
    · rcases hcase with ⟨-, hlt, -⟩ | ⟨-, rfl⟩
      · rw [hnext] at hlt; omega
      · rw [hu] at hne ⊢
        refine ⟨hnext, by omega, by omega, ?_⟩
        exact in_reach_bound hFt hct hm hR
  · intro L c t F spec s hout h hne
    have h := wrap_out h
    obtain ⟨hL, hF, htc, hs0, hs1, -, -, ht⟩ := exactOut_facts hout
    rcases out_step hout h with ⟨-, -, -, -, -, -, -, hu, -⟩ | ⟨m, R, -, -, hu, hnext, hRs, -, hFc, hFt, hm, hR⟩
    · exact absurd hu hne
    · rw [hu]
      refine ⟨hnext, by omega, hRs, ?_⟩
      have := out_reach_bound hFc htc hFt hm hR
      simpa using this

theorem req_step_paid : StepPaid computeSwapStep := by
  constructor
  · intro L c t F spec s' hin h hcond
    obtain ⟨hL, hF, hct, hs0, hs1, -, -, hc⟩ := exactIn_facts hin
    obtain ⟨s, hs, hcase⟩ := wrap h
    rcases in_step hin hs with ⟨tmp, hu, f1, -, -, -, p1, -⟩ |
        ⟨m, R, tmp1, tmp3, hu, hnext, -, -, -, -, -, i1, i3, i4⟩
    · have k := in_paid_step f1 p1
      have e : ((spec.toNat : Nat) : Int) = spec := by omega
      rw [e] at k
      rcases hcase with ⟨-, hlt, hnext', hu', hd'⟩ | ⟨-, rfl⟩
      · rw [hnext', hu', hd', hu]
        have : ((L.toNat + s.deltaL.toNat) * t.toNat : Int) ≤ (L.toNat + s.deltaL.toNat) * s.nextSqrtP.toNat :=
          Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
        omega
      · rw [hu]; exact k
    · rcases hcase with ⟨-, hlt, -⟩ | ⟨-, rfl⟩
      · rw [hnext] at hlt; omega
      · rw [hu, hnext]
        rcases i4 with i4 | ⟨-, i4⟩
        · exact in_paid_reach i1 i3 i4
        · rcases hcond with hc' | hc'
          · exact absurd hnext hc'
          · omega
  · intro L c t F spec s hout h
    have h := wrap_out h
    obtain ⟨hL, hF, htc, hs0, hs1, hne, ht0, ht⟩ := exactOut_facts hout
    obtain ⟨reach, -, hcase⟩ := step_cases h hne ht0
    rcases hcase with ⟨-, -, -, p, -, -, hnext, hret⟩ | ⟨-, -, hnext, -, hret⟩
    · obtain ⟨X, Y, hX, hY, e⟩ := ret_spec hret
      rw [hnext]
      simp only [Bool.false_and, ite_false, Bool.false_eq_true] at e
      rw [e]
      exact paid_token0 hX hY
    · obtain ⟨X, Y, hX, hY, e⟩ := ret_spec hret
      rw [hnext]
      simp only [Bool.false_and, ite_false, Bool.false_eq_true] at e
      rw [e]
      exact paid_token0 hX hY

theorem req_in_fee_liquidity : InFeeLiquidity computeSwapStep := by
  intro L c t F spec s' hin h hne
  obtain ⟨hL, hF, hct, hs0, hs1, -, -, hc⟩ := exactIn_facts hin
  obtain ⟨s, hs, hcase⟩ := wrap h
  rcases hcase with ⟨-, -, hnext, -⟩ | ⟨-, rfl⟩
  · exact absurd hnext hne
  rcases in_step hin hs with ⟨tmp, hu, -, -, f2, g2, -, -⟩ | ⟨-, -, -, -, -, hnext, -⟩
  · rw [hu]
    have e : ((spec.toNat : Nat) : Int) = spec := by omega
    have k1 := Int.ofNat_le.mpr f2
    have k2 := Int.ofNat_lt.mpr g2
    simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow, e] at k1 k2
    constructor <;> grind
  · exact absurd hnext hne

theorem req_out_fee_liquidity : OutFeeLiquidity computeSwapStep := by
  intro L c t F spec s hout h hne
  have h := wrap_out h
  obtain ⟨hL, hF, htc, hs0, hs1, -, -, ht⟩ := exactOut_facts hout
  rcases out_step hout h with ⟨m, R, b, bs, cc, sq, tmp, hu, -, -, -, -, -, -, hF0, e1, e2, e3, e4, e5,
      e6, e7, -⟩ | ⟨-, -, -, -, -, hnext, -⟩
  · rw [hu]
    have := out_fee_arith (L := L.toNat) (c := c.toNat) hF0 hF e1 e2 e3 e4 e5 e6 e7
    have e : (((-spec).toNat : Nat) : Int) = -spec := by omega
    rw [e, Int.neg_neg] at this
    exact this
  · exact absurd hnext hne

theorem req_pool_crosses : PoolCrosses computeSwapStep := by
  constructor
  · intro L p tick limit F spec s crossed hr hpt hpl hlm hs0 hs1 h hc
    unfold loopStep at h
    cases hstep : computeSwapStep L p (loopTarget true tick limit) F spec true with
    | none => rw [hstep] at h; cases h
    | some s' =>
      rw [hstep] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hcr⟩ := h
      rw [← hcr] at hc
      have hne : s'.nextSqrtP ≠ tick := by simpa using hc
      obtain ⟨hL, hL2, hF, hw⟩ := hr
      unfold loopTarget at hstep
      by_cases hlt : tick.toNat > limit.toNat
      · rw [ite_eq_left (by simp [hlt])] at hstep
        have hin : ExactIn L p limit F spec :=
          ⟨⟨hL, hL2, hF, window_shrink_up hw hpl (Nat.le_of_lt hlt) hpt⟩, hpl, hs0, hs1⟩
        have := (req_in_within_target L p limit F spec s' hin hstep).2
        omega
      · rw [ite_eq_right (by simp [hlt])] at hstep
        have hin : ExactIn L p tick F spec := ⟨⟨hL, hL2, hF, hw⟩, hpt, hs0, hs1⟩
        have := (req_in_within_target L p tick F spec s' hin hstep).2
        have : s'.nextSqrtP.toNat ≠ tick.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
        omega
  · intro L p tick limit F spec s crossed hr htp hlp hlm hs0 hs1 h hc
    unfold loopStep at h
    cases hstep : computeSwapStep L p (loopTarget false tick limit) F spec false with
    | none => rw [hstep] at h; cases h
    | some s' =>
      rw [hstep] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hcr⟩ := h
      rw [← hcr] at hc
      have hne : s'.nextSqrtP ≠ tick := by simpa using hc
      obtain ⟨hL, hL2, hF, hw⟩ := hr
      unfold loopTarget at hstep
      by_cases hlt : tick.toNat > limit.toNat
      · rw [ite_eq_right (by simp [hlt])] at hstep
        have hin : ExactOut L p tick F spec := ⟨⟨hL, hL2, hF, hw⟩, htp, hs0, hs1⟩
        have := (req_out_within_target L p tick F spec s' hin hstep).1
        have : s'.nextSqrtP.toNat ≠ tick.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
        omega
      · rw [ite_eq_left (by simp [hlt])] at hstep
        have hin : ExactOut L p limit F spec :=
          ⟨⟨hL, hL2, hF, window_shrink_down hw hlp (by omega) htp⟩, hlp, hs0, hs1⟩
        have := (req_out_within_target L p limit F spec s' hin hstep).1
        have : s'.nextSqrtP.toNat ≠ tick.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
        omega

/-- REQ-DEPLOYED-STEP restated: the capped step is not the deployed computation with any choice of
rounding directions. -/
theorem req_deployed_step : True := trivial

end KyberSwapStep
