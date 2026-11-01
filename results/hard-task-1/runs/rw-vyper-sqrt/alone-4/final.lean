import VyperSqrt.Spec
import VyperSqrt.Lemmas

namespace VyperSqrt

/-- Final choice of PR 4486: the minimum of the last two iterates. -/
def finMin (y z : Int) : Int := if y < z then y else z

def sqrt : SqrtFn := vyperSqrtWith finMin

/-! ## Natural-number Newton iteration -/

/-- One Newton step on naturals for `X = a * 10^10`. -/
def nstep (X z : Nat) : Nat := (X / z + z) / 2

theorem nstep_eq (X z : Nat) : nstep X z = (X / z + z) / 2 := rfl

/-- The deterministic Newton sequence from the seed. -/
def Zseq (X z0 : Nat) : Nat → Nat
  | 0 => z0
  | k + 1 => nstep X (Zseq X z0 k)

theorem Zseq_zero (X z0 : Nat) : Zseq X z0 0 = z0 := rfl

theorem Zseq_succ (X z0 k : Nat) : Zseq X z0 (k + 1) = nstep X (Zseq X z0 k) := rfl

/-- The loop body on naturals, mirroring `loop`. -/
def nloop (X : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, y, z => (y, z)
  | m + 1, y, z => if z = y then (y, z) else nloop X m z (nstep X z)

theorem nloop_zero (X y z : Nat) : nloop X 0 y z = (y, z) := rfl

theorem nloop_succ (X m y z : Nat) :
    nloop X (m + 1) y z = if z = y then (y, z) else nloop X m z (nstep X z) := rfl

/-- Square of a successor. -/
theorem sq_expand (t : Nat) : (t + 1) * (t + 1) = t * t + (t + t) + 1 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_one]
  omega

/-- Uniqueness of the integer square root. -/
theorem sqrt_uniq {X w s : Nat} (h1 : w * w ≤ X) (h2 : X < (w + 1) * (w + 1))
    (hs1 : s * s ≤ X) (hs2 : X < (s + 1) * (s + 1)) : w = s := by
  apply Nat.le_antisymm
  · cases Nat.lt_or_ge w (s + 1) with
    | inl h => omega
    | inr h =>
      have hcontra : (s + 1) * (s + 1) ≤ w * w := Nat.mul_self_le_mul_self h
      omega
  · cases Nat.lt_or_ge s (w + 1) with
    | inl h => omega
    | inr h =>
      have hcontra : (w + 1) * (w + 1) ≤ s * s := Nat.mul_self_le_mul_self h
      omega

/-- Difference of squares helper. -/
theorem sq_sub_add_sq (s d : Nat) (h : d ≤ s) :
    (s - d) * (s + d) + d * d = s * s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = d + t := ⟨s - d, by omega⟩
  have f1 : d + t - d = t := by omega
  rw [f1]
  have c : d * t = t * d := Nat.mul_comm _ _
  rw [Nat.mul_add, Nat.mul_add, Nat.add_mul, Nat.mul_add, Nat.mul_add, c]
  omega

/-- Newton step never goes below the root. -/
theorem newton_ge {X z s : Nat} (hz : 1 ≤ z) (hs : s * s ≤ X) :
    s ≤ (X / z + z) / 2 := by
  cases Nat.lt_or_ge ((X / z + z) / 2) s with
  | inr h => exact h
  | inl hlt =>
    generalize hu_eq : X / z = u at hlt ⊢
    generalize hr_eq : X % z = r
    have hdm : z * u + r = X := by
      rw [← hu_eq, ← hr_eq]; exact Nat.div_add_mod X z
    have hmod : r < z := by
      rw [← hr_eq]; exact Nat.mod_lt _ (by omega)
    have h2 : u + z < 2 * s := by
      have h3 := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp hlt
      omega
    have hle : u + z ≤ 2 * s - 1 := by omega
    have hz2 : z ≤ 2 * s - 1 := by omega
    have hX1 : X < (u + 1) * z := by
      have e : (u + 1) * z = u * z + z := by
        rw [Nat.add_mul, Nat.one_mul]
      have hc : z * u = u * z := Nat.mul_comm _ _
      omega
    have hu : u + 1 ≤ 2 * s - z := by omega
    have hmul := Nat.mul_le_mul_right z hu
    have hcap : (2 * s - z) * z ≤ s * s := by
      cases Nat.le_total z s with
      | inl hzs =>
        obtain ⟨d, rfl⟩ : ∃ d, s = z + d := ⟨s - z, by omega⟩
        have e2 : 2 * (z + d) - z = z + (d + d) := by omega
        rw [e2] at hmul ⊢
        have key := sq_sub_add_sq (z + d) d (Nat.le_add_left _ _)
        have f1 : (z + d) - d = z := Nat.add_sub_cancel _ _
        have f2 : (z + d) + d = z + (d + d) := by omega
        rw [f1, f2] at key
        have hcomm : (z + (d + d)) * z = z * (z + (d + d)) := Nat.mul_comm _ _
        omega
      | inr hsz =>
        obtain ⟨d, rfl⟩ : ∃ d, z = s + d := ⟨z - s, by omega⟩
        have e2s : 2 * s - (s + d) = s - d := by omega
        rw [e2s]
        have hd : d ≤ s := by omega
        have key := sq_sub_add_sq s d hd
        omega
    omega

/-- The quotient stays small once the iterate is past the root. -/
theorem newton_div_le {X z s : Nat} (hs1 : s * s ≤ X) (hs2 : X < (s + 1) * (s + 1))
    (hz : 1 ≤ z) (hzs : s ≤ z) : X / z ≤ s + 2 := by
  have eexpand : (s + 1) * (s + 1) = s * s + (s + s) + 1 := sq_expand s
  have hXle : X ≤ s * s + (s + s) := by omega
  have hsz : s * s ≤ s * z := Nat.mul_le_mul (Nat.le_refl _) hzs
  have h2s3z : 2 * s < 3 * z := by omega
  have e3z : (s + 3) * z = s * z + 3 * z := by rw [Nat.add_mul]
  have hlt : X / z < s + 3 := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < z)]
    omega
  omega

/-- Fixed points of the Newton step are the root. -/
theorem nstep_fixed {X w s : Nat} (hfix : nstep X w = w) (hw : 1 ≤ w)
    (hs1 : s * s ≤ X) (hs2 : X < (s + 1) * (s + 1)) : w = s := by
  rw [nstep_eq] at hfix
  generalize hu_eq : X / w = u at hfix
  have h2w : u + w = 2 * w ∨ u + w = 2 * w + 1 := by
    have hdm2 := Nat.div_add_mod (u + w) 2
    have hmod2 := Nat.mod_two_eq_zero_or_one (u + w)
    rcases hmod2 with h0 | h1
    · left
      have := hdm2
      rw [hfix, h0, Nat.add_zero] at this
      exact this.symm
    · right
      have := hdm2
      rw [hfix, h1] at this
      exact this.symm
  have huw : u = w ∨ u = w + 1 := by omega
  have hmul_le := Nat.div_mul_le_self X w
  rw [hu_eq] at hmul_le
  have hdm0 := Nat.div_add_mod X w
  rw [hu_eq] at hdm0
  generalize hr_eq : X % w = r at hdm0
  have hmod : r < w := by
    rw [← hr_eq]; exact Nat.mod_lt _ (by omega)
  cases huw with
  | inl hq =>
    have g1 : w * w ≤ X := by
      rw [hq] at hmul_le
      have hc : w * w = w * w := rfl
      omega
    have g2 : X < (w + 1) * (w + 1) := by
      have e : (u + 1) * w = u * w + w := by rw [Nat.add_mul, Nat.one_mul]
      have hc : w * u = u * w := Nat.mul_comm _ _
      have hlt : X < (u + 1) * w := by omega
      rw [hq] at hlt
      have hle2 := Nat.mul_le_mul_left (w + 1) (by omega : w ≤ w + 1)
      exact Nat.lt_of_lt_of_le hlt hle2
    exact sqrt_uniq g1 g2 hs1 hs2
  | inr hq =>
    have hle : w + 1 ≤ u := by omega
    have hleu : w + 1 ≤ X / w := by rw [hu_eq]; exact hle
    have g1' : (w + 1) * w ≤ X :=
      (Nat.le_div_iff_mul_le (by omega : 0 < w)).mp hleu
    have g1 : w * w ≤ X := by
      have hww := Nat.mul_le_mul_right w (by omega : w ≤ w + 1)
      have hc : w * (w + 1) = (w + 1) * w := Nat.mul_comm _ _
      omega
    have hlt2 : u < w + 2 := by omega
    have hXw : X < (w + 2) * w := by
      have hlt3 : X / w < w + 2 := by rw [hu_eq]; exact hlt2
      exact (Nat.div_lt_iff_lt_mul (by omega : 0 < w)).mp hlt3
    have eww : (w + 2) * w = w * w + (w + w) := by
      rw [Nat.add_mul]
      omega
    have esq := sq_expand w
    have g2 : X < (w + 1) * (w + 1) := by omega
    exact sqrt_uniq g1 g2 hs1 hs2

/-- Newton step upper bound. -/
theorem nstep_upper {X z s : Nat} (hs1 : s * s ≤ X) (hs2 : X < (s + 1) * (s + 1))
    (hz : 1 ≤ z) (hzs : s ≤ z) : nstep X z ≤ (s + 2 + z) / 2 := by
  rw [nstep_eq]
  have h := newton_div_le hs1 hs2 hz hzs
  have h2 : (X / z + z) / 2 ≤ (s + 2 + z) / 2 :=
    Nat.div_le_div_right (Nat.add_le_add h (Nat.le_refl z))
  exact h2

/-- Value at the root. -/
theorem nstep_mem_s {X s : Nat} (hs1 : s * s ≤ X) (hs2 : X < (s + 1) * (s + 1))
    (hspos : 1 ≤ s) : nstep X s = s ∨ nstep X s = s + 1 := by
  have hlo : s ≤ X / s :=
    (Nat.le_div_iff_mul_le (by omega : 0 < s)).mpr hs1
  have hhi : X / s ≤ s + 2 := newton_div_le hs1 hs2 hspos (Nat.le_refl _)
  rw [nstep_eq]
  generalize X / s = u at hlo hhi ⊢
  omega

/-- One above the root maps exactly to the root. -/
theorem nstep_succ_eq {X s : Nat} (hs1 : s * s ≤ X) (hs2 : X < (s + 1) * (s + 1))
    (hspos : 1 ≤ s) : nstep X (s + 1) = s := by
  have hhi : X / (s + 1) ≤ s := by
    have hlt : X / (s + 1) < s + 1 := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < s + 1)).mpr
      have e := sq_expand s
      omega
    omega
  have hlo : s - 1 ≤ X / (s + 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
    have e1 : r + 1 - 1 = r := by omega
    have e2 : r + 1 + 1 = r + 2 := by omega
    rw [e1, e2]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < r + 2)).mpr
    have er : r * (r + 2) = r * r + (r + r) := by
      rw [Nat.mul_add]
      omega
    have hsq := sq_expand r
    omega
  rw [nstep_eq]
  generalize X / (s + 1) = u at hlo hhi ⊢
  omega

/-- Two above the root maps back into the pair. -/
theorem nstep_s2_mem {X s : Nat} (hs1 : s * s ≤ X) (hs2 : X < (s + 1) * (s + 1))
    (hspos : 1 ≤ s) : nstep X (s + 2) = s ∨ nstep X (s + 2) = s + 1 := by
  have hlo : s ≤ nstep X (s + 2) := newton_ge (by omega) hs1
  have hhi : X / (s + 2) ≤ s := by
    have hlt : X / (s + 2) < s + 1 := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < s + 2)).mpr
      have e12 : (s + 1) * (s + 2) = (s + 1) * (s + 1) + (s + 1) := by
        have hss : s + 2 = (s + 1) + 1 := by omega
        rw [hss, Nat.mul_add, Nat.mul_one]
      have e2 := sq_expand s
      omega
    omega
  have hup : nstep X (s + 2) ≤ s + 1 := by
    rw [nstep_eq]
    generalize X / (s + 2) = u at hhi ⊢
    omega
  omega

/-- Square of a sum. -/
theorem sq_add (p q : Nat) : (p + q) * (p + q) = p * p + (p * q + p * q) + q * q := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm q p]
  omega

/-- Twice a product is bounded by the sum of squares. -/
theorem two_mul_le_add_sq (p q : Nat) : 2 * p * q ≤ p * p + q * q := by
  cases Nat.le_total p q with
  | inl hpq =>
    obtain ⟨t, rfl⟩ : ∃ t, q = p + t := ⟨q - p, by omega⟩
    have e1 : (p + t) * (p + t) = p * p + (p * t + p * t) + t * t := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm t p]
      omega
    have e2 : 2 * p * (p + t) = (p * p + p * p) + (p * t + p * t) := by
      rw [Nat.mul_add, Nat.mul_assoc, Nat.mul_assoc]
      omega
    omega
  | inr hqp =>
    obtain ⟨t, rfl⟩ : ∃ t, p = q + t := ⟨p - q, by omega⟩
    have e1 : (q + t) * (q + t) = q * q + (q * t + q * t) + t * t := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm t q]
      omega
    have e2 : 2 * (q + t) * q = (q * q + q * q) + (q * t + q * t) := by
      rw [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm t q]
      omega
    omega

/-- Assembly helper with small constants. -/
theorem seed_sq_bound_aux (a m r H D : Nat)
    (hdm : 2 * m + r = a) (hmod : r < 2)
    (hsq : m * H + m * H ≤ m * m + H * H)
    (e1 : (m + H) * (m + H) = m * m + (m * H + m * H) + H * H)
    (hD : D = H + H)
    (e_a : a * D ≤ (2 * m + 1) * D)
    (e_dist : (2 * m + 1) * D
      = ((m * H + m * H) + H) + ((m * H + m * H) + H)) :
    a * D ≤ (m + H) * (m + H) + D := by
  omega

/-- Small helper for the seed comparison. -/
theorem seed_lt_aux (Z H T : Nat) (hz2 : H + H ≤ Z + Z) (h10 : H + H = T)
    (e : (Z + 1) * (Z + 1) = Z * Z + (Z + Z) + 1) :
    Z * Z + T < (Z + 1) * (Z + 1) := by
  omega

/-- The seed almost dominates: `X ≤ z0 ^ 2 + 10 ^ 10`. -/
theorem seed_sq_bound (a : Nat) :
    a * 10 ^ 10 ≤ (a / 2 + 5 * 10 ^ 9) * (a / 2 + 5 * 10 ^ 9) + 10 ^ 10 := by
  have hdm := Nat.div_add_mod a 2
  have hmod : a % 2 < 2 := Nat.mod_lt _ (by decide)
  have e_a : a * (10 ^ 10) ≤ (2 * (a / 2) + 1) * (10 ^ 10) :=
    Nat.mul_le_mul_right _ (by omega)
  have hsq := two_mul_le_add_sq (a / 2) (5 * 10 ^ 9)
  have e1 := sq_add (a / 2) (5 * 10 ^ 9)
  have hD : (10 : Nat) ^ 10 = (5 * 10 ^ 9) + (5 * 10 ^ 9) := by decide
  have e2 : 2 * (a / 2) * (5 * 10 ^ 9)
      = (a / 2) * (5 * 10 ^ 9) + (a / 2) * (5 * 10 ^ 9) := by
    rw [Nat.mul_assoc, Nat.two_mul]
  rw [e2] at hsq
  have e_dist : (2 * (a / 2) + 1) * (10 ^ 10)
      = (((a / 2) * (5 * 10 ^ 9) + (a / 2) * (5 * 10 ^ 9)) + (5 * 10 ^ 9))
        + (((a / 2) * (5 * 10 ^ 9) + (a / 2) * (5 * 10 ^ 9)) + (5 * 10 ^ 9)) := by
    rw [hD, Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.two_mul]
  exact seed_sq_bound_aux a (a / 2) (a % 2) (5 * 10 ^ 9) (10 ^ 10)
    hdm hmod hsq e1 hD e_a e_dist

/-- The seed is past the root. -/
theorem seed_ge {a s : Nat} (ha : 1 ≤ a) (hs1 : s * s ≤ a * 10 ^ 10) :
    s ≤ a / 2 + 5 * 10 ^ 9 := by
  have hz0 : 5 * 10 ^ 9 ≤ a / 2 + 5 * 10 ^ 9 := Nat.le_add_left _ _
  cases Nat.lt_or_ge s (a / 2 + 5 * 10 ^ 9 + 1) with
  | inl h => omega
  | inr h =>
    exfalso
    have hF1 := seed_sq_bound a
    have hsq := Nat.mul_self_le_mul_self h
    have e := sq_expand (a / 2 + 5 * 10 ^ 9)
    have chain : (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1)
        ≤ (a / 2 + 5 * 10 ^ 9) * (a / 2 + 5 * 10 ^ 9) + 10 ^ 10 :=
      Nat.le_trans (Nat.le_trans hsq hs1) hF1
    have hz2 : (5 * 10 ^ 9) + (5 * 10 ^ 9)
        ≤ (a / 2 + 5 * 10 ^ 9) + (a / 2 + 5 * 10 ^ 9) :=
      Nat.add_le_add hz0 hz0
    have h10 : (5 : Nat) * 10 ^ 9 + 5 * 10 ^ 9 = 10 ^ 10 := by decide
    have hbig : (a / 2 + 5 * 10 ^ 9) * (a / 2 + 5 * 10 ^ 9) + 10 ^ 10
        < (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1) :=
      seed_lt_aux _ _ _ hz2 h10 e
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt chain hbig)

/-- The root of a positive input is positive. -/
theorem s_pos {a : Nat} (ha : 1 ≤ a) : 1 ≤ Nat.sqrt (a * 10 ^ 10) := by
  by_cases hz : Nat.sqrt (a * 10 ^ 10) = 0
  · exfalso
    have hs2 := Nat.lt_succ_sqrt (a * 10 ^ 10)
    rw [hz] at hs2
    simp at hs2
    have hX : (10 : Nat) ^ 10 ≤ a * 10 ^ 10 := by
      have hmul := Nat.mul_le_mul_right (10 ^ 10) ha
      simpa using hmul
    omega
  · exact Nat.pos_of_ne_zero hz

/-- The root fits well below `2 ^ 101`. -/
theorem s_lt_101 {X s : Nat} (hs1 : s * s ≤ X) (hX : X < 2 ^ 201) :
    s + 1 ≤ 2 ^ 101 := by
  cases Nat.lt_or_ge s (2 ^ 101) with
  | inl h => exact h
  | inr h =>
    have hsq := Nat.mul_self_le_mul_self h
    have e202 : (2 ^ 101) * (2 ^ 101) = 2 ^ 202 := by decide
    have h201 : (2 : Nat) ^ 201 ≤ 2 ^ 202 := by decide
    have hle : X < (2 ^ 101) * (2 ^ 101) := by
      rw [e202]; exact Nat.lt_of_lt_of_le hX h201
    have hge : (2 ^ 101) * (2 ^ 101) ≤ X := Nat.le_trans hsq hs1
    exfalso
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hge hle)

/-- Every iterate stays past the root. -/
theorem Zseq_ge {X s z0 : Nat} (hs1 : s * s ≤ X) (hspos : 1 ≤ s) (hz0 : s ≤ z0)
    (k : Nat) : s ≤ Zseq X z0 k := by
  induction k with
  | zero => exact hz0
  | succ k ih =>
    have h1 : 1 ≤ Zseq X z0 k := by omega
    have h2 : s ≤ (X / Zseq X z0 k + Zseq X z0 k) / 2 := newton_ge h1 hs1
    rw [Zseq_succ, nstep_eq]
    exact h2

/-- The excess over the root more than halves each step. -/
theorem Zseq_rate {X s z0 : Nat} (hs1 : s * s ≤ X) (hs2 : X < (s + 1) * (s + 1))
    (hspos : 1 ≤ s) (hz0 : s ≤ z0) (k : Nat) :
    k ≤ 200 → Zseq X z0 k - s ≤ 2 + (z0 - s) / 2 ^ k := by
  induction k with
  | zero =>
    intro _
    rw [Zseq_zero, Nat.pow_zero, Nat.div_one]
    omega
  | succ k ih =>
    intro hk
    have hk' : k ≤ 200 := by omega
    have ih' := ih hk'
    have hge := Zseq_ge hs1 hspos hz0 k
    have hdiv := newton_div_le hs1 hs2 (by omega : 1 ≤ Zseq X z0 k) hge
    have hup : nstep X (Zseq X z0 k) ≤ (s + 2 + Zseq X z0 k) / 2 :=
      nstep_upper hs1 hs2 (by omega : 1 ≤ Zseq X z0 k) hge
    have eB : (s + 2 + Zseq X z0 k) / 2 - s = ((Zseq X z0 k - s) + 2) / 2 := by
      omega
    have e4 : ((2 + (z0 - s) / 2 ^ k) + 2) / 2 = 2 + ((z0 - s) / 2 ^ k) / 2 := by
      omega
    have e5 : ((z0 - s) / 2 ^ k) / 2 = (z0 - s) / 2 ^ (k + 1) := by
      rw [Nat.div_div_eq_div_mul]
      have e6 : (2 : Nat) ^ k * 2 = 2 ^ (k + 1) := (Nat.pow_succ 2 k).symm
      rw [e6]
    have h1 : (Zseq X z0 k - s) + 2 ≤ ((2 + (z0 - s) / 2 ^ k) + 2) := by omega
    have h2 : ((Zseq X z0 k - s) + 2) / 2 ≤ (((2 + (z0 - s) / 2 ^ k) + 2)) / 2 :=
      Nat.div_le_div_right h1
    rw [Zseq_succ]
    omega

theorem req_sqrt_not_above   : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below   : SqrtNotBelow sqrt := sorry
theorem req_sqrt_total       : SqrtTotal sqrt := sorry
theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := sorry
theorem req_deployed_loop    : DeployedLoop sqrt := sorry

end VyperSqrt
