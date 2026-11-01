import OzSqrt.Spec
import OzSqrt.Lemmas
namespace OzSqrt

def sqrt : SqrtFn := newtonSqrt 7

theorem req_newton_budget : NewtonBudget sqrt :=
  ⟨7, Nat.le_refl 7, fun a => rfl⟩

/-- Floor square root existence on Nat, by induction. -/
theorem natFloorExists (a : Nat) : ∃ s, s * s ≤ a ∧ a < (s + 1) * (s + 1) := by
  induction a with
  | zero => exact ⟨0, by omega, by omega⟩
  | succ n ih =>
    obtain ⟨s, hs1, hs2⟩ := ih
    by_cases h : n + 1 < (s + 1) * (s + 1)
    · exact ⟨s, by omega, h⟩
    · have hle : n + 1 = (s + 1) * (s + 1) := by omega
      refine ⟨s + 1, by omega, ?_⟩
      have e1 : (s + 1 + 1) * (s + 1 + 1) = (s + 1) * (s + 1) + ((s + 1) + (s + 1 + 1)) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
        omega
      omega

/-- The Nat floor root, chosen classically. -/
noncomputable def natFloor (a : Nat) : Nat := Classical.choose (natFloorExists a)

theorem natFloor_sq_le (a : Nat) : natFloor a * natFloor a ≤ a :=
  (Classical.choose_spec (natFloorExists a)).1

theorem natFloor_lt_succ (a : Nat) : a < (natFloor a + 1) * (natFloor a + 1) :=
  (Classical.choose_spec (natFloorExists a)).2

theorem natFloor_maximal (a r : Nat) (h : r * r ≤ a) : r ≤ natFloor a := by
  apply Nat.le_of_not_gt
  intro hgt
  have h1 : natFloor a + 1 ≤ r := Nat.succ_le_of_lt hgt
  have h2 := Nat.mul_le_mul h1 h1
  have h3 := natFloor_lt_succ a
  omega

theorem natFloor_unique (a s : Nat) (h1 : s * s ≤ a) (h2 : a < (s + 1) * (s + 1)) :
    s = natFloor a := by
  apply Nat.le_antisymm
  · exact natFloor_maximal a s h1
  · apply Nat.le_of_not_gt
    intro hgt
    have h1' : s + 1 ≤ natFloor a := Nat.succ_le_of_lt hgt
    have h2' := Nat.mul_le_mul h1' h1'
    have h3 := natFloor_sq_le a
    omega

theorem log2_div_one_aux (a : U256) (hpos : 0 < a.toNat) :
    a.toNat / 2 ^ (log2 a).toNat = 1 := by
  have ha := a.isLt
  have hpos' : 0 < a.toNat := hpos
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
  have hq' : q.1.toNat = 1 := by omega
  omega

theorem log2_div_one (a : U256) (hpos : 0 < a.toNat) :
    a.toNat / 2 ^ (log2 a).toNat = 1 := log2_div_one_aux a hpos

theorem log2_bounds (a : U256) (hpos : 0 < a.toNat) :
    2 ^ (log2 a).toNat ≤ a.toNat ∧ a.toNat < 2 ^ ((log2 a).toNat + 1) := by
  have hdiv := log2_div_one_aux a hpos
  have hpow : 0 < 2 ^ (log2 a).toNat := Nat.two_pow_pos _
  constructor
  · have h1 : 1 ≤ a.toNat / 2 ^ (log2 a).toNat := by omega
    have h2 := (Nat.le_div_iff_mul_le hpow).mp h1
    simpa using h2
  · have h1 : a.toNat / 2 ^ (log2 a).toNat < 2 := by omega
    have h2 := (Nat.div_lt_iff_lt_mul hpow).mp h1
    have he : 2 * 2 ^ (log2 a).toNat = 2 ^ ((log2 a).toNat + 1) := by
      rw [Nat.pow_succ]
      omega
    omega

theorem log2_lt_256 (a : U256) : (log2 a).toNat < 256 := by
  by_cases hpos : a.toNat = 0
  · have h0 : a = 0 := BitVec.eq_of_toNat_eq (by simpa using hpos)
    subst h0
    decide
  · have hpos' : 0 < a.toNat := Nat.pos_of_ne_zero hpos
    have hb := log2_bounds a hpos'
    have ha := a.isLt
    have hle : 2 ^ (log2 a).toNat < 2 ^ 256 := by omega
    apply Nat.lt_of_not_ge
    intro hge
    have hge' : 256 ≤ (log2 a).toNat := hge
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hge'
    omega

/-- Initial estimate value on Nat. -/
def natR0 (a : U256) : Nat := 2 ^ ((log2 a).toNat / 2)

theorem natR0_sq_le (a : U256) (hpos : 0 < a.toNat) :
    natR0 a * natR0 a ≤ a.toNat := by
  unfold natR0
  have hb := log2_bounds a hpos
  have hle : 2 * ((log2 a).toNat / 2) ≤ (log2 a).toNat := by
    have h := Nat.div_mul_le_self (log2 a).toNat 2
    omega
  have hpow1 : 2 ^ (2 * ((log2 a).toNat / 2)) ≤ 2 ^ (log2 a).toNat :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hle
  have heq : (2 ^ ((log2 a).toNat / 2)) * (2 ^ ((log2 a).toNat / 2))
      = 2 ^ (2 * ((log2 a).toNat / 2)) := by
    rw [← Nat.pow_add, Nat.two_mul]
  omega

theorem natR0_lt_four_mul (a : U256) (hpos : 0 < a.toNat) :
    a.toNat < 4 * (natR0 a * natR0 a) := by
  unfold natR0
  have hb := log2_bounds a hpos
  have hmod : (log2 a).toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  have hdiv : 2 * ((log2 a).toNat / 2) + (log2 a).toNat % 2 = (log2 a).toNat :=
    Nat.div_add_mod _ _
  have hle : (log2 a).toNat + 1 ≤ 2 + 2 * ((log2 a).toNat / 2) := by omega
  have hpow : 2 ^ ((log2 a).toNat + 1) ≤ 2 ^ (2 + 2 * ((log2 a).toNat / 2)) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hle
  have heq1 : (2 ^ ((log2 a).toNat / 2)) * (2 ^ ((log2 a).toNat / 2))
      = 2 ^ (2 * ((log2 a).toNat / 2)) := by
    rw [← Nat.pow_add, Nat.two_mul]
  have heq2 : 2 ^ (2 + 2 * ((log2 a).toNat / 2))
      = 4 * ((2 ^ ((log2 a).toNat / 2)) * (2 ^ ((log2 a).toNat / 2))) := by
    have h4 : (4 : Nat) = 2 ^ 2 := by decide
    rw [h4, ← Nat.pow_add, ← Nat.pow_add, Nat.two_mul]
  omega

theorem natR0_le_floor (a : U256) (hpos : 0 < a.toNat) :
    natR0 a ≤ natFloor a.toNat := by
  apply natFloor_maximal
  exact natR0_sq_le a hpos

theorem natR0_pos (a : U256) : 0 < natR0 a := Nat.two_pow_pos _

theorem twoR0_ge_succ (a : U256) (hpos : 0 < a.toNat) :
    natFloor a.toNat + 1 ≤ 2 * natR0 a := by
  apply Nat.le_of_not_gt
  intro hgt
  have hlt : 2 * natR0 a < natFloor a.toNat + 1 := hgt
  have hle : 2 * natR0 a ≤ natFloor a.toNat := by omega
  have hmul := Nat.mul_le_mul hle hle
  have hsq := natFloor_sq_le a.toNat
  have h4 : (2 * natR0 a) * (2 * natR0 a) = 4 * (natR0 a * natR0 a) := by
    ac_rfl
  have hlt4 := natR0_lt_four_mul a hpos
  omega

theorem bvr0_eq (a : U256) : ((1 : U256) <<< (log2 a >>> 1)).toNat = natR0 a := by
  have hlog := log2_lt_256 a
  have hshift : (log2 a >>> 1).toNat = (log2 a).toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hk256 : (log2 a >>> 1).toNat < 256 := by omega
  have hrfl : ((1 : U256) <<< (log2 a >>> 1)).toNat
      = (((1 : U256) <<< ((log2 a >>> 1).toNat)).toNat) := rfl
  rw [hrfl, BitVec.toNat_shiftLeft]
  have h1nat : (1 : U256).toNat = 1 := by decide
  rw [h1nat]
  have hmod : (1 : Nat) <<< (log2 a >>> 1).toNat % 2 ^ 256
      = (1 : Nat) <<< (log2 a >>> 1).toNat := by
    apply Nat.mod_eq_of_lt
    have h2 : (1 : Nat) <<< (log2 a >>> 1).toNat = 2 ^ (log2 a >>> 1).toNat := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [h2]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hk256
  rw [hmod]
  have h3 : (1 : Nat) <<< (log2 a >>> 1).toNat = 2 ^ ((log2 a).toNat / 2) := by
    rw [hshift, Nat.shiftLeft_eq, Nat.one_mul]
  rw [h3]
  rfl

theorem s_lt_2pow128 (A : Nat) (hA : A < 2 ^ 256) : natFloor A < 2 ^ 128 := by
  apply Nat.lt_of_not_ge
  intro hge
  have hmul := Nat.mul_le_mul hge hge
  have hsq := natFloor_sq_le A
  have heq : (2 ^ 128) * (2 ^ 128) = 2 ^ 256 := by
    rw [← Nat.pow_add]
  omega

theorem s_pos_of_pos (A : Nat) (hA : 0 < A) : 0 < natFloor A := by
  have h1 : 1 * 1 ≤ A := by
    rw [Nat.one_mul]
    exact hA
  have hm := natFloor_maximal A 1 h1
  omega

/-- Nat Newton step. -/
def natNext (A r : Nat) : Nat := (r + A / r) / 2

/-- Nat Newton iterates from R0. -/
def natIter (A R0 : Nat) : Nat → Nat
  | 0 => R0
  | k + 1 => natNext A (natIter A R0 k)

theorem natIter_zero (A R0 : Nat) : natIter A R0 0 = R0 := rfl
theorem natIter_succ (A R0 k : Nat) : natIter A R0 (k + 1) = natNext A (natIter A R0 k) := rfl

theorem natNext_pos (A r : Nat) (hA : 0 < A) (hr : 0 < r) : 0 < natNext A r := by
  unfold natNext
  have h2 : 2 ≤ r + A / r := by
    by_cases hle : r ≤ A
    · have hq : 1 ≤ A / r := by
        have h1 : 1 * r ≤ A := by
          rw [Nat.one_mul]
          exact hle
        exact (Nat.le_div_iff_mul_le hr).mpr h1
      exact Nat.add_le_add hr hq
    · have hlt : A < r := Nat.lt_of_not_le hle
      have h1r : 1 < r := Nat.lt_of_le_of_lt hA hlt
      have hr2 : 2 ≤ r := Nat.succ_le_of_lt h1r
      exact Nat.le_trans hr2 (Nat.le_add_right r (A / r))
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr h2

theorem two_mul_div_two_le (n : Nat) : 2 * (n / 2) ≤ n := by
  have h := Nat.div_mul_le_self n 2
  omega

theorem div_two_le_of_le (m n : Nat) (h : m ≤ n) : m / 2 ≤ n / 2 :=
  Nat.div_le_div_right h

theorem two_mul_le_add_sq (s r : Nat) : 2 * s * r ≤ s * s + r * r := by
  by_cases h : s ≤ r
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hcomm : d * s = s * d := Nat.mul_comm _ _
    have h2 : 2 * s * d = s * d + s * d := by
      rw [Nat.two_mul, Nat.add_mul]
    have e1 : (s + d) * (s + d) = s * s + (s * d + (d * s + d * d)) := by
      rw [Nat.add_mul, Nat.mul_add s s d, Nat.mul_add d s d]
      ac_rfl
    have e2 : 2 * s * (s + d) = 2 * (s * s) + 2 * (s * d) := by
      rw [Nat.mul_assoc, Nat.mul_add s s d, Nat.mul_add 2 _ _]
    have e3 : (2 * s) * s = 2 * (s * s) := by ac_rfl
    have e4 : (2 * s) * d = 2 * (s * d) := by ac_rfl
    omega
  · have h' : r ≤ s := Nat.le_of_not_ge h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h'
    have hcomm : d * r = r * d := Nat.mul_comm _ _
    have h2 : 2 * r * d = r * d + r * d := by
      rw [Nat.two_mul, Nat.add_mul]
    have e1 : (r + d) * (r + d) = r * r + (r * d + (d * r + d * d)) := by
      rw [Nat.add_mul, Nat.mul_add r r d, Nat.mul_add d r d]
      ac_rfl
    have e2 : 2 * (r + d) * r = 2 * (r * r) + 2 * (r * d) := by
      rw [Nat.mul_add 2 r d, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
      ac_rfl
    omega

theorem natNext_ge_floor (A r : Nat) (hA : 0 < A) (hr : 0 < r) :
    natFloor A ≤ natNext A r := by
  have hs2 := natFloor_sq_le A
  have hmod : A % r < r := Nat.mod_lt _ hr
  have hdiv : r * (A / r) + A % r = A := Nat.div_add_mod A r
  have ham : 2 * natFloor A * r ≤ natFloor A * natFloor A + r * r :=
    two_mul_le_add_sq _ _
  unfold natNext
  have hle : natFloor A * 2 ≤ r + A / r := by
    apply Nat.le_of_not_gt
    intro hgt
    have hlt : r + A / r < natFloor A * 2 := hgt
    have hr2 : r < natFloor A * 2 := Nat.lt_of_le_of_lt (Nat.le_add_right r (A / r)) hlt
    have hrle : r ≤ natFloor A * 2 := Nat.le_of_lt hr2
    have hq1 : A / r + 1 ≤ natFloor A * 2 - r := by omega
    have hQr : r * (A / r + 1) ≤ r * (natFloor A * 2 - r) := Nat.mul_le_mul_left r hq1
    have hA1 : A + 1 ≤ r * (A / r + 1) := by
      have e1 : r * (A / r + 1) = r * (A / r) + r := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    have h2 : r * (natFloor A * 2 - r) = r * (natFloor A * 2) - r * r := Nat.mul_sub _ _ _
    have h3 : r * (natFloor A * 2) = 2 * natFloor A * r := by ac_rfl
    have h4 : A + 1 + r * r ≤ 2 * natFloor A * r + 2 := by omega
    omega
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr hle

theorem upper_aux (r S : Nat) (h1 : S ≤ 2 * r) (h2 : r ≤ 2 * S) :
    2 * r * r + 2 * S * S ≤ 5 * S * r := by
  have ha : S + (2 * r - S) = 2 * r := Nat.add_sub_of_le h1
  have hb : r + (2 * S - r) = 2 * S := Nat.add_sub_of_le h2
  have hcomm : r * S = S * r := Nat.mul_comm _ _
  have heq : (2 * r - S) * (2 * S - r) + 2 * r * r + 2 * S * S = 5 * S * r := by
    have hsub1 : (2 * r - S) * (2 * S - r)
        = (2 * r) * (2 * S - r) - S * (2 * S - r) := Nat.sub_mul _ _ _
    have hsub2 : (2 * r) * (2 * S - r)
        = (2 * r) * (2 * S) - (2 * r) * r := Nat.mul_sub _ _ _
    have hsub3 : S * (2 * S - r) = S * (2 * S) - S * r := Nat.mul_sub _ _ _
    have h44 : (4 : Nat) = 2 * 2 := by decide
    have e44 : (2 * r) * (2 * S) = 4 * (r * S) := by
      rw [h44]
      ac_rfl
    have e2r : (2 * r) * r = 2 * (r * r) := by ac_rfl
    have e2S : S * (2 * S) = 2 * (S * S) := by ac_rfl
    have hle1 : (2 * r) * r ≤ (2 * r) * (2 * S) := Nat.mul_le_mul_left _ h2
    have hle2 : S * r ≤ S * (2 * S) := Nat.mul_le_mul_left _ h2
    have hle3 : S * (2 * S - r) ≤ (2 * r) * (2 * S - r) :=
      Nat.mul_le_mul_right _ h1
    have hcomm1 : r * S = S * r := Nat.mul_comm _ _
    have hcomm2 : (2 * S) * S = S * (2 * S) := Nat.mul_comm _ _
    have hassoc5 : (5 * S) * r = 5 * (S * r) := Nat.mul_assoc _ _ _
    have hassoc4 : 4 * (r * S) = (4 * r) * S := (Nat.mul_assoc _ _ _).symm
    omega
  have hnn : 0 ≤ (2 * r - S) * (2 * S - r) := Nat.zero_le _
  omega

theorem quad_rec (A s e R Q R' e' t : Nat)
    (hs2 : s * s ≤ A) (ht : t = A - s * s)
    (hr : R = s + e) (hq : Q = A / R) (hR' : R' = (R + Q) / 2) (he' : e' = R' - s)
    (hRs : s ≤ R) (hR's : s ≤ R') :
    2 * e' * (s + e) ≤ e * e + t := by
  have hQR : Q * R ≤ A := by
    rw [hq]
    exact Nat.div_mul_le_self A R
  have hA : s * s + t = A := by omega
  have h2R' : 2 * R' ≤ R + Q := by
    rw [hR']
    have h := Nat.div_mul_le_self (R + Q) 2
    have hc : 2 * ((R + Q) / 2) = ((R + Q) / 2) * 2 := Nat.mul_comm _ _
    omega
  have he2 : 2 * e' = 2 * R' - 2 * s := by
    rw [he', Nat.mul_sub]
  have hgoal : 2 * e' * (s + e) = (2 * e') * R := by rw [← hr]
  have he2R : (2 * e') * R = (2 * R') * R - (2 * s) * R := by
    rw [he2, Nat.sub_mul]
  have h2Rle : (2 * R') * R ≤ (R + Q) * R := Nat.mul_le_mul_right R h2R'
  have hRQ : (R + Q) * R = R * R + Q * R := Nat.add_mul _ _ _
  have hQRle : Q * R ≤ s * s + t := by omega
  have hRR : R * R = (s + e) * (s + e) := by rw [hr]
  have hexpand1 : (s + e) * (s + e) = s * (s + e) + e * (s + e) := Nat.add_mul _ _ _
  have hexpand2 : s * (s + e) = s * s + s * e := Nat.mul_add _ _ _
  have hexpand3 : e * (s + e) = e * s + e * e := Nat.mul_add _ _ _
  have hcomm : e * s = s * e := Nat.mul_comm _ _
  have hsR : s * R = s * s + s * e := by rw [hr, Nat.mul_add]
  have heR : e' * R = e' * s + e' * e := by rw [hr, Nat.mul_add]
  have h2sR : (2 * s) * R = 2 * (s * R) := Nat.mul_assoc _ _ _
  have h2R'R2 : (2 * R') * R = 2 * (R' * R) := Nat.mul_assoc _ _ _
  have hR'e : R' = s + e' := by rw [he', Nat.add_sub_of_le hR's]
  have hR'R : R' * R = s * R + e' * R := by rw [hR'e, Nat.add_mul]
  have h2mul : 2 * (e' * R) = 2 * (e' * s) + 2 * (e' * e) := by
    rw [heR, Nat.mul_add]
  have h2eR : (2 * e') * R = 2 * (e' * R) := by ac_rfl
  omega

theorem natNext_upper (A r S : Nat) (hr : 0 < r) (hS : 0 < S)
    (h1 : S ≤ 2 * r) (h2 : r ≤ 2 * S) (hQr : (A / r) * r ≤ S * S - 1)
    (hSS : 1 ≤ S * S) :
    4 * natNext A r ≤ 5 * S := by
  unfold natNext
  have h2R : 2 * ((r + A / r) / 2) ≤ r + A / r := by
    have h := Nat.div_mul_le_self (r + A / r) 2
    have hc : 2 * ((r + A / r) / 2) = ((r + A / r) / 2) * 2 := Nat.mul_comm _ _
    omega
  have h4 : 4 * ((r + A / r) / 2) ≤ 2 * (r + A / r) := by
    have h44 : (4 : Nat) = 2 * 2 := by decide
    have e : (4 : Nat) * ((r + A / r) / 2) = 2 * (2 * ((r + A / r) / 2)) := by
      rw [h44, Nat.mul_assoc]
    have hle := Nat.mul_le_mul_left 2 h2R
    omega
  have hsuff : 2 * (r + A / r) ≤ 5 * S := by
    apply Nat.le_of_not_gt
    intro hgt
    have hge : 5 * S + 1 ≤ 2 * (r + A / r) := hgt
    have hmul : (5 * S + 1) * r ≤ (2 * (r + A / r)) * r :=
      Nat.mul_le_mul_right _ hge
    have e1 : (2 * (r + A / r)) * r = 2 * r * r + 2 * ((A / r) * r) := by
      rw [Nat.mul_add 2 r (A / r), Nat.add_mul, Nat.mul_assoc 2 (A / r) r]
    have e2 : (5 * S + 1) * r = 5 * S * r + r := by
      rw [Nat.add_mul, Nat.one_mul]
    have hleQ : 2 * ((A / r) * r) ≤ 2 * (S * S - 1) :=
      Nat.mul_le_mul_left _ hQr
    have hsub : 2 * (S * S - 1) = 2 * (S * S) - 2 := by
      rw [Nat.mul_sub, Nat.mul_one]
    have hass : (2 * S) * S = 2 * (S * S) := Nat.mul_assoc _ _ _
    have hupper := upper_aux r S h1 h2
    omega
  omega

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  show (newtonSqrt 7 a).toNat * (newtonSqrt 7 a).toNat ≤ a.toNat
  unfold newtonSqrt
  by_cases h : a = 0
  · subst h
    simp
  · rw [if_neg h]
    generalize iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)) = r7
    show (min r7 (a / r7)).toNat * (min r7 (a / r7)).toNat ≤ a.toNat
    have hmin : (min r7 (a / r7)).toNat
        = Nat.min r7.toNat (a.toNat / r7.toNat) := by
      rw [toNat_min, BitVec.toNat_udiv]
    rw [hmin]
    have hle1 : Nat.min r7.toNat (a.toNat / r7.toNat) ≤ r7.toNat := Nat.min_le_left _ _
    have hle2 : Nat.min r7.toNat (a.toNat / r7.toNat) ≤ a.toNat / r7.toNat := Nat.min_le_right _ _
    have hmul := Nat.mul_le_mul hle1 hle2
    have hdivle := Nat.mul_div_le a.toNat r7.toNat
    omega
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_backed    : MintBacked sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry

end OzSqrt
