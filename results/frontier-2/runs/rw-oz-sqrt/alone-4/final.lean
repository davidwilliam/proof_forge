import OzSqrt.Spec
import OzSqrt.Lemmas

namespace OzSqrt

def sqrt : SqrtFn := newtonSqrt 7

def nstep (A R : Nat) : Nat := (R + A / R) / 2

def niter (A : Nat) : Nat → Nat → Nat
  | 0, R => R
  | k + 1, R => niter A k (nstep A R)

def natR0 (A : Nat) : Nat := 2 ^ (Nat.log2 A / 2)

theorem four_mul_le_sq_add (a b : Nat) : 4 * a * b ≤ (a + b) * (a + b) := by
  by_cases h : a ≤ b
  · obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
    have h4 : (4 : Nat) = 1 + 1 + 1 + 1 := by decide
    have e : (a + (a + d)) * (a + (a + d)) = 4 * a * (a + d) + d * d := by
      rw [h4]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      ac_rfl
    omega
  · have h' : b ≤ a := by omega
    obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
    have h4 : (4 : Nat) = 1 + 1 + 1 + 1 := by decide
    have e : ((b + d) + b) * ((b + d) + b) = 4 * (b + d) * b + d * d := by
      rw [h4]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      ac_rfl
    omega

theorem single_step_ineq (A R : Nat) :
    4 * R * R * (nstep A R * nstep A R) ≤ (R * R + A) * (R * R + A) := by
  unfold nstep
  have h2 : 2 * ((R + A / R) / 2) ≤ R + A / R := Nat.mul_div_le _ _
  have hRq : A / R * R ≤ A := Nat.div_mul_le_self _ _
  have hRq' : R * (A / R) ≤ A := by
    rw [Nat.mul_comm]
    exact hRq
  have h1 : R * (R + A / R) ≤ R * R + A := by
    have e : R * (R + A / R) = R * R + R * (A / R) := by
      simp only [Nat.mul_add]
    rw [e]
    exact Nat.add_le_add_left hRq' _
  have h2R : 2 * R * ((R + A / R) / 2) ≤ R * (R + A / R) := by
    have h := Nat.mul_le_mul (Nat.le_refl R) h2
    have e1 : R * (2 * ((R + A / R) / 2)) = 2 * R * ((R + A / R) / 2) := by
      simp only [Nat.mul_comm, Nat.mul_assoc]
      ac_rfl
    rw [e1] at h
    exact h
  have hsq : (2 * R * ((R + A / R) / 2)) * (2 * R * ((R + A / R) / 2)) ≤ (R * (R + A / R)) * (R * (R + A / R)) :=
    Nat.mul_le_mul h2R h2R
  have hsq2 : (R * (R + A / R)) * (R * (R + A / R)) ≤ (R * R + A) * (R * R + A) :=
    Nat.mul_le_mul h1 h1
  have hchain : (2 * R * ((R + A / R) / 2)) * (2 * R * ((R + A / R) / 2)) ≤ (R * R + A) * (R * R + A) :=
    Nat.le_trans hsq hsq2
  have h44 : (4 : Nat) = 2 * 2 := rfl
  have e2 : (2 * R * ((R + A / R) / 2)) * (2 * R * ((R + A / R) / 2)) = 4 * R * R * (((R + A / R) / 2) * ((R + A / R) / 2)) := by
    rw [h44]
    simp only [Nat.mul_assoc]
    ac_rfl
  rw [e2] at hchain
  exact hchain

theorem sqrt_pos_of_pos (A : Nat) (hA : 0 < A) : 0 < Nat.sqrt A := by
  by_cases h : Nat.sqrt A = 0
  · have hlt := Nat.lt_succ_sqrt A
    rw [h] at hlt
    simp at hlt
    omega
  · omega

theorem step_ge_sqrt (A R : Nat) (hA : 0 < A) (hR : 0 < R) :
    Nat.sqrt A ≤ nstep A R := by
  unfold nstep
  have hs : 0 < Nat.sqrt A := sqrt_pos_of_pos A hA
  by_cases h : Nat.sqrt A ≤ (R + A / R) / 2
  · exact h
  · have hS : R + A / R ≤ 2 * Nat.sqrt A - 1 := by
      have hlt : (R + A / R) / 2 < Nat.sqrt A := by omega
      have hle : (R + A / R) / 2 ≤ Nat.sqrt A - 1 := by omega
      have hdiv := (Nat.div_le_iff_le_mul (by decide : 0 < 2)).mp hle
      omega
    have hT : R + A / R + 1 ≤ 2 * Nat.sqrt A := by omega
    have hRq : A / R * R ≤ A := Nat.div_mul_le_self _ _
    have hRq' : R * (A / R) ≤ A := by
      rw [Nat.mul_comm]
      exact hRq
    have ham : 4 * R * (A / R + 1) ≤ (R + (A / R + 1)) * (R + (A / R + 1)) :=
      four_mul_le_sq_add R (A / R + 1)
    have hT2 : (R + (A / R + 1)) * (R + (A / R + 1)) ≤ (2 * Nat.sqrt A) * (2 * Nat.sqrt A) := by
      have hleT : R + (A / R + 1) ≤ 2 * Nat.sqrt A := by omega
      exact Nat.mul_le_mul hleT hleT
    have h4 : 4 * R * (A / R + 1) ≤ (2 * Nat.sqrt A) * (2 * Nat.sqrt A) :=
      Nat.le_trans ham hT2
    have h44 : (4 : Nat) = 2 * 2 := rfl
    have e44 : (2 * Nat.sqrt A) * (2 * Nat.sqrt A) = 4 * (Nat.sqrt A * Nat.sqrt A) := by
      rw [h44]
      simp only [Nat.mul_assoc]
      ac_rfl
    rw [e44] at h4
    have h4' : 4 * (R * (A / R + 1)) ≤ 4 * (Nat.sqrt A * Nat.sqrt A) := by
      simp only [Nat.mul_assoc] at h4 ⊢
      exact h4
    have hRq1 : R * (A / R + 1) ≤ Nat.sqrt A * Nat.sqrt A := by omega
    have hAeq : R * (A / R) + A % R = A := Nat.div_add_mod A R
    have hrem : A % R < R := Nat.mod_lt _ hR
    have hAlt : A < R * (A / R + 1) := by
      have e : R * (A / R + 1) = R * (A / R) + R := by simp only [Nat.mul_add, Nat.mul_one]
      rw [e]
      omega
    have hsqs : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A
    have hleA : R * (A / R + 1) ≤ A := Nat.le_trans hRq1 hsqs
    have hAA : A < A := Nat.lt_of_lt_of_le hAlt hleA
    have hF : False := Nat.lt_irrefl _ hAA
    exact False.elim hF

theorem natR0_sq_le (A : Nat) (hA : 0 < A) : natR0 A * natR0 A ≤ A := by
  unfold natR0
  have hlog := (Nat.log2_eq_iff (by omega : A ≠ 0)).mp rfl
  obtain ⟨h1, h2⟩ := hlog
  have hle : 2 * (Nat.log2 A / 2) ≤ Nat.log2 A := by omega
  have hpow : 2 ^ (2 * (Nat.log2 A / 2)) ≤ 2 ^ Nat.log2 A :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hle
  have e : 2 ^ (Nat.log2 A / 2) * 2 ^ (Nat.log2 A / 2) = 2 ^ (2 * (Nat.log2 A / 2)) := by
    have := Nat.pow_add 2 (Nat.log2 A / 2) (Nat.log2 A / 2)
    have h22 : (Nat.log2 A / 2) + (Nat.log2 A / 2) = 2 * (Nat.log2 A / 2) := by omega
    rw [h22] at this
    rw [← this]
  rw [e]
  exact Nat.le_trans hpow h1

theorem natR0_le_sqrt (A : Nat) (hA : 0 < A) : natR0 A ≤ Nat.sqrt A := by
  by_cases h : natR0 A ≤ Nat.sqrt A
  · exact h
  · have hlt : Nat.sqrt A < natR0 A := by omega
    have h1 := natR0_sq_le A hA
    have h2 := Nat.lt_succ_sqrt A
    have h3 : (Nat.sqrt A + 1) * (Nat.sqrt A + 1) ≤ natR0 A * natR0 A :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2' : A < (Nat.sqrt A + 1) * (Nat.sqrt A + 1) := by
      simpa using h2
    omega

theorem f_decr (R1 R2 A : Nat) (hR1 : 0 < R1) (hle : R1 ≤ R2) (h : R1 * R2 ≤ A) :
    R2 + A / R2 ≤ R1 + A / R1 := by
  have hR2 : 0 < R2 := by omega
  have hk : (A - R1 * R2) + R1 * R2 = A := Nat.sub_add_cancel h
  have hk2 : (A - R1 * R2) + R2 * R1 = A := by
    rw [← Nat.mul_comm R1 R2]
    exact hk
  have h1 : ((A - R1 * R2) + R1 * R2) / R1 = R2 + (A - R1 * R2) / R1 := by
    rw [Nat.add_comm (A - R1 * R2) (R1 * R2)]
    exact Nat.mul_add_div hR1 _ _
  have hq1 : A / R1 = R2 + (A - R1 * R2) / R1 := by
    rw [hk] at h1
    exact h1
  have h2 : ((A - R1 * R2) + R2 * R1) / R2 = R1 + (A - R1 * R2) / R2 := by
    rw [Nat.add_comm (A - R1 * R2) (R2 * R1)]
    exact Nat.mul_add_div hR2 _ _
  have hq2 : A / R2 = R1 + (A - R1 * R2) / R2 := by
    rw [hk2] at h2
    exact h2
  have hdiv : (A - R1 * R2) / R2 ≤ (A - R1 * R2) / R1 :=
    Nat.div_le_div_left hle hR1
  have e1 : R1 + A / R1 = (R1 + R2) + (A - R1 * R2) / R1 := by
    rw [hq1]
    rw [← Nat.add_assoc]
  have e2 : R2 + A / R2 = (R1 + R2) + (A - R1 * R2) / R2 := by
    rw [hq2]
    rw [← Nat.add_assoc, Nat.add_comm R2 R1]
  rw [e1, e2]
  exact Nat.add_le_add_left hdiv _

theorem sqrt_lt_pow (A : Nat) (hA : A < 2 ^ 256) : Nat.sqrt A < 2 ^ 128 := by
  by_cases h : Nat.sqrt A < 2 ^ 128
  · exact h
  · have hge : 2 ^ 128 ≤ Nat.sqrt A := by omega
    have h1 : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A
    have h2 : (2 ^ 128) * (2 ^ 128) ≤ Nat.sqrt A * Nat.sqrt A :=
      Nat.mul_le_mul hge hge
    have hpow : 2 ^ (128 + 128) = 2 ^ 128 * 2 ^ 128 := Nat.pow_add 2 128 128
    have h128 : 128 + 128 = 256 := by decide
    rw [h128] at hpow
    omega

theorem log2_lt_256 {A : Nat} (hA0 : 0 < A) (hA : A < 2 ^ 256) : Nat.log2 A < 256 := by
  have hne : A ≠ 0 := by omega
  exact (Nat.log2_lt hne).mpr hA

theorem natR0_lt_129 {A : Nat} (hA0 : 0 < A) (hA : A < 2 ^ 256) : natR0 A < 2 ^ 129 := by
  unfold natR0
  have hL : Nat.log2 A < 256 := log2_lt_256 hA0 hA
  have hle : Nat.log2 A / 2 ≤ 127 := by omega
  have hpow_le : 2 ^ (Nat.log2 A / 2) ≤ 2 ^ 127 := Nat.pow_le_pow_right (by decide : 0 < 2) hle
  have hlt : (2 : Nat) ^ 127 < 2 ^ 129 := Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 127 < 129)
  exact Nat.lt_of_le_of_lt hpow_le hlt

theorem A_div_R0_lt {A : Nat} (hA0 : 0 < A) (hA : A < 2 ^ 256) : A / natR0 A < 2 ^ 129 := by
  unfold natR0
  have hR0pos : 0 < 2 ^ (Nat.log2 A / 2) := Nat.two_pow_pos _
  have hL : Nat.log2 A < 256 := log2_lt_256 hA0 hA
  have hne : A ≠ 0 := by omega
  have hlog := (Nat.log2_eq_iff hne).mp rfl
  obtain ⟨h1, h2⟩ := hlog
  have hle : Nat.log2 A + 1 ≤ 129 + Nat.log2 A / 2 := by omega
  have hpow_le : 2 ^ (Nat.log2 A + 1) ≤ 2 ^ (129 + Nat.log2 A / 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hle
  have hpow_eq : 2 ^ (129 + Nat.log2 A / 2) = 2 ^ 129 * 2 ^ (Nat.log2 A / 2) := by
    rw [Nat.pow_add]
  have hlt : A < 2 ^ 129 * 2 ^ (Nat.log2 A / 2) := by
    rw [← hpow_eq]
    exact Nat.lt_of_lt_of_le h2 hpow_le
  exact (Nat.div_lt_iff_lt_mul hR0pos).mpr hlt

theorem R0_lt_two_mul_sqrt {A : Nat} (hA0 : 0 < A) (hA : A < 2 ^ 256) :
    Nat.sqrt A < 2 * natR0 A := by
  by_cases h : Nat.sqrt A < 2 * natR0 A
  · exact h
  · have hge : 2 * natR0 A ≤ Nat.sqrt A := by omega
    have h1 : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A
    have hne : A ≠ 0 := by omega
    have hlog := (Nat.log2_eq_iff hne).mp rfl
    obtain ⟨hl1, hl2⟩ := hlog
    have hexp : Nat.log2 A + 1 ≤ Nat.log2 A / 2 * 2 + 2 := by omega
    have hpow_le : 2 ^ (Nat.log2 A + 1) ≤ 2 ^ (Nat.log2 A / 2 * 2 + 2) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hexp
    have h2R0 : 2 * natR0 A = 2 ^ (Nat.log2 A / 2 + 1) := by
      unfold natR0
      have h21 : (2 : Nat) = 2 ^ 1 := by decide
      rw [h21, ← Nat.pow_add]
      have : 1 + Nat.log2 A / 2 = Nat.log2 A / 2 + 1 := by omega
      rw [this]
    have hsq : (2 * natR0 A) * (2 * natR0 A) = 2 ^ (Nat.log2 A / 2 * 2 + 2) := by
      rw [h2R0]
      have hpa := Nat.pow_add 2 (Nat.log2 A / 2 + 1) (Nat.log2 A / 2 + 1)
      have he : Nat.log2 A / 2 + 1 + (Nat.log2 A / 2 + 1) = Nat.log2 A / 2 * 2 + 2 := by omega
      rw [he] at hpa
      exact hpa.symm
    have hle : 2 ^ (Nat.log2 A + 1) ≤ (2 * natR0 A) * (2 * natR0 A) := by
      rw [hsq]
      exact hpow_le
    have hgt : A < (2 * natR0 A) * (2 * natR0 A) :=
      Nat.lt_of_lt_of_le hl2 hle
    have hle2 : (2 * natR0 A) * (2 * natR0 A) ≤ Nat.sqrt A * Nat.sqrt A :=
      Nat.mul_le_mul hge hge
    have hlt : (2 * natR0 A) * (2 * natR0 A) < (2 * natR0 A) * (2 * natR0 A) :=
      Nat.lt_of_le_of_lt hle2 (Nat.lt_of_le_of_lt h1 hgt)
    have hF : False := Nat.lt_irrefl _ hlt
    exact False.elim hF

theorem niter_ge_sqrt_aux (A X k : Nat) (hA0 : 0 < A) (hX : Nat.sqrt A ≤ X) :
    Nat.sqrt A ≤ niter A k X := by
  induction k generalizing X with
  | zero => exact hX
  | succ k ih =>
    unfold niter
    have hXpos : 0 < X := by
      have hs : 0 < Nat.sqrt A := sqrt_pos_of_pos A hA0
      omega
    have h1 : Nat.sqrt A ≤ nstep A X := step_ge_sqrt A X hA0 hXpos
    exact ih (nstep A X) h1

theorem niter_ge_sqrt {A : Nat} (hA0 : 0 < A) (k : Nat) (hk : 1 ≤ k) :
    Nat.sqrt A ≤ niter A k (natR0 A) := by
  have hR0pos : 0 < natR0 A := Nat.two_pow_pos _
  have hR1 : Nat.sqrt A ≤ nstep A (natR0 A) := step_ge_sqrt A (natR0 A) hA0 hR0pos
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold niter
  exact niter_ge_sqrt_aux A (nstep A (natR0 A)) k' hA0 hR1

theorem niter_R0_lt {A : Nat} (hA0 : 0 < A) (hA : A < 2 ^ 256) :
    niter A 0 (natR0 A) < 2 ^ 129 := by
  unfold niter
  exact natR0_lt_129 hA0 hA

theorem niter_R1_lt {A : Nat} (hA0 : 0 < A) (hA : A < 2 ^ 256) :
    niter A 1 (natR0 A) < 2 ^ 129 := by
  have h1 := natR0_lt_129 hA0 hA
  have h2 := A_div_R0_lt hA0 hA
  have e : niter A 1 (natR0 A) = (natR0 A + A / natR0 A) / 2 := rfl
  rw [e]
  omega

theorem nstep_lt_129 {A R : Nat} (hA0 : 0 < A) (hA : A < 2 ^ 256)
    (hRge : Nat.sqrt A ≤ R) (hRlt : R < 2 ^ 129) : nstep A R < 2 ^ 129 := by
  unfold nstep
  have hs : 0 < Nat.sqrt A := sqrt_pos_of_pos A hA0
  have hRpos : 0 < R := by omega
  have hslt : Nat.sqrt A < 2 ^ 128 := sqrt_lt_pow A hA
  have hAle : A ≤ Nat.sqrt A * Nat.sqrt A + 2 * Nat.sqrt A := by
    have hlt := Nat.lt_succ_sqrt A
    have e : (Nat.sqrt A + 1) * (Nat.sqrt A + 1) = Nat.sqrt A * Nat.sqrt A + 2 * Nat.sqrt A + 1 := by
      have h4 : (2 : Nat) = 1 + 1 := by decide
      rw [h4]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      ac_rfl
    rw [e] at hlt
    omega
  have hAs : A ≤ Nat.sqrt A * (Nat.sqrt A + 2) := by
    have e : Nat.sqrt A * (Nat.sqrt A + 2) = Nat.sqrt A * Nat.sqrt A + 2 * Nat.sqrt A := by
      have h4 : (2 : Nat) = 1 + 1 := by decide
      rw [h4]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      ac_rfl
    rw [e]
    exact hAle
  have hAR : A / R ≤ Nat.sqrt A + 2 := by
    have h1 : A ≤ Nat.sqrt A * (Nat.sqrt A + 2) := hAs
    have h2 : A / R ≤ Nat.sqrt A * (Nat.sqrt A + 2) / R := Nat.div_le_div_right h1
    have h3 : Nat.sqrt A * (Nat.sqrt A + 2) / R ≤ Nat.sqrt A + 2 := by
      have hle : Nat.sqrt A * (Nat.sqrt A + 2) / R ≤ Nat.sqrt A * (Nat.sqrt A + 2) / Nat.sqrt A :=
        Nat.div_le_div_left hRge hs
      have heq : Nat.sqrt A * (Nat.sqrt A + 2) / Nat.sqrt A = Nat.sqrt A + 2 := by
        rw [Nat.mul_comm]
        exact Nat.mul_div_cancel _ hs
      rw [heq] at hle
      exact hle
    exact Nat.le_trans h2 h3
  have hs2 : Nat.sqrt A + 2 < 2 ^ 129 := by
    have h1lt : (1 : Nat) < 2 ^ 128 := by decide
    omega
  have hARlt : A / R < 2 ^ 129 := Nat.lt_of_le_of_lt hAR hs2
  omega

theorem niter_lt_129_general (A R k : Nat) (hA0 : 0 < A) (hA : A < 2 ^ 256)
    (hRge : Nat.sqrt A ≤ R) (hRlt : R < 2 ^ 129) : niter A k R < 2 ^ 129 := by
  induction k generalizing R with
  | zero => exact hRlt
  | succ k ih =>
    unfold niter
    have hs : 0 < Nat.sqrt A := sqrt_pos_of_pos A hA0
    have hRpos : 0 < R := by omega
    have h1 : Nat.sqrt A ≤ nstep A R := step_ge_sqrt A R hA0 hRpos
    have h2 : nstep A R < 2 ^ 129 := nstep_lt_129 hA0 hA hRge hRlt
    exact ih (nstep A R) h1 h2

theorem r0_toNat {a : U256} (hA0 : 0 < a.toNat) (hA : a.toNat < 2 ^ 256) :
    ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (Nat.log2 a.toNat / 2) := by
  have h1 : ((1 : U256) <<< (log2 a >>> 1)) = (1 : U256) <<< ((log2 a >>> 1).toNat) := by
    rw [BitVec.shiftLeft_eq']
  rw [h1]
  rw [BitVec.toNat_shiftLeft]
  have h1nat : (1 : U256).toNat = 1 := by decide
  rw [h1nat]
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  have h3 : ((log2 a >>> 1).toNat) = (log2 a).toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rw [h3]
  rw [toNat_log2]
  have h4 : 2 ^ (Nat.log2 a.toNat / 2) % 2 ^ 256 = 2 ^ (Nat.log2 a.toNat / 2) := by
    apply Nat.mod_eq_of_lt
    have hL : Nat.log2 a.toNat < 256 := by
      have hne : a.toNat ≠ 0 := by omega
      exact (Nat.log2_lt hne).mpr hA
    have hle : Nat.log2 a.toNat / 2 < 256 := by omega
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hle
  exact h4

theorem step_toNat {a : U256} {Rbv : U256} (h : Rbv.toNat + a.toNat / Rbv.toNat < 2 ^ 256) :
    (newtonStep a Rbv).toNat = nstep a.toNat Rbv.toNat := by
  unfold newtonStep nstep
  have h1 : (Rbv + a / Rbv).toNat = Rbv.toNat + a.toNat / Rbv.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_udiv]
    exact Nat.mod_eq_of_lt h
  have h2 : ((Rbv + a / Rbv) >>> (1 : Nat)).toNat = ((Rbv + a / Rbv).toNat) >>> 1 := by
    rw [BitVec.toNat_ushiftRight]
  rw [h2, h1, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem iter_toNat_general (a : U256) (Rbv : U256) (R k : Nat) (hA0 : 0 < a.toNat) (hA : a.toNat < 2 ^ 256)
    (hcorr : Rbv.toNat = R) (hRge : Nat.sqrt a.toNat ≤ R) (hRlt : R < 2 ^ 129) :
    (iterate (newtonStep a) k Rbv).toNat = niter a.toNat k R := by
  induction k generalizing Rbv R with
  | zero => exact hcorr
  | succ k ih =>
    unfold iterate niter
    have hs : 0 < Nat.sqrt a.toNat := sqrt_pos_of_pos _ hA0
    have hRpos : 0 < R := by omega
    have hslt : Nat.sqrt a.toNat < 2 ^ 128 := sqrt_lt_pow _ hA
    have hAR : a.toNat / R ≤ Nat.sqrt a.toNat + 2 := by
      have hAle : a.toNat ≤ Nat.sqrt a.toNat * Nat.sqrt a.toNat + 2 * Nat.sqrt a.toNat := by
        have hlt := Nat.lt_succ_sqrt a.toNat
        have e : (Nat.sqrt a.toNat + 1) * (Nat.sqrt a.toNat + 1) = Nat.sqrt a.toNat * Nat.sqrt a.toNat + 2 * Nat.sqrt a.toNat + 1 := by
          have h4 : (2 : Nat) = 1 + 1 := by decide
          rw [h4]
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
          ac_rfl
        rw [e] at hlt
        omega
      have hAs : a.toNat ≤ Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 2) := by
        have e : Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 2) = Nat.sqrt a.toNat * Nat.sqrt a.toNat + 2 * Nat.sqrt a.toNat := by
          have h4 : (2 : Nat) = 1 + 1 := by decide
          rw [h4]
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
          ac_rfl
        rw [e]
        exact hAle
      have h1 : a.toNat ≤ Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 2) := hAs
      have h2 : a.toNat / R ≤ Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 2) / R := Nat.div_le_div_right h1
      have h3 : Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 2) / R ≤ Nat.sqrt a.toNat + 2 := by
        have hle : Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 2) / R ≤ Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 2) / Nat.sqrt a.toNat :=
          Nat.div_le_div_left hRge hs
        have heq : Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 2) / Nat.sqrt a.toNat = Nat.sqrt a.toNat + 2 := by
          rw [Nat.mul_comm]
          exact Nat.mul_div_cancel _ hs
        rw [heq] at hle
        exact hle
      exact Nat.le_trans h2 h3
    have hs2 : Nat.sqrt a.toNat + 2 < 2 ^ 129 := by
      have h1lt : (1 : Nat) < 2 ^ 128 := by decide
      omega
    have hARlt : a.toNat / R < 2 ^ 129 := Nat.lt_of_le_of_lt hAR hs2
    have hsum : R + a.toNat / R < 2 ^ 256 := by
      have h130 : (2 : Nat) ^ 129 + 2 ^ 129 = 2 ^ 130 := by decide
      have hle130 : R + a.toNat / R < 2 ^ 130 := by omega
      have hle256 : (2 : Nat) ^ 130 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 130 ≤ 256)
      exact Nat.lt_of_lt_of_le hle130 hle256
    have hsum' : Rbv.toNat + a.toNat / Rbv.toNat < 2 ^ 256 := by
      rw [hcorr]
      exact hsum
    have hstep0 : (newtonStep a Rbv).toNat = nstep a.toNat Rbv.toNat := step_toNat hsum'
    have hstep : (newtonStep a Rbv).toNat = nstep a.toNat R := by
      rw [hcorr] at hstep0
      exact hstep0
    have h1 : Nat.sqrt a.toNat ≤ nstep a.toNat R := step_ge_sqrt _ _ hA0 hRpos
    have h2 : nstep a.toNat R < 2 ^ 129 := nstep_lt_129 hA0 hA hRge hRlt
    exact ih (newtonStep a Rbv) (nstep a.toNat R) hstep h1 h2

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  unfold sqrt newtonSqrt
  by_cases h : a = 0
  · rw [if_pos h]
    simp
  · rw [if_neg h]
    rw [toNat_min, BitVec.toNat_udiv]
    by_cases hR : (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat = 0
    · have hm : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) = 0 := by
        rw [hR]
        simp
      rw [hm]
      simp
    · have hle1 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat :=
        Nat.min_le_left _ _
      have hle2 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat :=
        Nat.min_le_right _ _
      have hmul : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) * Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat * (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) :=
        Nat.mul_le_mul hle1 hle2
      have hdiv : (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat * (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) = (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) * (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat := by
        rw [Nat.mul_comm]
      have hle3 : a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat * (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat ≤ a.toNat :=
        Nat.div_mul_le_self _ _
      omega

theorem req_newton_budget : NewtonBudget sqrt := ⟨7, by decide, fun a => rfl⟩
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight : SqrtUpTight sqrt := sorry
theorem req_mint_backed : MintBacked sqrt := sorry
theorem req_mint_full : MintFull sqrt := sorry
theorem req_mint_live : MintLive sqrt := sorry

end OzSqrt
