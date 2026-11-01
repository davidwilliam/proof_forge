import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.Sqrt
import ProofForgeFin.Word
import ProofForgeFin.Evm.Bits

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

-- The power-of-two estimate is below 256, so shifts are exact.
theorem log2_lt_256 (a : U256) : (log2 a).toNat < 256 := by
  rw [toNat_log2]
  by_cases h : a.toNat = 0
  · rw [h]
    simp
  · have hlt : a.toNat < 2 ^ 256 := a.isLt
    have h2 := (Nat.log2_lt h).mpr hlt
    omega

-- Initial estimate value.
theorem init_toNat (a : U256) :
    ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (Nat.log2 a.toNat / 2) := by
  have hlog : (log2 a).toNat = Nat.log2 a.toNat := toNat_log2 a
  have h1 : (log2 a >>> 1).toNat = (log2 a).toNat / 2 ^ 1 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h1b : (log2 a).toNat / 2 ^ 1 = (log2 a).toNat / 2 := by
    simp only [Nat.pow_one]
  have hlog256 : (log2 a).toNat < 256 := log2_lt_256 a
  have hlt : (log2 a >>> 1).toNat < 256 := by omega
  have hshift : ((1 : U256) <<< ((log2 a >>> 1) : U256)).toNat
      = 1 * 2 ^ ((log2 a >>> 1).toNat) := by
    apply ProofForgeFin.toNat_shiftLeft_of_lt
    have h2 : (log2 a >>> 1).toNat < 256 := hlt
    have h3 : 1 * 2 ^ ((log2 a >>> 1).toNat) < 2 ^ 256 := by
      have hp : 2 ^ ((log2 a >>> 1).toNat) < 2 ^ 256 :=
        Nat.pow_lt_pow_right (by decide) h2
      omega
    simpa using h3
  rw [hshift, h1, h1b, hlog]
  simp

-- The estimate is within a factor of two of the root.
theorem y0_le_sqrt (a : U256) (h : 0 < a.toNat) :
    2 ^ (Nat.log2 a.toNat / 2) ≤ Nat.sqrt a.toNat := by
  apply ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le
  have hne : a.toNat ≠ 0 := Nat.pos_iff_ne_zero.mp h
  have hspec := ProofForgeFin.Evm.log2_spec hne
  have hle : 2 * (Nat.log2 a.toNat / 2) ≤ Nat.log2 a.toNat := Nat.mul_div_le _ 2
  have hpow : 2 ^ (2 * (Nat.log2 a.toNat / 2)) ≤ 2 ^ Nat.log2 a.toNat :=
    Nat.pow_le_pow_right (by decide) hle
  have e : (2 ^ (Nat.log2 a.toNat / 2)) * (2 ^ (Nat.log2 a.toNat / 2))
      = 2 ^ (2 * (Nat.log2 a.toNat / 2)) := by
    have hkk : Nat.log2 a.toNat / 2 + Nat.log2 a.toNat / 2
        = 2 * (Nat.log2 a.toNat / 2) := by omega
    rw [← hkk, Nat.pow_add]
  rw [e]
  exact Nat.le_trans hpow hspec.1

theorem sqrt_lt_two_y0 (a : U256) (h : 0 < a.toNat) :
    Nat.sqrt a.toNat < 2 * 2 ^ (Nat.log2 a.toNat / 2) := by
  have hne : a.toNat ≠ 0 := Nat.pos_iff_ne_zero.mp h
  have hspec := ProofForgeFin.Evm.log2_spec hne
  have hle : 2 * (Nat.log2 a.toNat / 2) ≤ Nat.log2 a.toNat := Nat.mul_div_le _ 2
  have hlt : Nat.log2 a.toNat < 2 * (Nat.log2 a.toNat / 2) + 2 := by omega
  have h2 : a.toNat < 2 ^ (2 * (Nat.log2 a.toNat / 2) + 2) := by
    calc a.toNat < 2 ^ (Nat.log2 a.toNat + 1) := hspec.2
      _ ≤ 2 ^ (2 * (Nat.log2 a.toNat / 2) + 2) := by
          apply Nat.pow_le_pow_right (by decide)
          omega
  have h3 : a.toNat < 2 ^ (2 * (Nat.log2 a.toNat / 2 + 1)) := by
    have heq : 2 * (Nat.log2 a.toNat / 2 + 1) = 2 * (Nat.log2 a.toNat / 2) + 2 := by
      omega
    rw [heq]
    exact h2
  have h4 := ProofForgeFin.Sqrt.sqrt_lt_two_pow (a := a.toNat)
    (k := Nat.log2 a.toNat / 2 + 1) h3
  have e : 2 ^ (Nat.log2 a.toNat / 2 + 1) = 2 * 2 ^ (Nat.log2 a.toNat / 2) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  omega

-- First Newton error: at most a quarter of the root plus two.
theorem newton1_bound (A y0 : Nat) (hle : y0 ≤ Nat.sqrt A)
    (hlt : Nat.sqrt A < 2 * y0) (hpos : 0 < y0) :
    ProofForgeFin.Sqrt.newton A y0 - Nat.sqrt A ≤ Nat.sqrt A / 4 + 2 := by
  have hn : Nat.sqrt A ≤ ProofForgeFin.Sqrt.newton A y0 :=
    ProofForgeFin.Sqrt.sqrt_le_newton hpos
  have herr := ProofForgeFin.Sqrt.newton_err_below (a := A) (x := y0) hpos hle
  generalize Nat.sqrt A = s at *
  generalize ProofForgeFin.Sqrt.newton A y0 = n at *
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_sub_cancel_left] at herr ⊢
  have hdle : d ≤ y0 := by omega
  have h1 : d * d ≤ d * y0 := Nat.mul_le_mul (Nat.le_refl d) hdle
  have hle2 := Nat.add_le_add_right h1 (2 * y0 + 2 * d)
  have h2 : 2 * y0 * e ≤ d * y0 + 2 * y0 + 2 * d := by omega
  have h3a : d * y0 + 2 * y0 + 2 * d ≤ (d + 4) * y0 := by
    have hrr : (d + 4) * y0 = d * y0 + 4 * y0 := Nat.add_mul d 4 y0
    omega
  have h3b : (2 * e) * y0 = 2 * y0 * e := by ac_rfl
  have h3 : (2 * e) * y0 ≤ (d + 4) * y0 := by omega
  have h4 : 2 * e ≤ d + 4 := Nat.le_of_mul_le_mul_right h3 hpos
  omega

-- Doubling steps with concrete bounds (no search tactics, only ac_rfl,
-- explicit distributivity and omega over monomial atoms).
theorem step_4_32 (s e e' : Nat) (hs : 4 ≤ s) (he : e * 4 ≤ s + 8)
    (herr : 2 * (s + e) * e' ≤ e * e + 2 * s) :
    e' * 32 ≤ s + 64 := by
  have he2 : (e * 4) * (e * 4) ≤ (s + 8) * (s + 8) := Nat.mul_le_mul he he
  have hrr : (e * 4) * (e * 4) = e * e * 16 := by
    have h : (e * 4) * (e * 4) = (e * e) * (4 * 4) := by ac_rfl
    have h44 : (4 : Nat) * 4 = 16 := rfl
    omega
  have e_am1 : (s + 8) * (s + 8) = s * (s + 8) + 8 * (s + 8) :=
    Nat.add_mul s 8 (s + 8)
  have e_am2 : s * (s + 8) = s * s + s * 8 := Nat.mul_add s s 8
  have e_am3 : 8 * (s + 8) = 8 * s + 8 * 8 := Nat.mul_add 8 s 8
  have h88 : (8 : Nat) * 8 = 64 := rfl
  have c1 : s * 8 = 8 * s := Nat.mul_comm s 8
  have h1 : e * e * 16 ≤ s * s + s * 8 + (8 * s + 64) := by omega
  have ha : (e' * 32) * (s + e) = 16 * (2 * (s + e) * e') := by
    have h32 : (32 : Nat) = 16 * 2 := rfl
    rw [h32]; ac_rfl
  have hb : 16 * (2 * (s + e) * e') ≤ 16 * (e * e + 2 * s) :=
    Nat.mul_le_mul (Nat.le_refl 16) herr
  have hc1 : 16 * (e * e + 2 * s) = 16 * (e * e) + 16 * (2 * s) :=
    Nat.mul_add 16 (e * e) (2 * s)
  have hc2 : (16 : Nat) * (e * e) = e * e * 16 := by ac_rfl
  have hc3 : (16 : Nat) * (2 * s) = 32 * s := by ac_rfl
  have hd : 16 * (e * e + 2 * s) ≤ s * s + s * 8 + (8 * s + 64) + 32 * s := by
    omega
  have hge : (s + 64) * s ≤ (s + 64) * (s + e) :=
    Nat.mul_le_mul (Nat.le_refl (s + 64)) (Nat.le_add_right s e)
  have hex : (s + 64) * s = s * s + 64 * s := Nat.add_mul s 64 s
  have he2' : s * s + s * 8 + (8 * s + 64) + 32 * s ≤ (s + 64) * (s + e) := by
    omega
  have hgoal : (e' * 32) * (s + e) ≤ (s + 64) * (s + e) := by omega
  have hpos : 0 < s + e := by omega
  exact Nat.le_of_mul_le_mul_right hgoal hpos

theorem step_32_2048 (s e e' : Nat) (hs : 4 ≤ s) (he : e * 32 ≤ s + 64)
    (herr : 2 * (s + e) * e' ≤ e * e + 2 * s) :
    e' * 2048 ≤ s + 4096 := by
  have he2 : (e * 32) * (e * 32) ≤ (s + 64) * (s + 64) := Nat.mul_le_mul he he
  have hrr : (e * 32) * (e * 32) = e * e * 1024 := by
    have h : (e * 32) * (e * 32) = (e * e) * (32 * 32) := by ac_rfl
    have h32 : (32 : Nat) * 32 = 1024 := rfl
    omega
  have e_am1 : (s + 64) * (s + 64) = s * (s + 64) + 64 * (s + 64) :=
    Nat.add_mul s 64 (s + 64)
  have e_am2 : s * (s + 64) = s * s + s * 64 := Nat.mul_add s s 64
  have e_am3 : 64 * (s + 64) = 64 * s + 64 * 64 := Nat.mul_add 64 s 64
  have h64 : (64 : Nat) * 64 = 4096 := rfl
  have c1 : s * 64 = 64 * s := Nat.mul_comm s 64
  have h1 : e * e * 1024 ≤ s * s + s * 64 + (64 * s + 4096) := by omega
  have ha : (e' * 2048) * (s + e) = 1024 * (2 * (s + e) * e') := by
    have h2048 : (2048 : Nat) = 1024 * 2 := rfl
    rw [h2048]; ac_rfl
  have hb : 1024 * (2 * (s + e) * e') ≤ 1024 * (e * e + 2 * s) :=
    Nat.mul_le_mul (Nat.le_refl 1024) herr
  have hc1 : 1024 * (e * e + 2 * s) = 1024 * (e * e) + 1024 * (2 * s) :=
    Nat.mul_add 1024 (e * e) (2 * s)
  have hc2 : (1024 : Nat) * (e * e) = e * e * 1024 := by ac_rfl
  have hc3 : (1024 : Nat) * (2 * s) = 2048 * s := by ac_rfl
  have hd : 1024 * (e * e + 2 * s)
      ≤ s * s + s * 64 + (64 * s + 4096) + 2048 * s := by omega
  have hge : (s + 4096) * s ≤ (s + 4096) * (s + e) :=
    Nat.mul_le_mul (Nat.le_refl (s + 4096)) (Nat.le_add_right s e)
  have hex : (s + 4096) * s = s * s + 4096 * s := Nat.add_mul s 4096 s
  have he2' : s * s + s * 64 + (64 * s + 4096) + 2048 * s
      ≤ (s + 4096) * (s + e) := by omega
  have hgoal : (e' * 2048) * (s + e) ≤ (s + 4096) * (s + e) := by omega
  have hpos : 0 < s + e := by omega
  exact Nat.le_of_mul_le_mul_right hgoal hpos

theorem step_2048_8388608 (s e e' : Nat) (hs : 4 ≤ s) (he : e * 2048 ≤ s + 4096)
    (herr : 2 * (s + e) * e' ≤ e * e + 2 * s) :
    e' * 8388608 ≤ s + 16777216 := by
  have he2 : (e * 2048) * (e * 2048) ≤ (s + 4096) * (s + 4096) :=
    Nat.mul_le_mul he he
  have hrr : (e * 2048) * (e * 2048) = e * e * 4194304 := by
    have h : (e * 2048) * (e * 2048) = (e * e) * (2048 * 2048) := by ac_rfl
    have h2048 : (2048 : Nat) * 2048 = 4194304 := rfl
    rw [h, h2048]
  have e_am1 : (s + 4096) * (s + 4096) = s * (s + 4096) + 4096 * (s + 4096) :=
    Nat.add_mul s 4096 (s + 4096)
  have e_am2 : s * (s + 4096) = s * s + s * 4096 := Nat.mul_add s s 4096
  have e_am3 : 4096 * (s + 4096) = 4096 * s + 4096 * 4096 :=
    Nat.mul_add 4096 s 4096
  have h4096 : (4096 : Nat) * 4096 = 16777216 := rfl
  have hexp : (s + 4096) * (s + 4096)
      = s * s + s * 4096 + (4096 * s + 16777216) := by
    rw [e_am1, e_am2, e_am3, h4096]
  have h1 : e * e * 4194304 ≤ s * s + s * 4096 + (4096 * s + 16777216) := by
    rw [hrr, hexp] at he2
    exact he2
  have ha : (e' * 8388608) * (s + e) = 4194304 * (2 * (s + e) * e') := by
    have h8388608 : (8388608 : Nat) = 4194304 * 2 := rfl
    rw [h8388608]
    rw [Nat.mul_assoc e' (4194304 * 2) (s + e)]
    rw [Nat.mul_assoc 4194304 2 (s + e)]
    rw [Nat.mul_left_comm e' 4194304 (2 * (s + e))]
    rw [Nat.mul_comm e' (2 * (s + e))]
  have hb : 4194304 * (2 * (s + e) * e') ≤ 4194304 * (e * e + 2 * s) :=
    Nat.mul_le_mul (Nat.le_refl 4194304) herr
  have hc1 : 4194304 * (e * e + 2 * s)
      = 4194304 * (e * e) + 4194304 * (2 * s) :=
    Nat.mul_add 4194304 (e * e) (2 * s)
  have hc2 : (4194304 : Nat) * (e * e) = e * e * 4194304 :=
    Nat.mul_comm _ _
  have hc3 : (4194304 : Nat) * (2 * s) = 8388608 * s := by
    rw [← Nat.mul_assoc]
  have hd : 4194304 * (2 * (s + e) * e')
      ≤ s * s + s * 4096 + (4096 * s + 16777216) + 8388608 * s := by
    have hstep : 4194304 * (2 * (s + e) * e')
        ≤ 4194304 * (e * e + 2 * s) := hb
    rw [hc1, hc2, hc3] at hstep
    exact Nat.le_trans hstep (Nat.add_le_add_right h1 (8388608 * s))
  have hge : (s + 16777216) * s ≤ (s + 16777216) * (s + e) :=
    Nat.mul_le_mul (Nat.le_refl (s + 16777216)) (Nat.le_add_right s e)
  have hex : (s + 16777216) * s = s * s + 16777216 * s :=
    Nat.add_mul s 16777216 s
  have hle1 : s * 4096 + 4096 * s + 8388608 * s + 16777216 ≤ 16777216 * s := by
    have c0 : s * 4096 = 4096 * s := Nat.mul_comm s 4096
    rw [c0]
    have g1 : 4096 * s + 4096 * s + 8388608 * s + 16777216
        = 8396800 * s + 16777216 := by
      have e1 : (4096 + 4096 + 8388608) * s
          = 4096 * s + 4096 * s + 8388608 * s := by
        rw [Nat.add_mul, Nat.add_mul]
      have hsum : (4096 + 4096 + 8388608 : Nat) = 8396800 := rfl
      rw [← e1, hsum]
    rw [g1]
    have k1 : (16777216 : Nat) ≤ 8380416 * s := by
      have m1 : (8380416 : Nat) * 4 ≤ 8380416 * s :=
        Nat.mul_le_mul (Nat.le_refl 8380416) hs
      have m2 : (8380416 : Nat) * 4 = 33521664 := rfl
      rw [m2] at m1
      have m3 : (16777216 : Nat) ≤ 33521664 := by decide
      exact Nat.le_trans m3 m1
    have f1 : 8396800 * s + 16777216 ≤ 8396800 * s + 8380416 * s :=
      Nat.add_le_add_left k1 _
    have f2 : 8396800 * s + 8380416 * s = 16777216 * s := by
      have h : (8396800 + 8380416 : Nat) = 16777216 := rfl
      have e1 : 8396800 * s + 8380416 * s = (8396800 + 8380416) * s := by
        rw [Nat.add_mul]
      rw [e1, h]
    have f2le : 8396800 * s + 8380416 * s ≤ 16777216 * s := Nat.le_of_eq f2
    exact Nat.le_trans f1 f2le
  have he2' : s * s + s * 4096 + (4096 * s + 16777216) + 8388608 * s
      ≤ (s + 16777216) * (s + e) := by
    have r1 : (s + 16777216) * (s + e)
        = (s + 16777216) * s + (s + 16777216) * e :=
      Nat.mul_add (s + 16777216) s e
    have r2 : (s + 16777216) * s = s * s + 16777216 * s := hex
    have r3 : (s + 16777216) * e = s * e + 16777216 * e :=
      Nat.add_mul s 16777216 e
    have base : s * s + s * 4096 + (4096 * s + 16777216) + 8388608 * s
        ≤ s * s + 16777216 * s := by
      have hshape : s * s + s * 4096 + (4096 * s + 16777216) + 8388608 * s
          = s * s + (s * 4096 + 4096 * s + 8388608 * s + 16777216) := by ac_rfl
      rw [hshape]
      exact Nat.add_le_add_left hle1 _
    have hge2 : s * s + 16777216 * s ≤ s * s + 16777216 * s + (s * e + 16777216 * e) :=
      Nat.le_add_right _ _
    have hmid : s * s + s * 4096 + (4096 * s + 16777216) + 8388608 * s
        ≤ s * s + 16777216 * s + (s * e + 16777216 * e) :=
      Nat.le_trans base hge2
    rw [r1, r2, r3]
    exact hmid
  have hgoal : (e' * 8388608) * (s + e) ≤ (s + 16777216) * (s + e) := by
    have r1 : (e' * 8388608) * (s + e) = 4194304 * (2 * (s + e) * e') := ha
    have hmid : 4194304 * (2 * (s + e) * e')
        ≤ s * s + s * 4096 + (4096 * s + 16777216) + 8388608 * s := hd
    have hfin : s * s + s * 4096 + (4096 * s + 16777216) + 8388608 * s
        ≤ (s + 16777216) * (s + e) := he2'
    rw [r1]
    exact Nat.le_trans hmid hfin
  have hpos : 0 < s + e := by omega
  exact Nat.le_of_mul_le_mul_right hgoal hpos

theorem step_8388608_140737488355328 (s e e' : Nat) (hs : 4 ≤ s)
    (he : e * 8388608 ≤ s + 16777216)
    (herr : 2 * (s + e) * e' ≤ e * e + 2 * s) :
    e' * 140737488355328 ≤ s + 281474976710656 := by
  have he2 : (e * 8388608) * (e * 8388608)
      ≤ (s + 16777216) * (s + 16777216) := Nat.mul_le_mul he he
  have hrr : (e * 8388608) * (e * 8388608) = e * e * 70368744177664 := by
    have h1 : (e * 8388608) * (e * 8388608) = e * (8388608 * (e * 8388608)) :=
      Nat.mul_assoc e 8388608 (e * 8388608)
    have h2 : 8388608 * (e * 8388608) = e * (8388608 * 8388608) :=
      Nat.mul_left_comm 8388608 e 8388608
    have h3 : e * (e * (8388608 * 8388608)) = (e * e) * (8388608 * 8388608) := by
      rw [← Nat.mul_assoc]
    have h4 : (8388608 * 8388608 : Nat) = 70368744177664 := rfl
    rw [h1, h2, h3, h4]
  have e_am1 : (s + 16777216) * (s + 16777216)
      = s * (s + 16777216) + 16777216 * (s + 16777216) :=
    Nat.add_mul s 16777216 (s + 16777216)
  have e_am2 : s * (s + 16777216) = s * s + s * 16777216 :=
    Nat.mul_add s s 16777216
  have e_am3 : 16777216 * (s + 16777216) = 16777216 * s + 16777216 * 16777216 :=
    Nat.mul_add 16777216 s 16777216
  have h16777216 : (16777216 : Nat) * 16777216 = 281474976710656 := rfl
  have hexp : (s + 16777216) * (s + 16777216)
      = s * s + s * 16777216 + (16777216 * s + 281474976710656) := by
    rw [e_am1, e_am2, e_am3, h16777216]
  have h1 : e * e * 70368744177664
      ≤ s * s + s * 16777216 + (16777216 * s + 281474976710656) := by
    rw [hrr, hexp] at he2
    exact he2
  have ha : (e' * 140737488355328) * (s + e)
      = 70368744177664 * (2 * (s + e) * e') := by
    have h140 : (140737488355328 : Nat) = 70368744177664 * 2 := rfl
    rw [h140]
    rw [Nat.mul_assoc e' (70368744177664 * 2) (s + e)]
    rw [Nat.mul_assoc 70368744177664 2 (s + e)]
    rw [Nat.mul_left_comm e' 70368744177664 (2 * (s + e))]
    rw [Nat.mul_comm e' (2 * (s + e))]
  have hb : 70368744177664 * (2 * (s + e) * e')
      ≤ 70368744177664 * (e * e + 2 * s) :=
    Nat.mul_le_mul (Nat.le_refl 70368744177664) herr
  have hc1 : 70368744177664 * (e * e + 2 * s)
      = 70368744177664 * (e * e) + 70368744177664 * (2 * s) :=
    Nat.mul_add 70368744177664 (e * e) (2 * s)
  have hc2 : (70368744177664 : Nat) * (e * e) = e * e * 70368744177664 :=
    Nat.mul_comm _ _
  have hc3 : (70368744177664 : Nat) * (2 * s) = 140737488355328 * s := by
    have h : (70368744177664 : Nat) * (2 * s) = (70368744177664 * 2) * s := by
      rw [← Nat.mul_assoc]
    rw [h]
  have hd : 70368744177664 * (2 * (s + e) * e')
      ≤ s * s + s * 16777216 + (16777216 * s + 281474976710656)
        + 140737488355328 * s := by
    have hstep : 70368744177664 * (2 * (s + e) * e')
        ≤ 70368744177664 * (e * e + 2 * s) := hb
    rw [hc1, hc2, hc3] at hstep
    exact Nat.le_trans hstep (Nat.add_le_add_right h1 (140737488355328 * s))
  have hge : (s + 281474976710656) * s ≤ (s + 281474976710656) * (s + e) :=
    Nat.mul_le_mul (Nat.le_refl (s + 281474976710656)) (Nat.le_add_right s e)
  have hex : (s + 281474976710656) * s = s * s + 281474976710656 * s :=
    Nat.add_mul s 281474976710656 s
  have hle1 : s * 16777216 + 16777216 * s + 140737488355328 * s + 281474976710656
      ≤ 281474976710656 * s := by
    have c0 : s * 16777216 = 16777216 * s := Nat.mul_comm s 16777216
    rw [c0]
    have g1 : 16777216 * s + 16777216 * s + 140737488355328 * s + 281474976710656
        = 140737521909760 * s + 281474976710656 := by
      have e1 : (16777216 + 16777216 + 140737488355328 : Nat) = 140737521909760 :=
        rfl
      have f1 : 16777216 * s + 16777216 * s + 140737488355328 * s
          = (16777216 + 16777216 + 140737488355328) * s := by
        rw [Nat.add_mul, Nat.add_mul]
      rw [f1, e1]
    rw [g1]
    have k1 : (281474976710656 : Nat) ≤ 140737454800896 * s := by
      have m1 : (140737454800896 : Nat) * 4 ≤ 140737454800896 * s :=
        Nat.mul_le_mul (Nat.le_refl 140737454800896) hs
      have m2 : (140737454800896 : Nat) * 4 = 562949819203584 := rfl
      rw [m2] at m1
      have m3 : (281474976710656 : Nat) ≤ 562949819203584 := by decide
      exact Nat.le_trans m3 m1
    have f1 : 140737521909760 * s + 281474976710656
        ≤ 140737521909760 * s + 140737454800896 * s :=
      Nat.add_le_add_left k1 _
    have f2 : 140737521909760 * s + 140737454800896 * s = 281474976710656 * s := by
      have h : (140737521909760 + 140737454800896 : Nat) = 281474976710656 := rfl
      have e1 : 140737521909760 * s + 140737454800896 * s
          = (140737521909760 + 140737454800896) * s := by
        rw [Nat.add_mul]
      rw [e1, h]
    exact Nat.le_trans f1 (Nat.le_of_eq f2)
  have he2' : s * s + s * 16777216 + (16777216 * s + 281474976710656)
        + 140737488355328 * s ≤ (s + 281474976710656) * (s + e) := by
    have r1 : (s + 281474976710656) * (s + e)
        = (s + 281474976710656) * s + (s + 281474976710656) * e :=
      Nat.mul_add (s + 281474976710656) s e
    have r2 : (s + 281474976710656) * s = s * s + 281474976710656 * s := hex
    have r3 : (s + 281474976710656) * e = s * e + 281474976710656 * e :=
      Nat.add_mul s 281474976710656 e
    have base : s * s + s * 16777216 + (16777216 * s + 281474976710656)
          + 140737488355328 * s ≤ s * s + 281474976710656 * s := by
      have hshape : s * s + s * 16777216 + (16777216 * s + 281474976710656)
            + 140737488355328 * s
          = s * s + (s * 16777216 + 16777216 * s + 140737488355328 * s
            + 281474976710656) := by
        ac_rfl
      rw [hshape]
      exact Nat.add_le_add_left hle1 _
    have hge2 : s * s + 281474976710656 * s
        ≤ s * s + 281474976710656 * s + (s * e + 281474976710656 * e) :=
      Nat.le_add_right _ _
    have hmid : s * s + s * 16777216 + (16777216 * s + 281474976710656)
          + 140737488355328 * s
        ≤ s * s + 281474976710656 * s + (s * e + 281474976710656 * e) :=
      Nat.le_trans base hge2
    rw [r1, r2, r3]
    exact hmid
  have hgoal : (e' * 140737488355328) * (s + e)
      ≤ (s + 281474976710656) * (s + e) := by
    have hmid : 70368744177664 * (2 * (s + e) * e')
        ≤ s * s + s * 16777216 + (16777216 * s + 281474976710656)
          + 140737488355328 * s := hd
    have hfin : s * s + s * 16777216 + (16777216 * s + 281474976710656)
          + 140737488355328 * s ≤ (s + 281474976710656) * (s + e) := he2'
    have r1 : (e' * 140737488355328) * (s + e)
        = 70368744177664 * (2 * (s + e) * e') := ha
    rw [r1]
    exact Nat.le_trans hmid hfin
  have hpos : 0 < s + e := by omega
  exact Nat.le_of_mul_le_mul_right hgoal hpos

theorem step_140737488355328 (s e e' : Nat) (hs : 4 ≤ s)
    (he : e * 140737488355328 ≤ s + 281474976710656)
    (herr : 2 * (s + e) * e' ≤ e * e + 2 * s) :
    e' * 39614081257132168796771975168 ≤ s + 79228162514264337593543950336 := by
  have he2 : (e * 140737488355328) * (e * 140737488355328)
      ≤ (s + 281474976710656) * (s + 281474976710656) := Nat.mul_le_mul he he
  have hrr : (e * 140737488355328) * (e * 140737488355328)
      = e * e * 19807040628566084398385987584 := by
    have h1 : (e * 140737488355328) * (e * 140737488355328)
        = e * (140737488355328 * (e * 140737488355328)) :=
      Nat.mul_assoc e 140737488355328 (e * 140737488355328)
    have h2 : 140737488355328 * (e * 140737488355328)
        = e * (140737488355328 * 140737488355328) :=
      Nat.mul_left_comm 140737488355328 e 140737488355328
    have h3 : e * (e * (140737488355328 * 140737488355328))
        = (e * e) * (140737488355328 * 140737488355328) := by
      rw [← Nat.mul_assoc]
    have h4 : (140737488355328 * 140737488355328 : Nat)
        = 19807040628566084398385987584 := rfl
    rw [h1, h2, h3, h4]
  have e_am1 : (s + 281474976710656) * (s + 281474976710656)
      = s * (s + 281474976710656) + 281474976710656 * (s + 281474976710656) :=
    Nat.add_mul s 281474976710656 (s + 281474976710656)
  have e_am2 : s * (s + 281474976710656) = s * s + s * 281474976710656 :=
    Nat.mul_add s s 281474976710656
  have e_am3 : 281474976710656 * (s + 281474976710656)
      = 281474976710656 * s + 281474976710656 * 281474976710656 :=
    Nat.mul_add 281474976710656 s 281474976710656
  have h281 : (281474976710656 : Nat) * 281474976710656
      = 79228162514264337593543950336 := rfl
  have hexp : (s + 281474976710656) * (s + 281474976710656)
      = s * s + s * 281474976710656
        + (281474976710656 * s + 79228162514264337593543950336) := by
    rw [e_am1, e_am2, e_am3, h281]
  have h1 : e * e * 19807040628566084398385987584
      ≤ s * s + s * 281474976710656
        + (281474976710656 * s + 79228162514264337593543950336) := by
    rw [hrr, hexp] at he2
    exact he2
  have ha : (e' * 39614081257132168796771975168) * (s + e)
      = 19807040628566084398385987584 * (2 * (s + e) * e') := by
    have h396 : (39614081257132168796771975168 : Nat)
        = 19807040628566084398385987584 * 2 := rfl
    rw [h396]
    rw [Nat.mul_assoc e' (19807040628566084398385987584 * 2) (s + e)]
    rw [Nat.mul_assoc 19807040628566084398385987584 2 (s + e)]
    rw [Nat.mul_left_comm e' 19807040628566084398385987584 (2 * (s + e))]
    rw [Nat.mul_comm e' (2 * (s + e))]
  have hb : 19807040628566084398385987584 * (2 * (s + e) * e')
      ≤ 19807040628566084398385987584 * (e * e + 2 * s) :=
    Nat.mul_le_mul (Nat.le_refl 19807040628566084398385987584) herr
  have hc1 : 19807040628566084398385987584 * (e * e + 2 * s)
      = 19807040628566084398385987584 * (e * e)
        + 19807040628566084398385987584 * (2 * s) :=
    Nat.mul_add 19807040628566084398385987584 (e * e) (2 * s)
  have hc2 : (19807040628566084398385987584 : Nat) * (e * e)
      = e * e * 19807040628566084398385987584 :=
    Nat.mul_comm _ _
  have hc3 : (19807040628566084398385987584 : Nat) * (2 * s)
      = 39614081257132168796771975168 * s := by
    have h : (19807040628566084398385987584 : Nat) * (2 * s)
        = (19807040628566084398385987584 * 2) * s := by
      rw [← Nat.mul_assoc]
    rw [h]
  have hd : 19807040628566084398385987584 * (2 * (s + e) * e')
      ≤ s * s + s * 281474976710656
        + (281474976710656 * s + 79228162514264337593543950336)
        + 39614081257132168796771975168 * s := by
    have hstep : 19807040628566084398385987584 * (2 * (s + e) * e')
        ≤ 19807040628566084398385987584 * (e * e + 2 * s) := hb
    rw [hc1, hc2, hc3] at hstep
    exact Nat.le_trans hstep (Nat.add_le_add_right h1 (39614081257132168796771975168 * s))
  have hge : (s + 79228162514264337593543950336) * s
      ≤ (s + 79228162514264337593543950336) * (s + e) :=
    Nat.mul_le_mul (Nat.le_refl (s + 79228162514264337593543950336))
      (Nat.le_add_right s e)
  have hex : (s + 79228162514264337593543950336) * s
      = s * s + 79228162514264337593543950336 * s :=
    Nat.add_mul s 79228162514264337593543950336 s
  have hle1 : s * 281474976710656 + 281474976710656 * s
        + 39614081257132168796771975168 * s + 79228162514264337593543950336
        ≤ 79228162514264337593543950336 * s := by
    have c0 : s * 281474976710656 = 281474976710656 * s :=
      Nat.mul_comm s 281474976710656
    rw [c0]
    have g1 : 281474976710656 * s + 281474976710656 * s
        + 39614081257132168796771975168 * s + 79228162514264337593543950336
        = 39614081257132731746725396480 * s + 79228162514264337593543950336 := by
      have e1 : (281474976710656 + 281474976710656 + 39614081257132168796771975168 : Nat)
          = 39614081257132731746725396480 := rfl
      have f1 : 281474976710656 * s + 281474976710656 * s
          + 39614081257132168796771975168 * s
          = (281474976710656 + 281474976710656 + 39614081257132168796771975168) * s := by
        rw [Nat.add_mul, Nat.add_mul]
      rw [f1, e1]
    rw [g1]
    have k1 : (79228162514264337593543950336 : Nat)
        ≤ 39614081257131605846818553856 * s := by
      have m1 : (39614081257131605846818553856 : Nat) * 4
          ≤ 39614081257131605846818553856 * s :=
        Nat.mul_le_mul (Nat.le_refl 39614081257131605846818553856) hs
      have m2 : (39614081257131605846818553856 : Nat) * 4
          = 158456325028526423387274215424 := rfl
      rw [m2] at m1
      have m3 : (79228162514264337593543950336 : Nat)
          ≤ 158456325028526423387274215424 := by decide
      exact Nat.le_trans m3 m1
    have f1 : 39614081257132731746725396480 * s + 79228162514264337593543950336
        ≤ 39614081257132731746725396480 * s + 39614081257131605846818553856 * s :=
      Nat.add_le_add_left k1 _
    have f2 : 39614081257132731746725396480 * s + 39614081257131605846818553856 * s
        = 79228162514264337593543950336 * s := by
      have h : (39614081257132731746725396480 + 39614081257131605846818553856 : Nat)
          = 79228162514264337593543950336 := rfl
      have e1 : 39614081257132731746725396480 * s + 39614081257131605846818553856 * s
          = (39614081257132731746725396480 + 39614081257131605846818553856) * s := by
        rw [Nat.add_mul]
      rw [e1, h]
    exact Nat.le_trans f1 (Nat.le_of_eq f2)
  have he2' : s * s + s * 281474976710656
        + (281474976710656 * s + 79228162514264337593543950336)
        + 39614081257132168796771975168 * s
      ≤ (s + 79228162514264337593543950336) * (s + e) := by
    have r1 : (s + 79228162514264337593543950336) * (s + e)
        = (s + 79228162514264337593543950336) * s
          + (s + 79228162514264337593543950336) * e :=
      Nat.mul_add (s + 79228162514264337593543950336) s e
    have r2 : (s + 79228162514264337593543950336) * s
        = s * s + 79228162514264337593543950336 * s := hex
    have r3 : (s + 79228162514264337593543950336) * e
        = s * e + 79228162514264337593543950336 * e :=
      Nat.add_mul s 79228162514264337593543950336 e
    have base : s * s + s * 281474976710656
          + (281474976710656 * s + 79228162514264337593543950336)
          + 39614081257132168796771975168 * s
        ≤ s * s + 79228162514264337593543950336 * s := by
      have hshape : s * s + s * 281474976710656
            + (281474976710656 * s + 79228162514264337593543950336)
            + 39614081257132168796771975168 * s
          = s * s + (s * 281474976710656 + 281474976710656 * s
            + 39614081257132168796771975168 * s + 79228162514264337593543950336) := by
        ac_rfl
      rw [hshape]
      exact Nat.add_le_add_left hle1 _
    have hge2 : s * s + 79228162514264337593543950336 * s
        ≤ s * s + 79228162514264337593543950336 * s
          + (s * e + 79228162514264337593543950336 * e) :=
      Nat.le_add_right _ _
    have hmid : s * s + s * 281474976710656
          + (281474976710656 * s + 79228162514264337593543950336)
          + 39614081257132168796771975168 * s
        ≤ s * s + 79228162514264337593543950336 * s
          + (s * e + 79228162514264337593543950336 * e) :=
      Nat.le_trans base hge2
    rw [r1, r2, r3]
    exact hmid
  have hgoal : (e' * 39614081257132168796771975168) * (s + e)
      ≤ (s + 79228162514264337593543950336) * (s + e) := by
    have hmid : 19807040628566084398385987584 * (2 * (s + e) * e')
        ≤ s * s + s * 281474976710656
          + (281474976710656 * s + 79228162514264337593543950336)
          + 39614081257132168796771975168 * s := hd
    have hfin : s * s + s * 281474976710656
          + (281474976710656 * s + 79228162514264337593543950336)
          + 39614081257132168796771975168 * s
        ≤ (s + 79228162514264337593543950336) * (s + e) := he2'
    have r1 : (e' * 39614081257132168796771975168) * (s + e)
        = 19807040628566084398385987584 * (2 * (s + e) * e') := ha
    rw [r1]
    exact Nat.le_trans hmid hfin
  have hpos : 0 < s + e := by omega
  exact Nat.le_of_mul_le_mul_right hgoal hpos

-- The seventh Newton iterate is within one of the root once the sixth error squared fits.
theorem nat_seventh_mem {A y6 : Nat} (hs4 : 4 ≤ Nat.sqrt A)
    (hle6 : Nat.sqrt A ≤ y6)
    (hsq : (y6 - Nat.sqrt A) * (y6 - Nat.sqrt A) ≤ Nat.sqrt A) :
    ProofForgeFin.Sqrt.newton A y6 = Nat.sqrt A ∨
      (ProofForgeFin.Sqrt.newton A y6 = Nat.sqrt A + 1
        ∧ Nat.sqrt A * (Nat.sqrt A + 1) ≤ A) := by
  have hx : 0 < y6 := by omega
  exact ProofForgeFin.Sqrt.newton_eq_or_succ hx hle6 hsq

-- Main Nat convergence: seven Newton steps from the power-of-two estimate reach
-- the root or the root plus one (with the product condition), for s ≥ 4.
-- y0 = 2^(L/2), y1..y7 = newton iterates, eN = yN - s.
theorem nat_chain {A : Nat} (hs4 : 4 ≤ Nat.sqrt A) (hA256 : A < 2 ^ 256)
    (hle0 : 2 ^ (Nat.log2 A / 2) ≤ Nat.sqrt A)
    (hlt0 : Nat.sqrt A < 2 * 2 ^ (Nat.log2 A / 2))
    (hpos0 : 0 < 2 ^ (Nat.log2 A / 2)) :
    let y0 := 2 ^ (Nat.log2 A / 2)
    let y1 := ProofForgeFin.Sqrt.newton A y0
    let y2 := ProofForgeFin.Sqrt.newton A y1
    let y3 := ProofForgeFin.Sqrt.newton A y2
    let y4 := ProofForgeFin.Sqrt.newton A y3
    let y5 := ProofForgeFin.Sqrt.newton A y4
    let y6 := ProofForgeFin.Sqrt.newton A y5
    let y7 := ProofForgeFin.Sqrt.newton A y6
    (y7 = Nat.sqrt A ∨ (y7 = Nat.sqrt A + 1 ∧ Nat.sqrt A * (Nat.sqrt A + 1) ≤ A)) := by
  simp only
  set s := Nat.sqrt A with hs
  set y0 := 2 ^ (Nat.log2 A / 2) with hy0
  set y1 := ProofForgeFin.Sqrt.newton A y0 with hy1
  set y2 := ProofForgeFin.Sqrt.newton A y1 with hy2
  set y3 := ProofForgeFin.Sqrt.newton A y2 with hy3
  set y4 := ProofForgeFin.Sqrt.newton A y3 with hy4
  set y5 := ProofForgeFin.Sqrt.newton A y4 with hy5
  set y6 := ProofForgeFin.Sqrt.newton A y5 with hy6
  set y7 := ProofForgeFin.Sqrt.newton A y6 with hy7
  have hle0' : y0 ≤ s := hle0
  have hlt0' : s < 2 * y0 := hlt0
  have hn1 : s ≤ y1 := ProofForgeFin.Sqrt.sqrt_le_newton hpos0
  have herr1 := ProofForgeFin.Sqrt.newton_err_below (a := A) (x := y0) hpos0 hle0'
  have e1b : y1 - s ≤ s / 4 + 2 := newton1_bound A y0 hle0' hlt0' hpos0
  have e1m : (y1 - s) * 4 ≤ s + 8 := by
    have hle : y1 - s ≤ s / 4 + 2 := e1b
    have hmul := Nat.mul_le_mul (Nat.le_refl 4) hle
    have hexpand : 4 * (s / 4 + 2) = 4 * (s / 4) + 8 := Nat.mul_add 4 (s / 4) 2
    have hdiv : 4 * (s / 4) ≤ s := by omega
    have hle2 : 4 * (s / 4 + 2) ≤ s + 8 := by
      rw [hexpand]
      exact Nat.add_le_add_right hdiv 8
    have heq : (y1 - s) * 4 = 4 * (y1 - s) := Nat.mul_comm _ _
    rw [heq]
    exact Nat.le_trans hmul hle2
  have hpos1 : 0 < y1 := by omega
  have hn2 : s ≤ y2 := ProofForgeFin.Sqrt.sqrt_le_newton (by omega)
  have herr2 := ProofForgeFin.Sqrt.newton_err_above (a := A) (hx := hpos1) (h := hn1)
  have herr2' : 2 * (s + (y1 - s)) * (y2 - s) ≤ (y1 - s) * (y1 - s) + 2 * s := by
    have hy1eq : s + (y1 - s) = y1 := Nat.add_sub_cancel' hn1
    have hy2eq : ProofForgeFin.Sqrt.newton A y1 = y2 := hy2.symm
    rw [hy2eq] at herr2
    rw [hy1eq]
    exact herr2
  have e2m : (y2 - s) * 32 ≤ s + 64 :=
    step_4_32 s (y1 - s) (y2 - s) hs4 e1m herr2'
  have hpos2 : 0 < y2 := by omega
  have hn3 : s ≤ y3 := ProofForgeFin.Sqrt.sqrt_le_newton (by omega)
  have herr3 := ProofForgeFin.Sqrt.newton_err_above (a := A) (hx := hpos2) (h := hn2)
  have herr3' : 2 * (s + (y2 - s)) * (y3 - s) ≤ (y2 - s) * (y2 - s) + 2 * s := by
    have hy2eq : s + (y2 - s) = y2 := Nat.add_sub_cancel' hn2
    have hy3eq : ProofForgeFin.Sqrt.newton A y2 = y3 := hy3.symm
    rw [hy3eq] at herr3
    rw [hy2eq]
    exact herr3
  have e3m : (y3 - s) * 2048 ≤ s + 4096 :=
    step_32_2048 s (y2 - s) (y3 - s) hs4 e2m herr3'
  have hpos3 : 0 < y3 := by omega
  have hn4 : s ≤ y4 := ProofForgeFin.Sqrt.sqrt_le_newton (by omega)
  have herr4 := ProofForgeFin.Sqrt.newton_err_above (a := A) (hx := hpos3) (h := hn3)
  have herr4' : 2 * (s + (y3 - s)) * (y4 - s) ≤ (y3 - s) * (y3 - s) + 2 * s := by
    have hy3eq : s + (y3 - s) = y3 := Nat.add_sub_cancel' hn3
    have hy4eq : ProofForgeFin.Sqrt.newton A y3 = y4 := hy4.symm
    rw [hy4eq] at herr4
    rw [hy3eq]
    exact herr4
  have e4m : (y4 - s) * 8388608 ≤ s + 16777216 :=
    step_2048_8388608 s (y3 - s) (y4 - s) hs4 e3m herr4'
  have hpos4 : 0 < y4 := by omega
  have hn5 : s ≤ y5 := ProofForgeFin.Sqrt.sqrt_le_newton (by omega)
  have herr5 := ProofForgeFin.Sqrt.newton_err_above (a := A) (hx := hpos4) (h := hn4)
  have herr5' : 2 * (s + (y4 - s)) * (y5 - s) ≤ (y4 - s) * (y4 - s) + 2 * s := by
    have hy4eq : s + (y4 - s) = y4 := Nat.add_sub_cancel' hn4
    have hy5eq : ProofForgeFin.Sqrt.newton A y4 = y5 := hy5.symm
    rw [hy5eq] at herr5
    rw [hy4eq]
    exact herr5
  have e5m : (y5 - s) * 140737488355328 ≤ s + 281474976710656 :=
    step_8388608_140737488355328 s (y4 - s) (y5 - s) hs4 e4m herr5'
  have hpos5 : 0 < y5 := by omega
  have hn6 : s ≤ y6 := ProofForgeFin.Sqrt.sqrt_le_newton (by omega)
  have herr6 := ProofForgeFin.Sqrt.newton_err_above (a := A) (hx := hpos5) (h := hn5)
  have herr6' : 2 * (s + (y5 - s)) * (y6 - s) ≤ (y5 - s) * (y5 - s) + 2 * s := by
    have hy5eq : s + (y5 - s) = y5 := Nat.add_sub_cancel' hn5
    have hy6eq : ProofForgeFin.Sqrt.newton A y5 = y6 := hy6.symm
    rw [hy6eq] at herr6
    rw [hy5eq]
    exact herr6
  have e6m : (y6 - s) * 39614081257132168796771975168
      ≤ s + 79228162514264337593543950336 :=
    step_140737488355328 s (y5 - s) (y6 - s) hs4 e5m herr6'
  -- final square: (y6-s)^2 ≤ s, using s < 2^128 and the huge bound N = 2^95
  have hsq6 : (y6 - s) * (y6 - s) ≤ s := by
    have hle : (y6 - s) * 39614081257132168796771975168
        ≤ s + 79228162514264337593543950336 := e6m
    have hs128 : s < 2 ^ 128 :=
      ProofForgeFin.Sqrt.sqrt_lt_two_pow (a := A) (k := 128) (by omega)
    have hN95 : (39614081257132168796771975168 : Nat) = 2 ^ 95 := rfl
    have hC96 : (79228162514264337593543950336 : Nat) = 2 * 2 ^ 95 := by
      have h : (79228162514264337593543950336 : Nat) = 2 * 39614081257132168796771975168 := rfl
      rw [h, ← hN95]
    have he2 : ((y6 - s) * 39614081257132168796771975168)
          * ((y6 - s) * 39614081257132168796771975168)
        ≤ (s + 79228162514264337593543950336)
          * (s + 79228162514264337593543950336) :=
      Nat.mul_le_mul hle hle
    have hrr : ((y6 - s) * 39614081257132168796771975168)
          * ((y6 - s) * 39614081257132168796771975168)
        = ((y6 - s) * (y6 - s)) * (39614081257132168796771975168 * 39614081257132168796771975168) := by
      have h1 : ((y6 - s) * 39614081257132168796771975168)
            * ((y6 - s) * 39614081257132168796771975168)
          = ((y6 - s) * (y6 - s)) * (39614081257132168796771975168 * 39614081257132168796771975168) := by
        ac_rfl
      exact h1
    sorry
  sorry

theorem req_sqrt_not_above : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_backed    : MintBacked sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry
theorem req_newton_budget  : NewtonBudget sqrt := sorry

end OzSqrt
