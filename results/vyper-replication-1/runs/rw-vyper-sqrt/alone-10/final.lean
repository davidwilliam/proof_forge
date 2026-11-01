import VyperSqrt.Spec
import VyperSqrt.Lemmas
import Std

namespace VyperSqrt

/-- Fixed `sqrt`: the deployed loop with the PR-4486 choice `min y z`. -/
def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

/-! ## Nat utilities (no Mathlib) -/

theorem succ_sq (s : Nat) : (s + 1) * (s + 1) = s * s + (s + s + 1) := by
  simp [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  ac_rfl

theorem succ_sq_succ (s : Nat) : s.succ * s.succ = s * s + (s + s + 1) := by
  have h : s.succ = s + 1 := rfl
  rw [h]
  exact succ_sq s

theorem sq_le_sq_of_le {a b : Nat} (h : a ≤ b) : a * a ≤ b * b :=
  Nat.mul_le_mul h h

theorem sqrt_eq_of_sq {N s : Nat} (h1 : s * s ≤ N) (h2 : N < (s + 1) * (s + 1)) :
    N.sqrt = s := by
  have hs := Nat.sqrt_le N
  have hs2 := Nat.lt_succ_sqrt N
  rw [succ_sq_succ] at hs2
  rw [succ_sq] at h2
  by_cases hle : s ≤ N.sqrt
  · by_cases heq : s = N.sqrt
    · omega
    · have hlt : s < N.sqrt := by omega
      have h1' : s + 1 ≤ N.sqrt := hlt
      have hm := sq_le_sq_of_le h1'
      rw [succ_sq] at hm
      have hc : s * s + (s + s + 1) < s * s + (s + s + 1) :=
        Nat.lt_of_le_of_lt (Nat.le_trans hm hs) h2
      exact absurd hc (Nat.lt_irrefl _)
  · have hlt : N.sqrt < s := by omega
    have h1' : N.sqrt + 1 ≤ s := hlt
    have hm := sq_le_sq_of_le h1'
    rw [succ_sq] at hm
    have hc : N.sqrt * N.sqrt + (N.sqrt + N.sqrt + 1) <
        N.sqrt * N.sqrt + (N.sqrt + N.sqrt + 1) :=
      Nat.lt_of_le_of_lt (Nat.le_trans hm h1) hs2
    exact absurd hc (Nat.lt_irrefl _)

/-- `M = 2^167 - 1` dominates `10^10`. -/
theorem M_ge_10pow : 10000000000 ≤ 2 ^ 167 - 1 := by decide

theorem M_ge_16D : 16 * 10000000000 ≤ 2 ^ 167 - 1 := by decide

theorem M_ge_4D : 4 * 10000000000 ≤ 2 ^ 167 - 1 := by decide

theorem M_ge_big : 20000000003 ≤ 2 ^ 167 - 1 := by decide

/-! ## Newton iteration on `Nat` -/

/-- `N a = a * 10^10`: the scaled radicand. -/
def Nof (a : Nat) : Nat := a * 10000000000

/-- Integer square root of the scaled radicand. -/
def Sof (a : Nat) : Nat := (Nof a).sqrt

/-- The seed `a / 2 + 5 * 10^9`. -/
def seedOf (a : Nat) : Nat := a / 2 + 5000000000

/-- One Newton step `(N / z + z) / 2`. -/
def fstep (N z : Nat) : Nat := (N / z + z) / 2

/-- Pure-`Nat` loop mirror with `k` iterations left. -/
def nloop (N : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, y, z => (y, z)
  | k + 1, y, z => if z = y then (y, z) else nloop N k z (fstep N z)

theorem Nof_eq (a : Nat) : Nof a = a * 10000000000 := rfl

theorem Sof_sq_le (a : Nat) : Sof a * Sof a ≤ Nof a := Nat.sqrt_le (Nof a)

theorem Sof_lt_succ (a : Nat) : Nof a < (Sof a + 1) * (Sof a + 1) := by
  show Nof a < ((Nof a).sqrt + 1) * ((Nof a).sqrt + 1)
  have h := Nat.lt_succ_sqrt (Nof a)
  have h2 : (Nof a).sqrt.succ = (Nof a).sqrt + 1 := rfl
  rw [h2] at h
  exact h

/-- For `a ≥ 1`, `S ≥ 1` (else `N < 1`). -/
theorem Sof_pos {a : Nat} (ha : 1 ≤ a) : 1 ≤ Sof a := by
  apply Classical.byContradiction
  intro hc
  have h0 : Sof a = 0 := by omega
  have hs := Sof_lt_succ a
  rw [h0] at hs
  simp at hs
  have hN : Nof a = a * 10000000000 := rfl
  rw [hN] at hs
  have hD : 10000000000 ≤ a * 10000000000 :=
    Nat.le_mul_of_pos_left _ ha
  omega

/-- Seed stays in range. -/
theorem seed_le_M {a : Nat} (h : a ≤ 2 ^ 167 - 1) : seedOf a ≤ 2 ^ 167 - 1 := by
  have h2 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right h
  have hM := M_ge_10pow
  unfold seedOf
  omega

/-- Square nonneg over `Int`. -/
theorem sq_nonneg_I (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have h2 : 0 ≤ -x := by omega
    have hm := Int.mul_nonneg h2 h2
    have e1 : (-x) * (-x) = x * x := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [e1] at hm
    exact hm

/-- AM-GM over `Int`: `a^2 + D^2 ≥ 2·a·D`. -/
theorem AM_I (a : Nat) :
    (a : Int) * (a : Int) + 10000000000 * 10000000000 ≥
      (a : Int) * 10000000000 + ((a : Int) * 10000000000) := by
  have hsqI := sq_nonneg_I ((a : Int) - 10000000000)
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub] at hsqI
  have hc : (10000000000 : Int) * (a : Int) = (a : Int) * 10000000000 := by
    rw [Int.mul_comm]
  rw [hc] at hsqI
  simp [Int.mul_add, Int.add_mul] at hsqI ⊢
  omega

/-- `(s+1)^2` expansion over `Int`. -/
theorem esq_I (s : Int) : (s + 1) * (s + 1) = s * s + (s + s + 1) := by
  simp [Int.mul_add, Int.add_mul, Int.mul_one, Int.one_mul]
  ac_rfl

/-- `(a+D)^2` expansion over `Int`. -/
theorem eAD_I (a : Int) : (a + 10000000000) * (a + 10000000000) =
    a * a + ((a * 10000000000) + (a * 10000000000)) +
    (10000000000 * 10000000000) := by
  simp [Int.mul_add, Int.add_mul]
  rw [Int.mul_comm (10000000000 : Int) a]
  ac_rfl

/-- `(2t)^2` expansion over `Int`. -/
theorem e2t_I (t : Int) : ((2 : Int) * t) * ((2 : Int) * t) =
    (t * t) + (t * t) + ((t * t) + (t * t)) := by
  rw [Int.two_mul]
  simp [Int.add_mul, Int.mul_add]

/-- Strict square monotonicity over `Int` for nonneg bases. -/
theorem sq_lt_of_lt_nonneg_I {v u : Int} (hv : 0 ≤ v) (h : v < u) :
    v * v < u * u := by
  have h1 : v + 1 ≤ u := h
  have hm : (v + 1) * (v + 1) ≤ u * u :=
    Int.mul_le_mul h1 h1 (by omega) (by omega)
  have e := esq_I v
  omega

/-- `S ≤ seed`: AM-GM `(a-D)^2 ≥ 0` over `Int`, back to `Nat`. -/
theorem Sof_le_seed {a : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1) :
    Sof a ≤ seedOf a := by
  apply Classical.byContradiction
  intro hc
  have hlt : seedOf a < Sof a := by omega
  have hle2 : seedOf a + 1 ≤ Sof a := hlt
  have hsq := sq_le_sq_of_le hle2
  have hS := Sof_sq_le a
  have key : Nof a < (seedOf a + 1) * (seedOf a + 1) := by
    have hseed2 : 2 * (seedOf a + 1) > a + 10000000000 := by
      unfold seedOf
      omega
    -- lift to Int and conclude by linear arithmetic over atoms
    have hseed2I : (2 : Int) * ((seedOf a : Nat) + 1) > (a : Int) + 10000000000 := by
      have h2 : ((2 * (seedOf a + 1) : Nat) : Int) = (2 : Int) * ((seedOf a : Nat) + 1) := by
        simp [Int.natCast_mul, Int.natCast_add]
      have h3 : (((a + 10000000000 : Nat)) : Int) = (a : Int) + 10000000000 := by
        simp [Int.natCast_add]
      have h4 : (2 * (seedOf a + 1) : Nat) > a + 10000000000 := hseed2
      have h5 : (((2 * (seedOf a + 1) : Nat)) : Int) > (((a + 10000000000 : Nat)) : Int) := by
        exact (Int.ofNat_lt.mpr h4)
      rw [h2, h3] at h5
      exact h5
    have hAM := AM_I a
    have eAD := eAD_I (a : Int)
    have esq := esq_I ((seedOf a : Nat) : Int)
    have e2t := e2t_I (((seedOf a : Nat) : Int) + 1)
    have hmono := sq_lt_of_lt_nonneg_I (show (0 : Int) ≤ (a : Int) + 10000000000 by omega)
      (show (a : Int) + 10000000000 < 2 * (((seedOf a : Nat) : Int) + 1) by omega)
    have keyI : (a : Int) * 10000000000 <
        (((seedOf a : Nat) : Int) + 1) * (((seedOf a : Nat) : Int) + 1) := by
      omega
    have c1 : (((Nof a : Nat)) : Int) = (a : Int) * 10000000000 := by
      simp [Nof, Int.natCast_mul]
    have c2 : ((((seedOf a + 1) * (seedOf a + 1) : Nat)) : Int) =
        (((seedOf a : Nat) : Int) + 1) * (((seedOf a : Nat) : Int) + 1) := by
      simp [Int.natCast_mul, Int.natCast_add]
    have keyI2 : (((Nof a : Nat)) : Int) < (((((seedOf a + 1) * (seedOf a + 1) : Nat))) : Int) := by
      rw [c1, c2]
      exact keyI
    exact (Int.ofNat_lt.mp keyI2)
  have hc2 : (seedOf a + 1) * (seedOf a + 1) < (seedOf a + 1) * (seedOf a + 1) :=
    Nat.lt_of_le_of_lt (Nat.le_trans hsq hS) key
  exact absurd hc2 (Nat.lt_irrefl _)

/-! ## Newton step bounds -/

/-- `N ≤ S * (S + 2)`: from `N < (S+1)^2`. -/
theorem N_le_S_mul_S_add2 (a : Nat) : Nof a ≤ Sof a * (Sof a + 2) := by
  have h := Sof_lt_succ a
  have e := succ_sq (Sof a)
  have e2 : Sof a * (Sof a + 2) = Sof a * Sof a + (Sof a + Sof a) := by
    rw [Nat.mul_add]
    have h2 : Sof a * 2 = Sof a + Sof a := Nat.mul_two _
    rw [h2]
  omega

/-- `N / z ≤ S + 2` for `z ≥ S ≥ 1`. -/
theorem q_le_S_add2 {a z : Nat} (hzS : Sof a ≤ z) (hS1 : 1 ≤ Sof a) :
    Nof a / z ≤ Sof a + 2 := by
  have hN := N_le_S_mul_S_add2 a
  have hz0 : 0 < z := by omega
  have h2 : Sof a * (Sof a + 2) ≤ (Sof a + 2) * z := by
    have h3 : Sof a * (Sof a + 2) ≤ z * (Sof a + 2) :=
      Nat.mul_le_mul_right _ hzS
    rw [Nat.mul_comm z (Sof a + 2)] at h3
    exact h3
  have hle : Nof a ≤ (Sof a + 2) * z := Nat.le_trans hN h2
  rw [Nat.div_le_iff_le_mul hz0]
  omega

/-- Lower bound: `f(z) ≥ S` for `z ≥ 1`. -/
theorem f_ge_S {a z : Nat} (ha : 1 ≤ a) (hz : 1 ≤ z) :
    Sof a ≤ fstep (Nof a) z := by
  have hS := Sof_sq_le a
  have hz0 : 0 < z := hz
  have h2 : Sof a * 2 ≤ Nof a / z + z := by
    by_cases h2S : z ≤ 2 * Sof a
    · -- `w * z ≤ S * S` via `Int`, then `w ≤ N / z`
      have hSq := sq_nonneg_I ((z : Int) - (Sof a : Int))
      have eQ : ((z : Int) - (Sof a : Int)) * ((z : Int) - (Sof a : Int)) =
          (z : Int) * (z : Int) - (((Sof a : Int) * (z : Int)) + ((Sof a : Int) * (z : Int))) +
          (Sof a : Int) * (Sof a : Int) := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
        rw [Int.mul_comm (Sof a : Int) (z : Int)]
        omega
      have eP : ((2 : Int) * (Sof a : Int) - (z : Int)) * (z : Int) =
          (((Sof a : Int) * (z : Int)) + ((Sof a : Int) * (z : Int))) -
          (z : Int) * (z : Int) := by
        rw [Int.sub_mul]
        have h2S' : (2 : Int) * (Sof a : Int) * (z : Int) =
            (((Sof a : Int) * (z : Int)) + ((Sof a : Int) * (z : Int))) := by
          have h2t : (2 : Int) * (Sof a : Int) = (Sof a : Int) + (Sof a : Int) := by omega
          rw [h2t]
          simp [Int.add_mul]
        omega
      have hcast : ((((2 * Sof a - z) * z : Nat)) : Int) =
          ((2 : Int) * (Sof a : Int) - (z : Int)) * (z : Int) := by
        rw [Int.natCast_mul]
        have hw : (((2 * Sof a - z : Nat)) : Int) =
            (2 : Int) * (Sof a : Int) - (z : Int) := by
          have hsub : ((2 * Sof a - z : Nat) : Int) =
              ((2 * Sof a : Nat) : Int) - ((z : Nat) : Int) :=
            Int.natCast_sub h2S
          rw [hsub]
          simp [Int.natCast_mul]
        rw [hw]
      have hPS : ((2 : Int) * (Sof a : Int) - (z : Int)) * (z : Int) ≤
          (Sof a : Int) * (Sof a : Int) := by omega
      have hPN : ((2 : Int) * (Sof a : Int) - (z : Int)) * (z : Int) ≤
          ((Nof a : Nat) : Int) := by
        have hSc : (((Sof a * Sof a : Nat)) : Int) = (Sof a : Int) * (Sof a : Int) := by
          simp [Int.natCast_mul]
        have hNc : (((Nof a : Nat)) : Int) = ((Nof a : Nat) : Int) := rfl
        have hSS : (Sof a : Int) * (Sof a : Int) ≤ ((Nof a : Nat) : Int) := by
          have h1 : (((Sof a * Sof a : Nat)) : Int) ≤ (((Nof a : Nat)) : Int) :=
            (Int.ofNat_le.mpr hS)
          rw [hSc] at h1
          exact h1
        omega
      have hwN : (2 * Sof a - z) * z ≤ Nof a := by
        have h1 : ((((2 * Sof a - z) * z : Nat)) : Int) ≤ (((Nof a : Nat)) : Int) := by
          rw [hcast]
          exact hPN
        exact (Int.ofNat_le.mp h1)
      have hwdiv : 2 * Sof a - z ≤ Nof a / z := by
        exact ((Nat.le_div_iff_mul_le hz0).mpr hwN)
      omega
    · -- `z > 2S`: the `z` term alone suffices
      have hpush : 2 * Sof a < z := by omega
      have hq0 : 0 ≤ Nof a / z := Nat.zero_le _
      omega
  have h3 : Sof a ≤ (Nof a / z + z) / 2 := by
    have h4 : Sof a * 2 ≤ Nof a / z + z := h2
    have := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr h4
    simpa [fstep, Nat.mul_comm] using this
  exact h3

/-! ## Halving and fixed points -/

/-- `N / (S+1) ≤ S`. -/
theorem N_div_Sadd1_le {a : Nat} (hS1 : 1 ≤ Sof a) :
    Nof a / (Sof a + 1) ≤ Sof a := by
  have hN := N_le_S_mul_S_add2 a
  have h0 : 0 < Sof a + 1 := by omega
  have eA : Sof a * (Sof a + 1) = Sof a * Sof a + Sof a := by
    rw [Nat.mul_add, Nat.mul_one]
  have eB : Sof a * (Sof a + 2) = Sof a * Sof a + (Sof a + Sof a) := by
    rw [Nat.mul_add]
    have h2 : Sof a * 2 = Sof a + Sof a := Nat.mul_two _
    rw [h2]
  rw [Nat.div_le_iff_le_mul h0]
  omega

/-- Halving: `z ≥ S+1` gives `f(z) ≤ (z+S)/2`. -/
theorem f_half {a z : Nat} (hS1 : 1 ≤ Sof a) (hz : Sof a + 1 ≤ z) :
    fstep (Nof a) z ≤ (z + Sof a) / 2 := by
  have h0 : 0 < Sof a + 1 := by omega
  have hq1 := N_div_Sadd1_le hS1
  have hq : Nof a / z ≤ Sof a :=
    Nat.le_trans (Nat.div_le_div_left hz h0) hq1
  unfold fstep
  omega

/-- Strict decrease above `S`: `z ≥ S+1` gives `f(z) < z`. -/
theorem f_lt {a z : Nat} (hz : Sof a + 1 ≤ z) (hz1 : 1 ≤ z) :
    fstep (Nof a) z < z := by
  have hN := Sof_lt_succ a
  have hsq := sq_le_sq_of_le hz
  have e := succ_sq (Sof a)
  have hzz : Nof a < z * z := by omega
  have hz0 : 0 < z := hz1
  have hq : Nof a / z < z := (Nat.div_lt_iff_lt_mul hz0).mpr (by
    rw [Nat.mul_comm]; exact hzz)
  unfold fstep
  omega

/-- `f(S) ≤ S+1`. -/
theorem f_S_le {a : Nat} (hS1 : 1 ≤ Sof a) :
    fstep (Nof a) (Sof a) ≤ Sof a + 1 := by
  have hq := q_le_S_add2 (Nat.le_refl _) hS1
  unfold fstep
  omega

/-- `f(S+1) = S`. -/
theorem f_S1_eq {a : Nat} (ha : 1 ≤ a) (hS1 : 1 ≤ Sof a) :
    fstep (Nof a) (Sof a + 1) = Sof a := by
  apply Nat.le_antisymm
  · have hq := N_div_Sadd1_le hS1
    show (Nof a / (Sof a + 1) + (Sof a + 1)) / 2 ≤ Sof a
    omega
  · have hz1 : 1 ≤ Sof a + 1 := by omega
    have h := f_ge_S ha hz1
    simpa [fstep] using h

/-- `(X-1)+X ≤ X*2-1` for `X ≥ 1` (pow-free assembly helper). -/
theorem sub_add_self_le {X : Nat} (hX : 1 ≤ X) : (X - 1) + X ≤ X * 2 - 1 := by
  have h1 : (X - 1) + 1 = X := Nat.sub_add_cancel hX
  have h2 : X * 2 = X + X := Nat.mul_two _
  omega

/-- `S < 2^101`: crude range via `decide`d numeral facts (no `omega`-on-`^`). -/
theorem S_lt_pow {a : Nat} (hle : a ≤ 2 ^ 167 - 1) : Sof a < 2 ^ 101 := by
  apply Classical.byContradiction
  intro hc
  have hge : 2 ^ 101 ≤ Sof a := Nat.le_of_not_lt hc
  have hsq2 : (2 ^ 101) * (2 ^ 101) ≤ Sof a * Sof a := sq_le_sq_of_le hge
  have ePow : (2 ^ 101) * (2 ^ 101) = 2 ^ 202 := by decide
  have hS := Sof_sq_le a
  have hN : Nof a = a * 10000000000 := rfl
  have h1 : a * 10000000000 ≤ (2 ^ 167 - 1) * 10000000000 :=
    Nat.mul_le_mul_right _ hle
  have h2 : (2 ^ 167 - 1) * 10000000000 < 2 ^ 201 := by decide
  have hbig : a * 10000000000 < 2 ^ 201 := Nat.lt_of_le_of_lt h1 h2
  have hS' : Sof a * Sof a ≤ a * 10000000000 := by rw [← hN]; exact hS
  have hsq2' : 2 ^ 202 ≤ Sof a * Sof a := by rw [← ePow]; exact hsq2
  have hlt : 2 ^ 202 < 2 ^ 201 :=
    Nat.lt_of_le_of_lt (Nat.le_trans hsq2' hS') hbig
  have hle202 : 2 ^ 201 ≤ 2 ^ 202 :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 201 ≤ 202)
  have hcc : 2 ^ 201 < 2 ^ 201 := Nat.lt_of_le_of_lt hle202 hlt
  exact absurd hcc (Nat.lt_irrefl _)

/-- The invariant sum bound: `seed+1+S+2 ≤ M` (no `omega`-on-`^`). -/
theorem sum_le_M {a : Nat} (hle : a ≤ 2 ^ 167 - 1) (hS101 : Sof a + 1 ≤ 2 ^ 101) :
    seedOf a + 1 + (Sof a + 2) ≤ 2 ^ 167 - 1 := by
  have hdiv : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right hle
  have hhalf : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
  have hbig : 2 ^ 101 + 5000000002 ≤ 2 ^ 166 := by decide
  have hX1 : 1 ≤ 2 ^ 166 := by decide
  have hS : Sof a + 5000000003 ≤ 2 ^ 166 := by
    have h1 : Sof a + 5000000003 = (Sof a + 1) + 5000000002 := by omega
    rw [h1]
    exact Nat.le_trans (Nat.add_le_add hS101 (Nat.le_refl _)) hbig
  have eLHS : seedOf a + 1 + (Sof a + 2) = a / 2 + (Sof a + 5000000003) := by
    unfold seedOf
    omega
  rw [eLHS]
  have h1 : a / 2 + (Sof a + 5000000003) ≤ (2 ^ 167 - 1) / 2 + 2 ^ 166 :=
    Nat.add_le_add hdiv hS
  rw [hhalf] at h1
  have e167 : (2 : Nat) ^ 167 = 2 ^ 166 * 2 := by decide
  have hstep : (2 ^ 166 - 1) + 2 ^ 166 ≤ 2 ^ 167 - 1 := by
    rw [e167]
    exact sub_add_self_le hX1
  exact Nat.le_trans h1 hstep

/-! ## Convergence of the `Nat` iteration -/

/-- Pure iterate sequence. -/
def zseq (N z0 : Nat) : Nat → Nat
  | 0 => z0
  | k + 1 => fstep N (zseq N z0 k)

/-- Halving counter. -/
def hiter : Nat → Nat → Nat
  | 0, e => e
  | k + 1, e => hiter k (e / 2)

theorem hiter_half (k : Nat) : ∀ (E : Nat), hiter k E / 2 = hiter k (E / 2) := by
  induction k with
  | zero => intro E; rfl
  | succ k ih => intro E; exact ih (E / 2)

theorem halve_kill : ∀ (k e : Nat), e < 2 ^ k → hiter k e = 0 := by
  intro k
  induction k with
  | zero =>
    intro e h
    have h1 : (2 : Nat) ^ 0 = 1 := Nat.pow_zero 2
    rw [h1] at h
    show e = 0
    omega
  | succ k ih =>
    intro e h
    have hsk : k + 1 = k.succ := rfl
    rw [hsk, Nat.pow_succ] at h
    have hE2 : e / 2 < 2 ^ k :=
      ((Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr h)
    have hi := ih (e / 2) hE2
    show hiter k (e / 2) = 0
    exact hi

/-- `f` preserves the cap `U = seed+1`. -/
theorem f_le_U {a z : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1)
    (hlo : Sof a ≤ z) (hhi : z ≤ seedOf a + 1) :
    fstep (Nof a) z ≤ seedOf a + 1 := by
  have hS1 := Sof_pos ha
  have hq := q_le_S_add2 hlo hS1
  have hSU : Sof a + 1 ≤ seedOf a + 1 := by
    have h := Sof_le_seed ha hle
    omega
  show (Nof a / z + z) / 2 ≤ seedOf a + 1
  omega

/-- Invariant: iterates stay in `[S, U]`. -/
theorem zseq_mem {a z0 : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1)
    (hmem : Sof a ≤ z0) (hU : z0 ≤ seedOf a + 1) (k : Nat) :
    Sof a ≤ zseq (Nof a) z0 k ∧ zseq (Nof a) z0 k ≤ seedOf a + 1 := by
  induction k with
  | zero => exact ⟨hmem, hU⟩
  | succ k ih =>
    obtain ⟨hlo, hhi⟩ := ih
    have hz1 : 1 ≤ zseq (Nof a) z0 k := by
      have hS1 := Sof_pos ha
      omega
    have hge := f_ge_S ha hz1
    have hleU := f_le_U ha hle hlo hhi
    show Sof a ≤ fstep (Nof a) (zseq (Nof a) z0 k) ∧
      fstep (Nof a) (zseq (Nof a) z0 k) ≤ seedOf a + 1
    exact ⟨hge, hleU⟩

/-- One-step excess halving while above `S`. -/
theorem excess_half {a z : Nat} (hS1 : 1 ≤ Sof a) (hz : Sof a + 1 ≤ z) :
    fstep (Nof a) z - Sof a ≤ (z - Sof a) / 2 := by
  have h := f_half hS1 hz
  omega

/-- `max`-capped halving helper. -/
theorem max_half (H : Nat) : max 1 H / 2 ≤ max 1 (H / 2) := by
  cases Nat.lt_or_ge H 2 with
  | inl h =>
    have h1 : max 1 H / 2 = 0 := by omega
    omega
  | inr h =>
    have h1 : max 1 H = H := by omega
    omega

/-- One Newton step at most halves the `max`-capped excess. -/
theorem excess_step {a z : Nat} (ha : 1 ≤ a) (hz1 : 1 ≤ z) (hlo : Sof a ≤ z) :
    fstep (Nof a) z - Sof a ≤ max 1 ((z - Sof a) / 2) := by
  by_cases h1 : z - Sof a ≤ 1
  · have hzU : z ≤ Sof a + 1 := by omega
    have hS1 := Sof_pos ha
    cases Nat.lt_or_ge z (Sof a + 1) with
    | inl hlt =>
      have hzS : z = Sof a := by omega
      rw [hzS]
      have hfle := f_S_le hS1
      have hge := f_ge_S ha hS1
      omega
    | inr hge2 =>
      have hzS1 : z = Sof a + 1 := by omega
      rw [hzS1, f_S1_eq ha hS1]
      omega
  · have hS1 := Sof_pos ha
    have h := excess_half hS1 (show Sof a + 1 ≤ z by omega)
    omega

/-- Capped excess after `k` steps. -/
theorem zseq_excess {a : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1) (k : Nat) :
    ∀ (E z0 : Nat), z0 - Sof a ≤ E → Sof a ≤ z0 → z0 ≤ seedOf a + 1 →
      zseq (Nof a) z0 k - Sof a ≤ max 1 (hiter k E) := by
  induction k with
  | zero =>
    intro E z0 hE hmem hU
    exact Nat.le_trans hE (Nat.le_max_right 1 E)
  | succ k ih =>
    intro E z0 hE hmem hU
    have memk := zseq_mem ha hle hmem hU k
    have eb := ih E z0 hE hmem hU
    have hz1 : 1 ≤ zseq (Nof a) z0 k := by
      have hS1 := Sof_pos ha
      omega
    have es := excess_step ha hz1 memk.1
    have hdiv : (zseq (Nof a) z0 k - Sof a) / 2 ≤ max 1 (hiter k E / 2) := by
      have h1 : (zseq (Nof a) z0 k - Sof a) / 2 ≤ max 1 (hiter k E) / 2 :=
        Nat.div_le_div_right eb
      exact Nat.le_trans h1 (max_half _)
    have hhalf : hiter k E / 2 = hiter k (E / 2) := hiter_half k E
    rw [hhalf] at hdiv
    have hfin : fstep (Nof a) (zseq (Nof a) z0 k) - Sof a ≤
        max 1 (hiter k (E / 2)) := by
      omega
    show fstep (Nof a) (zseq (Nof a) z0 k) - Sof a ≤ max 1 (hiter (k + 1) E)
    have eH : hiter (k + 1) E = hiter k (E / 2) := rfl
    rw [eH]
    exact hfin

/-- After `k` steps with `E < 2^k`, the iterate is `S` or `S+1`. -/
theorem zseq_close {a z0 k : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1)
    (hmem : Sof a ≤ z0) (hU : z0 ≤ seedOf a + 1) (hk : z0 - Sof a < 2 ^ k) :
    Sof a ≤ zseq (Nof a) z0 k ∧ zseq (Nof a) z0 k ≤ Sof a + 1 := by
  have hmemk := (zseq_mem ha hle hmem hU k).1
  have hb := zseq_excess ha hle k (z0 - Sof a) z0 (Nat.le_refl _) hmem hU
  have hkill := halve_kill k (z0 - Sof a) hk
  rw [hkill] at hb
  have hm10 : max 1 0 = 1 := by decide
  rw [hm10] at hb
  have hU' : zseq (Nof a) z0 k ≤ Sof a + 1 := by omega
  exact ⟨hmemk, hU'⟩

/-! ## Fixed points and the exact-seed case -/

/-- A fixed point of `f` in range is `S`. -/
theorem fixed_is_S {a w : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1)
    (hlo : Sof a ≤ w) (hfix : fstep (Nof a) w = w) : w = Sof a := by
  have hS1 := Sof_pos ha
  by_cases h2 : Sof a + 2 ≤ w
  · have hlt := f_lt (show Sof a + 1 ≤ w by omega) (show 1 ≤ w by omega)
    omega
  · by_cases h1 : w = Sof a + 1
    · rw [h1] at hfix
      have hf := f_S1_eq ha hS1
      omega
    · omega

/-- Consecutive settled iterates have `min = S`. -/
theorem pair_min {a u v : Nat} (ha : 1 ≤ a)
    (hu : Sof a ≤ u) (hu2 : u ≤ Sof a + 1)
    (hv : Sof a ≤ v) (hv2 : v ≤ Sof a + 1)
    (hconsec : v = fstep (Nof a) u) : min u v = Sof a := by
  have hS1 := Sof_pos ha
  by_cases huS : u = Sof a + 1
  · have hvS : v = Sof a := by
      rw [huS, f_S1_eq ha hS1] at hconsec
      exact hconsec
    omega
  · have huS0 : u = Sof a := by omega
    omega

/-- If the seed is already fixed (`a = a/2+5e9`), then `a ∈ {D-1, D}` and `a = S`. -/
theorem seed_fixed {a : Nat} (h : a = seedOf a) : a = Sof a := by
  have hmem : a = 9999999999 ∨ a = 10000000000 := by
    unfold seedOf at h
    omega
  cases hmem with
  | inl hz =>
    have g1 : 9999999999 * 9999999999 ≤ Nof 9999999999 := by
      unfold Nof
      decide
    have g2 : Nof 9999999999 < (9999999999 + 1) * (9999999999 + 1) := by
      unfold Nof
      decide
    have hS : (Nof 9999999999).sqrt = 9999999999 := sqrt_eq_of_sq g1 g2
    have hSof : Sof 9999999999 = 9999999999 := hS
    rw [hz]
    exact hSof.symm
  | inr hz =>
    have g1 : 10000000000 * 10000000000 ≤ Nof 10000000000 := by
      unfold Nof
      decide
    have g2 : Nof 10000000000 < (10000000000 + 1) * (10000000000 + 1) := by
      unfold Nof
      decide
    have hS : (Nof 10000000000).sqrt = 10000000000 := sqrt_eq_of_sq g1 g2
    have hSof : Sof 10000000000 = 10000000000 := hS
    rw [hz]
    exact hSof.symm

/-- Start excess below `2^255`. -/
theorem E0_lt_255 {a : Nat} (hle : a ≤ 2 ^ 167 - 1) :
    seedOf a - Sof a < 2 ^ 255 := by
  have h1 : (1 : Nat) ≤ 2 ^ 167 := by decide
  have hM1 : 2 ^ 167 - 1 + 1 = 2 ^ 167 := Nat.sub_add_cancel h1
  have hUseed : seedOf a + 1 ≤ 2 ^ 167 := by
    have h0 := Nat.add_le_add_right (seed_le_M hle) (1 : Nat)
    rw [hM1] at h0
    exact h0
  have h2 : seedOf a - Sof a ≤ seedOf a + 1 := by omega
  have h3 : (2 : Nat) ^ 167 < 2 ^ 255 :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 167 < 255)
  exact Nat.lt_of_le_of_lt (Nat.le_trans h2 hUseed) h3

/-! ## `nloop` settles at `S`, and the `Int` transfer -/

theorem nloop_zero (N y z : Nat) : nloop N 0 y z = (y, z) := rfl

theorem nloop_succ (N k y z : Nat) :
    nloop N (k + 1) y z = if z = y then (y, z) else nloop N k z (fstep N z) :=
  rfl

theorem nloop_zseq {a : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1) (j k : Nat) :
    255 ≤ j + k →
    min (nloop (Nof a) k (zseq (Nof a) (seedOf a) j)
      (zseq (Nof a) (seedOf a) (j + 1))).1
      (nloop (Nof a) k (zseq (Nof a) (seedOf a) j)
      (zseq (Nof a) (seedOf a) (j + 1))).2 = Sof a := by
  induction k generalizing j with
  | zero =>
    intro hjk
    have hj : 255 ≤ j := by omega
    have hE := E0_lt_255 hle
    have hEj : seedOf a - Sof a < 2 ^ j :=
      Nat.lt_of_lt_of_le hE (Nat.pow_le_pow_right (by decide : 0 < 2) hj)
    have hEj1 : seedOf a - Sof a < 2 ^ (j + 1) :=
      Nat.lt_of_lt_of_le hE
        (Nat.pow_le_pow_right (by decide : 0 < 2) (show 255 ≤ j + 1 by omega))
    have hmem0 : Sof a ≤ seedOf a := Sof_le_seed ha hle
    have hU0 : seedOf a ≤ seedOf a + 1 := Nat.le_succ _
    have cj := zseq_close ha hle hmem0 hU0 hEj
    have cj1 := zseq_close ha hle hmem0 hU0 hEj1
    show min (zseq (Nof a) (seedOf a) j) (zseq (Nof a) (seedOf a) (j + 1)) =
      Sof a
    have hconsec : zseq (Nof a) (seedOf a) (j + 1) =
        fstep (Nof a) (zseq (Nof a) (seedOf a) j) := rfl
    exact pair_min ha cj.1 cj.2 cj1.1 cj1.2 hconsec
  | succ k ih =>
    intro hjk
    by_cases hzz : zseq (Nof a) (seedOf a) (j + 1) = zseq (Nof a) (seedOf a) j
    · have eN : nloop (Nof a) (k + 1) (zseq (Nof a) (seedOf a) j)
          (zseq (Nof a) (seedOf a) (j + 1)) =
          (zseq (Nof a) (seedOf a) j, zseq (Nof a) (seedOf a) (j + 1)) := by
        rw [nloop_succ, if_pos hzz]
      rw [eN]
      have hmem0 : Sof a ≤ seedOf a := Sof_le_seed ha hle
      have hU0 : seedOf a ≤ seedOf a + 1 := Nat.le_succ _
      have memj := zseq_mem ha hle hmem0 hU0 j
      have hconsec : zseq (Nof a) (seedOf a) (j + 1) =
          fstep (Nof a) (zseq (Nof a) (seedOf a) j) := rfl
      have hfix : fstep (Nof a) (zseq (Nof a) (seedOf a) j) =
          zseq (Nof a) (seedOf a) j := by
        rw [← hconsec]
        exact hzz
      have hW : zseq (Nof a) (seedOf a) j = Sof a :=
        fixed_is_S ha hle memj.1 hfix
      omega
    · have eN : nloop (Nof a) (k + 1) (zseq (Nof a) (seedOf a) j)
          (zseq (Nof a) (seedOf a) (j + 1)) =
          nloop (Nof a) k (zseq (Nof a) (seedOf a) (j + 1))
            (fstep (Nof a) (zseq (Nof a) (seedOf a) (j + 1))) := by
        rw [nloop_succ, if_neg hzz]
      rw [eN]
      have eF : fstep (Nof a) (zseq (Nof a) (seedOf a) (j + 1)) =
          zseq (Nof a) (seedOf a) (j + 1 + 1) := rfl
      rw [eF]
      show min (nloop (Nof a) k (zseq (Nof a) (seedOf a) (j + 1))
        (zseq (Nof a) (seedOf a) ((j + 1) + 1))).1
        (nloop (Nof a) k (zseq (Nof a) (seedOf a) (j + 1))
        (zseq (Nof a) (seedOf a) ((j + 1) + 1))).2 = Sof a
      exact ih (j + 1) (show 255 ≤ (j + 1) + k by omega)

theorem loop_transfer {a : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1) (k : Nat) :
    ∀ (y z : Nat), Sof a ≤ y → y ≤ seedOf a + 1 → Sof a ≤ z → z ≤ seedOf a + 1 →
      loop (a : Int) k (y : Int) (z : Int) =
        some (((nloop (Nof a) k y z).1 : Int), ((nloop (Nof a) k y z).2 : Int)) := by
  induction k with
  | zero =>
    intro y z hmy hUy hmz hUz
    rfl
  | succ k ih =>
    intro y z hmy hUy hmz hUz
    by_cases hzy : z = y
    · have eN : nloop (Nof a) (k + 1) y z = (y, z) := by
        unfold nloop
        rw [if_pos hzy]
      rw [eN]
      have hzyI : (z : Int) = (y : Int) := by rw [hzy]
      rw [hzyI]
      exact loop_stop _ _ _
    · have hS1 := Sof_pos ha
      have hsum := sum_le_M hle (S_lt_pow hle)
      have hq := q_le_S_add2 hmz hS1
      have hqz : Nof a / z + z ≤ 2 ^ 167 - 1 := by
        have h2 := Nat.add_le_add hq hUz
        rw [Nat.add_comm (Sof a + 2) (seedOf a + 1)] at h2
        exact Nat.le_trans h2 hsum
      have hz : 0 < z := by omega
      have hqz' : a * 10 ^ 10 / z + z ≤ 2 ^ 167 - 1 := hqz
      have hne : (z : Int) ≠ (y : Int) := fun c => hzy (Int.ofNat.inj c)
      have eI := loop_step (a := a) (y := y) (z := z) k hz hzy hqz'
      have eN : nloop (Nof a) (k + 1) y z = nloop (Nof a) k z (fstep (Nof a) z) := by
        rw [nloop_succ, if_neg hzy]
      rw [eI, eN]
      have hz1 : 1 ≤ z := by omega
      exact ih z (fstep (Nof a) z) hmz hUz (f_ge_S ha hz1)
        (f_le_U ha hle hmz hUz)

/-! ## Main lemma: `sqrt` returns the floor root -/

theorem sqrt_some_floor {a : Nat} (hle : a ≤ 2 ^ 167 - 1) :
    sqrt (a : Int) = some ((Sof a : Int)) := by
  by_cases ha0 : a = 0
  · subst ha0
    have hS0 : Sof 0 = 0 := by
      have h1 : (0 : Nat) * 0 ≤ Nof 0 := by
        unfold Nof
        omega
      have h2 : Nof 0 < (0 + 1) * (0 + 1) := by
        unfold Nof
        decide
      have h := sqrt_eq_of_sq h1 h2
      exact h
    rw [hS0]
    show vyperSqrtWith (fun y z => if y < z then y else z) (0 : Int) =
      some (0 : Int)
    unfold vyperSqrtWith
    rw [if_neg (by decide : ¬ ((0 : Int) < 0)), if_pos rfl]
  · have ha : 1 ≤ a := by omega
    have epos := vyperSqrtWith_pos (fun y z => if y < z then y else z) ha hle
    have eD : 5 * 10 ^ 9 = 5000000000 := by decide
    rw [eD] at epos
    show vyperSqrtWith (fun y z => if y < z then y else z) (a : Int) =
      some ((Sof a : Int))
    rw [epos]
    by_cases hseed : seedOf a = a
    · -- loop stops immediately; result is `a = S`
      have hSa : Sof a = a := (seed_fixed hseed.symm).symm
      have eSeed : ((a / 2 + 5000000000 : Nat) : Int) = ((seedOf a : Nat) : Int) :=
        rfl
      have hseedI : ((seedOf a : Nat) : Int) = (a : Int) := by rw [hseed]
      have e256 : (256 : Nat) = 255 + 1 := rfl
      rw [eSeed, e256, hseedI, loop_stop, Option.map_some]
      show some (if (a : Int) < (a : Int) then (a : Int) else (a : Int)) =
        some ((Sof a : Int))
      rw [if_neg (Int.lt_irrefl _), hSa]
    · have hneI : ((seedOf a : Nat) : Int) ≠ (a : Int) :=
        fun c => hseed (Int.ofNat_inj.mp c)
      have hzseed : 0 < seedOf a := by
        unfold seedOf
        omega
      have hqzseed : Nof a / seedOf a + seedOf a ≤ 2 ^ 167 - 1 := by
        have hq := q_le_S_add2 (Sof_le_seed ha hle) (Sof_pos ha)
        have hsum := sum_le_M hle (S_lt_pow hle)
        have h3 : Nof a / seedOf a + seedOf a ≤ seedOf a + 1 + (Sof a + 2) := by
          omega
        exact Nat.le_trans h3 hsum
      have hqz' : a * 10 ^ 10 / seedOf a + seedOf a ≤ 2 ^ 167 - 1 := hqzseed
      have eStep : loop (a : Int) (255 + 1) (a : Int) ((seedOf a : Nat) : Int) =
          loop (a : Int) 255 ((seedOf a : Nat) : Int)
            (((fstep (Nof a) (seedOf a) : Nat)) : Int) :=
        loop_step (a := a) (y := a) (z := seedOf a) 255 hzseed hseed hqz'
      have eSeed : ((a / 2 + 5000000000 : Nat) : Int) = ((seedOf a : Nat) : Int) :=
        rfl
      have e256 : (256 : Nat) = 255 + 1 := rfl
      rw [eSeed, e256, eStep]
      have hmemS : Sof a ≤ seedOf a := Sof_le_seed ha hle
      have hUS : seedOf a ≤ seedOf a + 1 := Nat.le_succ _
      have hmemF : Sof a ≤ fstep (Nof a) (seedOf a) :=
        f_ge_S ha (by omega)
      have hUF : fstep (Nof a) (seedOf a) ≤ seedOf a + 1 :=
        f_le_U ha hle hmemS hUS
      have etransfer := loop_transfer ha hle 255 (seedOf a)
        (fstep (Nof a) (seedOf a)) hmemS hUS hmemF hUF
      rw [etransfer, Option.map_some]
      have hmin := nloop_zseq ha hle 0 255 (by omega)
      have hmin' : min (nloop (Nof a) 255 (seedOf a)
          (fstep (Nof a) (seedOf a))).1
          (nloop (Nof a) 255 (seedOf a) (fstep (Nof a) (seedOf a))).2 =
          Sof a := hmin
      have hfin : (if ((nloop (Nof a) 255 (seedOf a)
          (fstep (Nof a) (seedOf a))).1 : Int) <
          ((nloop (Nof a) 255 (seedOf a) (fstep (Nof a) (seedOf a))).2 : Int)
          then ((nloop (Nof a) 255 (seedOf a) (fstep (Nof a) (seedOf a))).1 : Int)
          else ((nloop (Nof a) 255 (seedOf a)
          (fstep (Nof a) (seedOf a))).2 : Int)) = ((Sof a : Int)) := by
        by_cases hlt : (nloop (Nof a) 255 (seedOf a)
            (fstep (Nof a) (seedOf a))).1 <
            (nloop (Nof a) 255 (seedOf a) (fstep (Nof a) (seedOf a))).2
        · rw [if_pos (Int.ofNat_lt.mpr hlt)]
          have e1 : (nloop (Nof a) 255 (seedOf a)
              (fstep (Nof a) (seedOf a))).1 = Sof a := by
            omega
          rw [e1]
        · have hle' : (nloop (Nof a) 255 (seedOf a)
              (fstep (Nof a) (seedOf a))).2 ≤
              (nloop (Nof a) 255 (seedOf a) (fstep (Nof a) (seedOf a))).1 := by
            omega
          rw [if_neg (fun h => hlt (Int.ofNat_lt.mp h))]
          have e2 : (nloop (Nof a) 255 (seedOf a)
              (fstep (Nof a) (seedOf a))).2 = Sof a := by
            omega
          rw [e2]
      show some (if ((nloop (Nof a) 255 (seedOf a) (fstep (Nof a) (seedOf a))).1 : Int) <
          ((nloop (Nof a) 255 (seedOf a) (fstep (Nof a) (seedOf a))).2 : Int)
          then ((nloop (Nof a) 255 (seedOf a) (fstep (Nof a) (seedOf a))).1 : Int)
          else ((nloop (Nof a) 255 (seedOf a)
          (fstep (Nof a) (seedOf a))).2 : Int)) = some ((Sof a : Int))
      rw [hfin]

/-! ## The five requirements -/

theorem sqrt_neg {x : Int} (h : x < 0) : sqrt x = none := by
  show vyperSqrtWith (fun y z => if y < z then y else z) x = none
  unfold vyperSqrtWith
  rw [if_pos h]

theorem toNat_le {x : Int} (hx : IsDecimal x) (hx0 : 0 ≤ x) :
    x.toNat ≤ 2 ^ 167 - 1 := by
  obtain ⟨hlo, hhi⟩ := hx
  have hax := Int.toNat_of_nonneg hx0
  have h1 : ((x.toNat : Nat) : Int) ≤ (((2 ^ 167 - 1 : Nat)) : Int) := by
    rw [hax, ← max_decimal_eq]
    exact hhi
  exact Int.ofNat_le.mp h1

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx hr
  by_cases hxneg : x < 0
  · have hn := sqrt_neg hxneg
    rw [hn] at hr
    simp at hr
  · have hx0 : 0 ≤ x := by omega
    have hax := Int.toNat_of_nonneg hx0
    have hle := toNat_le hx hx0
    have hmain := sqrt_some_floor hle
    rw [hax] at hmain
    rw [hmain] at hr
    have hrr : r = ((Sof x.toNat : Nat) : Int) := (Option.some_inj.mp hr).symm
    rw [hrr, ← hax]
    unfold DIVISOR
    have hS := Sof_sq_le x.toNat
    have c1 : (((Sof x.toNat * Sof x.toNat : Nat)) : Int) =
        ((Sof x.toNat : Nat) : Int) * ((Sof x.toNat : Nat) : Int) := by
      simp [Int.natCast_mul]
    have c2 : (((Nof x.toNat : Nat)) : Int) =
        ((x.toNat : Nat) : Int) * 10000000000 := by
      simp [Nof, Int.natCast_mul]
    have hSS : ((Sof x.toNat : Nat) : Int) * ((Sof x.toNat : Nat) : Int) ≤
        ((x.toNat : Nat) : Int) * 10000000000 := by
      have h1 : (((Sof x.toNat * Sof x.toNat : Nat)) : Int) ≤
          (((Nof x.toNat : Nat)) : Int) :=
        Int.ofNat_le.mpr hS
      rw [c1, c2] at h1
      exact h1
    exact hSS

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx hr
  by_cases hxneg : x < 0
  · have hn := sqrt_neg hxneg
    rw [hn] at hr
    simp at hr
  · have hx0 : 0 ≤ x := by omega
    have hax := Int.toNat_of_nonneg hx0
    have hle := toNat_le hx hx0
    have hmain := sqrt_some_floor hle
    rw [hax] at hmain
    rw [hmain] at hr
    have hrr : r = ((Sof x.toNat : Nat) : Int) := (Option.some_inj.mp hr).symm
    rw [hrr, ← hax]
    unfold DIVISOR
    have hS := Sof_lt_succ x.toNat
    have c3 : ((((Sof x.toNat + 1) * (Sof x.toNat + 1) : Nat))) =
        (((Sof x.toNat : Nat) : Int) + 1) * (((Sof x.toNat : Nat) : Int) + 1) := by
      simp [Int.natCast_mul, Int.natCast_add]
    have c2 : (((Nof x.toNat : Nat)) : Int) =
        ((x.toNat : Nat) : Int) * 10000000000 := by
      simp [Nof, Int.natCast_mul]
    have hSS : ((x.toNat : Nat) : Int) * 10000000000 <
        (((Sof x.toNat : Nat) : Int) + 1) * (((Sof x.toNat : Nat) : Int) + 1) := by
      have h1 : (((Nof x.toNat : Nat)) : Int) <
          ((((Sof x.toNat + 1) * (Sof x.toNat + 1) : Nat))) :=
        Int.ofNat_lt.mpr hS
      rw [c2, c3] at h1
      exact h1
    exact hSS

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx hx0
  have hax := Int.toNat_of_nonneg hx0
  have hle := toNat_le hx hx0
  have hmain := sqrt_some_floor hle
  rw [hax] at hmain
  rw [hmain]
  rfl

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  exact sqrt_neg hx

theorem req_deployed_loop : DeployedLoop sqrt :=
  ⟨(fun y z => if y < z then y else z), fun x => rfl⟩

end VyperSqrt
