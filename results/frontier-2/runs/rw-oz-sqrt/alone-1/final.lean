import OzSqrt.Spec
import OzSqrt.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.BitVec.Lemmas

namespace OzSqrt

/-- Fixed routine: seven Newton steps (deployed OpenZeppelin count). -/
def sqrt : SqrtFn := newtonSqrt 7

/-- Nat-level initial estimate: 2 ^ (log2 N / 2). -/
def natInit (N : Nat) : Nat := 2 ^ (Nat.log2 N / 2)

/-- Nat-level Newton step. -/
def natStep (N X : Nat) : Nat := (X + N / X) / 2

/-- Nat-level iteration. -/
def natIter (N : Nat) : Nat → Nat
  | 0 => natInit N
  | k + 1 => natStep N (natIter N k)

/-- Every N has a floor square root. -/
theorem exists_floor_sqrt (N : Nat) : ∃ s, s * s ≤ N ∧ N < (s + 1) * (s + 1) := by
  induction N with
  | zero => exact ⟨0, by omega, by omega⟩
  | succ n ih =>
    obtain ⟨s, hs1, hs2⟩ := ih
    by_cases h : n + 1 < (s + 1) * (s + 1)
    · exact ⟨s, by omega, h⟩
    · have hs1' : (s + 1) * (s + 1) ≤ n + 1 := by omega
      refine ⟨s + 1, hs1', ?_⟩
      have h2 : (s + 1 + 1) * (s + 1 + 1) = (s + 1) * (s + 1) + (s + 1) + (s + 1) + 1 := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
        omega
      omega

theorem sq_add_sq_ge (X s : Nat) : 2 * s * X ≤ X * X + s * s := by
  by_cases h : X ≤ s
  · obtain ⟨d, hd⟩ := Nat.le.dest h
    have hs : s = X + d := by omega
    subst hs
    have eL : 2 * (X + d) * X = 2 * (X * X) + 2 * (X * d) := by
      have h1 : 2 * (X + d) = 2 * X + 2 * d := by rw [Nat.mul_add]
      rw [h1, Nat.add_mul, Nat.mul_assoc 2 X X, Nat.mul_assoc 2 d X,
        Nat.mul_comm d X]
    have eR : (X + d) * (X + d) = X * X + (2 * (X * d) + d * d) := by
      have h1 : (X + d) * (X + d) = X * X + X * d + (d * X + d * d) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      rw [h1, Nat.mul_comm d X]
      omega
    omega
  · have h2 : s ≤ X := by omega
    obtain ⟨d, hd⟩ := Nat.le.dest h2
    have hX : X = s + d := by omega
    subst hX
    have eL : 2 * s * (s + d) = 2 * (s * s) + 2 * (s * d) := by
      rw [Nat.mul_add, Nat.mul_assoc 2 s s, Nat.mul_assoc 2 s d]
    have eR : (s + d) * (s + d) = s * s + (2 * (s * d) + d * d) := by
      have h1 : (s + d) * (s + d) = s * s + s * d + (d * s + d * d) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      rw [h1, Nat.mul_comm d s]
      omega
    omega

theorem add_sqsq_div_ge (X s : Nat) (hX : 0 < X) : 2 * s ≤ X + s * s / X := by
  by_cases hs : s = 0
  · subst hs
    simp
  · by_cases h : 2 * s ≤ X + s * s / X
    · exact h
    · have hlt1 : X + s * s / X + 1 ≤ 2 * s := by omega
      have hmod : s * s % X < X := Nat.mod_lt _ hX
      have hdecomp : X * (s * s / X) + s * s % X = s * s := Nat.div_add_mod _ _
      have hsq := sq_add_sq_ge X s
      have hmul : (X + s * s / X + 1) * X ≤ 2 * s * X :=
        Nat.mul_le_mul_right _ hlt1
      have hexpand : (X + s * s / X + 1) * X
          = X * X + (s * s / X) * X + X := by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
      have hcomm : (s * s / X) * X = X * (s * s / X) := Nat.mul_comm _ _
      omega

theorem newton_ge (N X s : Nat) (hX : 0 < X) (hsq : s * s ≤ N) :
    s ≤ (X + N / X) / 2 := by
  have hdiv : s * s / X ≤ N / X := Nat.div_le_div_right hsq
  have hbase := add_sqsq_div_ge X s hX
  have hge : 2 * s ≤ X + N / X := by omega
  have hle : 2 * s / 2 ≤ (X + N / X) / 2 := Nat.div_le_div_right hge
  have heq : 2 * s / 2 = s := by omega
  omega

theorem quad_step (N X t d e : Nat)
    (hN : N < t * t) (hXd : X = t + d)
    (hXe : (X + N / X) / 2 = t + e) : 2 * e * X + 1 ≤ d * d := by
  have hqX : N / X * X + 1 ≤ t * t := by
    have h1 : N / X * X ≤ N := by
      have hdecomp : X * (N / X) + N % X = N := Nat.div_add_mod _ _
      have hcomm : X * (N / X) = N / X * X := Nat.mul_comm _ _
      omega
    omega
  have h2 : 2 * ((X + N / X) / 2) ≤ X + N / X := by omega
  rw [hXe] at h2
  have h4 : t + 2 * e ≤ d + N / X := by omega
  have h5 : (t + 2 * e) * X ≤ (d + N / X) * X :=
    Nat.mul_le_mul_right _ h4
  have eA : (t + 2 * e) * X = t * X + 2 * e * X := by
    rw [Nat.add_mul]
  have htX : t * X = t * t + t * d := by
    rw [hXd, Nat.mul_add]
  have eB : (d + N / X) * X = d * t + d * d + N / X * X := by
    have h1 : (d + N / X) * X = d * X + N / X * X := by rw [Nat.add_mul]
    have hdX : d * X = d * t + d * d := by rw [hXd, Nat.mul_add]
    omega
  have hcomm : d * t = t * d := Nat.mul_comm _ _
  omega

theorem key_ineq (X0 t : Nat) (h1 : t ≤ 2 * X0) (h2 : X0 ≤ t) :
    2 * X0 * X0 + 2 * t * t ≤ 5 * t * X0 := by
  obtain ⟨d2, hd2⟩ := Nat.le.dest h2
  have ht : t = X0 + d2 := by omega
  subst ht
  have hd2le : d2 ≤ X0 := by omega
  have hmul1 : d2 * d2 ≤ X0 * d2 := Nat.mul_le_mul_right _ hd2le
  have hmul2 : X0 * d2 ≤ X0 * X0 := Nat.mul_le_mul_left _ hd2le
  have g1 : 2 * X0 * X0 = 2 * (X0 * X0) := by rw [Nat.mul_assoc]
  have g2 : 2 * (X0 + d2) * (X0 + d2) = 2 * ((X0 + d2) * (X0 + d2)) := by
    rw [Nat.mul_assoc]
  have g3 : 5 * (X0 + d2) * X0 = 5 * ((X0 + d2) * X0) := by
    rw [Nat.mul_assoc]
  have hsq : (X0 + d2) * (X0 + d2) = X0 * X0 + X0 * d2 + (X0 * d2 + d2 * d2) := by
    have hh : (X0 + d2) * (X0 + d2) = X0 * X0 + X0 * d2 + (d2 * X0 + d2 * d2) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    rw [hh, Nat.mul_comm d2 X0]
  have hmulX : (X0 + d2) * X0 = X0 * X0 + X0 * d2 := by
    rw [Nat.add_mul, Nat.mul_comm d2 X0]
  omega

theorem four_X1 (X0 q t X1 : Nat) (_hX0 : 0 < X0)
    (hXt : t ≤ 2 * X0) (hX0t : X0 ≤ t)
    (hq : q * X0 + 1 ≤ t * t)
    (hX1 : 2 * X1 ≤ X0 + q) :
    4 * X1 + 1 ≤ 5 * t := by
  have hkey := key_ineq X0 t hXt hX0t
  have h4 : 4 * X1 ≤ 2 * X0 + 2 * q := by
    have hmul : 2 * X1 * 2 ≤ (X0 + q) * 2 := Nat.mul_le_mul_right _ hX1
    have e1 : 2 * X1 * 2 = 4 * X1 := by omega
    have e2 : (X0 + q) * 2 = 2 * X0 + 2 * q := by
      rw [Nat.add_mul, Nat.mul_comm X0 2, Nat.mul_comm q 2]
    omega
  have hq2 : 2 * q * X0 + 2 ≤ 2 * t * t := by
    have h1 : 2 * q * X0 = 2 * (q * X0) := by rw [Nat.mul_assoc]
    have h2 : 2 * t * t = 2 * (t * t) := by rw [Nat.mul_assoc]
    omega
  have e3 : (2 * X0 + 2 * q) * X0 = 2 * X0 * X0 + 2 * q * X0 := by
    rw [Nat.add_mul]
  have h5 : (2 * X0 + 2 * q) * X0 + 2 ≤ 5 * t * X0 := by omega
  have hlt : (2 * X0 + 2 * q) * X0 < 5 * t * X0 := by omega
  have hlt2 : 2 * X0 + 2 * q < 5 * t :=
    Nat.lt_of_mul_lt_mul_right hlt
  omega

theorem init_sq_le (N : Nat) (hN : 0 < N) : natInit N * natInit N ≤ N := by
  have hlog := (Nat.log2_eq_iff (by omega : N ≠ 0)).mp rfl
  obtain ⟨hle, hlt⟩ := hlog
  unfold natInit
  have heq : 2 ^ (Nat.log2 N / 2) * 2 ^ (Nat.log2 N / 2)
      = 2 ^ (2 * (Nat.log2 N / 2)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [heq]
  have hle2 : 2 * (Nat.log2 N / 2) ≤ Nat.log2 N := by omega
  have hpow : 2 ^ (2 * (Nat.log2 N / 2)) ≤ 2 ^ Nat.log2 N :=
    Nat.pow_le_pow_right (by omega) hle2
  omega

theorem two_init_sq_gt (N : Nat) (hN : 0 < N) :
    N < (2 * natInit N) * (2 * natInit N) := by
  have hlog := (Nat.log2_eq_iff (by omega : N ≠ 0)).mp rfl
  obtain ⟨hle, hlt⟩ := hlog
  unfold natInit
  have heq1 : 2 * 2 ^ (Nat.log2 N / 2) = 2 ^ (Nat.log2 N / 2 + 1) := by
    rw [Nat.pow_succ]
    omega
  have heq2 : (2 * 2 ^ (Nat.log2 N / 2)) * (2 * 2 ^ (Nat.log2 N / 2))
      = 2 ^ (2 * (Nat.log2 N / 2) + 2) := by
    rw [heq1, ← Nat.pow_add]
    congr 1
    omega
  rw [heq2]
  have hge : Nat.log2 N + 1 ≤ 2 * (Nat.log2 N / 2) + 2 := by omega
  have hpow : 2 ^ (Nat.log2 N + 1) ≤ 2 ^ (2 * (Nat.log2 N / 2) + 2) :=
    Nat.pow_le_pow_right (by omega) hge
  omega

theorem init_le_floor (N s : Nat) (hN : 0 < N)
    (hs2 : N < (s + 1) * (s + 1)) :
    natInit N ≤ s := by
  by_cases h : natInit N ≤ s
  · exact h
  · have hlt : s < natInit N := by omega
    have hle : s + 1 ≤ natInit N := by omega
    have hpow : (s + 1) * (s + 1) ≤ natInit N * natInit N :=
      Nat.mul_le_mul hle hle
    have hX0 := init_sq_le N hN
    omega

theorem succ_le_two_init (N s : Nat) (hN : 0 < N)
    (hs1 : s * s ≤ N) :
    s + 1 ≤ 2 * natInit N := by
  by_cases h : s + 1 ≤ 2 * natInit N
  · exact h
  · have hge : 2 * natInit N ≤ s := by omega
    have hpow : (2 * natInit N) * (2 * natInit N) ≤ s * s :=
      Nat.mul_le_mul hge hge
    have hgt := two_init_sq_gt N hN
    omega

theorem step_4_32 (t d d' X : Nat) (ht : 0 < t) (hXt : t ≤ X)
    (h4d : 4 * d ≤ t)
    (hquad : 2 * d' * X + 1 ≤ d * d) :
    32 * d' ≤ t := by
  have hle1 : 2 * d' * t ≤ 2 * d' * X := Nat.mul_le_mul_left _ hXt
  have hle2 : 2 * d' * t ≤ d * d := by omega
  have hsq : (4 * d) * (4 * d) ≤ t * t := Nat.mul_le_mul h4d h4d
  have e16 : (4 * d) * (4 * d) = 16 * (d * d) := by
    rw [Nat.mul_assoc 4 d (4 * d), ← Nat.mul_assoc d 4 d,
      Nat.mul_comm d 4, Nat.mul_assoc 4 d d, ← Nat.mul_assoc 4 4 (d * d)]
  have h16 : 16 * (d * d) ≤ t * t := by omega
  have e32 : 32 * d' * t = 16 * (2 * d' * t) := by
    rw [Nat.mul_assoc 32 d' t, Nat.mul_assoc 2 d' t, ← Nat.mul_assoc 16 2 (d' * t)]
  have h32 : 32 * d' * t ≤ t * t := by omega
  exact Nat.le_of_mul_le_mul_right h32 ht

theorem step_32_2048 (t d d' X : Nat) (ht : 0 < t) (hXt : t ≤ X)
    (h4d : 32 * d ≤ t)
    (hquad : 2 * d' * X + 1 ≤ d * d) :
    2048 * d' ≤ t := by
  have hle1 : 2 * d' * t ≤ 2 * d' * X := Nat.mul_le_mul_left _ hXt
  have hle2 : 2 * d' * t ≤ d * d := by omega
  have hsq : (32 * d) * (32 * d) ≤ t * t := Nat.mul_le_mul h4d h4d
  have e16 : (32 * d) * (32 * d) = 1024 * (d * d) := by
    rw [Nat.mul_assoc 32 d (32 * d), ← Nat.mul_assoc d 32 d,
      Nat.mul_comm d 32, Nat.mul_assoc 32 d d, ← Nat.mul_assoc 32 32 (d * d)]
  have h16 : 1024 * (d * d) ≤ t * t := by omega
  have e32 : 2048 * d' * t = 1024 * (2 * d' * t) := by
    rw [Nat.mul_assoc 2048 d' t, Nat.mul_assoc 2 d' t, ← Nat.mul_assoc 1024 2 (d' * t)]
  have h32 : 2048 * d' * t ≤ t * t := by omega
  exact Nat.le_of_mul_le_mul_right h32 ht

theorem step_2048_8388608 (t d d' X : Nat) (ht : 0 < t) (hXt : t ≤ X)
    (h4d : 2048 * d ≤ t)
    (hquad : 2 * d' * X + 1 ≤ d * d) :
    8388608 * d' ≤ t := by
  have hle1 : 2 * d' * t ≤ 2 * d' * X := Nat.mul_le_mul_left _ hXt
  have hle2 : 2 * d' * t ≤ d * d := by omega
  have hsq : (2048 * d) * (2048 * d) ≤ t * t := Nat.mul_le_mul h4d h4d
  have e16 : (2048 * d) * (2048 * d) = 4194304 * (d * d) := by
    rw [Nat.mul_assoc 2048 d (2048 * d), ← Nat.mul_assoc d 2048 d,
      Nat.mul_comm d 2048, Nat.mul_assoc 2048 d d, ← Nat.mul_assoc 2048 2048 (d * d)]
  have h16 : 4194304 * (d * d) ≤ t * t := by omega
  have e32 : 8388608 * d' * t = 4194304 * (2 * d' * t) := by
    rw [Nat.mul_assoc 8388608 d' t, Nat.mul_assoc 2 d' t, ← Nat.mul_assoc 4194304 2 (d' * t)]
  have h32 : 8388608 * d' * t ≤ t * t := by omega
  exact Nat.le_of_mul_le_mul_right h32 ht

theorem step_8388608_2pow47 (t d d' X : Nat) (ht : 0 < t) (hXt : t ≤ X)
    (h4d : 8388608 * d ≤ t)
    (hquad : 2 * d' * X + 1 ≤ d * d) :
    2 ^ 47 * d' ≤ t := by
  have hle1 : 2 * d' * t ≤ 2 * d' * X := Nat.mul_le_mul_left _ hXt
  have hle2 : 2 * d' * t ≤ d * d := by omega
  have hsq : (8388608 * d) * (8388608 * d) ≤ t * t := Nat.mul_le_mul h4d h4d
  have e16 : (8388608 * d) * (8388608 * d) = 2 ^ 46 * (d * d) := by
    rw [Nat.mul_assoc 8388608 d (8388608 * d), ← Nat.mul_assoc d 8388608 d,
      Nat.mul_comm d 8388608, Nat.mul_assoc 8388608 d d, ← Nat.mul_assoc 8388608 8388608 (d * d)]
  have h16 : 2 ^ 46 * (d * d) ≤ t * t := by omega
  have e32 : 2 ^ 47 * d' * t = 2 ^ 46 * (2 * d' * t) := by
    rw [Nat.mul_assoc (2 ^ 47) d' t, Nat.mul_assoc 2 d' t, ← Nat.mul_assoc (2 ^ 46) 2 (d' * t)]
  have h32 : 2 ^ 47 * d' * t ≤ t * t := by omega
  exact Nat.le_of_mul_le_mul_right h32 ht

theorem step_2pow47_2pow95 (t d d' X : Nat) (ht : 0 < t) (hXt : t ≤ X)
    (h4d : 2 ^ 47 * d ≤ t)
    (hquad : 2 * d' * X + 1 ≤ d * d) :
    2 ^ 95 * d' ≤ t := by
  have hle1 : 2 * d' * t ≤ 2 * d' * X := Nat.mul_le_mul_left _ hXt
  have hle2 : 2 * d' * t ≤ d * d := by omega
  have hsq : (2 ^ 47 * d) * (2 ^ 47 * d) ≤ t * t := Nat.mul_le_mul h4d h4d
  have e16 : (2 ^ 47 * d) * (2 ^ 47 * d) = 2 ^ 94 * (d * d) := by
    rw [Nat.mul_assoc (2 ^ 47) d ((2 ^ 47) * d), ← Nat.mul_assoc d (2 ^ 47) d,
      Nat.mul_comm d (2 ^ 47), Nat.mul_assoc (2 ^ 47) d d, ← Nat.mul_assoc (2 ^ 47) (2 ^ 47) (d * d)]
  have h16 : 2 ^ 94 * (d * d) ≤ t * t := by omega
  have e32 : 2 ^ 95 * d' * t = 2 ^ 94 * (2 * d' * t) := by
    rw [Nat.mul_assoc (2 ^ 95) d' t, Nat.mul_assoc 2 d' t, ← Nat.mul_assoc (2 ^ 94) 2 (d' * t)]
  have h32 : 2 ^ 95 * d' * t ≤ t * t := by omega
  exact Nat.le_of_mul_le_mul_right h32 ht

theorem step_2pow95_2pow191 (t d d' X : Nat) (ht : 0 < t) (hXt : t ≤ X)
    (h4d : 2 ^ 95 * d ≤ t)
    (hquad : 2 * d' * X + 1 ≤ d * d) :
    2 ^ 191 * d' ≤ t := by
  have hle1 : 2 * d' * t ≤ 2 * d' * X := Nat.mul_le_mul_left _ hXt
  have hle2 : 2 * d' * t ≤ d * d := by omega
  have hsq : (2 ^ 95 * d) * (2 ^ 95 * d) ≤ t * t := Nat.mul_le_mul h4d h4d
  have e16 : (2 ^ 95 * d) * (2 ^ 95 * d) = 2 ^ 190 * (d * d) := by
    rw [Nat.mul_assoc (2 ^ 95) d ((2 ^ 95) * d), ← Nat.mul_assoc d (2 ^ 95) d,
      Nat.mul_comm d (2 ^ 95), Nat.mul_assoc (2 ^ 95) d d, ← Nat.mul_assoc (2 ^ 95) (2 ^ 95) (d * d)]
  have h16 : 2 ^ 190 * (d * d) ≤ t * t := by omega
  have e32 : 2 ^ 191 * d' * t = 2 ^ 190 * (2 * d' * t) := by
    rw [Nat.mul_assoc (2 ^ 191) d' t, Nat.mul_assoc 2 d' t, ← Nat.mul_assoc (2 ^ 190) 2 (d' * t)]
  have h32 : 2 ^ 191 * d' * t ≤ t * t := by omega
  exact Nat.le_of_mul_le_mul_right h32 ht

theorem stays_le (N s t X : Nat) (hs : s + 1 = t) (hN : N < t * t)
    (hXs : s ≤ X) (hXt : X ≤ t) (_hXpos : 0 < X) (hspos : 0 < s) :
    (X + N / X) / 2 ≤ t := by
  by_cases heq : X = s
  · rw [heq]
    have hNle : N ≤ t * t - 1 := by omega
    have htt : t * t - 1 = s * (t + 1) := by
      have ht : t = s + 1 := by omega
      rw [ht]
      simp [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    have hdiv : (t * t - 1) / s = t + 1 := by
      rw [htt]
      rw [Nat.mul_comm s (t + 1)]
      exact Nat.mul_div_cancel _ hspos
    have hle : N / s ≤ t + 1 := by
      have h2 : N / s ≤ (t * t - 1) / s := Nat.div_le_div_right hNle
      omega
    omega
  · have heqt : X = t := by omega
    rw [heqt]
    have hNle : N ≤ t * t - 1 := by omega
    have htt : t * t - 1 = s * t + s := by
      have ht : t = s + 1 := by omega
      rw [ht]
      simp [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    have hpos : 0 < t * t := Nat.mul_pos (by omega) (by omega)
    have hdiv : (t * t - 1) / t = s := by
      apply Nat.div_eq_of_lt_le
      · omega
      · have e2 : (s + 1) * t = t * t := by
          have ht : t = s + 1 := by omega
          rw [ht]
        omega
    have hle : N / t ≤ s := by
      have h2 : N / t ≤ (t * t - 1) / t := Nat.div_le_div_right hNle
      omega
    omega

theorem s_pos_of_pos (N s : Nat) (hN : 0 < N) (hs1 : s * s ≤ N) (hs2 : N < (s + 1) * (s + 1)) :
    0 < s := by
  by_cases hs : s = 0
  · subst hs
    simp at hs2
    omega
  · omega

theorem natIter_pos (N : Nat) (hN : 0 < N) : ∀ k, 0 < natIter N k := by
  intro k
  induction k with
  | zero =>
    show 0 < natInit N
    unfold natInit
    exact Nat.two_pow_pos _
  | succ k ih =>
    show 0 < natStep N (natIter N k)
    unfold natStep
    by_cases hX1 : natIter N k = 1
    · rw [hX1]
      have hdiv : N / 1 = N := Nat.div_one N
      rw [hdiv]
      have hge : 1 + N ≥ 2 := by omega
      have hle : (1 + N) / 2 ≥ 1 := by
        have h1 : 2 / 2 ≤ (1 + N) / 2 := Nat.div_le_div_right hge
        have heq : 2 / 2 = 1 := by omega
        omega
      omega
    · have hge2 : natIter N k ≥ 2 := by omega
      have hc0 : 0 ≤ N / natIter N k := Nat.zero_le _
      have hsum : natIter N k + N / natIter N k ≥ 2 := by omega
      have hle : (natIter N k + N / natIter N k) / 2 ≥ 1 := by
        have h1 : 2 / 2 ≤ (natIter N k + N / natIter N k) / 2 := Nat.div_le_div_right hsum
        have heq : 2 / 2 = 1 := by omega
        omega
      omega

theorem natIter_ge (N s : Nat) (hN : 0 < N) (hs1 : s * s ≤ N) : ∀ k, s ≤ natIter N (k + 1) := by
  intro k
  induction k with
  | zero =>
    show s ≤ natStep N (natInit N)
    unfold natStep
    exact newton_ge N (natInit N) s (Nat.two_pow_pos _) hs1
  | succ k ih =>
    have hpos : 0 < natIter N (k + 1) := natIter_pos N hN (k + 1)
    show s ≤ natStep N (natIter N (k + 1))
    unfold natStep
    exact newton_ge N (natIter N (k + 1)) s hpos hs1

theorem natIter_7_le (N s t : Nat) (hN : 0 < N) (hs1 : s * s ≤ N) (hs2 : N < t * t)
    (hst : s + 1 = t) (hN256 : N < 2 ^ 256) : natIter N 7 ≤ t := by
  have hs2' : N < (s + 1) * (s + 1) := by
    have h := hs2
    rw [hst.symm] at h
    -- h : N < (s+1)*(s+1)? No, hst.symm : t = s+1, rewriting t in N<t*t gives N<(s+1)*(s+1)? Check:
    -- hs2 : N < t * t, with t = s+1, so N < (s+1)*(s+1). rw [hst.symm] rewrites t to s+1? hst : s+1 = t, hst.symm : t = s+1, yes.
    exact h
  have hspos : 0 < s := s_pos_of_pos N s hN hs1 hs2'
  have htpos : 0 < t := by omega
  have hX0pos : 0 < natInit N := Nat.two_pow_pos _
  have hX0le : natInit N ≤ s := init_le_floor N s hN hs2'
  have hXt : t ≤ 2 * natInit N := by
    have h := succ_le_two_init N s hN hs1
    omega
  have hX0t : natInit N ≤ t := by omega
  have hX0pos' : 0 < natIter N 0 := natIter_pos N hN 0
  have hX1ge : s ≤ natIter N 1 := natIter_ge N s hN hs1 0
  have hX1pos : 0 < natIter N 1 := natIter_pos N hN 1
  have hX0eq : natIter N 0 = natInit N := rfl
  have hq0 : N / natIter N 0 * natIter N 0 + 1 ≤ t * t := by
    have hdecomp : natIter N 0 * (N / natIter N 0) + N % natIter N 0 = N := Nat.div_add_mod _ _
    have hcomm : natIter N 0 * (N / natIter N 0) = N / natIter N 0 * natIter N 0 := Nat.mul_comm _ _
    have hle : N / natIter N 0 * natIter N 0 ≤ N := by omega
    have hlt : N + 1 ≤ t * t := by omega
    omega
  have hX1eq : natIter N 1 = (natIter N 0 + N / natIter N 0) / 2 := rfl
  have hX1le2 : 2 * natIter N 1 ≤ natIter N 0 + N / natIter N 0 := by
    rw [hX1eq]
    omega
  have h41 : 4 * natIter N 1 + 1 ≤ 5 * t :=
    four_X1 (natIter N 0) (N / natIter N 0) t (natIter N 1) hX0pos' hXt hX0t hq0 hX1le2
  by_cases hX1le : natIter N 1 ≤ t
  · -- X1 ≤ t: stays to X7
    have hX2ge : s ≤ natIter N 2 := natIter_ge N s hN hs1 1
    have hX2pos : 0 < natIter N 2 := natIter_pos N hN 2
    have hX2le : natIter N 2 ≤ t := stays_le N s t (natIter N 1) hst hs2 hX1ge hX1le hX1pos hspos
    have hX3ge : s ≤ natIter N 3 := natIter_ge N s hN hs1 2
    have hX3pos : 0 < natIter N 3 := natIter_pos N hN 3
    have hX3le : natIter N 3 ≤ t := stays_le N s t (natIter N 2) hst hs2 hX2ge hX2le hX2pos hspos
    have hX4ge : s ≤ natIter N 4 := natIter_ge N s hN hs1 3
    have hX4pos : 0 < natIter N 4 := natIter_pos N hN 4
    have hX4le : natIter N 4 ≤ t := stays_le N s t (natIter N 3) hst hs2 hX3ge hX3le hX3pos hspos
    have hX5ge : s ≤ natIter N 5 := natIter_ge N s hN hs1 4
    have hX5pos : 0 < natIter N 5 := natIter_pos N hN 5
    have hX5le : natIter N 5 ≤ t := stays_le N s t (natIter N 4) hst hs2 hX4ge hX4le hX4pos hspos
    have hX6ge : s ≤ natIter N 6 := natIter_ge N s hN hs1 5
    have hX6pos : 0 < natIter N 6 := natIter_pos N hN 6
    have hX6le : natIter N 6 ≤ t := stays_le N s t (natIter N 5) hst hs2 hX5ge hX5le hX5pos hspos
    have hX7ge : s ≤ natIter N 7 := natIter_ge N s hN hs1 6
    have hX7pos : 0 < natIter N 7 := natIter_pos N hN 7
    exact stays_le N s t (natIter N 6) hst hs2 hX6ge hX6le hX6pos hspos
  · -- X1 > t: write X1 = t + d0
    have hX1lt : t < natIter N 1 := by omega
    have hX1le' : t ≤ natIter N 1 := by omega
    obtain ⟨d0, hd0⟩ := Nat.le.dest hX1le'
    have hd0pos : 0 < d0 := by omega
    have heq1 : natIter N 1 = t + d0 := by omega
    have h4d0 : 4 * d0 + 1 ≤ t := by
      have e : 4 * natIter N 1 = 4 * t + 4 * d0 := by
        rw [heq1, Nat.mul_add]
      omega
    have h4d0' : 4 * d0 ≤ t := by omega
    have hX1Xt : t ≤ natIter N 1 := by omega
    -- X2 by_cases
    have hX2ge : s ≤ natIter N 2 := natIter_ge N s hN hs1 1
    have hX2pos : 0 < natIter N 2 := natIter_pos N hN 2
    by_cases hX2le : natIter N 2 ≤ t
    · -- X2 ≤ t: stays to X7 (5 steps)
      have hX3ge : s ≤ natIter N 3 := natIter_ge N s hN hs1 2
      have hX3pos : 0 < natIter N 3 := natIter_pos N hN 3
      have hX3le : natIter N 3 ≤ t := stays_le N s t (natIter N 2) hst hs2 hX2ge hX2le hX2pos hspos
      have hX4ge : s ≤ natIter N 4 := natIter_ge N s hN hs1 3
      have hX4pos : 0 < natIter N 4 := natIter_pos N hN 4
      have hX4le : natIter N 4 ≤ t := stays_le N s t (natIter N 3) hst hs2 hX3ge hX3le hX3pos hspos
      have hX5ge : s ≤ natIter N 5 := natIter_ge N s hN hs1 4
      have hX5pos : 0 < natIter N 5 := natIter_pos N hN 5
      have hX5le : natIter N 5 ≤ t := stays_le N s t (natIter N 4) hst hs2 hX4ge hX4le hX4pos hspos
      have hX6ge : s ≤ natIter N 6 := natIter_ge N s hN hs1 5
      have hX6pos : 0 < natIter N 6 := natIter_pos N hN 6
      have hX6le : natIter N 6 ≤ t := stays_le N s t (natIter N 5) hst hs2 hX5ge hX5le hX5pos hspos
      exact stays_le N s t (natIter N 6) hst hs2 hX6ge hX6le hX6pos hspos
    · -- X2 > t: X2 = t + d1, quad X1->X2
      have hX2lt : t < natIter N 2 := by omega
      have hX2le' : t ≤ natIter N 2 := by omega
      obtain ⟨d1, hd1⟩ := Nat.le.dest hX2le'
      have heq2 : natIter N 2 = t + d1 := by omega
      have hquad1 : 2 * d1 * natIter N 1 + 1 ≤ d0 * d0 :=
        quad_step N (natIter N 1) t d0 d1 hs2 heq1 heq2
      have h32d1 : 32 * d1 ≤ t := step_4_32 t d0 d1 (natIter N 1) htpos hX1Xt h4d0' hquad1
      have hX3ge : s ≤ natIter N 3 := natIter_ge N s hN hs1 2
      have hX3pos : 0 < natIter N 3 := natIter_pos N hN 3
      by_cases hX3le : natIter N 3 ≤ t
      · -- X3 ≤ t: stays to X7 (4 steps)
        have hX4ge : s ≤ natIter N 4 := natIter_ge N s hN hs1 3
        have hX4pos : 0 < natIter N 4 := natIter_pos N hN 4
        have hX4le : natIter N 4 ≤ t := stays_le N s t (natIter N 3) hst hs2 hX3ge hX3le hX3pos hspos
        have hX5ge : s ≤ natIter N 5 := natIter_ge N s hN hs1 4
        have hX5pos : 0 < natIter N 5 := natIter_pos N hN 5
        have hX5le : natIter N 5 ≤ t := stays_le N s t (natIter N 4) hst hs2 hX4ge hX4le hX4pos hspos
        have hX6ge : s ≤ natIter N 6 := natIter_ge N s hN hs1 5
        have hX6pos : 0 < natIter N 6 := natIter_pos N hN 6
        have hX6le : natIter N 6 ≤ t := stays_le N s t (natIter N 5) hst hs2 hX5ge hX5le hX5pos hspos
        exact stays_le N s t (natIter N 6) hst hs2 hX6ge hX6le hX6pos hspos
      · -- X3 > t: X3 = t + d2, quad X2->X3
        have hX3lt : t < natIter N 3 := by omega
        have hX3le' : t ≤ natIter N 3 := by omega
        obtain ⟨d2, hd2⟩ := Nat.le.dest hX3le'
        have heq3 : natIter N 3 = t + d2 := by omega
        have hX2Xt : t ≤ natIter N 2 := by omega
        have hquad2 : 2 * d2 * natIter N 2 + 1 ≤ d1 * d1 :=
          quad_step N (natIter N 2) t d1 d2 hs2 heq2 heq3
        have h2048d2 : 2048 * d2 ≤ t := step_32_2048 t d1 d2 (natIter N 2) htpos hX2Xt h32d1 hquad2
        have hX4ge : s ≤ natIter N 4 := natIter_ge N s hN hs1 3
        have hX4pos : 0 < natIter N 4 := natIter_pos N hN 4
        by_cases hX4le : natIter N 4 ≤ t
        · -- X4 ≤ t: stays to X7 (3 steps)
          have hX5ge : s ≤ natIter N 5 := natIter_ge N s hN hs1 4
          have hX5pos : 0 < natIter N 5 := natIter_pos N hN 5
          have hX5le : natIter N 5 ≤ t := stays_le N s t (natIter N 4) hst hs2 hX4ge hX4le hX4pos hspos
          have hX6ge : s ≤ natIter N 6 := natIter_ge N s hN hs1 5
          have hX6pos : 0 < natIter N 6 := natIter_pos N hN 6
          have hX6le : natIter N 6 ≤ t := stays_le N s t (natIter N 5) hst hs2 hX5ge hX5le hX5pos hspos
          exact stays_le N s t (natIter N 6) hst hs2 hX6ge hX6le hX6pos hspos
        · -- X4 > t: X4 = t + d3, quad X3->X4
          have hX4lt : t < natIter N 4 := by omega
          have hX4le' : t ≤ natIter N 4 := by omega
          obtain ⟨d3, hd3⟩ := Nat.le.dest hX4le'
          have heq4 : natIter N 4 = t + d3 := by omega
          have hX3Xt : t ≤ natIter N 3 := by omega
          have hquad3 : 2 * d3 * natIter N 3 + 1 ≤ d2 * d2 :=
            quad_step N (natIter N 3) t d2 d3 hs2 heq3 heq4
          have h8388608d3 : 8388608 * d3 ≤ t := step_2048_8388608 t d2 d3 (natIter N 3) htpos hX3Xt h2048d2 hquad3
          have hX5ge : s ≤ natIter N 5 := natIter_ge N s hN hs1 4
          have hX5pos : 0 < natIter N 5 := natIter_pos N hN 5
          by_cases hX5le : natIter N 5 ≤ t
          · -- X5 ≤ t: stays to X7 (2 steps)
            have hX6ge : s ≤ natIter N 6 := natIter_ge N s hN hs1 5
            have hX6pos : 0 < natIter N 6 := natIter_pos N hN 6
            have hX6le : natIter N 6 ≤ t := stays_le N s t (natIter N 5) hst hs2 hX5ge hX5le hX5pos hspos
            exact stays_le N s t (natIter N 6) hst hs2 hX6ge hX6le hX6pos hspos
          · -- X5 > t: X5 = t + d4, quad X4->X5
            have hX5lt : t < natIter N 5 := by omega
            have hX5le' : t ≤ natIter N 5 := by omega
            obtain ⟨d4, hd4⟩ := Nat.le.dest hX5le'
            have heq5 : natIter N 5 = t + d4 := by omega
            have hX4Xt : t ≤ natIter N 4 := by omega
            have hquad4 : 2 * d4 * natIter N 4 + 1 ≤ d3 * d3 :=
              quad_step N (natIter N 4) t d3 d4 hs2 heq4 heq5
            have h2pow47d4 : 2 ^ 47 * d4 ≤ t :=
              step_8388608_2pow47 t d3 d4 (natIter N 4) htpos hX4Xt h8388608d3 hquad4
            have hX6ge : s ≤ natIter N 6 := natIter_ge N s hN hs1 5
            have hX6pos : 0 < natIter N 6 := natIter_pos N hN 6
            by_cases hX6le : natIter N 6 ≤ t
            · -- X6 ≤ t: stays to X7 (1 step)
              exact stays_le N s t (natIter N 6) hst hs2 hX6ge hX6le hX6pos hspos
            · -- X6 > t: X6 = t + d5, quad X5->X6, then X7
              have hX6lt : t < natIter N 6 := by omega
              have hX6le' : t ≤ natIter N 6 := by omega
              obtain ⟨d5, hd5⟩ := Nat.le.dest hX6le'
              have heq6 : natIter N 6 = t + d5 := by omega
              have hX5Xt : t ≤ natIter N 5 := by omega
              have hquad5 : 2 * d5 * natIter N 5 + 1 ≤ d4 * d4 :=
                quad_step N (natIter N 5) t d4 d5 hs2 heq5 heq6
              have h2pow95d5 : 2 ^ 95 * d5 ≤ t :=
                step_2pow47_2pow95 t d4 d5 (natIter N 5) htpos hX5Xt h2pow47d4 hquad5
              have hX7ge : s ≤ natIter N 7 := natIter_ge N s hN hs1 6
              have hX7pos : 0 < natIter N 7 := natIter_pos N hN 7
              by_cases hX7le : natIter N 7 ≤ t
              · exact hX7le
              · -- X7 > t: X7 = t + d6, quad X6->X7, then 2^191*d6 ≤ t forces d6 = 0
                have hX7lt : t < natIter N 7 := by omega
                have hX7le' : t ≤ natIter N 7 := by omega
                obtain ⟨d6, hd6⟩ := Nat.le.dest hX7le'
                have heq7 : natIter N 7 = t + d6 := by omega
                have hX6Xt : t ≤ natIter N 6 := by omega
                have hquad6 : 2 * d6 * natIter N 6 + 1 ≤ d5 * d5 :=
                  quad_step N (natIter N 6) t d5 d6 hs2 heq6 heq7
                have h2pow191d6 : 2 ^ 191 * d6 ≤ t :=
                  step_2pow95_2pow191 t d5 d6 (natIter N 6) htpos hX6Xt h2pow95d5 hquad6
                have ht128 : t ≤ 2 ^ 128 := by
                  by_cases hs128 : s < 2 ^ 128
                  · omega
                  · have hge : 2 ^ 128 ≤ s := by omega
                    have hsq : (2 ^ 128) * (2 ^ 128) ≤ s * s := Nat.mul_le_mul hge hge
                    have heq : (2 ^ 128) * (2 ^ 128) = 2 ^ 256 := by
                      rw [← Nat.pow_add]
                    have hle : (2 ^ 128) * (2 ^ 128) ≤ N := by omega
                    omega
                have h128191 : (2 : Nat) ^ 128 < 2 ^ 191 :=
                  Nat.pow_lt_pow_right (by omega) (by omega)
                have hd6pos : 0 < d6 := by omega
                have h1d6 : 1 ≤ d6 := hd6pos
                have hle191 : 2 ^ 191 ≤ 2 ^ 191 * d6 := by
                  have h1 : 2 ^ 191 * 1 ≤ 2 ^ 191 * d6 := Nat.mul_le_mul_left _ h1d6
                  have heq : 2 ^ 191 * 1 = 2 ^ 191 := Nat.mul_one _
                  omega
                have h191t : 2 ^ 191 ≤ t := by omega
                have hfalse : False := by omega
                exact False.elim hfalse
