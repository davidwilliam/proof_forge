import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt
import ProofForgeFin.Rounding

namespace VyperSqrt

open ProofForgeFin.Sqrt

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

/-! ## Nat-level Newton iteration -/

def ANat (a : Nat) : Nat := a * 10 ^ 10

def seedNat (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

def seqAux (A s : Nat) : Nat → Nat
  | 0 => s
  | n + 1 => newton A (seqAux A s n)

def seqNat (a : Nat) (n : Nat) : Nat := seqAux (ANat a) (seedNat a) n

/-! ## Seed bounds over a variable scale -/

theorem seed_aux_gen (a b D C0 : Nat) (h2C : 2 * C0 = D) (hle : a ≤ 2 * b + 1) :
    (b + C0 + 1) * (b + C0 + 1) > a * D := by
  have hAMGM : 4 * b * C0 ≤ (b + C0) * (b + C0) := four_mul_le_sq b C0
  have hexp : (b + C0 + 1) * (b + C0 + 1)
      = (b + C0) * (b + C0) + (2 * (b + C0) + 1) := by grind
  have h1 : (2 * b + 1) * D = 2 * b * D + D := by grind
  have h2 : 2 * b * D = 2 * b * (2 * C0) := by rw [h2C]
  have h3 : 2 * b * (2 * C0) = 4 * b * C0 := by grind
  have hmul : a * D ≤ (2 * b + 1) * D := Nat.mul_le_mul_right _ hle
  omega

theorem sqrt_le_seed_gen (a b D C0 : Nat)
    (hgt : (b + C0 + 1) * (b + C0 + 1) > a * D) :
    (a * D).sqrt ≤ b + C0 := by
  have hlt : (a * D).sqrt < b + C0 + 1 := sqrt_lt_of_lt_mul_self hgt
  exact Nat.le_of_lt_succ hlt

theorem sqrt_le_seed_inst (a : Nat) : (a * 10 ^ 10).sqrt ≤ a / 2 + 5 * 10 ^ 9 := by
  have h2C : 2 * (5 * 10 ^ 9) = 10 ^ 10 := by decide
  have hle : a ≤ 2 * (a / 2) + 1 := by omega
  have hgt := seed_aux_gen a (a / 2) (10 ^ 10) (5 * 10 ^ 9) h2C hle
  exact sqrt_le_seed_gen a (a / 2) (10 ^ 10) (5 * 10 ^ 9) hgt

theorem seedNat_pos (a : Nat) : 0 < seedNat a := by
  unfold seedNat
  have h : 0 < 5 * 10 ^ 9 := by decide
  omega

theorem ANat_pos_gen (a D : Nat) (ha : 0 < a) (hD : 0 < D) : 0 < a * D :=
  Nat.mul_pos ha hD

theorem ANat_pos (a : Nat) (ha : 0 < a) : 0 < ANat a := by
  unfold ANat
  have hD : 0 < 10 ^ 10 := by decide
  exact Nat.mul_pos ha hD

theorem sqrt_pos_inst (a : Nat) (ha : 0 < a) : 0 < (ANat a).sqrt := by
  unfold ANat
  apply sqrt_pos
  have hD : 0 < 10 ^ 10 := by decide
  exact Nat.mul_pos ha hD

theorem sqrt_le_seedNat (a : Nat) : (ANat a).sqrt ≤ seedNat a := by
  unfold ANat seedNat
  exact sqrt_le_seed_inst a

/-! ## Basic seq properties -/

theorem seqAux_pos_gen (A s0 : Nat) (hs : 0 < A.sqrt) (hs0 : 0 < s0)
    (hle : A.sqrt ≤ s0) (n : Nat) : 0 < seqAux A s0 n ∧ A.sqrt ≤ seqAux A s0 n := by
  induction n with
  | zero => exact ⟨hs0, hle⟩
  | succ k ih =>
    have hkpos : 0 < seqAux A s0 k := ih.1
    have hge : A.sqrt ≤ newton A (seqAux A s0 k) := sqrt_le_newton hkpos
    have hpos : 0 < newton A (seqAux A s0 k) := Nat.lt_of_lt_of_le hs hge
    exact ⟨hpos, hge⟩

theorem seqNat_pos (a : Nat) (ha : 0 < a) (n : Nat) : 0 < seqNat a n := by
  unfold seqNat
  have hs : 0 < (ANat a).sqrt := sqrt_pos_inst a ha
  have hs0 : 0 < seedNat a := seedNat_pos a
  have hle : (ANat a).sqrt ≤ seedNat a := sqrt_le_seedNat a
  exact (seqAux_pos_gen (ANat a) (seedNat a) hs hs0 hle n).1

theorem seqNat_ge (a : Nat) (ha : 0 < a) (n : Nat) :
    (ANat a).sqrt ≤ seqNat a n := by
  unfold seqNat
  have hs : 0 < (ANat a).sqrt := sqrt_pos_inst a ha
  have hs0 : 0 < seedNat a := seedNat_pos a
  have hle : (ANat a).sqrt ≤ seedNat a := sqrt_le_seedNat a
  exact (seqAux_pos_gen (ANat a) (seedNat a) hs hs0 hle n).2

theorem Adiv_le_gen (A x s : Nat) (hsx : s ≤ x)
    (hA : A ≤ s * s + 2 * s) : A / x ≤ s + 2 := by
  have h3 : (s + 2) * s = s * s + 2 * s := by grind
  have h2 : (s + 2) * s ≤ (s + 2) * x := Nat.mul_le_mul_left _ hsx
  have h1 : A ≤ x * (s + 2) := by
    have h4 : (s + 2) * x = x * (s + 2) := Nat.mul_comm _ _
    omega
  exact Nat.div_le_of_le_mul h1

theorem Alat_gen (A s : Nat) (hlt : A < (s + 1) * (s + 1)) :
    A ≤ s * s + 2 * s := by
  have hexp : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by grind
  omega

theorem Adiv_le_inst (a x : Nat) (hsx : (ANat a).sqrt ≤ x) :
    ANat a / x ≤ (ANat a).sqrt + 2 := by
  apply Adiv_le_gen _ _ _ hsx
  apply Alat_gen
  exact Nat.lt_succ_sqrt _

theorem seqAux_le_all_gen (A s0 : Nat) (hs : 0 < A.sqrt) (hs0 : 0 < s0)
    (hle : A.sqrt ≤ s0) (hA : A ≤ A.sqrt * A.sqrt + 2 * A.sqrt) (n : Nat) :
    seqAux A s0 n ≤ s0 + 1 := by
  induction n with
  | zero => exact Nat.le_succ _
  | succ k ih =>
    have hkpos : 0 < seqAux A s0 k :=
      (seqAux_pos_gen A s0 hs hs0 hle k).1
    have hks : A.sqrt ≤ seqAux A s0 k :=
      (seqAux_pos_gen A s0 hs hs0 hle k).2
    have hdiv : A / seqAux A s0 k ≤ A.sqrt + 2 :=
      Adiv_le_gen A _ _ hks hA
    have hadd : seqAux A s0 k + A / seqAux A s0 k
        ≤ (s0 + 1) + (A.sqrt + 2) := Nat.add_le_add ih hdiv
    have hdiv2 : (seqAux A s0 k + A / seqAux A s0 k) / 2
        ≤ ((s0 + 1) + (A.sqrt + 2)) / 2 := Nat.div_le_div_right hadd
    have hle2 : ((s0 + 1) + (A.sqrt + 2)) / 2 ≤ s0 + 1 := by omega
    have heq : seqAux A s0 (k + 1)
        = (seqAux A s0 k + A / seqAux A s0 k) / 2 := rfl
    omega

theorem seqNat_le1 (a : Nat) (ha : 0 < a) (n : Nat) :
    seqNat a n ≤ seedNat a + 1 := by
  unfold seqNat
  exact seqAux_le_all_gen (ANat a) (seedNat a)
    (sqrt_pos_inst a ha) (seedNat_pos a) (sqrt_le_seedNat a)
    (Alat_gen _ _ (Nat.lt_succ_sqrt _)) n

/-! ## Halving error bound -/

theorem seqAux_err_gen (A s0 m : Nat) (hs : 0 < A.sqrt) (hs0 : 0 < s0)
    (hle : A.sqrt ≤ s0) (h0 : s0 - A.sqrt ≤ 2 ^ m + 2) (k : Nat) (hkm : k ≤ m) :
    seqAux A s0 k - A.sqrt ≤ 2 ^ (m - k) + 2 := by
  induction k with
  | zero =>
    have hm : m - 0 = m := Nat.sub_zero m
    rw [hm]
    simpa [seqAux] using h0
  | succ k ih =>
    have hkle : k ≤ m := by omega
    have hkpos : 0 < seqAux A s0 k :=
      (seqAux_pos_gen A s0 hs hs0 hle k).1
    have hks : A.sqrt ≤ seqAux A s0 k :=
      (seqAux_pos_gen A s0 hs hs0 hle k).2
    have hIH := ih hkle
    have hmt : m - (k + 1) + 1 = m - k := by omega
    have hpow : 2 ^ (m - k) = 2 * 2 ^ (m - (k + 1)) := by
      rw [← hmt]
      grind
    have hhalf : newton A (seqAux A s0 k) - A.sqrt
        ≤ (seqAux A s0 k - A.sqrt) / 2 + 1 :=
      newton_sub_sqrt_le_half hkpos hks
    have hdiv : (seqAux A s0 k - A.sqrt) / 2 ≤ (2 ^ (m - k) + 2) / 2 :=
      Nat.div_le_div_right (by omega)
    have hdiv2 : (2 ^ (m - k) + 2) / 2 = 2 ^ (m - (k + 1)) + 1 := by
      rw [hpow]
      grind
    have heq : seqAux A s0 (k + 1) = newton A (seqAux A s0 k) := rfl
    omega

theorem newton_le_succ_gen (A x : Nat) (hx : 0 < x)
    (hle : A.sqrt ≤ x) (he : x - A.sqrt ≤ 2) (hs2 : 2 ≤ A.sqrt) :
    newton A x ≤ A.sqrt + 1 := by
  apply newton_le_sqrt_add_one hx hle
  have he2 : (x - A.sqrt) * (x - A.sqrt) ≤ 2 * 2 :=
    Nat.mul_le_mul he he
  have h4 : 2 * 2 ≤ 2 * A.sqrt := by omega
  omega

theorem newton_mem_le_gen (A x : Nat) (hx : 0 < x)
    (h1 : A.sqrt ≤ x) (h2 : x ≤ A.sqrt + 1) :
    newton A x ≤ A.sqrt + 1 ∧ A.sqrt ≤ newton A x := by
  have hge : A.sqrt ≤ newton A x := sqrt_le_newton hx
  have hmem := newton_of_mem hx h1 h2
  have hle : newton A x ≤ A.sqrt + 1 := by
    rcases hmem with h | ⟨_, h, _⟩
    · omega
    · omega
  exact ⟨hle, hge⟩

theorem seqAux_stay_gen (A s0 K : Nat) (hs : 0 < A.sqrt) (hs0 : 0 < s0)
    (hle : A.sqrt ≤ s0)
    (hKle : seqAux A s0 K ≤ A.sqrt + 1) (j : Nat) :
    seqAux A s0 (K + j) ≤ A.sqrt + 1 ∧ A.sqrt ≤ seqAux A s0 (K + j) := by
  induction j with
  | zero =>
    have hKge : A.sqrt ≤ seqAux A s0 (K + 0) := by
      have hKm : K + 0 = K := Nat.add_zero K
      rw [hKm]
      exact (seqAux_pos_gen A s0 hs hs0 hle K).2
    have hKle0 : seqAux A s0 (K + 0) ≤ A.sqrt + 1 := by
      have hKm : K + 0 = K := Nat.add_zero K
      rw [hKm]
      exact hKle
    exact ⟨hKle0, hKge⟩
  | succ j ih =>
    have hKj : K + (j + 1) = (K + j) + 1 := by omega
    rw [hKj]
    have hpos : 0 < seqAux A s0 (K + j) := by
      have hge := ih.2
      have hle0 := ih.1
      have hKjj : K + j = K + j := rfl
      have h1 : 0 < A.sqrt := hs
      omega
    have hmem := newton_mem_le_gen A (seqAux A s0 (K + j)) hpos ih.2 ih.1
    have heq : seqAux A s0 ((K + j) + 1) = newton A (seqAux A s0 (K + j)) := rfl
    rw [heq]
    exact hmem

/-! ## Absolute lower bound for the root -/

theorem sqrt_ge100k_gen (A : Nat) (hA : 100000 * 100000 ≤ A) :
    100000 ≤ A.sqrt := le_sqrt_of_mul_self_le hA

theorem sqrt_ge_100000 (a : Nat) (ha : 0 < a) : 100000 ≤ (ANat a).sqrt := by
  apply sqrt_ge100k_gen
  unfold ANat
  have h100 : 100000 * 100000 = 10 ^ 10 := by decide
  have hle : 10 ^ 10 ≤ a * 10 ^ 10 := Nat.le_mul_of_pos_left _ ha
  omega

theorem seedNat_lt_2pow167 (a : Nat) (haM : a ≤ 2 ^ 167 - 1) :
    seedNat a < 2 ^ 167 := by
  have hle : seedNat a ≤ 2 ^ 167 - 1 := by
    unfold seedNat
    have h4 : a / 2 + 5 * 10 ^ 9 ≤ 2 ^ 167 - 1 := by
      have hdiv : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right haM
      have hclose : (2 ^ 167 - 1) / 2 + 5 * 10 ^ 9 ≤ 2 ^ 167 - 1 := by decide
      exact Nat.le_trans (Nat.add_le_add_right hdiv _) hclose
    exact h4
  exact Nat.lt_of_le_of_lt hle (by decide : 2 ^ 167 - 1 < 2 ^ 167)

theorem seqNat_err167 (a : Nat) (ha : 0 < a) (haM : a ≤ 2 ^ 167 - 1) :
    seqNat a 167 - (ANat a).sqrt ≤ 2 ^ (167 - 167) + 2 := by
  have hs : 0 < (ANat a).sqrt := sqrt_pos_inst a ha
  have hs0 : 0 < seedNat a := seedNat_pos a
  have hle : (ANat a).sqrt ≤ seedNat a := sqrt_le_seedNat a
  have hseed : seedNat a < 2 ^ 167 := seedNat_lt_2pow167 a haM
  have h0 : seedNat a - (ANat a).sqrt ≤ 2 ^ 167 + 2 := by
    have hsub : seedNat a - (ANat a).sqrt ≤ seedNat a := Nat.sub_le _ _
    have hlt : seedNat a ≤ 2 ^ 167 := Nat.le_of_lt hseed
    have hadd : (2 : Nat) ^ 167 ≤ 2 ^ 167 + 2 := Nat.le_add_right _ _
    exact Nat.le_trans (Nat.le_trans hsub hlt) hadd
  have hkm : 167 ≤ 167 := Nat.le_refl _
  have h := seqAux_err_gen (ANat a) (seedNat a) 167 hs hs0 hle h0 167 hkm
  simpa [seqNat] using h

theorem seqNat_167_le3 (a : Nat) (ha : 0 < a) (haM : a ≤ 2 ^ 167 - 1) :
    seqNat a 167 - (ANat a).sqrt ≤ 3 := by
  have h := seqNat_err167 a ha haM
  have h0 : 167 - 167 = 0 := Nat.sub_self _
  have h1 : (2 : Nat) ^ (167 - 167) = 1 := by
    rw [h0]
  omega

theorem seqNat_168_le2 (a : Nat) (ha : 0 < a) (haM : a ≤ 2 ^ 167 - 1) :
    seqNat a 168 - (ANat a).sqrt ≤ 2 := by
  have hge167 : (ANat a).sqrt ≤ seqNat a 167 := seqNat_ge a ha 167
  have hpos167 : 0 < seqNat a 167 := seqNat_pos a ha 167
  have h3 := seqNat_167_le3 a ha haM
  have hhalf : newton (ANat a) (seqNat a 167) - (ANat a).sqrt
      ≤ (seqNat a 167 - (ANat a).sqrt) / 2 + 1 :=
    newton_sub_sqrt_le_half hpos167 hge167
  have hdiv : (seqNat a 167 - (ANat a).sqrt) / 2 ≤ 3 / 2 :=
    Nat.div_le_div_right (by omega)
  have heq : seqNat a 168 = newton (ANat a) (seqNat a 167) := rfl
  omega

theorem seqNat_step (a k : Nat) (hk : 1 ≤ k) :
    seqNat a k = newton (ANat a) (seqNat a (k - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp [seqNat, seqAux]

theorem seqNat_169_le1 (a : Nat) (ha : 0 < a) (haM : a ≤ 2 ^ 167 - 1) :
    seqNat a 169 ≤ (ANat a).sqrt + 1 := by
  have hge168 : (ANat a).sqrt ≤ seqNat a 168 := seqNat_ge a ha 168
  have hpos168 : 0 < seqNat a 168 := seqNat_pos a ha 168
  have he2 := seqNat_168_le2 a ha haM
  have hs2 : 2 ≤ (ANat a).sqrt := by
    have h100 := sqrt_ge_100000 a ha
    omega
  have h := newton_le_succ_gen (ANat a) (seqNat a 168) hpos168 hge168 he2 hs2
  have heq : seqNat a 169 = newton (ANat a) (seqNat a 168) := by
    have h1 := seqNat_step a 169 (by omega)
    have hsub : 169 - 1 = 168 := by decide
    rw [hsub] at h1
    exact h1
  omega

theorem seqNat_stay (a : Nat) (ha : 0 < a) (haM : a ≤ 2 ^ 167 - 1) (j : Nat) :
    seqNat a (169 + j) ≤ (ANat a).sqrt + 1
    ∧ (ANat a).sqrt ≤ seqNat a (169 + j) := by
  have hs : 0 < (ANat a).sqrt := sqrt_pos_inst a ha
  have hs0 : 0 < seedNat a := seedNat_pos a
  have hle : (ANat a).sqrt ≤ seedNat a := sqrt_le_seedNat a
  have hKle : seqAux (ANat a) (seedNat a) 169 ≤ (ANat a).sqrt + 1 := by
    have h := seqNat_169_le1 a ha haM
    simpa [seqNat] using h
  have h := seqAux_stay_gen (ANat a) (seedNat a) 169 hs hs0 hle hKle j
  simpa [seqNat] using h

theorem M_le_2x_gen (M x : Nat) (h : M / 2 < x) : M ≤ 2 * x := by
  have h1 : M ≤ 2 * (M / 2) + 1 := by omega
  have h2 : 2 * (M / 2) < 2 * x := Nat.mul_lt_mul_of_pos_left h (by decide : 0 < 2)
  omega

theorem Adiv_le_2D_gen (a D x M : Nat) (haM : a ≤ M) (hM2x : M ≤ 2 * x)
    (_hx : 0 < x) (_hD : 0 < D) : a * D / x ≤ 2 * D := by
  have h1 : a * D ≤ M * D := Nat.mul_le_mul_right _ haM
  have h2 : M * D ≤ 2 * x * D := Nat.mul_le_mul_right _ hM2x
  have h3 : 2 * x * D = x * (2 * D) := by grind
  have h4 : M * D ≤ x * (2 * D) := by
    have h5 : 2 * x * D = x * (2 * D) := by grind
    omega
  have h6 : a * D ≤ x * (2 * D) := Nat.le_trans h1 h4
  exact Nat.div_le_of_le_mul h6

theorem Adiv_le_add_gen (A x : Nat) (hsx : A.sqrt ≤ x) :
    A / x ≤ x + 2 := by
  have hlt : A < (x + 1) * (x + 1) := by
    have h1 : A < (A.sqrt + 1) * (A.sqrt + 1) := Nat.lt_succ_sqrt _
    have h2 : (A.sqrt + 1) * (A.sqrt + 1) ≤ (x + 1) * (x + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hexp : (x + 1) * (x + 1) = x * x + 2 * x + 1 := by grind
  have hle : A ≤ x * x + 2 * x := by omega
  have h1 : A ≤ x * (x + 2) := by
    have heq : x * (x + 2) = x * x + 2 * x := by grind
    omega
  exact Nat.div_le_of_le_mul h1

theorem sum_le_MAX (a x : Nat) (_ha : 0 < a) (haM : a ≤ 2 ^ 167 - 1)
    (hsx : (ANat a).sqrt ≤ x) (hxle : x ≤ seedNat a + 1)
    (hxpos : 0 < x) :
    ANat a / x + x ≤ 2 ^ 167 - 1 := by
  by_cases hbig : (2 ^ 167 - 1) / 2 < x
  · have hM2x : (2 ^ 167 - 1) ≤ 2 * x :=
      M_le_2x_gen (2 ^ 167 - 1) x hbig
    have hDpos : 0 < 10 ^ 10 := by decide
    have hdiv : ANat a / x ≤ 2 * 10 ^ 10 := by
      unfold ANat
      exact Adiv_le_2D_gen a (10 ^ 10) x (2 ^ 167 - 1) haM hM2x hxpos hDpos
    have hseed : seedNat a + 1 ≤ (2 ^ 167 - 1) / 2 + (5 * 10 ^ 9 + 1) := by
      unfold seedNat
      have hdiv2 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right haM
      have hadd : a / 2 + 5 * 10 ^ 9 + 1
          ≤ (2 ^ 167 - 1) / 2 + 5 * 10 ^ 9 + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_right hdiv2 _) _
      have heq : a / 2 + 5 * 10 ^ 9 + 1 = a / 2 + (5 * 10 ^ 9 + 1) :=
        Nat.add_assoc _ _ _
      have heq2 : (2 ^ 167 - 1) / 2 + 5 * 10 ^ 9 + 1
          = (2 ^ 167 - 1) / 2 + (5 * 10 ^ 9 + 1) :=
        Nat.add_assoc _ _ _
      rw [heq, heq2] at hadd
      exact hadd
    have hsum : ANat a / x + x ≤ (2 * 10 ^ 10) + (seedNat a + 1) :=
      Nat.add_le_add hdiv hxle
    have hclose : (2 * 10 ^ 10) + ((2 ^ 167 - 1) / 2 + (5 * 10 ^ 9 + 1))
        ≤ 2 ^ 167 - 1 := by decide
    have hle : (2 * 10 ^ 10) + (seedNat a + 1)
        ≤ (2 * 10 ^ 10) + ((2 ^ 167 - 1) / 2 + (5 * 10 ^ 9 + 1)) :=
      Nat.add_le_add_left hseed _
    exact Nat.le_trans (Nat.le_trans hsum hle) hclose
  · have hleM2 : x ≤ (2 ^ 167 - 1) / 2 := Nat.le_of_not_gt hbig
    by_cases h2D : 2 * 10 ^ 10 ≤ x
    · have hDpos : 0 < 10 ^ 10 := by decide
      have h2Dpos : 0 < 2 * 10 ^ 10 := by decide
      have hanti : ANat a / x ≤ ANat a / (2 * 10 ^ 10) :=
        ProofForgeFin.div_anti_right _ h2Dpos h2D
      have hcancel : ANat a / (2 * 10 ^ 10) = a / 2 := by
        unfold ANat
        exact Nat.mul_div_mul_right _ _ (by decide : 0 < 10 ^ 10)
      have hdiv : ANat a / x ≤ a / 2 := by
        rw [hcancel] at hanti
        exact hanti
      have hdiv2 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right haM
      have hdiv3 : ANat a / x ≤ (2 ^ 167 - 1) / 2 :=
        Nat.le_trans hdiv hdiv2
      have hsum : ANat a / x + x ≤ (2 ^ 167 - 1) / 2 + (2 ^ 167 - 1) / 2 :=
        Nat.add_le_add hdiv3 hleM2
      have h2mul : (2 ^ 167 - 1) / 2 + (2 ^ 167 - 1) / 2 ≤ 2 ^ 167 - 1 := by
        have hself : (2 ^ 167 - 1) / 2 * 2 ≤ 2 ^ 167 - 1 :=
          Nat.div_mul_le_self _ _
        have heq : (2 ^ 167 - 1) / 2 + (2 ^ 167 - 1) / 2
            = (2 ^ 167 - 1) / 2 * 2 := by grind
        rw [heq]
        exact hself
      exact Nat.le_trans hsum h2mul
    · have hlt2D : x < 2 * 10 ^ 10 := Nat.lt_of_not_ge h2D
      have hdiv : ANat a / x ≤ x + 2 := Adiv_le_add_gen _ _ hsx
      have hsum : ANat a / x + x ≤ (x + 2) + x :=
        Nat.add_le_add hdiv (Nat.le_refl _)
      have heq : (x + 2) + x = 2 * x + 2 := by grind
      have hlt : 2 * x + 2 < 4 * 10 ^ 10 + 2 := by
        have h2x : 2 * x < 2 * (2 * 10 ^ 10) :=
          Nat.mul_lt_mul_of_pos_left hlt2D (by decide : 0 < 2)
        have heq2 : 2 * (2 * 10 ^ 10) = 4 * 10 ^ 10 := by grind
        rw [heq2] at h2x
        exact Nat.add_lt_add_right h2x _
      have hclose : 4 * 10 ^ 10 + 2 ≤ 2 ^ 167 - 1 := by decide
      have hle : (x + 2) + x ≤ 4 * 10 ^ 10 + 2 := by
        rw [heq]
        exact Nat.le_of_lt hlt
      exact Nat.le_trans (Nat.le_trans hsum hle) hclose

def nloop (A : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, y, z => (y, z)
  | n + 1, y, z => if z = y then (y, z) else nloop A n z (newton A z)

theorem nloop_zero (A y z : Nat) : nloop A 0 y z = (y, z) := rfl

theorem nloop_succ_stop (A n y : Nat) :
    nloop A (n + 1) y y = (y, y) := by
  simp [nloop]

theorem nloop_min_eq (a : Nat) (ha : 0 < a) (haM : a ≤ 2 ^ 167 - 1)
    (f k : Nat) (hk1 : 1 ≤ k) (hkf : 170 ≤ k + f) :
    min (nloop (ANat a) f (seqNat a (k - 1)) (seqNat a k)).1
      (nloop (ANat a) f (seqNat a (k - 1)) (seqNat a k)).2
      = (ANat a).sqrt := by
  induction f generalizing k with
  | zero =>
    obtain ⟨j1, rfl⟩ : ∃ j, k = 169 + (j + 1) := ⟨k - 170, by omega⟩
    have hk1sub : 169 + (j1 + 1) - 1 = 169 + j1 := by omega
    have h1 := (seqNat_stay a ha haM j1).1
    have h1ge := (seqNat_stay a ha haM j1).2
    have h2 := (seqNat_stay a ha haM (j1 + 1)).1
    have hpos : 0 < seqNat a (169 + j1) := seqNat_pos a ha _
    have hstep : seqNat a (169 + (j1 + 1)) = newton (ANat a) (seqNat a (169 + j1)) := by
      have h169 : 169 + (j1 + 1) = (169 + j1) + 1 := by omega
      have h1le : 1 ≤ 169 + (j1 + 1) := by omega
      have hs := seqNat_step a (169 + (j1 + 1)) h1le
      have hsub : 169 + (j1 + 1) - 1 = 169 + j1 := by omega
      rw [hsub] at hs
      rw [h169]
      exact hs
    have hkm1 : 169 + (j1 + 1) - 1 = 169 + j1 := by omega
    simp [nloop, hkm1]
    have hmin := min_newton_eq_sqrt hpos h1ge h1
    omega
  | succ f ih =>
    by_cases hzy : seqNat a k = seqNat a (k - 1)
    · have hstop : nloop (ANat a) (f + 1) (seqNat a (k - 1)) (seqNat a k)
          = (seqNat a (k - 1), seqNat a k) := by
        simp [nloop, hzy]
      rw [hstop]
      simp only
      have hpos : 0 < seqNat a (k - 1) := seqNat_pos a ha _
      have hstep := seqNat_step a k hk1
      have hfix : newton (ANat a) (seqNat a (k - 1)) = seqNat a (k - 1) := by
        omega
      have hsqrt := eq_sqrt_of_newton_eq_self hpos hfix
      omega
    · have hseq : seqNat a (k + 1) = newton (ANat a) (seqNat a k) := by
        have h1 := seqNat_step a (k + 1) (by omega)
        have hsub : k + 1 - 1 = k := by omega
        rw [hsub] at h1
        exact h1
      have hstep : nloop (ANat a) (f + 1) (seqNat a (k - 1)) (seqNat a k)
          = nloop (ANat a) f (seqNat a k) (seqNat a (k + 1)) := by
        have hcond : ¬ (seqNat a k = seqNat a (k - 1)) := hzy
        simp [nloop, hcond, hseq]
      rw [hstep]
      have hk1' : 1 ≤ k + 1 := by omega
      have hkf' : 170 ≤ (k + 1) + f := by omega
      exact ih (k + 1) hk1' hkf'

theorem loop_eq_nloop (a : Nat) (ha : 0 < a) (haM : a ≤ 2 ^ 167 - 1)
    (f k : Nat) (hk1 : 1 ≤ k) :
    loop (a : Int) f (seqNat a (k - 1) : Int) (seqNat a k : Int) =
      some (((nloop (ANat a) f (seqNat a (k - 1)) (seqNat a k)).1 : Int),
        ((nloop (ANat a) f (seqNat a (k - 1)) (seqNat a k)).2 : Int)) := by
  induction f generalizing k with
  | zero => rfl
  | succ f ih =>
    by_cases hzy : seqNat a k = seqNat a (k - 1)
    · have hIzy : (seqNat a k : Int) = (seqNat a (k - 1) : Int) := by
        rw [hzy]
      have hnloop : nloop (ANat a) (f + 1) (seqNat a (k - 1)) (seqNat a k)
          = (seqNat a (k - 1), seqNat a k) := by
        simp [nloop, hzy]
      simp [loop, hIzy, hnloop]
    · have hIzy : ¬ (seqNat a k : Int) = (seqNat a (k - 1) : Int) := by
        intro hcon
        apply hzy
        exact Int.ofNat.inj hcon
      have hzpos : 0 < seqNat a k := seqNat_pos a ha _
      have hge : (ANat a).sqrt ≤ seqNat a k := seqNat_ge a ha _
      have hle : seqNat a k ≤ seedNat a + 1 := seqNat_le1 a ha _
      have hsum : a * 10 ^ 10 / seqNat a k + seqNat a k ≤ 2 ^ 167 - 1 := by
        have hAN : a * 10 ^ 10 = ANat a := rfl
        rw [hAN]
        exact sum_le_MAX a (seqNat a k) ha haM hge hle hzpos
      have hne : seqNat a k ≠ seqNat a (k - 1) := hzy
      have hloop_step := loop_step (a := a) (y := seqNat a (k - 1))
        (z := seqNat a k) f hzpos hne hsum
      have hseq : seqNat a (k + 1) = newton (ANat a) (seqNat a k) := by
        have h1 := seqNat_step a (k + 1) (by omega)
        have hsub : k + 1 - 1 = k := by omega
        rw [hsub] at h1
        exact h1
      have hnewton_eq : (a * 10 ^ 10 / seqNat a k + seqNat a k) / 2
          = seqNat a (k + 1) := by
        have hAN : a * 10 ^ 10 = ANat a := rfl
        rw [hAN, hseq]
        unfold newton
        have hcomm : ANat a / seqNat a k + seqNat a k
            = seqNat a k + ANat a / seqNat a k := Nat.add_comm _ _
        rw [hcomm]
      have hnloop_step : nloop (ANat a) (f + 1) (seqNat a (k - 1)) (seqNat a k)
          = nloop (ANat a) f (seqNat a k) (seqNat a (k + 1)) := by
        have hcond : ¬ (seqNat a k = seqNat a (k - 1)) := hzy
        simp [nloop, hcond, hseq]
      have hIH := ih (k + 1) (by omega)
      have hsub2 : k + 1 - 1 = k := by omega
      rw [hsub2] at hIH
      rw [hloop_step, hnloop_step, hnewton_eq] at *
      exact hIH

theorem min_cast_eq (y z : Nat) : ((min y z : Nat) : Int)
    = (if (y : Int) < (z : Int) then (y : Int) else (z : Int)) := by
  rcases Nat.lt_or_ge y z with h | h
  · have hI : (y : Int) < (z : Int) := Int.ofNat_lt.mpr h
    have hmin : min y z = y := Nat.min_eq_left (Nat.le_of_lt h)
    simp [hI, hmin]
  · have hI : ¬ (y : Int) < (z : Int) := by
      intro hc
      have := Int.ofNat_lt.mp hc
      omega
    have hmin : min y z = z := Nat.min_eq_right h
    simp [hI, hmin]

theorem sqrt_eq_sqrtNat (a : Nat) (ha : 0 < a) (haM : a ≤ 2 ^ 167 - 1) :
    sqrt (a : Int) = some (((ANat a).sqrt : Nat) : Int) := by
  have hV := vyperSqrtWith_pos (fun y z => if y < z then y else z) ha haM
  have hsqrt_unfold : sqrt (a : Int)
      = vyperSqrtWith (fun y z => if y < z then y else z) (a : Int) := rfl
  rw [hsqrt_unfold, hV]
  show Option.map (fun p => if p.1 < p.2 then p.1 else p.2)
    (loop (a : Int) 256 (a : Int) ((a / 2 + 5 * 10 ^ 9 : Nat) : Int))
    = some (((ANat a).sqrt : Nat) : Int)
  have hseed_eq : ((a / 2 + 5 * 10 ^ 9 : Nat) : Int) = (seedNat a : Int) := rfl
  rw [hseed_eq]
  by_cases heq : seedNat a = a
  · have hIeq : (seedNat a : Int) = (a : Int) := by rw [heq]
    have hloop : loop (a : Int) 256 (a : Int) (seedNat a : Int)
        = some ((a : Int), (a : Int)) := by
      rw [hIeq]
      exact loop_stop (a : Int) 255 (a : Int)
    have hsqrt_eq : a = (ANat a).sqrt := by
      have hsle : (ANat a).sqrt ≤ seedNat a := sqrt_le_seedNat a
      rw [heq] at hsle
      have hble : a / 2 ≤ 5 * 10 ^ 9 := by
        have h1 : a = a / 2 + 5 * 10 ^ 9 := by
          have : seedNat a = a / 2 + 5 * 10 ^ 9 := rfl
          rw [← this, heq]
        omega
      have hsq : a * a ≤ ANat a := by
        unfold ANat
        have h2C : 2 * (5 * 10 ^ 9) = 10 ^ 10 := by decide
        have hmul : a * a ≤ a * (2 * (5 * 10 ^ 9)) := by
          apply Nat.mul_le_mul_left
          omega
        have hrew : a * (2 * (5 * 10 ^ 9)) = a * 10 ^ 10 := by
          rw [h2C]
        omega
      have hle : a ≤ (ANat a).sqrt := le_sqrt_of_mul_self_le hsq
      exact Nat.le_antisymm hle hsle
    rw [hloop]
    simp only [Option.map_some]
    have hlt : ¬ (a : Int) < (a : Int) := by omega
    have hIf : (if (a : Int) < (a : Int) then (a : Int) else (a : Int)) = (a : Int) :=
      ite_eq_right hlt
    rw [hIf]
    have hcast : (a : Int) = (((ANat a).sqrt : Nat) : Int) :=
      congrArg (fun n : Nat => (n : Int)) hsqrt_eq
    rw [hcast]
  · have hsum0 : a * 10 ^ 10 / seedNat a + seedNat a ≤ 2 ^ 167 - 1 := by
      have hAN : a * 10 ^ 10 = ANat a := rfl
      rw [hAN]
      exact sum_le_MAX a (seedNat a) ha haM (sqrt_le_seedNat a) (Nat.le_succ _) (seedNat_pos a)
    have hfirst : loop (a : Int) 256 (a : Int) (seedNat a : Int)
        = loop (a : Int) 255 (seedNat a : Int) (seqNat a 1 : Int) := by
      have hls := loop_step (a := a) (y := a) (z := seedNat a) 255
        (seedNat_pos a) heq hsum0
      have hseq1 : seqNat a 1 = (a * 10 ^ 10 / seedNat a + seedNat a) / 2 := by
        have h1 := seqNat_step a 1 (by omega)
        have h10 : (1 : Nat) - 1 = 0 := by decide
        rw [h10] at h1
        have h0 : seqNat a 0 = seedNat a := rfl
        rw [h0] at h1
        have hAN : a * 10 ^ 10 = ANat a := rfl
        rw [hAN] at *
        unfold newton at h1
        have hcomm : seedNat a + ANat a / seedNat a
            = ANat a / seedNat a + seedNat a := Nat.add_comm _ _
        omega
      rw [← hseq1] at hls
      exact hls
    have hloop_eq := loop_eq_nloop a ha haM 255 1 (by omega)
    have hmin_eq := nloop_min_eq a ha haM 255 1 (by omega) (by omega)
    have h1sub : (1 : Nat) - 1 = 0 := rfl
    rw [h1sub] at hloop_eq hmin_eq
    have h0N : seqNat a 0 = seedNat a := rfl
    rw [h0N] at hloop_eq hmin_eq
    have hmin_cast := min_cast_eq
      (nloop (ANat a) 255 (seedNat a) (seqNat a 1)).1
      (nloop (ANat a) 255 (seedNat a) (seqNat a 1)).2
    have hmin_eq' : min (nloop (ANat a) 255 (seedNat a) (seqNat a 1)).1
        (nloop (ANat a) 255 (seedNat a) (seqNat a 1)).2
        = (ANat a).sqrt := by
      have h0 : seqNat a 0 = seedNat a := rfl
      rw [← h0]
      exact hmin_eq
    rw [hmin_eq'] at hmin_cast
    have hcast := hmin_cast.symm
    rw [hfirst, hloop_eq]
    simp only [Option.map_some, hcast]

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  unfold SqrtNegReverts
  intro x hx
  unfold sqrt vyperSqrtWith
  simp [hx]

theorem req_deployed_loop : DeployedLoop sqrt := by
  unfold DeployedLoop
  exact ⟨fun y z => if y < z then y else z, fun x => rfl⟩

theorem req_sqrt_total : SqrtTotal sqrt := by
  unfold SqrtTotal
  intro x hx hx0
  by_cases hx00 : x = 0
  · rw [hx00]
    unfold sqrt vyperSqrtWith
    simp
  · have hxpos : 0 < x := by omega
    have haM : x ≤ MAX_DECIMAL := hx.2
    have ha : 0 < x.toNat := by grind
    have hx_eq : ((x.toNat : Nat) : Int) = x := by grind
    have haMnat : x.toNat ≤ 2 ^ 167 - 1 := by
      have hmax : MAX_DECIMAL = ((2 ^ 167 - 1 : Nat) : Int) := max_decimal_eq
      have hle : x ≤ ((2 ^ 167 - 1 : Nat) : Int) := by
        rw [← hmax]
        exact haM
      grind
    have hsqrt := sqrt_eq_sqrtNat x.toNat ha haMnat
    rw [hx_eq] at hsqrt
    rw [hsqrt]
    simp

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  unfold SqrtNotAbove
  intro x r hx hr
  by_cases hx00 : x = 0
  · rw [hx00] at hr ⊢
    unfold sqrt vyperSqrtWith at hr
    simp at hr
    rw [← hr]
    simp [DIVISOR]
  · have hnn : 0 ≤ x := by
      by_cases hneg : x < 0
      · unfold sqrt vyperSqrtWith at hr
        simp [hneg] at hr
      · omega
    have hxpos : 0 < x := by omega
    have ha : 0 < x.toNat := by grind
    have hx_eq : ((x.toNat : Nat) : Int) = x := by grind
    have haMnat : x.toNat ≤ 2 ^ 167 - 1 := by
      have hmax : MAX_DECIMAL = ((2 ^ 167 - 1 : Nat) : Int) := max_decimal_eq
      have hle : x ≤ ((2 ^ 167 - 1 : Nat) : Int) := by
        rw [← hmax]
        exact hx.2
      grind
    have hsqrt := sqrt_eq_sqrtNat x.toNat ha haMnat
    rw [hx_eq] at hsqrt
    rw [hsqrt] at hr
    have hr_eq : r = (((ANat x.toNat).sqrt : Nat) : Int) := by
      simpa using hr.symm
    rw [hr_eq]
    have hNat : (ANat x.toNat).sqrt * (ANat x.toNat).sqrt ≤ ANat x.toNat :=
      Nat.sqrt_le _
    have hcast : (((ANat x.toNat).sqrt * (ANat x.toNat).sqrt : Nat) : Int)
        ≤ ((ANat x.toNat : Nat) : Int) := by grind
    have hAN : ((ANat x.toNat : Nat) : Int) = x * DIVISOR := by
      unfold ANat
      have hD : DIVISOR = ((10 ^ 10 : Nat) : Int) := divisor_eq
      rw [hD]
      have hx2 : x = ((x.toNat : Nat) : Int) := by grind
      rw [hx2]
      grind
    have hrr : ((((ANat x.toNat).sqrt : Nat) : Int)
        * (((ANat x.toNat).sqrt : Nat) : Int))
        = (((ANat x.toNat).sqrt * (ANat x.toNat).sqrt : Nat) : Int) := by grind
    omega

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  unfold SqrtNotBelow
  intro x r hx hr
  by_cases hx00 : x = 0
  · rw [hx00] at hr ⊢
    unfold sqrt vyperSqrtWith at hr
    simp at hr
    rw [← hr]
    simp [DIVISOR]
  · have hnn : 0 ≤ x := by
      by_cases hneg : x < 0
      · unfold sqrt vyperSqrtWith at hr
        simp [hneg] at hr
      · omega
    have hxpos : 0 < x := by omega
    have ha : 0 < x.toNat := by grind
    have hx_eq : ((x.toNat : Nat) : Int) = x := by grind
    have haMnat : x.toNat ≤ 2 ^ 167 - 1 := by
      have hmax : MAX_DECIMAL = ((2 ^ 167 - 1 : Nat) : Int) := max_decimal_eq
      have hle : x ≤ ((2 ^ 167 - 1 : Nat) : Int) := by
        rw [← hmax]
        exact hx.2
      grind
    have hsqrt := sqrt_eq_sqrtNat x.toNat ha haMnat
    rw [hx_eq] at hsqrt
    rw [hsqrt] at hr
    have hr_eq : r = (((ANat x.toNat).sqrt : Nat) : Int) := by
      simpa using hr.symm
    rw [hr_eq]
    have hNat : ANat x.toNat < ((ANat x.toNat).sqrt + 1) * ((ANat x.toNat).sqrt + 1) :=
      Nat.lt_succ_sqrt _
    have hcast : ((ANat x.toNat : Nat) : Int)
        < ((((ANat x.toNat).sqrt + 1) * ((ANat x.toNat).sqrt + 1) : Nat) : Int) := by grind
    have hAN : ((ANat x.toNat : Nat) : Int) = x * DIVISOR := by
      unfold ANat
      have hD : DIVISOR = ((10 ^ 10 : Nat) : Int) := divisor_eq
      rw [hD]
      have hx2 : x = ((x.toNat : Nat) : Int) := by grind
      rw [hx2]
      grind
    have hrr : ((((ANat x.toNat).sqrt : Nat) : Int) + 1)
        * ((((ANat x.toNat).sqrt : Nat) : Int) + 1)
        = ((((ANat x.toNat).sqrt + 1) * ((ANat x.toNat).sqrt + 1) : Nat) : Int) := by grind
    omega

end VyperSqrt
