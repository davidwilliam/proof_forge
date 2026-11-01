import VyperSqrt.Spec
import VyperSqrt.Lemmas

namespace VyperSqrt

theorem sub_mul_add_le_sq (r e : Nat) (h : e ≤ r) : (r - e) * (r + e) ≤ r * r := by
  have hre : r + e = (r - e) + (e + e) := by omega
  rw [hre]
  rw [Nat.mul_add]
  have hr : r = (r - e) + e := by omega
  have hexp : r * r = ((r - e) + e) * ((r - e) + e) := by rw [← hr]
  rw [hexp]
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  rw [Nat.mul_comm ((r - e)) e]
  omega

theorem hq_le_of_hlt (q r e : Nat) (hlt : q + (r + e) < r * 2) : q + e + 1 ≤ r := by
  omega

theorem her_of_hlt (q r e : Nat) (hlt : q + (r + e) < r * 2) : e ≤ r := by
  omega

theorem h1_of_hlt (q r e : Nat) (hlt : q + (r + e) < r * 2) : q + 1 ≤ r - e := by
  omega

theorem newton_ge (S z r : Nat) (hz : 0 < z)
    (hlo : r * r ≤ S) (hzr : r ≤ z) : r ≤ (S / z + z) / 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, z = r + e := ⟨z - r, by omega⟩
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
  by_cases hle : r * 2 ≤ S / (r + e) + (r + e)
  · exact hle
  · have hlt : S / (r + e) + (r + e) < r * 2 := by omega
    have hq_le : S / (r + e) + e + 1 ≤ r := hq_le_of_hlt _ _ _ hlt
    have h_er : e ≤ r := her_of_hlt _ _ _ hlt
    have h1 : S / (r + e) + 1 ≤ r - e := h1_of_hlt _ _ _ hlt
    have hzpos : 0 < r + e := hz
    have hdecomp : (r + e) * (S / (r + e)) + S % (r + e) = S :=
      Nat.div_add_mod S (r + e)
    have hrem : S % (r + e) < r + e := Nat.mod_lt S hzpos
    have hexpand : (r + e) * (S / (r + e)) + (r + e) = (r + e) * (S / (r + e) + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    have hSlt : S < (r + e) * (S / (r + e) + 1) :=
      calc S = (r + e) * (S / (r + e)) + S % (r + e) := hdecomp.symm
        _ < (r + e) * (S / (r + e)) + (r + e) :=
            Nat.add_lt_add_left hrem _
        _ = (r + e) * (S / (r + e) + 1) := hexpand
    have h2 : (S / (r + e) + 1) * (r + e) ≤ (r - e) * (r + e) :=
      Nat.mul_le_mul h1 (Nat.le_refl _)
    have h3 : (r - e) * (r + e) ≤ r * r := sub_mul_add_le_sq r e h_er
    have hcomm : (r + e) * (S / (r + e) + 1) = (S / (r + e) + 1) * (r + e) :=
      Nat.mul_comm _ _
    have h5 : S < r * r :=
      calc S < (r + e) * (S / (r + e) + 1) := hSlt
        _ = (S / (r + e) + 1) * (r + e) := hcomm
        _ ≤ (r - e) * (r + e) := h2
        _ ≤ r * r := h3
    have hcontra : r * r < r * r := Nat.lt_of_le_of_lt hlo h5
    exact False.elim (Nat.lt_irrefl _ hcontra)

theorem div_lt_of_lt_mul_sq (S z r : Nat) (hz : 0 < z)
    (hhi : S < (r + 1) * (r + 1)) (hzr : r + 1 ≤ z) : S / z < z := by
  have h1 : S < z * z := by
    have h2 : (r + 1) * (r + 1) ≤ z * z :=
      Nat.mul_le_mul hzr hzr
    omega
  exact (Nat.div_lt_iff_lt_mul hz).mpr h1

theorem add_div_lt_of (q z : Nat) (h : q < z) : (q + z) / 2 < z := by
  have h2 : q + z < z * 2 := by
    have e : z * 2 = z + z := by rw [Nat.mul_two]
    omega
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr h2

theorem newton_lt (S z r : Nat) (hz : 0 < z)
    (hhi : S < (r + 1) * (r + 1)) (hzr : r + 1 ≤ z) :
    (S / z + z) / 2 < z :=
  add_div_lt_of _ _ (div_lt_of_lt_mul_sq S z r hz hhi hzr)

theorem sle_of_ge2_aux1 (r : Nat) : (r + 1) * (r + 1) = r * r + (r * 2 + 1) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  rw [Nat.mul_two]
  omega

theorem sle_of_ge2_aux2 (r z : Nat) (h : r + 2 ≤ z) : r * (r + 2) ≤ r * z :=
  Nat.mul_le_mul (Nat.le_refl _) h

theorem sle_of_ge2_aux3 (r : Nat) : r * (r + 2) = r * r + r * 2 := by
  rw [Nat.mul_add]

theorem S_le_rz_of_ge2 (S r z : Nat)
    (hhi : S < (r + 1) * (r + 1)) (hz : r + 2 ≤ z) : S ≤ r * z := by
  have e1 : (r + 1) * (r + 1) = r * r + (r * 2 + 1) := sle_of_ge2_aux1 r
  have hSle : S ≤ r * r + r * 2 := by omega
  have e3 : r * (r + 2) = r * r + r * 2 := sle_of_ge2_aux3 r
  have h2 : r * (r + 2) ≤ r * z := sle_of_ge2_aux2 r z hz
  omega

theorem div_le_of_le_mul (S z r : Nat) (hz : 0 < z) (h : S ≤ r * z) : S / z ≤ r := by
  have h2 : S < (r + 1) * z := by
    have e : (r + 1) * z = r * z + z := by rw [Nat.add_mul, Nat.one_mul]
    omega
  have hlt : S / z < r + 1 := (Nat.div_lt_iff_lt_mul hz).mpr h2
  omega

theorem newton_le_avg (S z r : Nat) (hz : 0 < z)
    (hhi : S < (r + 1) * (r + 1)) (hz2 : r + 2 ≤ z) :
    (S / z + z) / 2 ≤ (r + z) / 2 := by
  have hle : S ≤ r * z := S_le_rz_of_ge2 S r z hhi hz2
  have hq : S / z ≤ r := div_le_of_le_mul S z r hz hle
  have hsum : S / z + z ≤ r + z := Nat.add_le_add_right hq _
  exact Nat.div_le_div_right hsum

theorem seed_sq_gt (k : Nat) :
    (2 * k + 1) * 10000000000 < (k + 5000000001) * (k + 5000000001) := by
  by_cases h : 5000000000 ≤ k
  · obtain ⟨d, rfl⟩ : ∃ d, k = 5000000000 + d := ⟨k - 5000000000, by omega⟩
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
    omega
  · have hlt : k < 5000000000 := by omega
    obtain ⟨d, hd⟩ : ∃ d, 5000000000 = k + d := ⟨5000000000 - k, by omega⟩
    have hky : k + 5000000001 = 10000000001 - d := by omega
    rw [hky]
    simp only [Nat.sub_mul, Nat.mul_sub]
    omega

theorem floor_exists (S : Nat) : ∃ r, r * r ≤ S ∧ S < (r + 1) * (r + 1) := by
  induction S with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, h1, h2⟩ := ih
    by_cases h : n + 1 < (r + 1) * (r + 1)
    · exact ⟨r, by omega, h⟩
    · have hle : (r + 1) * (r + 1) ≤ n + 1 := by omega
      have heq : (r + 1) * (r + 1) = n + 1 := by omega
      refine ⟨r + 1, by omega, ?_⟩
      rw [← heq]
      have hlt : r + 1 < r + 1 + 1 := Nat.lt_succ_self _
      have hle2 : r + 1 ≤ r + 1 + 1 := Nat.le_succ _
      have hpos : 0 < r + 1 + 1 := by omega
      have := Nat.mul_lt_mul_of_le_of_lt hle2 hlt hpos
      simpa using this

theorem eq_of_le_ge (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  omega

theorem newton_succ_eq (S r : Nat) (hr : 0 < r)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1)) :
    (S / (r + 1) + (r + 1)) / 2 = r := by
  have hz : 0 < r + 1 := by omega
  have hq_le : S / (r + 1) ≤ r := by
    have h2 : S < (r + 1) * (r + 1) := hhi
    have hlt : S / (r + 1) < r + 1 := (Nat.div_lt_iff_lt_mul hz).mpr h2
    omega
  have hle : (S / (r + 1) + (r + 1)) / 2 ≤ r := by
    have hsum : S / (r + 1) + (r + 1) ≤ r + (r + 1) := Nat.add_le_add_right hq_le _
    have hdiv : (S / (r + 1) + (r + 1)) / 2 ≤ (r + (r + 1)) / 2 :=
      Nat.div_le_div_right hsum
    have heq : (r + (r + 1)) / 2 = r := by omega
    omega
  have hge : r ≤ (S / (r + 1) + (r + 1)) / 2 :=
    newton_ge S (r + 1) r hz hlo (by omega)
  exact eq_of_le_ge _ _ hle hge

theorem newton_at_r_le (S r : Nat) (hr : 0 < r)
    (hhi : S < (r + 1) * (r + 1)) :
    (S / r + r) / 2 ≤ r + 1 := by
  have hz : 0 < r := hr
  have hq_le : S / r ≤ r + 2 := by
    have h2 : S < (r + 3) * r := by
      have e1 : (r + 1) * (r + 1) = r * r + (r * 2 + 1) := sle_of_ge2_aux1 r
      have e2 : (r + 3) * r = r * r + r * 2 + r := by
        simp only [Nat.add_mul]
        omega
      omega
    have hlt : S / r < r + 3 := (Nat.div_lt_iff_lt_mul hz).mpr h2
    omega
  have hsum : S / r + r ≤ (r + 2) + r := Nat.add_le_add_right hq_le _
  have hdiv : (S / r + r) / 2 ≤ ((r + 2) + r) / 2 := Nat.div_le_div_right hsum
  have heq : ((r + 2) + r) / 2 = r + 1 := by omega
  omega

theorem seed_ge_r (a r : Nat)
    (hlo : r * r ≤ a * 10000000000) (hhi : a * 10000000000 < (r + 1) * (r + 1)) :
    r ≤ a / 2 + 5000000000 := by
  have hmod : a % 2 < 2 := Nat.mod_lt _ (by decide)
  have ha : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
  have hseed1 : a / 2 + 5000000000 + 1 = (a / 2) + 5000000001 := by clear hlo hhi; omega
  have hS : a * 10000000000 = (2 * (a / 2) + a % 2) * 10000000000 := by rw [ha]
  have hle1 : 2 * (a / 2) + a % 2 ≤ 2 * (a / 2) + 1 := by clear hlo hhi; omega
  have hle : (2 * (a / 2) + a % 2) * 10000000000 ≤ (2 * (a / 2) + 1) * 10000000000 :=
    Nat.mul_le_mul hle1 (Nat.le_refl _)
  have hsq : (2 * (a / 2) + 1) * 10000000000 < ((a / 2) + 5000000001) * ((a / 2) + 5000000001) :=
    seed_sq_gt _
  have hSlt : a * 10000000000 < ((a / 2) + 5000000001) * ((a / 2) + 5000000001) :=
    calc a * 10000000000 = (2 * (a / 2) + a % 2) * 10000000000 := hS
      _ ≤ (2 * (a / 2) + 1) * 10000000000 := hle
      _ < ((a / 2) + 5000000001) * ((a / 2) + 5000000001) := hsq
  have hseed_eq : a / 2 + 5000000000 + 1 = (a / 2) + 5000000001 := hseed1
  have hSlt2 : a * 10000000000 < (a / 2 + 5000000000 + 1) * (a / 2 + 5000000000 + 1) := by
    rw [hseed_eq]; exact hSlt
  by_cases hle2 : r ≤ a / 2 + 5000000000
  · exact hle2
  · have hlt2 : a / 2 + 5000000000 < r := by clear hlo hhi; omega
    have hle3 : a / 2 + 5000000000 + 1 ≤ r := by clear hlo hhi; omega
    have hsq_le : (a / 2 + 5000000000 + 1) * (a / 2 + 5000000000 + 1) ≤ r * r :=
      Nat.mul_le_mul hle3 hle3
    have hle_mid : (a / 2 + 5000000000 + 1) * (a / 2 + 5000000000 + 1) ≤ a * 10000000000 :=
      Nat.le_trans hsq_le hlo
    have hcontra : (a / 2 + 5000000000 + 1) * (a / 2 + 5000000000 + 1) <
        (a / 2 + 5000000000 + 1) * (a / 2 + 5000000000 + 1) :=
      Nat.lt_of_le_of_lt hle_mid hSlt2
    exact False.elim (Nat.lt_irrefl _ hcontra)

theorem r_pos_of_a_pos (a r : Nat) (ha0 : 0 < a)
    (hlo : r * r ≤ a * 10000000000) (hhi : a * 10000000000 < (r + 1) * (r + 1)) :
    0 < r := by
  by_cases h : 0 < r
  · exact h
  · have hr0 : r = 0 := by clear hlo hhi; omega
    have e1 : (0 + 1) * (0 + 1) = 1 := by decide
    have e2 : (r + 1) * (r + 1) = 1 := by rw [hr0]
    have hhi2 : a * 10000000000 < 1 := by clear hlo; omega
    have h1a : 1 ≤ a := by clear hlo hhi; omega
    have hge : 10000000000 ≤ a * 10000000000 := by
      have h1 : 1 * 10000000000 ≤ a * 10000000000 :=
        Nat.mul_le_mul h1a (Nat.le_refl _)
      have eone : 1 * 10000000000 = 10000000000 := Nat.one_mul _
      clear hlo hhi; omega
    have hcontra : 10000000000 < 1 := Nat.lt_of_le_of_lt hge hhi2
    exact False.elim (absurd hcontra (by decide))

def N (S z : Nat) : Nat := (S / z + z) / 2

def iter (S seed : Nat) : Nat → Nat
  | 0 => seed
  | n + 1 => N S (iter S seed n)

theorem iter_zero (S seed : Nat) : iter S seed 0 = seed := rfl

theorem iter_succ (S seed n : Nat) : iter S seed (n + 1) = N S (iter S seed n) := rfl

theorem avg_eq (r e : Nat) : (r + (r + e)) / 2 = r + e / 2 := by
  have heq : r + (r + e) = e + 2 * r := by omega
  rw [heq]
  rw [Nat.add_mul_div_left e r (by decide : 0 < 2)]
  rw [Nat.add_comm]

theorem iter_ge_r (S seed r : Nat) (hr : 0 < r)
    (hlo : r * r ≤ S) (hseed : r ≤ seed) : ∀ n, r ≤ iter S seed n := by
  intro n
  induction n with
  | zero => simpa [iter_zero] using hseed
  | succ k ih =>
    have hz : 0 < iter S seed k := by clear hlo; omega
    have hge2 := newton_ge S (iter S seed k) r hz hlo ih
    simpa [iter_succ, N] using hge2

theorem iter_le_max (S seed r : Nat) (hr : 0 < r)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1)) (hseed : r ≤ seed) :
    ∀ n, iter S seed n ≤ max seed (r + 1) := by
  have hge : ∀ n, r ≤ iter S seed n := iter_ge_r S seed r hr hlo hseed
  intro n
  induction n with
  | zero => exact Nat.le_max_left _ _
  | succ k ih =>
    have hzk : r ≤ iter S seed k := hge k
    have hz : 0 < iter S seed k := Nat.lt_of_lt_of_le hr hzk
    by_cases h : iter S seed k = r
    · have hNle : N S r ≤ r + 1 := by
        have hle2 := newton_at_r_le S r hr hhi
        simpa [N] using hle2
      have heq : iter S seed (k + 1) = N S r := by
        simp [iter_succ, N, h]
      have hmax : r + 1 ≤ max seed (r + 1) := Nat.le_max_right _ _
      exact Nat.le_trans (Nat.le_trans (Nat.le_of_eq heq) hNle) hmax
    · have hge2 : r + 1 ≤ iter S seed k := by clear hlo hhi ih; omega
      have hlt : N S (iter S seed k) < iter S seed k :=
        newton_lt S (iter S seed k) r hz hhi hge2
      have heq : iter S seed (k + 1) = N S (iter S seed k) := rfl
      have hltmax : N S (iter S seed k) < max seed (r + 1) :=
        Nat.lt_of_lt_of_le hlt ih
      have hle_max : N S (iter S seed k) ≤ max seed (r + 1) :=
        Nat.le_of_lt hltmax
      exact Nat.le_trans (Nat.le_of_eq heq) hle_max

theorem err_half_aux1 (e : Nat) : 2 * (e / 2) ≤ e := by
  have h := Nat.div_add_mod e 2
  omega

theorem newton_err_half (S z r : Nat) (hr : 0 < r) (hz : 0 < z)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1))
    (hzr : r ≤ z) (hz2 : r + 2 ≤ z) :
    (N S z - r) * 2 ≤ z - r := by
  obtain ⟨e, he⟩ : ∃ e, z = r + e := ⟨z - r, by omega⟩
  have he2 : 2 ≤ e := by clear hlo hhi; omega
  have hNle : N S z ≤ (r + z) / 2 := newton_le_avg S z r hz hhi hz2
  have hNge : r ≤ N S z := newton_ge S z r hz hlo hzr
  have havg : (r + z) / 2 = r + e / 2 := by
    rw [he]
    exact avg_eq r e
  have hNle2 : N S z ≤ r + e / 2 := by omega
  have hsub1 : N S z - r ≤ e / 2 := by
    have h1 : N S z = r + (N S z - r) := by
      have := Nat.sub_add_cancel hNge
      omega
    omega
  have h2 : 2 * (N S z - r) ≤ 2 * (e / 2) :=
    Nat.mul_le_mul (Nat.le_refl _) hsub1
  have h3 : 2 * (e / 2) ≤ e := err_half_aux1 e
  have hz_eq : z - r = e := by rw [he]; omega
  omega

theorem le_one_cases (e : Nat) (h : e ≤ 1) : e = 0 ∨ e = 1 := by
  omega

theorem newton_stay1 (S r : Nat) (hr : 0 < r)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1)) :
    N S r ≤ r + 1 :=
  newton_at_r_le S r hr hhi

theorem newton_stay (S z r : Nat) (hr : 0 < r) (hz : 0 < z)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1))
    (hzr : r ≤ z) (hle1 : z ≤ r + 1) : N S z ≤ r + 1 ∧ r ≤ N S z := by
  have hNge : r ≤ N S z := newton_ge S z r hz hlo hzr
  have hle : N S z ≤ r + 1 := by
    by_cases h : z = r
    · have h1 : N S z = N S r := by rw [h]
      have h2 : N S r ≤ r + 1 := newton_stay1 S r hr hlo hhi
      omega
    · have hge2 : r + 1 ≤ z := by clear hlo hhi; omega
      have heq : z = r + 1 := by clear hlo hhi; omega
      have heq2 : N S z = N S (r + 1) := by rw [heq]
      have hN : N S (r + 1) = r := newton_succ_eq S r hr hlo hhi
      omega
  exact ⟨hle, hNge⟩

theorem iter_stay_step (S seed r : Nat) (hr : 0 < r)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1)) (hseed : r ≤ seed)
    (k : Nat) (hk : iter S seed k ≤ r + 1) : iter S seed (k + 1) ≤ r + 1 := by
  have hge_k : r ≤ iter S seed k := iter_ge_r S seed r hr hlo hseed k
  have hz : 0 < iter S seed k := Nat.lt_of_lt_of_le hr hge_k
  have hst := newton_stay S (iter S seed k) r hr hz hlo hhi hge_k hk
  have heq : iter S seed (k + 1) = N S (iter S seed k) := rfl
  omega

theorem iter_stay_fwd (S seed r K : Nat) (hr : 0 < r)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1)) (hseed : r ≤ seed)
    (hK : K ≤ 256) (hk : iter S seed K ≤ r + 1) : iter S seed 256 ≤ r + 1 := by
  have hKK : K + (256 - K) = 256 := Nat.add_sub_cancel' hK
  have hall : ∀ d, iter S seed (K + d) ≤ r + 1 := by
    intro d
    induction d with
    | zero => simpa using hk
    | succ d ih =>
      have h1 : K + (d + 1) = (K + d) + 1 := by omega
      rw [h1]
      exact iter_stay_step S seed r hr hlo hhi hseed (K + d) ih
  have h256 := hall (256 - K)
  rw [hKK] at h256
  exact h256

theorem pow_two_succ (n : Nat) : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n

theorem dbl_bound_aux (S seed r n : Nat) (hr : 0 < r)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1)) (hseed : r ≤ seed)
    (hall2 : ∀ j, j < n → r + 2 ≤ iter S seed j) :
    2 ^ n * (iter S seed n - r) ≤ seed - r := by
  induction n with
  | zero =>
    simp [iter_zero]
  | succ k ih =>
    have hall2k : ∀ j, j < k → r + 2 ≤ iter S seed j := by
      intro j hj
      exact hall2 j (Nat.lt_trans hj (Nat.lt_succ_self k))
    have ih2 := ih hall2k
    have hk2 : r + 2 ≤ iter S seed k := hall2 k (Nat.lt_succ_self k)
    have hge_k : r ≤ iter S seed k := iter_ge_r S seed r hr hlo hseed k
    have hz : 0 < iter S seed k := Nat.lt_of_lt_of_le hr hge_k
    have hhalf : (iter S seed (k + 1) - r) * 2 ≤ iter S seed k - r := by
      have h1 : iter S seed (k + 1) = N S (iter S seed k) := rfl
      have h2 := newton_err_half S (iter S seed k) r hr hz hlo hhi hge_k hk2
      omega
    have hpow : 2 ^ (k + 1) * (iter S seed (k + 1) - r) =
        2 ^ k * ((iter S seed (k + 1) - r) * 2) := by
      rw [pow_two_succ]
      rw [Nat.mul_assoc]
      rw [Nat.mul_comm ((iter S seed (k + 1) - r)) 2]
    have hle1 : 2 ^ k * ((iter S seed (k + 1) - r) * 2) ≤ 2 ^ k * (iter S seed k - r) :=
      Nat.mul_le_mul (Nat.le_refl _) hhalf
    have hle2 : 2 ^ k * (iter S seed k - r) ≤ seed - r := ih2
    omega

theorem seed_lt_pow (a : Nat) (ha : a ≤ 2 ^ 167 - 1) : a / 2 + 5000000000 < 2 ^ 167 := by
  have hdiv : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right ha
  have hdiv2 : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
  have hle : a / 2 ≤ 2 ^ 166 - 1 := by omega
  have hlt : (2 ^ 166 - 1) + 5000000000 < 2 ^ 167 := by decide
  omega

theorem pow167_le_pow256 : 2 ^ 167 ≤ 2 ^ 256 :=
  Nat.pow_le_pow_right (by decide) (by decide)

theorem pow256_lt_two_mul : 2 ^ 256 < 2 ^ 256 * 2 := by
  have h1 : 2 ^ 256 * 1 < 2 ^ 256 * 2 := by
    apply Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl _) (by decide) (by omega)
  have e1 : 2 ^ 256 * 1 = 2 ^ 256 := Nat.mul_one _
  omega

theorem iter_256_le (S seed r : Nat) (hr : 0 < r)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1)) (hseed : r ≤ seed)
    (hseed167 : seed < 2 ^ 167) : iter S seed 256 ≤ r + 1 := by
  by_cases h : ∃ K, K ≤ 256 ∧ iter S seed K ≤ r + 1
  · obtain ⟨K, hK, hk⟩ := h
    exact iter_stay_fwd S seed r K hr hlo hhi hseed hK hk
  · have hall_ge2 : ∀ K, K ≤ 256 → r + 2 ≤ iter S seed K := by
      intro K hK
      have hgeK : r ≤ iter S seed K := iter_ge_r S seed r hr hlo hseed K
      have hnot : ¬ iter S seed K ≤ r + 1 := by
        intro hc
        exact h ⟨K, hK, hc⟩
      clear hlo hhi
      omega
    have hall2 : ∀ j, j < 256 → r + 2 ≤ iter S seed j := by
      intro j hj
      exact hall_ge2 j (Nat.le_of_lt hj)
    have hbd := dbl_bound_aux S seed r 256 hr hlo hhi hseed hall2
    have hge256 : r ≤ iter S seed 256 := iter_ge_r S seed r hr hlo hseed 256
    have h256ge2 : r + 2 ≤ iter S seed 256 := hall_ge2 256 (Nat.le_refl _)
    have herr2 : 2 ≤ iter S seed 256 - r := by
      have : iter S seed 256 = r + (iter S seed 256 - r) := by
        have := Nat.sub_add_cancel hge256
        omega
      clear hlo hhi
      omega
    have h2mul : 2 ^ 256 * 2 ≤ 2 ^ 256 * (iter S seed 256 - r) :=
      Nat.mul_le_mul (Nat.le_refl _) herr2
    have hle256 : 2 ^ 256 * 2 ≤ seed - r := Nat.le_trans h2mul hbd
    have hseed_r : seed - r < 2 ^ 167 := by
      have : seed - r ≤ seed := Nat.sub_le _ _
      have hlt : seed < 2 ^ 167 := hseed167
      omega
    have h167 : (2 : Nat) ^ 167 ≤ 2 ^ 256 := pow167_le_pow256
    have hlt256 : 2 ^ 256 * 2 < 2 ^ 256 * 2 := by
      have h1 : 2 ^ 256 * 2 ≤ seed - r := hle256
      have h2 : seed - r < 2 ^ 167 := hseed_r
      have h3 : (2 : Nat) ^ 167 ≤ 2 ^ 256 := h167
      have h4 : 2 ^ 256 < 2 ^ 256 * 2 := pow256_lt_two_mul
      omega
    exact False.elim (Nat.lt_irrefl _ hlt256)

theorem r_lt_pow101 (S r : Nat) (hS201 : S < 2 ^ 201) (hlo : r * r ≤ S) :
    r < 2 ^ 101 := by
  by_cases h : r < 2 ^ 101
  · exact h
  · have hge : 2 ^ 101 ≤ r := by omega
    have hsq : 2 ^ 101 * 2 ^ 101 ≤ r * r := Nat.mul_le_mul hge hge
    have e202 : 2 ^ 101 * 2 ^ 101 = 2 ^ 202 := by decide
    have e201 : (2 : Nat) ^ 202 = 2 ^ 201 * 2 := by rw [pow_two_succ]
    have hlt202 : 2 ^ 201 < 2 ^ 202 := by
      have e : 2 ^ 202 = 2 ^ 201 + 2 ^ 201 := by
        rw [e201, Nat.mul_two]
      have hpos : 0 < 2 ^ 201 := by decide
      omega
    have hcontra : 2 ^ 202 < 2 ^ 202 := by
      have h1 : 2 ^ 101 * 2 ^ 101 ≤ S := Nat.le_trans hsq hlo
      have h2 : S < 2 ^ 201 := hS201
      have h3 : 2 ^ 201 < 2 ^ 202 := hlt202
      have h4 : 2 ^ 101 * 2 ^ 101 < 2 ^ 202 := by
        calc 2 ^ 101 * 2 ^ 101 ≤ S := h1
          _ < 2 ^ 201 := h2
          _ < 2 ^ 202 := h3
      omega
    exact False.elim (Nat.lt_irrefl _ hcontra)

theorem S_lt_pow201 (a : Nat) (ha : a ≤ 2 ^ 167 - 1) : a * 10000000000 < 2 ^ 201 := by
  have h10 : 10000000000 ≤ 2 ^ 34 - 1 := by decide
  have hle : a * 10000000000 ≤ (2 ^ 167 - 1) * (2 ^ 34 - 1) :=
    Nat.mul_le_mul ha h10
  have hlt : (2 ^ 167 - 1) * (2 ^ 34 - 1) < 2 ^ 201 := by decide
  exact Nat.lt_of_le_of_lt hle hlt

theorem range_bound (a S seed r z : Nat) (ha : a ≤ 2 ^ 167 - 1)
    (hS : S = a * 10000000000) (hseed_eq : seed = a / 2 + 5000000000)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1))
    (hr : 0 < r) (hzr : r ≤ z) (hzmax : z ≤ max seed (r + 1)) :
    S / z + z ≤ 2 ^ 167 - 1 := by
  have hz : 0 < z := Nat.lt_of_lt_of_le hr hzr
  have hS201 : S < 2 ^ 201 := by rw [hS]; exact S_lt_pow201 a ha
  have hr101 : r < 2 ^ 101 := r_lt_pow101 S r hS201 hlo
  have hSr : S / r ≤ r + 2 := by
    have hle2 : S ≤ (r + 2) * r := by
      have e1 : (r + 1) * (r + 1) = r * r + (r * 2 + 1) := sle_of_ge2_aux1 r
      have e3 : (r + 2) * r = r * r + r * 2 := by
        rw [Nat.add_mul]
        have : (2 : Nat) * r = r * 2 := Nat.mul_comm _ _
        omega
      omega
    have hdiv2 := div_le_of_le_mul S r (r + 2) hr hle2
    simpa [Nat.mul_comm] using hdiv2
  have hSz : S / z ≤ r + 2 := by
    have h1 : S / z ≤ S / r := Nat.div_le_div_left hzr (by omega)
    omega
  have hseed_le : seed ≤ 2 ^ 166 - 1 + 5000000000 := by
    have hdiv : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right ha
    have hdiv2 : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
    omega
  have hr_le : r ≤ 2 ^ 101 - 1 := by clear hlo hhi; omega
  have hlo_a : r * r ≤ a * 10000000000 := by rw [← hS]; exact hlo
  have hhi_a : a * 10000000000 < (r + 1) * (r + 1) := by rw [← hS]; exact hhi
  have hge_seed : r ≤ seed := by
    rw [hseed_eq]
    exact seed_ge_r a r hlo_a hhi_a
  have hmax1 : max seed (r + 1) ≤ seed + 1 :=
    Nat.max_le.mpr ⟨Nat.le_succ _, Nat.succ_le_succ hge_seed⟩
  have hz_le : z ≤ seed + 1 := Nat.le_trans hzmax hmax1
  have hsum_le : S / z + z ≤ (r + 2) + (seed + 1) := Nat.add_le_add hSz hz_le
  have hclosed : (2 ^ 101 - 1 + 2) + ((2 ^ 166 - 1 + 5000000000) + 1) ≤ 2 ^ 167 - 1 := by
    decide
  clear hlo hhi
  omega

theorem floor_unique (S r1 r2 : Nat) (h1lo : r1 * r1 ≤ S) (h1hi : S < (r1 + 1) * (r1 + 1))
    (h2lo : r2 * r2 ≤ S) (h2hi : S < (r2 + 1) * (r2 + 1)) : r1 = r2 := by
  by_cases h : r1 ≤ r2
  · by_cases h2 : r1 = r2
    · exact h2
    · have hlt : r1 + 1 ≤ r2 := by clear h1lo h1hi h2lo h2hi; omega
      have hsq : (r1 + 1) * (r1 + 1) ≤ r2 * r2 := Nat.mul_le_mul hlt hlt
      have hcontra : (r1 + 1) * (r1 + 1) < (r1 + 1) * (r1 + 1) := by
        calc (r1 + 1) * (r1 + 1) ≤ r2 * r2 := hsq
          _ ≤ S := h2lo
          _ < (r1 + 1) * (r1 + 1) := h1hi
      exact False.elim (Nat.lt_irrefl _ hcontra)
  · have hle : r2 ≤ r1 := by clear h1lo h1hi h2lo h2hi; omega
    by_cases h2 : r2 = r1
    · omega
    · have hlt : r2 + 1 ≤ r1 := by clear h1lo h1hi h2lo h2hi; omega
      have hsq : (r2 + 1) * (r2 + 1) ≤ r1 * r1 := Nat.mul_le_mul hlt hlt
      have hcontra : (r2 + 1) * (r2 + 1) < (r2 + 1) * (r2 + 1) := by
        calc (r2 + 1) * (r2 + 1) ≤ r1 * r1 := hsq
          _ ≤ S := h1lo
          _ < (r2 + 1) * (r2 + 1) := h2hi
      exact False.elim (Nat.lt_irrefl _ hcontra)

theorem a_eq_seed_eq_floor (a r : Nat) (haMAX : a ≤ 2 ^ 167 - 1)
    (hlo : r * r ≤ a * 10000000000) (hhi : a * 10000000000 < (r + 1) * (r + 1))
    (heq : a = a / 2 + 5000000000) : a = r := by
  have hmod : a % 2 < 2 := Nat.mod_lt _ (by decide)
  have ha : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
  have heq2 : (a / 2) + a % 2 = 5000000000 := by clear hlo hhi; omega
  have h01 : a % 2 = 0 ∨ a % 2 = 1 := by clear hlo hhi; omega
  have hfloor_a : a * a ≤ a * 10000000000 ∧ a * 10000000000 < (a + 1) * (a + 1) := by
    rcases h01 with h0 | h1
    · have hdiv : a / 2 = 5000000000 := by clear hlo hhi; omega
      have ha10 : a = 10000000000 := by clear hlo hhi; omega
      rw [ha10]
      constructor <;> decide
    · have hdiv : a / 2 = 4999999999 := by clear hlo hhi; omega
      have ha9 : a = 9999999999 := by clear hlo hhi; omega
      rw [ha9]
      constructor <;> decide
  exact floor_unique (a * 10000000000) a r hfloor_a.1 hfloor_a.2 hlo hhi

theorem fixed_eq_floor (S z r : Nat) (hr : 0 < r) (hz : 0 < z)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1))
    (hzr : r ≤ z) (hfix : N S z = z) : z = r := by
  by_cases h : z = r
  · exact h
  · have hge : r + 1 ≤ z := by clear hlo hhi; omega
    have hlt : N S z < z := newton_lt S z r hz hhi hge
    have hcontra : z < z := by omega
    exact False.elim (Nat.lt_irrefl _ hcontra)

theorem base_min_eq (S seed r : Nat) (hr : 0 < r)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1)) (hseed : r ≤ seed)
    (h255 : iter S seed 255 ≤ r + 1) (h256 : iter S seed 256 ≤ r + 1) :
    (if iter S seed 255 < iter S seed 256 then iter S seed 255 else iter S seed 256) = r := by
  have hge255 : r ≤ iter S seed 255 := iter_ge_r S seed r hr hlo hseed 255
  have hge256 : r ≤ iter S seed 256 := iter_ge_r S seed r hr hlo hseed 256
  have hy : iter S seed 255 = r ∨ iter S seed 255 = r + 1 := by clear hlo hhi; omega
  have hiter_eq : iter S seed 256 = N S (iter S seed 255) := rfl
  rcases hy with hyr | hyr1
  · have hz_ge : r ≤ iter S seed 256 := hge256
    have hz_le : iter S seed 256 ≤ r + 1 := h256
    have hz_eq : iter S seed 256 = N S r := by rw [hyr] at hiter_eq; exact hiter_eq
    have hNr_ge : r ≤ N S r := newton_ge S r r hr hlo (Nat.le_refl _)
    have hNr_le : N S r ≤ r + 1 := newton_at_r_le S r hr hhi
    have hmin : (if r < iter S seed 256 then r else iter S seed 256) = r := by
      by_cases h : r < iter S seed 256
      · rw [if_pos h]
      · have hle : iter S seed 256 ≤ r := by clear hlo hhi; omega
        have heq2 : iter S seed 256 = r := eq_of_le_ge _ _ hle hz_ge
        rw [if_neg (by clear hlo hhi; omega : ¬ r < iter S seed 256)]
        exact heq2
    calc (if iter S seed 255 < iter S seed 256 then iter S seed 255 else iter S seed 256)
        = (if r < iter S seed 256 then r else iter S seed 256) := by rw [hyr]
      _ = r := hmin
  · have hz_eq : iter S seed 256 = r := by
      have h1 : iter S seed 256 = N S (r + 1) := by rw [hyr1] at hiter_eq; exact hiter_eq
      rw [h1]
      exact newton_succ_eq S r hr hlo hhi
    have hmin : (if r + 1 < r then r + 1 else r) = r := by
      have hneg : ¬ r + 1 < r := by clear hlo hhi; omega
      rw [if_neg hneg]
    calc (if iter S seed 255 < iter S seed 256 then iter S seed 255 else iter S seed 256)
        = (if r + 1 < r then r + 1 else r) := by rw [hyr1, hz_eq]
      _ = r := hmin

theorem pow167_le_pow255 : 2 ^ 167 ≤ 2 ^ 255 :=
  Nat.pow_le_pow_right (by decide) (by decide)

theorem pow255_lt_two_mul : 2 ^ 255 < 2 ^ 255 * 2 := by
  have h1 : 2 ^ 255 * 1 < 2 ^ 255 * 2 := by
    apply Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl _) (by decide) (by omega)
  have e1 : 2 ^ 255 * 1 = 2 ^ 255 := Nat.mul_one _
  omega

theorem iter_255_le (S seed r : Nat) (hr : 0 < r)
    (hlo : r * r ≤ S) (hhi : S < (r + 1) * (r + 1)) (hseed : r ≤ seed)
    (hseed167 : seed < 2 ^ 167) : iter S seed 255 ≤ r + 1 := by
  by_cases h : ∃ K, K ≤ 255 ∧ iter S seed K ≤ r + 1
  · obtain ⟨K, hK, hk⟩ := h
    have hKK : K + (255 - K) = 255 := Nat.add_sub_cancel' hK
    have hall : ∀ d, iter S seed (K + d) ≤ r + 1 := by
      intro d
      induction d with
      | zero => simpa using hk
      | succ d ih =>
        have h1 : K + (d + 1) = (K + d) + 1 := by omega
        rw [h1]
        exact iter_stay_step S seed r hr hlo hhi hseed (K + d) ih
    have h255 := hall (255 - K)
    rw [hKK] at h255
    exact h255
  · have hall_ge2 : ∀ K, K ≤ 255 → r + 2 ≤ iter S seed K := by
      intro K hK
      have hgeK : r ≤ iter S seed K := iter_ge_r S seed r hr hlo hseed K
      have hnot : ¬ iter S seed K ≤ r + 1 := by
        intro hc
        exact h ⟨K, hK, hc⟩
      clear hlo hhi
      omega
    have hall2 : ∀ j, j < 255 → r + 2 ≤ iter S seed j := by
      intro j hj
      exact hall_ge2 j (Nat.le_of_lt hj)
    have hbd := dbl_bound_aux S seed r 255 hr hlo hhi hseed hall2
    have hge255 : r ≤ iter S seed 255 := iter_ge_r S seed r hr hlo hseed 255
    have h255ge2 : r + 2 ≤ iter S seed 255 := hall_ge2 255 (Nat.le_refl _)
    have herr2 : 2 ≤ iter S seed 255 - r := by
      have : iter S seed 255 = r + (iter S seed 255 - r) := by
        have := Nat.sub_add_cancel hge255
        omega
      clear hlo hhi
      omega
    have h2mul : 2 ^ 255 * 2 ≤ 2 ^ 255 * (iter S seed 255 - r) :=
      Nat.mul_le_mul (Nat.le_refl _) herr2
    have hle255 : 2 ^ 255 * 2 ≤ seed - r := Nat.le_trans h2mul hbd
    have hseed_r : seed - r < 2 ^ 167 := by
      have : seed - r ≤ seed := Nat.sub_le _ _
      have hlt : seed < 2 ^ 167 := hseed167
      omega
    have h167 : (2 : Nat) ^ 167 ≤ 2 ^ 255 := pow167_le_pow255
    have hlt255 : 2 ^ 255 * 2 < 2 ^ 255 * 2 := by
      have h1 : 2 ^ 255 * 2 ≤ seed - r := hle255
      have h2 : seed - r < 2 ^ 167 := hseed_r
      have h3 : (2 : Nat) ^ 167 ≤ 2 ^ 255 := h167
      have h4 : 2 ^ 255 < 2 ^ 255 * 2 := pow255_lt_two_mul
      omega
    exact False.elim (Nat.lt_irrefl _ hlt255)

theorem loop_base_min (aNat r : Nat) (haMAX : aNat ≤ 2 ^ 167 - 1)
    (hlo : r * r ≤ aNat * 10000000000) (hhi : aNat * 10000000000 < (r + 1) * (r + 1))
    (hr : 0 < r) :
    let S := aNat * 10000000000
    let seed := aNat / 2 + 5000000000
    let yN := iter S seed 255
    let zN := iter S seed 256
    (if yN < zN then (yN : Int) else (zN : Int)) = (r : Nat) := by
  intro S seed yN zN
  have hS : S = aNat * 10000000000 := rfl
  have hseed_eq : seed = aNat / 2 + 5000000000 := rfl
  have hseed_ge : r ≤ seed := by
    rw [hseed_eq]
    exact seed_ge_r aNat r hlo hhi
  have hseed167 : seed < 2 ^ 167 := by
    rw [hseed_eq]
    exact seed_lt_pow aNat haMAX
  have h255 : iter S seed 255 ≤ r + 1 :=
    iter_255_le S seed r hr hlo hhi hseed_ge hseed167
  have h256 : iter S seed 256 ≤ r + 1 :=
    iter_256_le S seed r hr hlo hhi hseed_ge hseed167
  have hNat : (if yN < zN then yN else zN) = r := by
    have hyN : yN = iter S seed 255 := rfl
    have hzN : zN = iter S seed 256 := rfl
    rw [hyN, hzN]
    exact base_min_eq S seed r hr hlo hhi hseed_ge h255 h256
  by_cases hN : yN < zN
  · rw [if_pos hN]
    have h1 : yN = r := by
      have := hNat
      rw [if_pos hN] at this
      exact this
    rw [h1]
  · rw [if_neg hN]
    have h1 : zN = r := by
      have := hNat
      rw [if_neg hN] at this
      exact this
    rw [h1]

theorem loop_aux_general (aNat r : Nat) (haMAX : aNat ≤ 2 ^ 167 - 1) (ha0 : 0 < aNat)
    (hlo : r * r ≤ aNat * 10000000000) (hhi : aNat * 10000000000 < (r + 1) * (r + 1))
    (hr : 0 < r) :
    ∀ m k, k + m = 256 →
      ((loop (aNat : Int) m
        ((if k = 0 then aNat else iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1)) : Int)
        ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) k : Nat) : Int)).map
        (fun p => if p.1 < p.2 then p.1 else p.2)) = some (r : Nat) := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have hk256 : k = 256 := by clear hlo hhi; omega
    rw [hk256]
    have h256ne : ¬ (256 = 0) := by decide
    have e256 : 256 - 1 = 255 := by decide
    have hy : (if 256 = 0 then aNat else iter (aNat * 10000000000) (aNat / 2 + 5000000000) (256 - 1))
        = iter (aNat * 10000000000) (aNat / 2 + 5000000000) 255 := by
      rw [if_neg h256ne, e256]
    have hbase := loop_base_min aNat r haMAX hlo hhi hr
    simp [loop, hy]
    exact hbase
  | succ m ih =>
    intro k hk
    have hD : (10 ^ 10 : Nat) = 10000000000 := by decide
    have hseed_ge : r ≤ aNat / 2 + 5000000000 := seed_ge_r aNat r hlo hhi
    have hzr : r ≤ iter (aNat * 10000000000) (aNat / 2 + 5000000000) k :=
      iter_ge_r _ _ r hr hlo hseed_ge k
    have hzmax : iter (aNat * 10000000000) (aNat / 2 + 5000000000) k
        ≤ max (aNat / 2 + 5000000000) (r + 1) :=
      iter_le_max _ _ r hr hlo hhi hseed_ge k
    have hrange : (aNat * 10000000000) / iter (aNat * 10000000000) (aNat / 2 + 5000000000) k
        + iter (aNat * 10000000000) (aNat / 2 + 5000000000) k ≤ 2 ^ 167 - 1 :=
      range_bound aNat _ _ r _ haMAX rfl rfl hlo hhi hr hzr hzmax
    have hz_pos : 0 < iter (aNat * 10000000000) (aNat / 2 + 5000000000) k :=
      Nat.lt_of_lt_of_le hr hzr
    by_cases hk0 : k = 0
    · subst hk0
      have hy0 : (if (0 : Nat) = 0 then (aNat : Int) else ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) ((0 : Nat) - 1) : Nat) : Int)) = (aNat : Int) := by
        rw [if_pos rfl]
      have hz0 : iter (aNat * 10000000000) (aNat / 2 + 5000000000) 0 = aNat / 2 + 5000000000 := rfl
      rw [hy0, hz0]
      by_cases heq0 : aNat / 2 + 5000000000 = aNat
      · have har : aNat = r := by
          have hsym : aNat = aNat / 2 + 5000000000 := heq0.symm
          exact a_eq_seed_eq_floor aNat r haMAX hlo hhi hsym
        have hzI : ((aNat / 2 + 5000000000 : Nat) : Int) = (aNat : Int) := by rw [heq0]
        rw [hzI]
        have hstop := loop_stop (aNat : Int) m (aNat : Int)
        rw [hstop]
        simp only [Option.map_some]
        have hmin : (if (aNat : Int) < (aNat : Int) then (aNat : Int) else (aNat : Int)) = (aNat : Int) := by
          have hneg : ¬ (aNat : Int) < (aNat : Int) := Int.lt_irrefl _
          rw [if_neg hneg]
        rw [hmin, har]
      · have hne0 : aNat / 2 + 5000000000 ≠ aNat := heq0
        have hne0' : (iter (aNat * 10000000000) (aNat / 2 + 5000000000) 0) ≠ aNat := by
          rw [hz0]; exact hne0
        have hrange10_0 : aNat * 10 ^ 10 / iter (aNat * 10000000000) (aNat / 2 + 5000000000) 0
            + iter (aNat * 10000000000) (aNat / 2 + 5000000000) 0 ≤ 2 ^ 167 - 1 := by
          rw [← hD]
          have := hrange
          rw [hz0] at this ⊢
          exact this
        have hz_pos0 : 0 < iter (aNat * 10000000000) (aNat / 2 + 5000000000) 0 := by
          rw [hz0]; exact Nat.lt_of_lt_of_le hr hseed_ge
        have hstep0 := loop_step (a := aNat) (y := aNat)
          (z := iter (aNat * 10000000000) (aNat / 2 + 5000000000) 0) m hz_pos0 hne0' hrange10_0
        rw [hstep0, hz0]
        have hkm0 : (0 + 1) + m = 256 := by clear hrange hrange10_0 hstep0; omega
        have hIH0 := ih (0 + 1) hkm0
        have hyEq0 : (if (0 + 1 : Nat) = 0 then (aNat : Int) else ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) ((0 + 1 : Nat) - 1) : Nat) : Int))
            = ((aNat / 2 + 5000000000 : Nat) : Int) := by
          have h1ne : ¬ ((0 : Nat) + 1 = 0) := by decide
          have h1sub : ((0 : Nat) + 1) - 1 = 0 := by decide
          rw [if_neg h1ne, h1sub, hz0]
        have hzEq0 : iter (aNat * 10000000000) (aNat / 2 + 5000000000) (0 + 1)
            = (aNat * 10 ^ 10 / (aNat / 2 + 5000000000) + (aNat / 2 + 5000000000)) / 2 := by
          have e : iter (aNat * 10000000000) (aNat / 2 + 5000000000) (0 + 1)
              = N (aNat * 10000000000) (iter (aNat * 10000000000) (aNat / 2 + 5000000000) 0) := rfl
          rw [e, hz0, hD]
          rfl
        rw [hyEq0, hzEq0] at hIH0
        exact hIH0
    · have hyK : (if k = 0 then (aNat : Int) else ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1) : Nat) : Int))
          = ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1) : Nat) : Int) := by
        rw [if_neg hk0]
      rw [hyK]
      by_cases heq : iter (aNat * 10000000000) (aNat / 2 + 5000000000) k
          = iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1)
      · have hk1 : k = (k - 1) + 1 := by clear hlo hhi; omega
        have hiter : iter (aNat * 10000000000) (aNat / 2 + 5000000000) k
            = N (aNat * 10000000000) (iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1)) := by
          rw [hk1]; rfl
        have hfix : N (aNat * 10000000000) (iter (aNat * 10000000000) (aNat / 2 + 5000000000) k)
            = iter (aNat * 10000000000) (aNat / 2 + 5000000000) k := by
          rw [heq]
          rw [← hiter]
          exact heq
        have hzKr : iter (aNat * 10000000000) (aNat / 2 + 5000000000) k = r :=
          fixed_eq_floor _ _ r hr hz_pos hlo hhi hzr hfix
        have heqI : ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) k : Nat) : Int)
            = ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1) : Nat) : Int) := by
          rw [heq]
        rw [heqI]
        have hstop := loop_stop (aNat : Int) m
          ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1) : Nat) : Int)
        rw [hstop]
        simp only [Option.map_some]
        have hmin : (if ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1) : Nat) : Int) < ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1) : Nat) : Int) then ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1) : Nat) : Int) else ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1) : Nat) : Int)) = ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1) : Nat) : Int) := by
          have hneg : ¬ ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1) : Nat) : Int) < ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1) : Nat) : Int) := Int.lt_irrefl _
          rw [if_neg hneg]
        rw [hmin, ← heq, hzKr]
        rfl
      · have hne : iter (aNat * 10000000000) (aNat / 2 + 5000000000) k
            ≠ iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1) := heq
        have hrange10 : aNat * 10 ^ 10 / iter (aNat * 10000000000) (aNat / 2 + 5000000000) k
            + iter (aNat * 10000000000) (aNat / 2 + 5000000000) k ≤ 2 ^ 167 - 1 := by
          rw [← hD]; exact hrange
        have hstep := loop_step (a := aNat)
          (y := iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k - 1))
          (z := iter (aNat * 10000000000) (aNat / 2 + 5000000000) k) m hz_pos hne hrange10
        rw [hstep]
        have hkm : (k + 1) + m = 256 := by clear hrange hrange10 hstep; omega
        have hIH := ih (k + 1) hkm
        have hk1ne : ¬ (k + 1 = 0) := by clear hlo hhi; omega
        have hk1sub : (k + 1) - 1 = k := by clear hlo hhi; omega
        have hyEq : (if k + 1 = 0 then (aNat : Int) else ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) ((k + 1) - 1) : Nat) : Int))
            = ((iter (aNat * 10000000000) (aNat / 2 + 5000000000) k : Nat) : Int) := by
          rw [if_neg hk1ne, hk1sub]
        have hzEq : iter (aNat * 10000000000) (aNat / 2 + 5000000000) (k + 1)
            = (aNat * 10 ^ 10 / iter (aNat * 10000000000) (aNat / 2 + 5000000000) k
              + iter (aNat * 10000000000) (aNat / 2 + 5000000000) k) / 2 := by
          rw [hD]
          rfl
        rw [hyEq, hzEq] at hIH
        exact hIH

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  unfold sqrt vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop : DeployedLoop sqrt :=
  ⟨(fun y z => if y < z then y else z), fun _ => rfl⟩

theorem req_sqrt_not_above : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_total : SqrtTotal sqrt := sorry

end VyperSqrt
