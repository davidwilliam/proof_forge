import OzSqrt.Spec
import OzSqrt.Lemmas
import Init.Data.Nat.Lemmas
namespace OzSqrt

def sqrt : SqrtFn := newtonSqrt 7

theorem req_newton_budget : NewtonBudget sqrt := ⟨7, Nat.le_refl 7, fun _ => rfl⟩

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  show (sqrt a).toNat * (sqrt a).toNat ≤ a.toNat
  unfold sqrt newtonSqrt
  by_cases h0 : a = 0
  · subst h0; simp
  · simp only [h0, ite_false]
    rw [toNat_min, BitVec.toNat_udiv]
    generalize (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat = X
    generalize a.toNat = A
    show Nat.min X (A / X) * Nat.min X (A / X) ≤ A
    by_cases hX0 : X = 0
    · rw [hX0]; simp
    · have hle1 : Nat.min X (A / X) ≤ X := Nat.min_le_left _ _
      have hle2 : Nat.min X (A / X) ≤ A / X := Nat.min_le_right _ _
      have hmul1 : Nat.min X (A / X) * Nat.min X (A / X) ≤ Nat.min X (A / X) * X :=
        Nat.mul_le_mul_left _ hle1
      have hmul2 : Nat.min X (A / X) * X ≤ (A / X) * X :=
        Nat.mul_le_mul_right _ hle2
      have hdiv : X * (A / X) ≤ A := by
        have h := Nat.div_add_mod A X
        omega
      have hcomm : (A / X) * X = X * (A / X) := Nat.mul_comm _ _
      exact Nat.le_trans (Nat.le_trans hmul1 hmul2) (hcomm ▸ hdiv)

theorem sqrt_lt_pow (a : U256) : (sqrt a).toNat < 2 ^ 128 := by
  by_cases h : (sqrt a).toNat < 2 ^ 128
  · exact h
  · have hge : 2 ^ 128 ≤ (sqrt a).toNat := by omega
    have hle : (2 ^ 128) * (2 ^ 128) ≤ (sqrt a).toNat * (sqrt a).toNat :=
      Nat.mul_le_mul hge hge
    have hpow : (2 ^ 128) * (2 ^ 128) = 2 ^ 256 := by
      rw [← Nat.pow_add]
    have hAbove := req_sqrt_not_above a
    have hlt := a.isLt
    omega

theorem sqrt_sq_lt (a : U256) : (sqrt a).toNat * (sqrt a).toNat < 2 ^ 256 := by
  have h128 := sqrt_lt_pow a
  have hle1 : (sqrt a).toNat + 1 ≤ 2 ^ 128 := Nat.succ_le_of_lt h128
  have hle2 : ((sqrt a).toNat + 1) * ((sqrt a).toNat + 1) ≤ (2 ^ 128) * (2 ^ 128) :=
    Nat.mul_le_mul hle1 hle1
  have hpow : (2 ^ 128) * (2 ^ 128) = 2 ^ 256 := by rw [← Nat.pow_add]
  have hlt : (sqrt a).toNat * (sqrt a).toNat < ((sqrt a).toNat + 1) * ((sqrt a).toNat + 1) := by
    have h1 : (sqrt a).toNat * (sqrt a).toNat + (2 * (sqrt a).toNat + 1) = ((sqrt a).toNat + 1) * ((sqrt a).toNat + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      omega
    omega
  omega

theorem sqrt_succ_lt (a : U256) : (sqrt a).toNat + 1 < 2 ^ 256 := by
  have h128 := sqrt_lt_pow a
  have hle1 : (sqrt a).toNat + 1 ≤ 2 ^ 128 := Nat.succ_le_of_lt h128
  have hle2 : (2 : Nat) ^ 128 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by decide)
  omega

theorem sqrtUp_toNat (a : U256) : (sqrtUp sqrt a).toNat = (sqrt a).toNat + (if (sqrt a).toNat * (sqrt a).toNat < a.toNat then 1 else 0) := by
  unfold sqrtUp
  have hsq : ((sqrt a) * (sqrt a)).toNat = (sqrt a).toNat * (sqrt a).toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (sqrt_sq_lt a)]
  have hiff : (((sqrt a) * (sqrt a) < a) ↔ (sqrt a).toNat * (sqrt a).toNat < a.toNat) := by
    rw [BitVec.lt_def, hsq]
  have h1 : (1 : U256).toNat = 1 := by decide
  have h0 : (0 : U256).toNat = 0 := by decide
  by_cases hc : (sqrt a).toNat * (sqrt a).toNat < a.toNat
  · have hp : ((sqrt a) * (sqrt a) < a) := hiff.mpr hc
    simp only [hp, ite_true]
    rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (sqrt_succ_lt a), if_pos hc]
  · have hp : ¬ ((sqrt a) * (sqrt a) < a) := fun h => hc (hiff.mp h)
    simp only [hp, ite_false]
    have hr256 : (sqrt a).toNat < 2 ^ 256 := by
      have h128 := sqrt_lt_pow a
      omega
    rw [BitVec.toNat_add, h0, Nat.add_zero, Nat.mod_eq_of_lt hr256, if_neg hc, Nat.add_zero]

theorem exists_floor : ∀ A : Nat, ∃ s, s * s ≤ A ∧ A < (s + 1) * (s + 1) := by
  intro A
  induction A with
  | zero => exact ⟨0, by omega⟩
  | succ n ih =>
    obtain ⟨s, hs1, hs2⟩ := ih
    by_cases h : n + 1 < (s + 1) * (s + 1)
    · exact ⟨s, by omega, h⟩
    · have heq : n + 1 = (s + 1) * (s + 1) := by omega
      refine ⟨s + 1, by omega, ?_⟩
      have h1 : (s + 1 + 1) * (s + 1 + 1) = (s + 1) * (s + 1) + (2 * (s + 1) + 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
        omega
      omega

def natStep (A x : Nat) : Nat := (x + A / x) / 2
def natInit (A : Nat) : Nat := 2 ^ (Nat.log2 A / 2)
def natIter (A : Nat) : Nat → Nat
  | 0 => natInit A
  | n + 1 => natStep A (natIter A n)
def natR (A : Nat) : Nat := Nat.min (natIter A 7) (A / natIter A 7)

theorem log2_le_of_pos (A : Nat) (h : A ≠ 0) : 2 ^ Nat.log2 A ≤ A :=
  ((Nat.log2_eq_iff h).mp rfl).1
theorem log2_lt_succ (A : Nat) (h : A ≠ 0) : A < 2 ^ (Nat.log2 A + 1) :=
  ((Nat.log2_eq_iff h).mp rfl).2
theorem natInit_pos (A : Nat) : 0 < natInit A := by
  unfold natInit
  exact Nat.two_pow_pos _
theorem natIter_pos_of_pos (A : Nat) (hA : 0 < A) : ∀ n, 0 < natIter A n := by
  have hne : A ≠ 0 := by omega
  intro n
  induction n with
  | zero => exact natInit_pos _
  | succ n ih =>
    unfold natIter natStep
    generalize hQ : A / natIter A n = Q
    by_cases hx : natIter A n = 1
    · rw [hx] at hQ
      have h1 : A / 1 = A := Nat.div_one _
      omega
    · have hge : 2 ≤ natIter A n := by omega
      omega
theorem natIter_ge_half (A x : Nat) : x / 2 ≤ natStep A x := by
  unfold natStep
  generalize A / x = Q
  omega
theorem log2_ge_of_ge_pow (A : Nat) (k : Nat) (hA : 2 ^ k ≤ A) (hne : A ≠ 0) :
    k ≤ Nat.log2 A := by
  have hle := log2_le_of_pos A hne
  have hlt := log2_lt_succ A hne
  by_cases h : k ≤ Nat.log2 A
  · exact h
  · have hgt : Nat.log2 A < k := by omega
    have hle1 : Nat.log2 A + 1 ≤ k := Nat.succ_le_of_lt hgt
    have hle2 : 2 ^ (Nat.log2 A + 1) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by decide) hle1
    omega
theorem natInit_ge_pow (A : Nat) (k : Nat) (hk : 2 * k ≤ Nat.log2 A) :
    2 ^ k ≤ natInit A := by
  unfold natInit
  have hle : k ≤ Nat.log2 A / 2 := by omega
  exact Nat.pow_le_pow_right (by decide) hle
theorem natInit_lt_200 (A : Nat) (hA : A < 2 ^ 256) (hne : A ≠ 0) :
    natInit A < 2 ^ 200 := by
  have hlog : Nat.log2 A < 256 := by
    by_cases h : Nat.log2 A < 256
    · exact h
    · have hge : 256 ≤ Nat.log2 A := by omega
      have hle1 := log2_le_of_pos A hne
      have hpow : 2 ^ 256 ≤ 2 ^ Nat.log2 A :=
        Nat.pow_le_pow_right (by decide) hge
      omega
  have hdiv : Nat.log2 A / 2 < 200 := by omega
  have hle : natInit A ≤ 2 ^ 127 := by
    unfold natInit
    have hle1 : Nat.log2 A / 2 ≤ 127 := by omega
    exact Nat.pow_le_pow_right (by decide) hle1
  have hlt : (2 : Nat) ^ 127 < 2 ^ 200 := by decide
  exact Nat.lt_of_le_of_lt hle hlt
theorem natInit_sq_le (A : Nat) (hne : A ≠ 0) : natInit A * natInit A ≤ A := by
  unfold natInit
  have hle1 := log2_le_of_pos A hne
  have h2 : 2 ^ (Nat.log2 A / 2) * 2 ^ (Nat.log2 A / 2) = 2 ^ (Nat.log2 A / 2 + Nat.log2 A / 2) := by
    rw [← Nat.pow_add]
  have h3 : Nat.log2 A / 2 + Nat.log2 A / 2 ≤ Nat.log2 A := by omega
  have h4 : 2 ^ (Nat.log2 A / 2 + Nat.log2 A / 2) ≤ 2 ^ Nat.log2 A :=
    Nat.pow_le_pow_right (by decide) h3
  omega
theorem natInit_le_floor (A s : Nat) (hs1 : s * s ≤ A) (hs2 : A < (s + 1) * (s + 1))
    (hne : A ≠ 0) : natInit A ≤ s := by
  by_cases h : natInit A ≤ s
  · exact h
  · have hge : s + 1 ≤ natInit A := by omega
    have hle : (s + 1) * (s + 1) ≤ natInit A * natInit A :=
      Nat.mul_le_mul hge hge
    have hsq := natInit_sq_le A hne
    omega
theorem floor_lt_two_init (A s : Nat) (hs1 : s * s ≤ A) (hs2 : A < (s + 1) * (s + 1))
    (hne : A ≠ 0) : s < 2 * natInit A := by
  have hle_log := log2_lt_succ A hne
  unfold natInit
  by_cases h : s < 2 * 2 ^ (Nat.log2 A / 2)
  · exact h
  · have hge : 2 * 2 ^ (Nat.log2 A / 2) ≤ s := by omega
    have hmul : (2 * 2 ^ (Nat.log2 A / 2)) * (2 * 2 ^ (Nat.log2 A / 2)) ≤ s * s :=
      Nat.mul_le_mul hge hge
    have h2a : (2 : Nat) * 2 ^ (Nat.log2 A / 2) = 2 ^ (Nat.log2 A / 2 + 1) := by
      rw [Nat.mul_comm, ← Nat.pow_succ]
    have h2b : (2 * 2 ^ (Nat.log2 A / 2)) * (2 * 2 ^ (Nat.log2 A / 2))
        = 2 ^ (Nat.log2 A / 2 + 1) * 2 ^ (Nat.log2 A / 2 + 1) := by
      rw [h2a]
    have h2c : 2 ^ (Nat.log2 A / 2 + 1) * 2 ^ (Nat.log2 A / 2 + 1)
        = 2 ^ ((Nat.log2 A / 2 + 1) + (Nat.log2 A / 2 + 1)) := by
      rw [← Nat.pow_add]
    have hexp : Nat.log2 A + 1 ≤ (Nat.log2 A / 2 + 1) + (Nat.log2 A / 2 + 1) := by omega
    have hpow : 2 ^ (Nat.log2 A + 1) ≤ 2 ^ ((Nat.log2 A / 2 + 1) + (Nat.log2 A / 2 + 1)) :=
      Nat.pow_le_pow_right (by decide) hexp
    omega

theorem init_toNat (a : U256) : (((1 : U256) <<< (log2 a >>> 1))).toNat = natInit a.toNat := by
  have hlog : (log2 a).toNat = Nat.log2 a.toNat := toNat_log2 a
  have hshr : (log2 a >>> (1 : Nat)).toNat = (log2 a).toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hkk : (log2 a >>> (1 : Nat)).toNat = Nat.log2 a.toNat / 2 := by
    rw [hshr, hlog]
  have h1 : ((1 : U256) <<< (log2 a >>> 1)) = ((1 : U256) <<< (log2 a >>> 1).toNat) := rfl
  rw [h1, BitVec.toNat_shiftLeft]
  have h1nat : (1 : U256).toNat = 1 := rfl
  rw [h1nat]
  have hsh : (1 : Nat) <<< (log2 a >>> 1).toNat = 2 ^ (log2 a >>> 1).toNat := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hsh, hkk]
  unfold natInit
  have hlog2 : Nat.log2 a.toNat < 256 := by
    by_cases h0 : a.toNat = 0
    · rw [h0]; simp
    · have hle1 := log2_le_of_pos a.toNat h0
      have ha := a.isLt
      by_cases hge : 256 ≤ Nat.log2 a.toNat
      · have hpow : 2 ^ 256 ≤ 2 ^ Nat.log2 a.toNat :=
          Nat.pow_le_pow_right (by decide) hge
        omega
      · omega
  have hle : Nat.log2 a.toNat / 2 < 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlog2
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hle)]

theorem iterate_toNat (a : U256) (k : Nat) : True := trivial

theorem sq_add_sq_ge_two_mul (X s : Nat) : 2 * s * X ≤ X * X + s * s := by
  have h7 : 2 * s * X = s * X + s * X := by
    rw [Nat.mul_assoc, Nat.two_mul]
  by_cases h : X ≤ s
  · have h1 : X * (s - X) ≤ s * (s - X) := Nat.mul_le_mul_right _ h
    have h2 : X * (s - X) = X * s - X * X := Nat.mul_sub _ _ _
    have h3 : s * (s - X) = s * s - s * X := Nat.mul_sub _ _ _
    have h4 : X * s = s * X := Nat.mul_comm _ _
    have h5 : X * X ≤ s * X := Nat.mul_le_mul h (Nat.le_refl _)
    have h6 : s * X ≤ s * s := Nat.mul_le_mul_left _ h
    omega
  · have hle : s ≤ X := by omega
    have h1 : s * (X - s) ≤ X * (X - s) := Nat.mul_le_mul_right _ hle
    have h2 : s * (X - s) = s * X - s * s := Nat.mul_sub _ _ _
    have h3 : X * (X - s) = X * X - X * s := Nat.mul_sub _ _ _
    have h4 : X * s = s * X := Nat.mul_comm _ _
    have h5 : s * s ≤ s * X := Nat.mul_le_mul_left _ hle
    have h6 : s * X ≤ X * X := Nat.mul_le_mul hle (Nat.le_refl _)
    omega

theorem natStep_ge_s_of_le_two (A X s : Nat) (hs1 : s * s ≤ A) (hspos : 0 < s)
    (hXle : X ≤ 2 * s) (hXpos : 0 < X) : s ≤ natStep A X := by
  unfold natStep
  have hdiv : s * s / X ≤ A / X := Nat.div_le_div_right hs1
  have hge : 2 * s ≤ X + s * s / X := by
    have hmul : 2 * s * X ≤ X * X + s * s := sq_add_sq_ge_two_mul X s
    have hdiv2 : (X * X + s * s) / X = X + s * s / X := by
      rw [Nat.add_comm (X * X) (s * s), Nat.add_mul_div_right _ _ hXpos, Nat.add_comm]
    have hle : 2 * s * X / X = 2 * s := Nat.mul_div_cancel _ hXpos
    have hmono : 2 * s * X / X ≤ (X * X + s * s) / X := Nat.div_le_div_right hmul
    omega
  omega

theorem natStep_lt_of_gt (A X s : Nat) (hs2 : A < (s + 1) * (s + 1))
    (hX : s + 1 ≤ X) (hXpos : 0 < X) : natStep A X < X := by
  unfold natStep
  have hXX : (s + 1) * (s + 1) ≤ X * X := Nat.mul_le_mul hX hX
  have hAX : A < X * X := Nat.lt_of_lt_of_le hs2 hXX
  have hdiv : A / X < X := (Nat.div_lt_iff_lt_mul hXpos).mpr hAX
  have hsum : X + A / X < X * 2 := by
    have h2 : X + X = X * 2 := by rw [Nat.mul_comm, Nat.two_mul]
    omega
  have hlt : (X + A / X) / 2 < X := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  exact hlt

theorem natR_eq_floor (A s : Nat) (hs1 : s * s ≤ A) (hs2 : A < (s + 1) * (s + 1))
    (hA : A < 2 ^ 256) : natR A = s := sorry

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro a
  show a.toNat < ((sqrt a).toNat + 1) * ((sqrt a).toNat + 1)
  unfold sqrt newtonSqrt
  by_cases h0 : a = 0
  · subst h0
    simp
  · simp only [h0, ite_false]
    have hA : a.toNat ≠ 0 := by
      intro h
      apply h0
      exact BitVec.eq_of_toNat_eq (by simpa using h)
    obtain ⟨s, hs1, hs2⟩ := exists_floor a.toNat
    have hA256 : a.toNat < 2 ^ 256 := a.isLt
    have hR : natR a.toNat = s := natR_eq_floor _ _ hs1 hs2 hA256
    have hLift : (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat = natR a.toNat := sorry
    rw [toNat_min] at *
    sorry

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  intro a
  have hAbove := req_sqrt_not_above a
  have hBelow := req_sqrt_not_below a
  rw [sqrtUp_toNat]
  by_cases hc : (sqrt a).toNat * (sqrt a).toNat < a.toNat
  · simp only [hc, ite_true]
    omega
  · simp only [hc, ite_false, Nat.add_zero]
    omega

theorem pred_sq_lt (r : Nat) (h : 0 < r) : (r - 1) * (r - 1) < r * r := by
  cases r with
  | zero => omega
  | succ n =>
    simp only [Nat.add_sub_cancel]
    have h1 : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      omega
    omega

theorem req_sqrt_up_tight  : SqrtUpTight sqrt := by
  intro a hpos
  have hAbove := req_sqrt_not_above a
  have hBelow := req_sqrt_not_below a
  rw [sqrtUp_toNat] at hpos ⊢
  by_cases hc : (sqrt a).toNat * (sqrt a).toNat < a.toNat
  · simp only [hc, ite_true, Nat.add_sub_cancel] at hpos ⊢
  · simp only [hc, ite_false, Nat.add_zero] at hpos ⊢
    have heq : (sqrt a).toNat * (sqrt a).toNat = a.toNat := by omega
    have hgt : 0 < (sqrt a).toNat := by omega
    have hlt := pred_sq_lt _ hgt
    omega

theorem req_mint_backed    : MintBacked sqrt := by
  intro a0 a1 l hl
  have h := firstMint_eq_some hl
  obtain ⟨hprod, _, heq⟩ := h
  have hAbove := req_sqrt_not_above (a0 * a1)
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have hrw : l.toNat + 1000 = ((sqrt (a0 * a1)).toNat) := heq
  have hle : (l.toNat + 1000) * (l.toNat + 1000) ≤ (a0 * a1).toNat := by
    rw [hrw]
    exact hAbove
  rw [hmul] at hle
  exact hle

theorem req_mint_full      : MintFull sqrt := by
  intro a0 a1 l hl
  have h := firstMint_eq_some hl
  obtain ⟨hprod, _, heq⟩ := h
  have hBelow := req_sqrt_not_below (a0 * a1)
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have hrw : l.toNat + 1000 = ((sqrt (a0 * a1)).toNat) := heq
  have hlt : a0.toNat * a1.toNat < (((sqrt (a0 * a1)).toNat) + 1) * (((sqrt (a0 * a1)).toNat) + 1) := by
    rw [← hmul]
    exact hBelow
  have hrw2 : ((sqrt (a0 * a1)).toNat + 1) = (l.toNat + 1001) := by
    rw [← hrw, Nat.add_assoc]
  rw [hrw2] at hlt
  exact hlt

theorem req_mint_live      : MintLive sqrt := by
  intro a0 a1 hprod hge
  have hBelow := req_sqrt_not_below (a0 * a1)
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have hgt : 1000 < ((sqrt (a0 * a1)).toNat) := by
    clear hprod
    by_cases hc : 1000 < ((sqrt (a0 * a1)).toNat)
    · exact hc
    · have hle1 : ((sqrt (a0 * a1)).toNat) + 1 ≤ 1001 := by omega
      have hle2 : (((sqrt (a0 * a1)).toNat) + 1) * (((sqrt (a0 * a1)).toNat) + 1) ≤ 1001 * 1001 :=
        Nat.mul_le_mul hle1 hle1
      have hlt : (a0 * a1).toNat < (((sqrt (a0 * a1)).toNat) + 1) * (((sqrt (a0 * a1)).toNat) + 1) := hBelow
      omega
  exact firstMint_isSome hprod hgt

end OzSqrt
