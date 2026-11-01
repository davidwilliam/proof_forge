import VyperSqrt.Spec
import VyperSqrt.Lemmas

namespace VyperSqrt

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  unfold SqrtNegReverts sqrt vyperSqrtWith
  intro x hx
  have h : x < 0 := hx
  simp [h]

theorem req_deployed_loop : DeployedLoop sqrt := by
  exact ⟨(fun y z => if y < z then y else z), fun x => rfl⟩

-- Nat helpers for the analysis.
def Dnat : Nat := 10 ^ 10
def Mnat : Nat := 2 ^ 167 - 1
def Xnat (a : Nat) : Nat := a * 10 ^ 10
def Snat (a : Nat) : Nat := Nat.sqrt (a * 10 ^ 10)
def s0nat (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9
def Znat (a : Nat) : Nat → Nat
  | 0 => s0nat a
  | n + 1 => (Xnat a / Znat a n + Znat a n) / 2

-- Concrete bounds on Mnat, by decide.
theorem Mnat_gt_10e10 : 10000000000 ≤ Mnat := by decide
theorem Mnat_gt_5e9 : 5000000000 ≤ Mnat := by decide
theorem Mnat_gt_9D : 9 * 10000000000 ≤ Mnat := by decide
theorem Mnat_gt_18D : 18 * 10000000000 ≤ Mnat := by decide
theorem Mnat_gt_30e9 : 30000000000 ≤ Mnat := by decide
theorem Mnat_pos : 0 < Mnat := by decide
theorem pow2_167_pos : 0 < 2 ^ 167 := by decide
theorem five_e9_le_half_Mnat : 5 * 10 ^ 9 ≤ Mnat / 2 := by decide
theorem one_e10_le_Mnat : 10 ^ 10 ≤ Mnat := by decide

theorem Snat_sq_le (a : Nat) : Snat a * Snat a ≤ Xnat a := Nat.sqrt_le _
theorem Snat_lt_succ (a : Nat) : Xnat a < (Snat a + 1) * (Snat a + 1) :=
  Nat.lt_succ_sqrt _

theorem sqrt_unique {X z : Nat} (hle : z * z ≤ X) (hlt : X < (z + 1) * (z + 1)) :
    z = Nat.sqrt X := by
  have hle2 : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
  have hlt2 : X < (Nat.sqrt X + 1) * (Nat.sqrt X + 1) := Nat.lt_succ_sqrt X
  have h1 : z ≤ Nat.sqrt X := by
    cases Nat.lt_or_ge z (Nat.sqrt X) with
    | inl h => exact Nat.le_of_lt h
    | inr hge =>
      by_cases heq : z = Nat.sqrt X
      · omega
      · have hlt' : Nat.sqrt X < z := by omega
        have hle' : Nat.sqrt X + 1 ≤ z := Nat.succ_le_of_lt hlt'
        have hmul2 : (Nat.sqrt X + 1) * (Nat.sqrt X + 1) ≤ z * z :=
          Nat.mul_le_mul hle' hle'
        omega
  have h2 : Nat.sqrt X ≤ z := by
    cases Nat.lt_or_ge (Nat.sqrt X) z with
    | inl h => exact Nat.le_of_lt h
    | inr hge =>
      by_cases heq : Nat.sqrt X = z
      · omega
      · have hlt' : z < Nat.sqrt X := by omega
        have hle' : z + 1 ≤ Nat.sqrt X := Nat.succ_le_of_lt hlt'
        have hmul2 : (z + 1) * (z + 1) ≤ Nat.sqrt X * Nat.sqrt X :=
          Nat.mul_le_mul hle' hle'
        omega
  omega

-- Seed bounds.
theorem s0nat_ge_5e9 (a : Nat) : 5 * 10 ^ 9 ≤ s0nat a := by
  unfold s0nat
  omega

theorem s0nat_le_Mnat {a : Nat} (h : a ≤ Mnat) : s0nat a ≤ Mnat := by
  unfold s0nat
  have h5 := five_e9_le_half_Mnat
  omega

theorem s0nat_pos (a : Nat) : 0 < s0nat a := by
  have h := s0nat_ge_5e9 a
  omega

theorem int_mul_self_nonneg (m : Int) : 0 ≤ m * m := by
  by_cases h : 0 ≤ m
  · exact Int.mul_nonneg h h
  · have h2 : 0 ≤ -m := by omega
    have h3 : 0 ≤ (-m) * (-m) := Int.mul_nonneg h2 h2
    have e : (-m) * (-m) = m * m := Int.neg_mul_neg m m
    omega

-- Helpers with small context to avoid omega blowup.
theorem s0sq_expand (k : Nat) :
    (k + 5000000000) * (k + 5000000000)
      = k * k + 10000000000 * k + 25000000000000000000 := by
  have e1 : (k + 5000000000) * (k + 5000000000)
    = k * k + k * 5000000000 + (5000000000 * k + 5000000000 * 5000000000) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  have hc : 5000000000 * k = k * 5000000000 := Nat.mul_comm _ _
  have e2 : k * 5000000000 + 5000000000 * k = 10000000000 * k := by omega
  have e3 : (5000000000 : Nat) * 5000000000 = 25000000000000000000 := by decide
  calc (k + 5000000000) * (k + 5000000000)
      = k * k + k * 5000000000 + (5000000000 * k + 5000000000 * 5000000000) := e1
    _ = k * k + (k * 5000000000 + 5000000000 * k) + 5000000000 * 5000000000 := by ac_rfl
    _ = k * k + 10000000000 * k + 25000000000000000000 := by rw [e2, e3]

theorem Xexp_expand (k r : Nat) :
    (2 * k + r) * 10000000000 = 20000000000 * k + r * 10000000000 := by
  have e3 : 2 * k * 10000000000 = 20000000000 * k := by omega
  have e1 : (2 * k + r) * 10000000000
    = 2 * k * 10000000000 + r * 10000000000 := Nat.add_mul _ _ _
  calc (2 * k + r) * 10000000000
      = 2 * k * 10000000000 + r * 10000000000 := e1
    _ = 20000000000 * k + r * 10000000000 := by rw [e3]

-- X ≤ s0^2 + 10^10.
theorem Xnat_le_s0sq_add (a : Nat) : Xnat a ≤ s0nat a * s0nat a + 10 ^ 10 := by
  have hdiv : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
  have hr : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a
  -- Work in Int.
  have hsq : 0 ≤ (↑(a / 2) : Int) * (↑(a / 2) : Int)
    - 10000000000 * (↑(a / 2) : Int) + 25000000000000000000 := by
    have hnn := int_mul_self_nonneg ((↑(a / 2) : Int) - 5000000000)
    have e : ((↑(a / 2) : Int) - 5000000000) * ((↑(a / 2) : Int) - 5000000000)
      = (↑(a / 2) : Int) * (↑(a / 2) : Int)
        - 10000000000 * (↑(a / 2) : Int) + 25000000000000000000 := by
      have h1 : ((↑(a / 2) : Int) - 5000000000) * ((↑(a / 2) : Int) - 5000000000)
        = (↑(a / 2) : Int) * (↑(a / 2) : Int)
          - (↑(a / 2) : Int) * 5000000000
          - (5000000000 * (↑(a / 2) : Int) - 5000000000 * 5000000000) := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      have h2 : (↑(a / 2) : Int) * 5000000000
        + 5000000000 * (↑(a / 2) : Int) = 10000000000 * (↑(a / 2) : Int) := by
        rw [Int.mul_comm (↑(a / 2) : Int) 5000000000]
        omega
      have h3 : (5000000000 : Int) * 5000000000 = 25000000000000000000 := by decide
      omega
    omega
  -- Key Nat inequality from hsq.
  have hNat : 10000000000 * (a / 2) ≤ (a / 2) * (a / 2) + 25000000000000000000 := by
    have hInt : (10000000000 : Int) * (↑(a / 2) : Int)
      ≤ (↑(a / 2) : Int) * (↑(a / 2) : Int) + 25000000000000000000 := by omega
    have hcast : (((10000000000 * (a / 2) : Nat) : Int))
      ≤ ((((a / 2) * (a / 2) + 25000000000000000000 : Nat) : Int)) := by
      have e1 : (((10000000000 * (a / 2) : Nat) : Int))
        = (10000000000 : Int) * (↑(a / 2) : Int) := by
        rw [Int.natCast_mul]
        rfl
      have e2 : ((((a / 2) * (a / 2) + 25000000000000000000 : Nat) : Int))
        = (↑(a / 2) : Int) * (↑(a / 2) : Int) + 25000000000000000000 := by
        rw [Int.natCast_add, Int.natCast_mul]
        rfl
      omega
    exact Int.ofNat_le.mp hcast
  -- r * D ≤ D, in literals.
  have hrD : a % 2 * 10000000000 ≤ 10000000000 := by
    cases hr with
    | inl h0 =>
      have : a % 2 * 10000000000 = 0 * 10000000000 := by omega
      omega
    | inr h1 =>
      have : a % 2 * 10000000000 = 1 * 10000000000 := by omega
      omega
  -- Use top-level expansions (no large omega).
  have hs0eq : s0nat a = a / 2 + 5000000000 := rfl
  have h1eq : a = 2 * (a / 2) + a % 2 := Eq.symm hdiv
  have hXeq : Xnat a = (2 * (a / 2) + a % 2) * 10000000000 := by
    have hbase : Xnat a = a * 10000000000 := rfl
    have hcong : a * 10000000000 = (2 * (a / 2) + a % 2) * 10000000000 :=
      congrArg (· * 10000000000) h1eq
    exact Eq.trans hbase hcong
  have hs0sq : s0nat a * s0nat a
    = (a / 2) * (a / 2) + 10000000000 * (a / 2) + 25000000000000000000 := by
    rw [hs0eq]
    exact s0sq_expand (a / 2)
  have hXexp : (2 * (a / 2) + a % 2) * 10000000000
    = 20000000000 * (a / 2) + a % 2 * 10000000000 :=
    Xexp_expand (a / 2) (a % 2)
  -- Combine hNat + hrD.
  have hcomb : 10000000000 * (a / 2) + a % 2 * 10000000000
    ≤ ((a / 2) * (a / 2) + 25000000000000000000) + 10000000000 :=
    Nat.add_le_add hNat hrD
  have h20eq : 20000000000 * (a / 2)
    = 10000000000 * (a / 2) + 10000000000 * (a / 2) := by
    have h20 : (20000000000 : Nat) = 10000000000 + 10000000000 := by decide
    rw [h20, Nat.add_mul]
  -- Final chain via rewriting only.
  have hXval : Xnat a
    = 10000000000 * (a / 2)
      + (10000000000 * (a / 2) + a % 2 * 10000000000) := by
    rw [hXeq, hXexp, h20eq]
    ac_rfl
  have hs0val : s0nat a * s0nat a + 10 ^ 10
    = 10000000000 * (a / 2)
      + (((a / 2) * (a / 2) + 25000000000000000000) + 10000000000) := by
    have hs0rw : s0nat a * s0nat a
      = (a / 2) * (a / 2) + 10000000000 * (a / 2) + 25000000000000000000 := hs0sq
    have hD : (10 ^ 10 : Nat) = 10000000000 := rfl
    rw [hs0rw, hD]
    ac_rfl
  rw [hXval, hs0val]
  exact Nat.add_le_add (Nat.le_refl _) hcomb

theorem Q_le_S {a z : Nat} (hz : Snat a < z) : Xnat a / z ≤ Snat a := by
  have hzpos : 0 < z := by omega
  have hlt : Xnat a < (Snat a + 1) * (Snat a + 1) := Snat_lt_succ a
  have hle : Snat a + 1 ≤ z := Nat.succ_le_of_lt hz
  have hmul : (Snat a + 1) * (Snat a + 1) ≤ (Snat a + 1) * z :=
    Nat.mul_le_mul_left _ hle
  have hXlt : Xnat a < (Snat a + 1) * z := by omega
  have hdivlt : Xnat a / z < Snat a + 1 :=
    (Nat.div_lt_iff_lt_mul hzpos).mpr hXlt
  omega

theorem two_mul_le_add_sq (S z : Nat) : 2 * S * z ≤ S * S + z * z := by
  have hnn := int_mul_self_nonneg ((S : Int) - (z : Int))
  have e : ((S : Int) - (z : Int)) * ((S : Int) - (z : Int))
    = (S : Int) * (S : Int) - 2 * (S : Int) * (z : Int) + (z : Int) * (z : Int) := by
    have h1 : ((S : Int) - (z : Int)) * ((S : Int) - (z : Int))
      = (S : Int) * (S : Int) - (S : Int) * (z : Int)
        - ((z : Int) * (S : Int) - (z : Int) * (z : Int)) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have h2 : (S : Int) * (z : Int) + (z : Int) * (S : Int)
      = 2 * (S : Int) * (z : Int) := by
      have hc : (z : Int) * (S : Int) = (S : Int) * (z : Int) :=
        Int.mul_comm _ _
      have hassoc : 2 * (S : Int) * (z : Int) = 2 * ((S : Int) * (z : Int)) := by
        rw [Int.mul_assoc]
      have hdouble : (S : Int) * (z : Int) + (S : Int) * (z : Int)
        = 2 * ((S : Int) * (z : Int)) := by
        have h21 : (2 : Int) * ((S : Int) * (z : Int))
          = (1 + 1) * ((S : Int) * (z : Int)) := rfl
        rw [h21, Int.add_mul, Int.one_mul]
      omega
    omega
  have hle : 2 * (S : Int) * (z : Int)
    ≤ (S : Int) * (S : Int) + (z : Int) * (z : Int) := by omega
  have hcast : (((2 * S * z : Nat) : Int)) ≤ ((((S * S + z * z : Nat)) : Int)) := by
    have e1 : (((2 * S * z : Nat) : Int)) = 2 * (S : Int) * (z : Int) := by
      rw [Int.natCast_mul, Int.natCast_mul]
      rfl
    have e2 : ((((S * S + z * z : Nat)) : Int))
      = (S : Int) * (S : Int) + (z : Int) * (z : Int) := by
      rw [Int.natCast_add, Int.natCast_mul, Int.natCast_mul]
    omega
  exact Int.ofNat_le.mp hcast

theorem Snat_pos {a : Nat} (ha : 0 < a) : 0 < Snat a := by
  by_cases h : Snat a = 0
  · have hlt := Snat_lt_succ a
    rw [h] at hlt
    have h1 : (1 : Nat) ≤ a := by omega
    have hge : 1 * 10000000000 ≤ a * 10000000000 :=
      Nat.mul_le_mul_right _ h1
    have hXeq : Xnat a = a * 10000000000 := rfl
    omega
  · omega

theorem N_le_halving {a z : Nat} (hlt : Snat a < z) :
    (Xnat a / z + z) / 2 ≤ (Snat a + z) / 2 := by
  have hQ := Q_le_S hlt
  have hle : Xnat a / z + z ≤ Snat a + z := Nat.add_le_add_right hQ _
  exact Nat.div_le_div_right hle

theorem Q_ge_self {a : Nat} (hpos : 0 < Snat a) :
    Snat a ≤ Xnat a / Snat a :=
  (Nat.le_div_iff_mul_le hpos).mpr (Snat_sq_le a)

theorem Q_le_S2 {a z : Nat} (hle : Snat a ≤ z) (_hzpos : 0 < z) :
    Xnat a / z ≤ Snat a + 2 := by
  have hlt : Xnat a < (Snat a + 1) * (Snat a + 1) := Snat_lt_succ a
  have hexp : (Snat a + 1) * (Snat a + 1)
    = Snat a * Snat a + 2 * Snat a + 1 := by
    have e1 : (Snat a + 1) * (Snat a + 1)
      = Snat a * Snat a + Snat a * 1 + (1 * Snat a + 1 * 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have h1 : Snat a * 1 = Snat a := Nat.mul_one _
    have h2 : (1 : Nat) * Snat a = Snat a := Nat.one_mul _
    have h3 : (1 : Nat) * 1 = 1 := rfl
    omega
  have hXle : Xnat a ≤ Snat a * Snat a + 2 * Snat a := by omega
  have hSeq : Snat a * Snat a + 2 * Snat a = Snat a * (Snat a + 2) := by
    have e : Snat a * (Snat a + 2) = Snat a * Snat a + Snat a * 2 := Nat.mul_add _ _ _
    have hc : Snat a * 2 = 2 * Snat a := Nat.mul_comm _ _
    omega
  have hXle2 : Xnat a ≤ Snat a * (Snat a + 2) := by omega
  have hle2 : Snat a * (Snat a + 2) ≤ z * (Snat a + 2) :=
    Nat.mul_le_mul_right _ hle
  have hXle3 : Xnat a ≤ z * (Snat a + 2) := by omega
  exact Nat.div_le_of_le_mul hXle3

theorem pred_mul_succ_eq {S : Nat} (hpos : 0 < S) :
    (S - 1) * (S + 1) + 1 = S * S := by
  cases S with
  | zero => omega
  | succ k =>
    have e1 : (k + 1 - 1) * (k + 1 + 1) + 1 = (k + 1) * (k + 1) := by
      have hsub : k + 1 - 1 = k := Nat.add_sub_cancel _ _
      rw [hsub]
      have eL : k * (k + 1 + 1) = k * k + k * 1 + k * 1 := by
        rw [Nat.mul_add, Nat.mul_add]
      have eR : (k + 1) * (k + 1) = k * k + k * 1 + (1 * k + 1 * 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have h1 : k * 1 = k := Nat.mul_one _
      have h2 : (1 : Nat) * k = k := Nat.one_mul _
      have h3 : (1 : Nat) * 1 = 1 := rfl
      omega
    omega

theorem N_S_mem {a : Nat} (hpos : 0 < Snat a) :
    Snat a ≤ (Xnat a / Snat a + Snat a) / 2
    ∧ (Xnat a / Snat a + Snat a) / 2 ≤ Snat a + 1 := by
  have hQge := Q_ge_self hpos
  have hQle := Q_le_S2 (Nat.le_refl _) hpos
  have h1 : Snat a + Snat a ≤ Xnat a / Snat a + Snat a :=
    Nat.add_le_add_right hQge _
  have h2 : Xnat a / Snat a + Snat a ≤ (Snat a + 2) + Snat a :=
    Nat.add_le_add_right hQle _
  have h3 : (Snat a + Snat a) / 2 = Snat a := by
    have hSS : Snat a + Snat a = Snat a * 2 := by omega
    rw [hSS]
    exact Nat.mul_div_cancel _ (by omega : 0 < 2)
  have h4 : ((Snat a + 2) + Snat a) / 2 = Snat a + 1 := by
    have heq : (Snat a + 2) + Snat a = (Snat a + 1) * 2 := by omega
    rw [heq]
    exact Nat.mul_div_cancel _ (by omega : 0 < 2)
  constructor
  · omega
  · omega

theorem Q_ge_pred {a : Nat} (hpos : 0 < Snat a) :
    Snat a - 1 ≤ Xnat a / (Snat a + 1) := by
  have hmul : (Snat a - 1) * (Snat a + 1) ≤ Xnat a := by
    have heq := pred_mul_succ_eq hpos
    have hle : (Snat a - 1) * (Snat a + 1)
      ≤ (Snat a - 1) * (Snat a + 1) + 1 := Nat.le_add_right _ _
    have hsq : Snat a * Snat a ≤ Xnat a := Snat_sq_le a
    omega
  exact (Nat.le_div_iff_mul_le (by omega : 0 < Snat a + 1)).mpr hmul

theorem fixed_eq_S {a z : Nat} (hzpos : 0 < z)
    (hfix : (Xnat a / z + z) / 2 = z) : z = Snat a := by
  have hQ : Xnat a / z = Xnat a / z := rfl
  have hm : (Xnat a / z + z) / 2 = z := hfix
  have hdivmod : 2 * ((Xnat a / z + z) / 2) + (Xnat a / z + z) % 2
    = Xnat a / z + z := Nat.div_add_mod _ 2
  rw [hm] at hdivmod
  have hr : (Xnat a / z + z) % 2 = 0 ∨ (Xnat a / z + z) % 2 = 1 :=
    Nat.mod_two_eq_zero_or_one _
  have hcases : Xnat a / z + z = 2 * z ∨ Xnat a / z + z = 2 * z + 1 := by
    cases hr with
    | inl h0 =>
      have : Xnat a / z + z = 2 * z + 0 := by omega
      omega
    | inr h1 =>
      have : Xnat a / z + z = 2 * z + 1 := by omega
      omega
  have hQcases : Xnat a / z = z ∨ Xnat a / z = z + 1 := by omega
  cases hQcases with
  | inl hQz =>
    have hle1 : z * z ≤ Xnat a :=
      (Nat.le_div_iff_mul_le hzpos).mp (by omega : z ≤ Xnat a / z)
    have hlt1 : Xnat a / z < z + 1 := by omega
    have hXlt : Xnat a < (z + 1) * z :=
      (Nat.div_lt_iff_lt_mul hzpos).mp hlt1
    have hleM : (z + 1) * z ≤ (z + 1) * (z + 1) :=
      Nat.mul_le_mul_left _ (by omega : z ≤ z + 1)
    have hlt : Xnat a < (z + 1) * (z + 1) := by omega
    exact sqrt_unique hle1 hlt
  | inr hQz1 =>
    have hleM : z * z ≤ (z + 1) * z :=
      Nat.mul_le_mul_right _ (by omega : z ≤ z + 1)
    have hle1 : (z + 1) * z ≤ Xnat a :=
      (Nat.le_div_iff_mul_le hzpos).mp (by omega : z + 1 ≤ Xnat a / z)
    have hle : z * z ≤ Xnat a := Nat.le_trans hleM hle1
    have hlt1 : Xnat a / z < z + 2 := by omega
    have hXlt : Xnat a < (z + 2) * z :=
      (Nat.div_lt_iff_lt_mul hzpos).mp hlt1
    have hexp1 : (z + 2) * z = z * z + 2 * z := by
      rw [Nat.add_mul]
    have hexp2 : (z + 1) * (z + 1) = z * z + 2 * z + 1 := by
      have e1 : (z + 1) * (z + 1)
        = z * z + z * 1 + (1 * z + 1 * 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have h1 : z * 1 = z := Nat.mul_one _
      have h2 : (1 : Nat) * z = z := Nat.one_mul _
      omega
    have hlt : Xnat a < (z + 1) * (z + 1) := by omega
    exact sqrt_unique hle hlt

theorem N_ge_S_aux {a z : Nat} (_hle : Snat a ≤ z) (hzpos : 0 < z) :
    Snat a ≤ (Xnat a / z + z) / 2 := by
  by_cases h : (Xnat a / z + z) / 2 < Snat a
  · have hz2 : (0 : Nat) < 2 := by omega
    have hQz : Xnat a / z + z < Snat a * 2 :=
      (Nat.div_lt_iff_lt_mul hz2).mp h
    cases Nat.lt_or_ge z (2 * Snat a) with
    | inl hlt2 =>
      have hQlt : Xnat a / z < 2 * Snat a - z := by omega
      have hXlt : Xnat a < (2 * Snat a - z) * z :=
        (Nat.div_lt_iff_lt_mul hzpos).mp hQlt
      have hsq : (2 * Snat a - z) * z ≤ Snat a * Snat a := by
        have h2 := two_mul_le_add_sq (Snat a) z
        have hsub : (2 * Snat a - z) * z = 2 * Snat a * z - z * z :=
          Nat.sub_mul _ _ _
        omega
      have hle2 : Snat a * Snat a ≤ Xnat a := Snat_sq_le a
      omega
    | inr hge =>
      have hmul : Snat a * 2 ≤ z := by omega
      have hSle : Snat a ≤ z / 2 :=
        (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr hmul
      have hzle : z / 2 ≤ (Xnat a / z + z) / 2 :=
        Nat.div_le_div_right (Nat.le_add_left _ _)
      exact Nat.le_trans hSle hzle
  · omega

theorem Snat_le_s0nat_aux (a : Nat) : Snat a ≤ s0nat a := by
  by_cases h : Snat a ≤ s0nat a
  · exact h
  · have hlt : s0nat a < Snat a := by omega
    have hle : s0nat a + 1 ≤ Snat a := Nat.succ_le_of_lt hlt
    have hmul : (s0nat a + 1) * (s0nat a + 1) ≤ Snat a * Snat a :=
      Nat.mul_le_mul hle hle
    have hsqle : Snat a * Snat a ≤ Xnat a := Snat_sq_le a
    have hXle : Xnat a ≤ s0nat a * s0nat a + 10 ^ 10 := Xnat_le_s0sq_add a
    have hexp : (s0nat a + 1) * (s0nat a + 1)
      = s0nat a * s0nat a + 2 * s0nat a + 1 := by
      have e1 : (s0nat a + 1) * (s0nat a + 1)
        = s0nat a * s0nat a + s0nat a * 1 + (1 * s0nat a + 1 * 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have h1 : s0nat a * 1 = s0nat a := Nat.mul_one _
      have h2 : (1 : Nat) * s0nat a = s0nat a := Nat.one_mul _
      have h3 : (1 : Nat) * 1 = 1 := rfl
      omega
    have h5 : 5 * 10 ^ 9 ≤ s0nat a := s0nat_ge_5e9 a
    omega

def Bgen (e : Nat) : Nat → Nat
  | 0 => e
  | n + 1 => Bgen e n / 2

theorem Bgen_succ (e k : Nat) : Bgen e (k + 1) = Bgen (e / 2) k := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    calc Bgen e (k + 1 + 1)
        = Bgen e (k + 1) / 2 := rfl
      _ = Bgen (e / 2) k / 2 := by rw [ih]
      _ = Bgen (e / 2) (k + 1) := rfl

theorem Bgen_zero (k e : Nat) (h : e < 2 ^ k) : Bgen e k = 0 := by
  induction k generalizing e with
  | zero =>
    have h1 : (2 : Nat) ^ 0 = 1 := rfl
    rw [h1] at h
    show e = 0
    omega
  | succ k ih =>
    have hpow : (2 : Nat) ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ _ _
    rw [hpow] at h
    have hdiv : e / 2 < 2 ^ k :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr h
    have heq : Bgen e (k + 1) = Bgen (e / 2) k := Bgen_succ e k
    rw [heq]
    exact ih _ hdiv

def Bnat (a : Nat) : Nat → Nat
  | 0 => s0nat a - Snat a
  | n + 1 => Bnat a n / 2

theorem Bnat_eq_Bgen (a n : Nat) : Bnat a n = Bgen (s0nat a - Snat a) n := by
  induction n with
  | zero => rfl
  | succ k ih => unfold Bnat Bgen; rw [ih]

theorem Bnat_167_zero {a : Nat} (hM : a ≤ Mnat) : Bnat a 167 = 0 := by
  have hs0 : s0nat a ≤ Mnat := s0nat_le_Mnat hM
  have hS : Snat a ≤ s0nat a := Snat_le_s0nat_aux a
  have hB0 : s0nat a - Snat a ≤ Mnat := by omega
  have hM1 : Mnat + 1 = 2 ^ 167 := rfl
  have hlt : s0nat a - Snat a < 2 ^ 167 := by omega
  have heq := Bnat_eq_Bgen a 167
  rw [heq]
  exact Bgen_zero 167 _ hlt

theorem Bnat_ge_167_zero {a : Nat} (hM : a ≤ Mnat) (n : Nat) :
    Bnat a (167 + n) = 0 := by
  induction n with
  | zero => exact Bnat_167_zero hM
  | succ k ih =>
    have heq : 167 + (k + 1) = (167 + k) + 1 := by omega
    have h1 : Bnat a (167 + (k + 1)) = Bnat a (167 + k) / 2 := by
      rw [heq]
      rfl
    rw [h1, ih]

theorem Bnat_255_zero {a : Nat} (hM : a ≤ Mnat) : Bnat a 255 = 0 :=
  Bnat_ge_167_zero hM 88

theorem Bnat_256_zero {a : Nat} (hM : a ≤ Mnat) : Bnat a 256 = 0 :=
  Bnat_ge_167_zero hM 89

theorem Znat_le_s0plus1_aux {a : Nat} (ha : 0 < a) (n : Nat) :
    Znat a n ≤ s0nat a + 1 := by
  have hle := Znat_le_B ha n
  have hB : Bnat a n ≤ Bnat a 0 := by
    induction n with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      exact Nat.le_trans (Nat.div_le_self _ _) ih
  have hB0 : Bnat a 0 = s0nat a - Snat a := rfl
  have hS := Snat_le_s0nat_aux a
  have heq : Snat a + (s0nat a - Snat a) = s0nat a := by
    have h := Nat.sub_add_cancel hS
    omega
  omega

theorem a_eq_s0_imp_eq_S {a : Nat} (ha : 0 < a) (h : a = s0nat a) :
    a = Snat a := by
  have hdiv : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
  have hr : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a
  have hs0 : s0nat a = a / 2 + 5000000000 := rfl
  rw [hs0] at h
  have hkr : a / 2 + a % 2 = 5000000000 := by omega
  cases hr with
  | inl hr0 =>
    have hk : a / 2 = 5000000000 := by omega
    have ha10 : a = 10000000000 := by omega
    have hX : Xnat a = 10000000000 * 10000000000 := by
      unfold Xnat
      rw [ha10]
    have hS : Snat a = 10000000000 := by
      unfold Snat
      rw [ha10]
      have h1 : (10000000000 : Nat) * 10000000000 ≤ 10000000000 * 10 ^ 10 :=
        Nat.le_refl _
      have h2 : 10000000000 * 10 ^ 10
        < (10000000000 + 1) * (10000000000 + 1) := by decide
      exact Eq.symm (sqrt_unique h1 h2)
    omega
  | inr hr1 =>
    have hk : a / 2 = 4999999999 := by omega
    have ha9 : a = 9999999999 := by omega
    have hS : Snat a = 9999999999 := by
      unfold Snat
      rw [ha9]
      have h1 : 9999999999 * 9999999999 ≤ 9999999999 * 10 ^ 10 := by
        exact Nat.mul_le_mul_left _ (by decide : 9999999999 ≤ 10000000000)
      have h2 : 9999999999 * 10 ^ 10 < (9999999999 + 1) * (9999999999 + 1) := by
        decide
      exact Eq.symm (sqrt_unique h1 h2)
    omega

theorem three_mul_S_le_M_aux {a : Nat} (hM : a ≤ Mnat) : 3 * Snat a ≤ Mnat := by
  by_cases h : 3 * Snat a ≤ Mnat
  · exact h
  · have hlt : Mnat < 3 * Snat a := by omega
    have hle1 : Mnat + 1 ≤ 3 * Snat a := Nat.succ_le_of_lt hlt
    have hmul1 : (Mnat + 1) * (Mnat + 1) ≤ (3 * Snat a) * (3 * Snat a) :=
      Nat.mul_le_mul hle1 hle1
    have hexp1 : (3 * Snat a) * (3 * Snat a) = 9 * (Snat a * Snat a) := by
      have h33 : (3 : Nat) * 3 = 9 := rfl
      ac_rfl
    have hexpM : (Mnat + 1) * (Mnat + 1)
      = Mnat * Mnat + (2 * Mnat + 1) := by
      have e1 : (Mnat + 1) * (Mnat + 1)
        = Mnat * Mnat + Mnat * 1 + (1 * Mnat + 1 * 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have h1 : Mnat * 1 = Mnat := Nat.mul_one _
      have h2 : (1 : Nat) * Mnat = Mnat := Nat.one_mul _
      omega
    have hMlt : Mnat * Mnat < (Mnat + 1) * (Mnat + 1) := by omega
    have hXle : Snat a * Snat a ≤ a * 10000000000 := by
      have h1 : Snat a * Snat a ≤ Xnat a := Snat_sq_le a
      have h2 : Xnat a = a * 10000000000 := rfl
      omega
    have haM : a * 10000000000 ≤ Mnat * 10000000000 :=
      Nat.mul_le_mul_right _ hM
    have hSle : Snat a * Snat a ≤ Mnat * 10000000000 := Nat.le_trans hXle haM
    have hchain1 : Mnat * Mnat < 9 * (Snat a * Snat a) := calc
      Mnat * Mnat < (Mnat + 1) * (Mnat + 1) := hMlt
      _ ≤ (3 * Snat a) * (3 * Snat a) := hmul1
      _ = 9 * (Snat a * Snat a) := hexp1
    have hchain2 : 9 * (Snat a * Snat a) ≤ Mnat * Mnat := calc
      9 * (Snat a * Snat a) ≤ 9 * (Mnat * 10000000000) :=
        Nat.mul_le_mul_left _ hSle
      _ = 9 * 10000000000 * Mnat := by ac_rfl
      _ ≤ Mnat * Mnat :=
        Nat.mul_le_mul_right _ Mnat_gt_9D
    have hcontra : Mnat * Mnat < Mnat * Mnat :=
      Nat.lt_of_lt_of_le hchain1 hchain2
    exact absurd hcontra (Nat.lt_irrefl _)

theorem Mnat_gt_60e9 : 60000000000 ≤ Mnat := by decide

theorem S_le_third_M {a : Nat} (hM : a ≤ Mnat) : Snat a ≤ Mnat / 3 := by
  have h3 := three_mul_S_le_M_aux hM
  have hc : Snat a * 3 = 3 * Snat a := Nat.mul_comm _ _
  have hle : Snat a * 3 ≤ Mnat := by omega
  exact (Nat.le_div_iff_mul_le (by omega : 0 < 3)).mpr hle

theorem s0_le_half_M_add {a : Nat} (hM : a ≤ Mnat) :
    s0nat a ≤ Mnat / 2 + 5000000000 := by
  have hdiv : a / 2 ≤ Mnat / 2 := Nat.div_le_div_right hM
  have hs0 : s0nat a = a / 2 + 5000000000 := rfl
  omega

theorem Q_add_Z_le_M {a z : Nat} (hM : a ≤ Mnat) (hle : Snat a ≤ z)
    (hzpos : 0 < z) (hzle : z ≤ s0nat a + 1) : Xnat a / z + z ≤ Mnat := by
  have hQ := Q_le_S2 hle hzpos
  have hs0M := s0_le_half_M_add hM
  have hS3 := S_le_third_M hM
  have h60 := Mnat_gt_60e9
  omega

theorem three_mul_S_le_M {a : Nat} (hM : a ≤ Mnat) : 3 * Snat a ≤ Mnat := by
  by_cases h : 3 * Snat a ≤ Mnat
  · exact h
  · have hlt : Mnat < 3 * Snat a := by omega
    have hle1 : Mnat + 1 ≤ 3 * Snat a := Nat.succ_le_of_lt hlt
    have hmul1 : (Mnat + 1) * (Mnat + 1) ≤ (3 * Snat a) * (3 * Snat a) :=
      Nat.mul_le_mul hle1 hle1
    have hexp1 : (3 * Snat a) * (3 * Snat a) = 9 * (Snat a * Snat a) := by
      have h33 : (3 : Nat) * 3 = 9 := rfl
      ac_rfl
    have hexpM : (Mnat + 1) * (Mnat + 1)
      = Mnat * Mnat + (2 * Mnat + 1) := by
      have e1 : (Mnat + 1) * (Mnat + 1)
        = Mnat * Mnat + Mnat * 1 + (1 * Mnat + 1 * 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have h1 : Mnat * 1 = Mnat := Nat.mul_one _
      have h2 : (1 : Nat) * Mnat = Mnat := Nat.one_mul _
      omega
    have hMlt : Mnat * Mnat < (Mnat + 1) * (Mnat + 1) := by omega
    have hXle : Snat a * Snat a ≤ a * 10000000000 := by
      have h1 : Snat a * Snat a ≤ Xnat a := Snat_sq_le a
      have h2 : Xnat a = a * 10000000000 := rfl
      omega
    have haM : a * 10000000000 ≤ Mnat * 10000000000 :=
      Nat.mul_le_mul_right _ hM
    have hSle : Snat a * Snat a ≤ Mnat * 10000000000 := Nat.le_trans hXle haM
    have hchain1 : Mnat * Mnat < 9 * (Snat a * Snat a) := calc
      Mnat * Mnat < (Mnat + 1) * (Mnat + 1) := hMlt
      _ ≤ (3 * Snat a) * (3 * Snat a) := hmul1
      _ = 9 * (Snat a * Snat a) := hexp1
    have hchain2 : 9 * (Snat a * Snat a) ≤ Mnat * Mnat := calc
      9 * (Snat a * Snat a) ≤ 9 * (Mnat * 10000000000) :=
        Nat.mul_le_mul_left _ hSle
      _ = 9 * 10000000000 * Mnat := by ac_rfl
      _ ≤ Mnat * Mnat :=
        Nat.mul_le_mul_right _ Mnat_gt_9D
    have hcontra : Mnat * Mnat < Mnat * Mnat :=
      Nat.lt_of_lt_of_le hchain1 hchain2
    exact absurd hcontra (Nat.lt_irrefl _)

theorem Znat_ge_S {a : Nat} (ha : 0 < a) (n : Nat) : Snat a ≤ Znat a n := by
  have hpos : 0 < Snat a := Snat_pos ha
  have hs0 : Snat a ≤ s0nat a := Snat_le_s0nat_aux a
  induction n with
  | zero =>
    unfold Znat
    exact hs0
  | succ k ih =>
    unfold Znat
    have hzpos : 0 < Znat a k := by omega
    exact N_ge_S_aux ih hzpos

theorem Znat_le_B {a : Nat} (ha : 0 < a) (n : Nat) :
    Znat a n ≤ Snat a + Bnat a n + 1 := by
  have hpos : 0 < Snat a := Snat_pos ha
  have hs0 : Snat a ≤ s0nat a := Snat_le_s0nat_aux a
  induction n with
  | zero =>
    unfold Znat Bnat
    have heq : s0nat a = Snat a + (s0nat a - Snat a) := by
      have h := Nat.sub_add_cancel hs0
      omega
    omega
  | succ k ih =>
    have hzge := Znat_ge_S ha k
    have hzpos : 0 < Znat a k := by omega
    cases Nat.lt_or_ge (Snat a) (Znat a k) with
    | inl hlt =>
      have hNle := N_le_halving hlt
      have hZeq : Znat a (k + 1) = (Xnat a / Znat a k + Znat a k) / 2 := rfl
      have hSz : Snat a + Znat a k = 2 * Snat a + (Znat a k - Snat a) := by
        have heq : Znat a k = Snat a + (Znat a k - Snat a) := by
          have h := Nat.sub_add_cancel hzge
          omega
        omega
      have hB : Bnat a (k + 1) = Bnat a k / 2 := rfl
      have hle1 : (Xnat a / Znat a k + Znat a k) / 2
        ≤ (Snat a + Znat a k) / 2 := hNle
      have hle2 : (Snat a + Znat a k) / 2
        ≤ Snat a + Bnat a (k + 1) + 1 := by
        have hZle : Znat a k ≤ Snat a + Bnat a k + 1 := ih
        have h2 : Snat a + Znat a k ≤ 2 * Snat a + (Bnat a k + 1) := by omega
        have h3 : (Snat a + Znat a k) / 2 ≤ (2 * Snat a + (Bnat a k + 1)) / 2 :=
          Nat.div_le_div_right (by omega : Snat a + Znat a k ≤ 2 * Snat a + (Bnat a k + 1))
        have h4 : (2 * Snat a + (Bnat a k + 1)) / 2
          = Snat a + (Bnat a k + 1) / 2 := by
          have e : 2 * Snat a + (Bnat a k + 1) = 2 * Snat a + (Bnat a k + 1) := rfl
          omega
        omega
      omega
    | inr hge =>
      have heq : Znat a k = Snat a := by omega
      have hZeq : Znat a (k + 1) = (Xnat a / Snat a + Snat a) / 2 := by
        unfold Znat
        rw [heq]
      have hmem := N_S_mem hpos
      omega

theorem Bnat_mono_le_aux {a n : Nat} : Bnat a (n + 1) ≤ Bnat a n :=
  Nat.div_le_self _ _

theorem Bnat_le_zero_init_aux {a : Nat} (n : Nat) : Bnat a n ≤ Bnat a 0 := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    exact Nat.le_trans (Bnat_mono_le_aux (a := a) (n := k)) ih

theorem Znat_le_s0plus1 {a : Nat} (ha : 0 < a) : ∀ n, Znat a n ≤ s0nat a + 1 := by
  intro n
  have hle := Znat_le_B ha n
  have hB := Bnat_le_zero_init_aux (a := a) (n := n)
  have hB0 : Bnat a 0 = s0nat a - Snat a := rfl
  have hS := Snat_le_s0nat_aux a
  have heq : Snat a + (s0nat a - Snat a) = s0nat a := by
    have h := Nat.sub_add_cancel hS
    omega
  omega

theorem Znat_mem_succ {a : Nat} (ha : 0 < a) (hM : a ≤ Mnat) (n : Nat)
    (hn : 167 ≤ n) : Znat a n = Snat a ∨ Znat a n = Snat a + 1 := by
  have hge := Znat_ge_S ha n
  have hle := Znat_le_B ha n
  have hB0 : Bnat a n = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = 167 + k := Nat.exists_eq_add_of_le hn
    exact Bnat_ge_167_zero hM k
  omega

theorem Znat_255_mem {a : Nat} (ha : 0 < a) (hM : a ≤ Mnat) :
    Znat a 255 = Snat a ∨ Znat a 255 = Snat a + 1 :=
  Znat_mem_succ ha hM 255 (by omega)

theorem Znat_256_mem {a : Nat} (ha : 0 < a) (hM : a ≤ Mnat) :
    Znat a 256 = Snat a ∨ Znat a 256 = Snat a + 1 :=
  Znat_mem_succ ha hM 256 (by omega)

theorem N_Ssucc {a : Nat} (hpos : 0 < Snat a) :
    (Xnat a / (Snat a + 1) + (Snat a + 1)) / 2 = Snat a := by
  have hlt : Snat a < Snat a + 1 := by omega
  have hQle := Q_le_S hlt
  have hQge := Q_ge_pred hpos
  have h1 : 2 * Snat a ≤ Xnat a / (Snat a + 1) + (Snat a + 1) := by omega
  have h2 : Xnat a / (Snat a + 1) + (Snat a + 1) ≤ 2 * Snat a + 1 := by omega
  omega

theorem N_ge_S {a z : Nat} (_hle : Snat a ≤ z) (hzpos : 0 < z) :
    Snat a ≤ (Xnat a / z + z) / 2 := by
  by_cases h : (Xnat a / z + z) / 2 < Snat a
  · have hz2 : (0 : Nat) < 2 := by omega
    have hQz : Xnat a / z + z < Snat a * 2 :=
      (Nat.div_lt_iff_lt_mul hz2).mp h
    cases Nat.lt_or_ge z (2 * Snat a) with
    | inl hlt2 =>
      have hQlt : Xnat a / z < 2 * Snat a - z := by omega
      have hXlt : Xnat a < (2 * Snat a - z) * z :=
        (Nat.div_lt_iff_lt_mul hzpos).mp hQlt
      have hsq : (2 * Snat a - z) * z ≤ Snat a * Snat a := by
        have h2 := two_mul_le_add_sq (Snat a) z
        have hsub : (2 * Snat a - z) * z = 2 * Snat a * z - z * z :=
          Nat.sub_mul _ _ _
        omega
      have hle2 : Snat a * Snat a ≤ Xnat a := Snat_sq_le a
      omega
    | inr hge =>
      have hmul : Snat a * 2 ≤ z := by omega
      have hSle : Snat a ≤ z / 2 :=
        (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr hmul
      have hzle : z / 2 ≤ (Xnat a / z + z) / 2 :=
        Nat.div_le_div_right (Nat.le_add_left _ _)
      exact Nat.le_trans hSle hzle
  · omega

theorem Snat_le_s0nat (a : Nat) : Snat a ≤ s0nat a := by
  by_cases h : Snat a ≤ s0nat a
  · exact h
  · have hlt : s0nat a < Snat a := by omega
    have hle : s0nat a + 1 ≤ Snat a := Nat.succ_le_of_lt hlt
    have hmul : (s0nat a + 1) * (s0nat a + 1) ≤ Snat a * Snat a :=
      Nat.mul_le_mul hle hle
    have hsqle : Snat a * Snat a ≤ Xnat a := Snat_sq_le a
    have hXle : Xnat a ≤ s0nat a * s0nat a + 10 ^ 10 := Xnat_le_s0sq_add a
    have hexp : (s0nat a + 1) * (s0nat a + 1)
      = s0nat a * s0nat a + 2 * s0nat a + 1 := by
      have e1 : (s0nat a + 1) * (s0nat a + 1)
        = s0nat a * s0nat a + s0nat a * 1 + (1 * s0nat a + 1 * 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have h1 : s0nat a * 1 = s0nat a := Nat.mul_one _
      have h2 : (1 : Nat) * s0nat a = s0nat a := Nat.one_mul _
      have h3 : (1 : Nat) * 1 = 1 := rfl
      omega
    have h5 : 5 * 10 ^ 9 ≤ s0nat a := s0nat_ge_5e9 a
    omega


theorem req_sqrt_not_above   : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below   : SqrtNotBelow sqrt := sorry
theorem req_sqrt_total       : SqrtTotal sqrt := sorry

end VyperSqrt
