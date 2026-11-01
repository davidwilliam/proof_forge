import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.Sqrt
import ProofForgeFin.Word
import ProofForgeFin.Evm.Bits
/-!
The square-root routine under repair, `Math.sqrt(uint256 a)` in the style of OpenZeppelin
Contracts `Math.sol`, as this pool's first deposit calls it:

```
function sqrt(uint256 a) internal pure returns (uint256) {
    if (a == 0) {
        return 0;
    }
    uint256 result = 1 << (log2(a) >> 1);
    unchecked {
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        return min(result, a / result);
    }
}
```
-/
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

theorem ushiftRightBV (x k : U256) : (x >>> k).toNat = x.toNat / 2 ^ k.toNat := by
  have h : (x >>> k) = (x >>> k.toNat) := rfl
  rw [h, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem shiftLeftBV1 (k : U256) (h : k.toNat < 256) :
    ((1 : U256) <<< k).toNat = 2 ^ k.toNat := by
  have h1 : ((1 : U256) <<< k) = ((1 : U256) <<< k.toNat) := rfl
  have h0 : ((1 : U256)).toNat = 1 := rfl
  have h2 : ((1 : BitVec 256) <<< k.toNat).toNat = 1 * 2 ^ k.toNat % 2 ^ 256 := by
    rw [BitVec.toNat_shiftLeft, h0, Nat.shiftLeft_eq]
  rw [h1, h2, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h)

theorem sqrt_eq7 : ∀ a : U256, sqrt a = newtonSqrt 7 a := by
  intro a
  simp only [sqrt, newtonSqrt, iterate, newtonStep]

theorem log2_lt256 (a : U256) (h0 : a.toNat ≠ 0) : Nat.log2 a.toNat < 256 := by
  have hA := a.isLt
  have h := (Nat.log2_lt h0).mpr hA
  simpa using h

theorem init_val (a : U256) :
    ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (Nat.log2 a.toNat / 2) := by
  have hk : (log2 a >>> 1).toNat = Nat.log2 a.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, toNat_log2]
  have hlt : (log2 a >>> 1).toNat < 256 := by
    rw [hk]
    by_cases h0 : a.toNat = 0
    · rw [h0]; decide
    · have hlog := log2_lt256 a h0
      omega
  rw [shiftLeftBV1 _ hlt, hk]

def nx (A q : Nat) : Nat → Nat
  | 0 => 2 ^ q
  | n+1 => ProofForgeFin.Sqrt.newton A (nx A q n)

theorem pow_le_sqrt_aux (A : Nat) (h0 : A ≠ 0) :
    2 ^ (Nat.log2 A / 2) ≤ Nat.sqrt A := by
  apply ProofForgeFin.Sqrt.two_pow_le_sqrt
  have h2 : 2 * (Nat.log2 A / 2) ≤ Nat.log2 A := by omega
  have h3 : (2 : Nat) ^ (2 * (Nat.log2 A / 2)) ≤ 2 ^ Nat.log2 A :=
    Nat.pow_le_pow_right (by decide) h2
  have h4 : 2 ^ Nat.log2 A ≤ A := (ProofForgeFin.Evm.log2_spec h0).1
  omega

theorem sqrt_le_nx_succ (A q : Nat) (h0 : A ≠ 0) (hq : q = Nat.log2 A / 2)
    (n : Nat) : Nat.sqrt A ≤ nx A q (n + 1) := by
  induction n with
  | zero =>
    show Nat.sqrt A ≤ ProofForgeFin.Sqrt.newton A (2 ^ q)
    rw [hq]
    apply ProofForgeFin.Sqrt.sqrt_le_newton
    exact Nat.two_pow_pos _
  | succ n ih =>
    show Nat.sqrt A ≤ ProofForgeFin.Sqrt.newton A (nx A q (n + 1))
    apply ProofForgeFin.Sqrt.sqrt_le_newton
    have hs : 0 < Nat.sqrt A := ProofForgeFin.Sqrt.sqrt_pos (by omega)
    omega

theorem pow_le_nx (A q : Nat) (h0 : A ≠ 0) (hq : q = Nat.log2 A / 2)
    (n : Nat) : 2 ^ q ≤ nx A q n := by
  cases n with
  | zero => exact Nat.le_refl _
  | succ n =>
    have h1 : 2 ^ q ≤ Nat.sqrt A := by rw [hq]; exact pow_le_sqrt_aux A h0
    have h2 : Nat.sqrt A ≤ nx A q (n + 1) := sqrt_le_nx_succ A q h0 hq n
    omega

theorem nx_le_succ_bound (A q : Nat) (h0 : A ≠ 0) (hq : q = Nat.log2 A / 2)
    (n : Nat) : nx A q (n + 1) ≤ nx A q 1 + 1 := by
  have hsqrt : ∀ m : Nat, Nat.sqrt A ≤ nx A q (m + 1) := fun m =>
    sqrt_le_nx_succ A q h0 hq m
  induction n with
  | zero => exact Nat.le_succ _
  | succ n ih =>
    have hle : Nat.sqrt A ≤ nx A q (n + 1) := hsqrt n
    have hX1 : Nat.sqrt A ≤ nx A q 1 := hsqrt 0
    have hspos : 0 < Nat.sqrt A := ProofForgeFin.Sqrt.sqrt_pos (by omega)
    have hpos : 0 < nx A q (n + 1) := by omega
    have hgoal : nx A q (n + 1 + 1) =
        ProofForgeFin.Sqrt.newton A (nx A q (n + 1)) := rfl
    rw [hgoal]
    rcases Nat.lt_or_ge (Nat.sqrt A) (nx A q (n + 1)) with hlt | hge
    · have hlt2 : ProofForgeFin.Sqrt.newton A (nx A q (n + 1)) <
          nx A q (n + 1) :=
        ProofForgeFin.Sqrt.newton_lt_self hlt
      omega
    · have heq : nx A q (n + 1) = Nat.sqrt A := by omega
      rw [heq]
      have hmem := ProofForgeFin.Sqrt.newton_of_mem hpos hle (by omega)
      rw [heq] at hmem
      rcases hmem with h | h
      · omega
      · obtain ⟨-, h2, -⟩ := h
        omega

theorem div_four_bound (A : Nat) (h0 : A ≠ 0) :
    A / 2 ^ (Nat.log2 A / 2) < 4 * 2 ^ (Nat.log2 A / 2) := by
  have hAup : A < 2 ^ (Nat.log2 A + 1) := (ProofForgeFin.Evm.log2_spec h0).2
  have hle : Nat.log2 A + 1 ≤ 2 * (Nat.log2 A / 2) + 2 := by omega
  have hcap : A < 2 ^ (2 * (Nat.log2 A / 2) + 2) :=
    Nat.lt_of_lt_of_le hAup (Nat.pow_le_pow_right (by decide) hle)
  have hpow : (2 : Nat) ^ (2 * (Nat.log2 A / 2) + 2)
      = (4 * 2 ^ (Nat.log2 A / 2)) * 2 ^ (Nat.log2 A / 2) := by
    have e1 : 2 * (Nat.log2 A / 2) + 2 =
        (Nat.log2 A / 2) + (2 + (Nat.log2 A / 2)) := by omega
    rw [e1, Nat.pow_add, Nat.pow_add]
    have h4 : (2 : Nat) ^ 2 = 4 := by decide
    rw [h4]
    exact Nat.mul_comm _ _
  have hpos : 0 < 2 ^ (Nat.log2 A / 2) := Nat.two_pow_pos _
  rw [hpow] at hcap
  exact (Nat.div_lt_iff_lt_mul hpos).mpr hcap

theorem q_le127 (a : U256) (h0 : a.toNat ≠ 0) :
    Nat.log2 a.toNat / 2 ≤ 127 := by
  have hlog := log2_lt256 a h0
  omega

theorem nx_overflow (a : U256) (h0 : a.toNat ≠ 0) (n : Nat) :
    nx a.toNat (Nat.log2 a.toNat / 2) n +
      a.toNat / nx a.toNat (Nat.log2 a.toNat / 2) n < 2 ^ 256 := by
  have hq : Nat.log2 a.toNat / 2 = Nat.log2 a.toNat / 2 := rfl
  have hA256 : a.toNat < 2 ^ 256 := a.isLt
  have hq127 : Nat.log2 a.toNat / 2 ≤ 127 := q_le127 a h0
  have h2q : (2 : Nat) ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 127 :=
    Nat.pow_le_pow_right (by decide) hq127
  have hdiv4 : a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 4 * 2 ^ (Nat.log2 a.toNat / 2) :=
    div_four_bound a.toNat h0
  have h4pow : (4 : Nat) * 2 ^ (Nat.log2 a.toNat / 2) ≤ 4 * 2 ^ 127 := by
    apply Nat.mul_le_mul_left
    exact h2q
  cases n with
  | zero =>
    show 2 ^ (Nat.log2 a.toNat / 2) +
      a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 256
    omega
  | succ n =>
    have hlo : 2 ^ (Nat.log2 a.toNat / 2) ≤
        nx a.toNat (Nat.log2 a.toNat / 2) (n + 1) :=
      pow_le_nx a.toNat (Nat.log2 a.toNat / 2) h0 rfl (n + 1)
    have hposq : 0 < 2 ^ (Nat.log2 a.toNat / 2) := Nat.two_pow_pos _
    have hdivmono : a.toNat / nx a.toNat (Nat.log2 a.toNat / 2) (n + 1) ≤
        a.toNat / 2 ^ (Nat.log2 a.toNat / 2) :=
      Nat.div_le_div_left hlo hposq
    have hub : nx a.toNat (Nat.log2 a.toNat / 2) (n + 1) ≤
        nx a.toNat (Nat.log2 a.toNat / 2) 1 + 1 :=
      nx_le_succ_bound a.toNat (Nat.log2 a.toNat / 2) h0 rfl n
    have hX1 : ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) ≤
        3 * 2 ^ (Nat.log2 a.toNat / 2) := by
      unfold ProofForgeFin.Sqrt.newton
      omega
    have hX1eq : nx a.toNat (Nat.log2 a.toNat / 2) 1 =
        ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) := rfl
    rw [hX1eq] at hub
    omega

theorem e1_four_aux (x d s e1 : Nat) (hx : 0 < x) (hs : s = x + d) (hd : d ≤ x)
    (herr : 2 * x * e1 ≤ d * d + 2 * s) : 4 * e1 ≤ s + 8 := by
  have h1 : d * d ≤ d * x := Nat.mul_le_mul_left d hd
  have h2 : 2 * (d * d) ≤ 2 * (d * x) := Nat.mul_le_mul_left 2 h1
  have h3 : d * (x + 4) ≤ x * (x + 4) := Nat.mul_le_mul_right (x + 4) hd
  have h3e : d * x + d * 4 ≤ x * x + x * 4 := by
    have a : d * (x + 4) = d * x + d * 4 := Nat.mul_add d x 4
    have b : x * (x + 4) = x * x + x * 4 := Nat.mul_add x x 4
    rw [a] at h3
    rw [b] at h3
    exact h3
  have h3f : d * x + 4 * d ≤ x * x + 4 * x := by
    have h3c : d * 4 = 4 * d := Nat.mul_comm d 4
    have h4c : x * 4 = 4 * x := Nat.mul_comm x 4
    rw [h3c] at h3e
    rw [h4c] at h3e
    exact h3e
  have h5 : 2 * (d * d) + 4 * d ≤ 2 * (d * x) + 4 * d := Nat.add_le_add_right h2 (4 * d)
  have h6 : 2 * (d * x) + 4 * d ≤ x * x + d * x + 4 * x := by omega
  have h7 : 2 * (d * d) + 4 * d ≤ x * x + d * x + 4 * x := Nat.le_trans h5 h6
  have hs4 : 4 * s = 4 * x + 4 * d := by rw [hs]; exact Nat.mul_add 4 x d
  have h8 : 2 * (d * d) + 4 * s ≤ x * x + d * x + 8 * x := by omega
  have h9 : 2 * (2 * x * e1) ≤ 2 * (d * d + 2 * s) := Nat.mul_le_mul_left 2 herr
  have h9e : 2 * (d * d + 2 * s) = 2 * (d * d) + 4 * s := by
    have a : 2 * (d * d + 2 * s) = 2 * (d * d) + 2 * (2 * s) := Nat.mul_add 2 (d * d) (2 * s)
    have b : 2 * (2 * s) = 4 * s := by
      have c : (2 : Nat) * 2 = 4 := by decide
      calc 2 * (2 * s) = (2 * 2) * s := by rw [Nat.mul_assoc]
        _ = 4 * s := by rw [c]
    rw [a, b]
  have h10a : 4 * e1 * x = 2 * (2 * x * e1) := by ac_rfl
  have h10b : (s + 8) * x = x * x + d * x + 8 * x := by
    have a : (s + 8) * x = s * x + 8 * x := Nat.add_mul s 8 x
    have b : s * x = x * x + d * x := by
      rw [hs, Nat.add_mul, Nat.mul_comm d x]
    rw [a, b]
  have h10 : 4 * e1 * x ≤ (s + 8) * x := by
    calc 4 * e1 * x = 2 * (2 * x * e1) := h10a
      _ ≤ 2 * (d * d + 2 * s) := h9
      _ = 2 * (d * d) + 4 * s := h9e
      _ ≤ x * x + d * x + 8 * x := h8
      _ = (s + 8) * x := by rw [h10b]
  exact Nat.le_of_mul_le_mul_right h10 hx

theorem quad_step_aux (s e e' C K C' K' : Nat) (hs4 : 4 ≤ s) (hs0 : 0 < s)
    (hC : C * e ≤ s + K) (herr : (e' - 1) * (2 * s) ≤ e * e)
    (hC' : C' = 2 * C * C) (hK' : K' = 2 * K + K * K / 4 + C' + 1) :
    C' * e' ≤ s + K' := by
  by_cases he' : e' = 0
  · subst he'
    simp
  · have he1 : 1 ≤ e' := by omega
    have hCe2 : (C * e) * (C * e) ≤ (s + K) * (s + K) := Nat.mul_le_mul hC hC
    have hsq1 : (C * e) * (C * e) = (e * e) * (C * C) := by ac_rfl
    have hsq2 : (e * e) * (C * C) ≤ (s + K) * (s + K) := by
      rw [← hsq1]; exact hCe2
    have hmul1 : ((e' - 1) * (2 * s)) * (C * C) ≤ (e * e) * (C * C) :=
      Nat.mul_le_mul_right (C * C) herr
    have hmid_eq : (e' - 1) * C' * s = ((e' - 1) * (2 * s)) * (C * C) := by
      rw [hC']; ac_rfl
    have hmid : (e' - 1) * C' * s ≤ (s + K) * (s + K) := by
      rw [hmid_eq]; exact Nat.le_trans hmul1 hsq2
    have he'e : (e' - 1) + 1 = e' := Nat.sub_add_cancel he1
    have hCe'e : C' * e' = C' * (e' - 1) + C' := by
      conv => lhs; rw [← he'e, Nat.mul_add, Nat.mul_one]
    have hmod : 4 * (K * K / 4) + K * K % 4 = K * K := Nat.div_add_mod (K * K) 4
    have hmodlt : K * K % 4 < 4 := Nat.mod_lt _ (by decide)
    have hK4le : (K * K / 4) * 4 ≤ (K * K / 4) * s :=
      Nat.mul_le_mul_left (K * K / 4) hs4
    have hK4eq : (K * K / 4) * 4 = 4 * (K * K / 4) := Nat.mul_comm _ _
    have hKKs : K * K ≤ (K * K / 4) * s + s := by grind
    have hsq_expand : (s + K) * (s + K) = s * s + 2 * K * s + K * K := by
      grind
    have hgoal_mul : C' * e' * s ≤ (s + K') * s := by
      have e1 : C' * e' * s = (e' - 1) * C' * s + C' * s := by
        rw [hCe'e, Nat.add_mul, Nat.mul_comm (C') (e' - 1)]
      have e2 : (s + K') * s = s * s + K' * s := Nat.add_mul _ _ _
      have e3 : K' * s = (2 * K + K * K / 4 + C' + 1) * s := by rw [hK']
      have e4 : (2 * K + K * K / 4 + C' + 1) * s =
          2 * K * s + (K * K / 4) * s + C' * s + s := by
        have a1 : (2 * K + K * K / 4 + C' + 1) * s =
            (2 * K + K * K / 4 + C') * s + s := by
          rw [Nat.add_mul, Nat.one_mul]
        have a2 : (2 * K + K * K / 4 + C') * s =
            (2 * K + K * K / 4) * s + C' * s := by
          rw [Nat.add_mul]
        have a3 : (2 * K + K * K / 4) * s =
            (2 * K) * s + (K * K / 4) * s := by
          rw [Nat.add_mul]
        rw [a1, a2, a3]
      grind
    exact Nat.le_of_mul_le_mul_right hgoal_mul hs0

theorem sq_err_of_le_aux (s e e' : Nat) (hle : e' ≤ e * e / (2 * s) + 1) :
    (e' - 1) * (2 * s) ≤ e * e := by
  by_cases he' : e' = 0
  · subst he'
    simp
  · have he1 : 1 ≤ e' := by omega
    have h1 : e' - 1 ≤ e * e / (2 * s) := by omega
    have h2 : (e' - 1) * (2 * s) ≤ (e * e / (2 * s)) * (2 * s) :=
      Nat.mul_le_mul_right (2 * s) h1
    have h3 : (e * e / (2 * s)) * (2 * s) ≤ e * e :=
      Nat.div_mul_le_self (e * e) (2 * s)
    exact Nat.le_trans h2 h3

theorem s_lt_2x_aux (A : Nat) (h0 : A ≠ 0) :
    Nat.sqrt A < 2 * 2 ^ (Nat.log2 A / 2) := by
  have hAup : A < 2 ^ (Nat.log2 A + 1) := (ProofForgeFin.Evm.log2_spec h0).2
  have hle : Nat.log2 A + 1 ≤ 2 * ((Nat.log2 A / 2) + 1) := by omega
  have hcap : A < 2 ^ (2 * ((Nat.log2 A / 2) + 1)) :=
    Nat.lt_of_lt_of_le hAup (Nat.pow_le_pow_right (by decide) hle)
  have hs := ProofForgeFin.Sqrt.sqrt_lt_two_pow (k := (Nat.log2 A / 2) + 1) (a := A) (by omega)
  have heq : (2 : Nat) ^ ((Nat.log2 A / 2) + 1) = 2 * 2 ^ (Nat.log2 A / 2) := by
    rw [Nat.pow_add, Nat.pow_one]
    exact Nat.mul_comm _ _
  omega

theorem nx_pos_aux (A q : Nat) (h0 : A ≠ 0) (hq : q = Nat.log2 A / 2) (n : Nat) :
    0 < nx A q (n + 1) := by
  have hs : 0 < Nat.sqrt A := ProofForgeFin.Sqrt.sqrt_pos (by omega)
  have hle := sqrt_le_nx_succ A q h0 hq n
  omega

theorem e1_bound_aux (A : Nat) (h0 : A ≠ 0) :
    4 * (nx A (Nat.log2 A / 2) 1 - Nat.sqrt A) ≤ Nat.sqrt A + 8 := by
  have hxpos : 0 < 2 ^ (Nat.log2 A / 2) := Nat.two_pow_pos _
  have hxs : 2 ^ (Nat.log2 A / 2) ≤ Nat.sqrt A := pow_le_sqrt_aux A h0
  have hs2x : Nat.sqrt A < 2 * 2 ^ (Nat.log2 A / 2) := s_lt_2x_aux A h0
  have hs_eq : Nat.sqrt A = 2 ^ (Nat.log2 A / 2) + (Nat.sqrt A - 2 ^ (Nat.log2 A / 2)) := by
    omega
  have hd_le : Nat.sqrt A - 2 ^ (Nat.log2 A / 2) ≤ 2 ^ (Nat.log2 A / 2) := by omega
  have hnx1 : nx A (Nat.log2 A / 2) 1 = ProofForgeFin.Sqrt.newton A (2 ^ (Nat.log2 A / 2)) := rfl
  have herr : 2 * 2 ^ (Nat.log2 A / 2) *
      (ProofForgeFin.Sqrt.newton A (2 ^ (Nat.log2 A / 2)) - Nat.sqrt A) ≤
      (Nat.sqrt A - 2 ^ (Nat.log2 A / 2)) * (Nat.sqrt A - 2 ^ (Nat.log2 A / 2)) +
        2 * Nat.sqrt A :=
    ProofForgeFin.Sqrt.newton_err_below hxpos hxs
  have heq : nx A (Nat.log2 A / 2) 1 - Nat.sqrt A =
      ProofForgeFin.Sqrt.newton A (2 ^ (Nat.log2 A / 2)) - Nat.sqrt A := by
    rw [hnx1]
  rw [heq]
  exact e1_four_aux (2 ^ (Nat.log2 A / 2)) (Nat.sqrt A - 2 ^ (Nat.log2 A / 2))
    (Nat.sqrt A) _ hxpos hs_eq hd_le herr

theorem nx6_sq_le_aux (A : Nat) (h0 : A ≠ 0) (hA256 : A < 2 ^ 256)
    (hs4 : 4 ≤ Nat.sqrt A) :
    (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A) *
      (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A) ≤ Nat.sqrt A := by
  have hs0 : 0 < Nat.sqrt A := ProofForgeFin.Sqrt.sqrt_pos (by omega)
  have hs_lt128 : Nat.sqrt A < 2 ^ 128 := by
    have hcap : A < 2 ^ (2 * 128) := by
      have h1 : (2 : Nat) ^ 256 = 2 ^ (2 * 128) := by omega
      omega
    exact ProofForgeFin.Sqrt.sqrt_lt_two_pow hcap
  have hq : Nat.log2 A / 2 = Nat.log2 A / 2 := rfl
  have hC1 : 4 * (nx A (Nat.log2 A / 2) 1 - Nat.sqrt A) ≤ Nat.sqrt A + 8 :=
    e1_bound_aux A h0
  have hle1 : Nat.sqrt A ≤ nx A (Nat.log2 A / 2) 1 :=
    sqrt_le_nx_succ A _ h0 rfl 0
  have hle2 : Nat.sqrt A ≤ nx A (Nat.log2 A / 2) 2 :=
    sqrt_le_nx_succ A _ h0 rfl 1
  have hle3 : Nat.sqrt A ≤ nx A (Nat.log2 A / 2) 3 :=
    sqrt_le_nx_succ A _ h0 rfl 2
  have hle4 : Nat.sqrt A ≤ nx A (Nat.log2 A / 2) 4 :=
    sqrt_le_nx_succ A _ h0 rfl 3
  have hle5 : Nat.sqrt A ≤ nx A (Nat.log2 A / 2) 5 :=
    sqrt_le_nx_succ A _ h0 rfl 4
  have hle6 : Nat.sqrt A ≤ nx A (Nat.log2 A / 2) 6 :=
    sqrt_le_nx_succ A _ h0 rfl 5
  have hnx1eq : nx A (Nat.log2 A / 2) 2 =
      ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 1) := rfl
  have hnx2eq : nx A (Nat.log2 A / 2) 3 =
      ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 2) := rfl
  have hnx3eq : nx A (Nat.log2 A / 2) 4 =
      ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 3) := rfl
  have hnx4eq : nx A (Nat.log2 A / 2) 5 =
      ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 4) := rfl
  have hnx5eq : nx A (Nat.log2 A / 2) 6 =
      ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 5) := rfl
  have hq1 : ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 1) - Nat.sqrt A ≤
      (nx A (Nat.log2 A / 2) 1 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 1 - Nat.sqrt A) /
        (2 * Nat.sqrt A) + 1 :=
    ProofForgeFin.Sqrt.newton_sub_sqrt_le_sq_div hs0 hle1
  have herr1 : (nx A (Nat.log2 A / 2) 2 - Nat.sqrt A - 1) * (2 * Nat.sqrt A) ≤
      (nx A (Nat.log2 A / 2) 1 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 1 - Nat.sqrt A) := by
    have heq2 : nx A (Nat.log2 A / 2) 2 - Nat.sqrt A =
        ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 1) - Nat.sqrt A := by
      rw [hnx1eq]
    rw [heq2]
    exact sq_err_of_le_aux _ _ _ hq1
  have hC2 : 32 * (nx A (Nat.log2 A / 2) 2 - Nat.sqrt A) ≤ Nat.sqrt A + 65 := by
    have herr1' : ((nx A (Nat.log2 A / 2) 2 - Nat.sqrt A) - 1) * (2 * Nat.sqrt A) ≤
        (nx A (Nat.log2 A / 2) 1 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 1 - Nat.sqrt A) := by
      have : nx A (Nat.log2 A / 2) 2 - Nat.sqrt A - 1 =
          (nx A (Nat.log2 A / 2) 2 - Nat.sqrt A) - 1 := by omega
      rw [this]
      exact herr1
    exact quad_step_aux _ _ _ _ _ _ _ hs4 hs0 hC1 herr1' rfl rfl
  have hq2 : ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 2) - Nat.sqrt A ≤
      (nx A (Nat.log2 A / 2) 2 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 2 - Nat.sqrt A) /
        (2 * Nat.sqrt A) + 1 :=
    ProofForgeFin.Sqrt.newton_sub_sqrt_le_sq_div hs0 hle2
  have herr2 : (nx A (Nat.log2 A / 2) 3 - Nat.sqrt A - 1) * (2 * Nat.sqrt A) ≤
      (nx A (Nat.log2 A / 2) 2 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 2 - Nat.sqrt A) := by
    have heq3 : nx A (Nat.log2 A / 2) 3 - Nat.sqrt A =
        ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 2) - Nat.sqrt A := by
      rw [hnx2eq]
    rw [heq3]
    exact sq_err_of_le_aux _ _ _ hq2
  have hC3 : 2048 * (nx A (Nat.log2 A / 2) 3 - Nat.sqrt A) ≤ Nat.sqrt A + 3235 := by
    have herr2' : ((nx A (Nat.log2 A / 2) 3 - Nat.sqrt A) - 1) * (2 * Nat.sqrt A) ≤
        (nx A (Nat.log2 A / 2) 2 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 2 - Nat.sqrt A) := by
      have : nx A (Nat.log2 A / 2) 3 - Nat.sqrt A - 1 =
          (nx A (Nat.log2 A / 2) 3 - Nat.sqrt A) - 1 := by omega
      rw [this]
      exact herr2
    exact quad_step_aux _ _ _ _ _ _ _ hs4 hs0 hC2 herr2' rfl rfl
  have hq3 : ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 3) - Nat.sqrt A ≤
      (nx A (Nat.log2 A / 2) 3 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 3 - Nat.sqrt A) /
        (2 * Nat.sqrt A) + 1 :=
    ProofForgeFin.Sqrt.newton_sub_sqrt_le_sq_div hs0 hle3
  have herr3 : (nx A (Nat.log2 A / 2) 4 - Nat.sqrt A - 1) * (2 * Nat.sqrt A) ≤
      (nx A (Nat.log2 A / 2) 3 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 3 - Nat.sqrt A) := by
    have heq4 : nx A (Nat.log2 A / 2) 4 - Nat.sqrt A =
        ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 3) - Nat.sqrt A := by
      rw [hnx3eq]
    rw [heq4]
    exact sq_err_of_le_aux _ _ _ hq3
  have hC4 : 8388608 * (nx A (Nat.log2 A / 2) 4 - Nat.sqrt A) ≤ Nat.sqrt A + 11011385 := by
    have herr3' : ((nx A (Nat.log2 A / 2) 4 - Nat.sqrt A) - 1) * (2 * Nat.sqrt A) ≤
        (nx A (Nat.log2 A / 2) 3 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 3 - Nat.sqrt A) := by
      have : nx A (Nat.log2 A / 2) 4 - Nat.sqrt A - 1 =
          (nx A (Nat.log2 A / 2) 4 - Nat.sqrt A) - 1 := by omega
      rw [this]
      exact herr3
    exact quad_step_aux _ _ _ _ _ _ _ hs4 hs0 hC3 herr3' rfl rfl
  have hq4 : ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 4) - Nat.sqrt A ≤
      (nx A (Nat.log2 A / 2) 4 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 4 - Nat.sqrt A) /
        (2 * Nat.sqrt A) + 1 :=
    ProofForgeFin.Sqrt.newton_sub_sqrt_le_sq_div hs0 hle4
  have herr4 : (nx A (Nat.log2 A / 2) 5 - Nat.sqrt A - 1) * (2 * Nat.sqrt A) ≤
      (nx A (Nat.log2 A / 2) 4 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 4 - Nat.sqrt A) := by
    have heq5 : nx A (Nat.log2 A / 2) 5 - Nat.sqrt A =
        ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 4) - Nat.sqrt A := by
      rw [hnx4eq]
    rw [heq5]
    exact sq_err_of_le_aux _ _ _ hq4
  have hC5 : 140737488355328 * (nx A (Nat.log2 A / 2) 5 - Nat.sqrt A) ≤
      Nat.sqrt A + (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) := by
    have herr4' : ((nx A (Nat.log2 A / 2) 5 - Nat.sqrt A) - 1) * (2 * Nat.sqrt A) ≤
        (nx A (Nat.log2 A / 2) 4 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 4 - Nat.sqrt A) := by
      have : nx A (Nat.log2 A / 2) 5 - Nat.sqrt A - 1 =
          (nx A (Nat.log2 A / 2) 5 - Nat.sqrt A) - 1 := by omega
      rw [this]
      exact herr4
    exact quad_step_aux _ _ _ _ _ _ _ hs4 hs0 hC4 herr4' rfl rfl
  have hq5 : ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 5) - Nat.sqrt A ≤
      (nx A (Nat.log2 A / 2) 5 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 5 - Nat.sqrt A) /
        (2 * Nat.sqrt A) + 1 :=
    ProofForgeFin.Sqrt.newton_sub_sqrt_le_sq_div hs0 hle5
  have herr5 : (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A - 1) * (2 * Nat.sqrt A) ≤
      (nx A (Nat.log2 A / 2) 5 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 5 - Nat.sqrt A) := by
    have heq6 : nx A (Nat.log2 A / 2) 6 - Nat.sqrt A =
        ProofForgeFin.Sqrt.newton A (nx A (Nat.log2 A / 2) 5) - Nat.sqrt A := by
      rw [hnx5eq]
    rw [heq6]
    exact sq_err_of_le_aux _ _ _ hq5
  have hC6 : (2 * 140737488355328 * 140737488355328) *
      (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A) ≤
      Nat.sqrt A + (2 * (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) +
        (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) *
        (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) / 4 +
        (2 * 140737488355328 * 140737488355328) + 1) := by
    have herr5' : ((nx A (Nat.log2 A / 2) 6 - Nat.sqrt A) - 1) * (2 * Nat.sqrt A) ≤
        (nx A (Nat.log2 A / 2) 5 - Nat.sqrt A) * (nx A (Nat.log2 A / 2) 5 - Nat.sqrt A) := by
      have : nx A (Nat.log2 A / 2) 6 - Nat.sqrt A - 1 =
          (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A) - 1 := by omega
      rw [this]
      exact herr5
    exact quad_step_aux _ _ _ _ _ _ _ hs4 hs0 hC5 herr5' rfl rfl
  have hsq6 : (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A) *
      (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A) ≤ Nat.sqrt A := by
    have hC6' : (2 * 140737488355328 * 140737488355328) *
        (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A) ≤
        Nat.sqrt A + (2 * (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) +
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) *
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) / 4 +
          (2 * 140737488355328 * 140737488355328) + 1) := hC6
    have hCpos : 0 < 2 * 140737488355328 * 140737488355328 := by decide
    have h2pow : (2 : Nat) ^ 128 ≤
        (2 * 140737488355328 * 140737488355328) *
        (2 * 140737488355328 * 140737488355328) := by decide
    have hs128 : Nat.sqrt A < 2 ^ 128 := hs_lt128
    have hleC : Nat.sqrt A ≤
        (2 * 140737488355328 * 140737488355328) *
        (2 * 140737488355328 * 140737488355328) := by omega
    have hCe6sq : ((2 * 140737488355328 * 140737488355328) *
        (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A)) *
        ((2 * 140737488355328 * 140737488355328) *
        (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A)) ≤
        (Nat.sqrt A + (2 * (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) +
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) *
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) / 4 +
          (2 * 140737488355328 * 140737488355328) + 1)) *
        (Nat.sqrt A + (2 * (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) +
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) *
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) / 4 +
          (2 * 140737488355328 * 140737488355328) + 1)) :=
      Nat.mul_le_mul hC6' hC6'
    have hsq_eq : ((2 * 140737488355328 * 140737488355328) *
        (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A)) *
        ((2 * 140737488355328 * 140737488355328) *
        (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A)) =
        ((nx A (Nat.log2 A / 2) 6 - Nat.sqrt A) *
        (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A)) *
        ((2 * 140737488355328 * 140737488355328) *
        (2 * 140737488355328 * 140737488355328)) := by ac_rfl
    have hle_sq : ((nx A (Nat.log2 A / 2) 6 - Nat.sqrt A) *
        (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A)) *
        ((2 * 140737488355328 * 140737488355328) *
        (2 * 140737488355328 * 140737488355328)) ≤
        Nat.sqrt A *
        ((2 * 140737488355328 * 140737488355328) *
        (2 * 140737488355328 * 140737488355328)) := by
      have h1 : ((nx A (Nat.log2 A / 2) 6 - Nat.sqrt A) *
          (nx A (Nat.log2 A / 2) 6 - Nat.sqrt A)) *
          ((2 * 140737488355328 * 140737488355328) *
          (2 * 140737488355328 * 140737488355328)) ≤
          (Nat.sqrt A + (2 * (2 * 11011385 + 11011385 * 11011385 / 4 +
          140737488355328 + 1) +
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) *
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) / 4 +
          (2 * 140737488355328 * 140737488355328) + 1)) *
          (Nat.sqrt A + (2 * (2 * 11011385 + 11011385 * 11011385 / 4 +
          140737488355328 + 1) +
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) *
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) / 4 +
          (2 * 140737488355328 * 140737488355328) + 1)) := by
        rw [← hsq_eq]
        exact hCe6sq
      have hbound : (Nat.sqrt A + (2 * (2 * 11011385 + 11011385 * 11011385 / 4 +
          140737488355328 + 1) +
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) *
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) / 4 +
          (2 * 140737488355328 * 140737488355328) + 1)) *
          (Nat.sqrt A + (2 * (2 * 11011385 + 11011385 * 11011385 / 4 +
          140737488355328 + 1) +
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) *
          (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) / 4 +
          (2 * 140737488355328 * 140737488355328) + 1)) ≤
          Nat.sqrt A *
          ((2 * 140737488355328 * 140737488355328) *
          (2 * 140737488355328 * 140737488355328)) := by
        have hC6 : (2 : Nat) * 140737488355328 * 140737488355328 =
            2 * 140737488355328 * 140737488355328 := rfl
        have hK6 : (2 * (2 * 11011385 + 11011385 * 11011385 / 4 +
            140737488355328 + 1) +
            (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) *
            (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) / 4 +
            (2 * 140737488355328 * 140737488355328) + 1) =
            2 * (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) +
            (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) *
            (2 * 11011385 + 11011385 * 11011385 / 4 + 140737488355328 + 1) / 4 +
            (2 * 140737488355328 * 140737488355328) + 1 := rfl
        have h2pow_le : (2 : Nat) ^ 128 ≤
            (2 * 140737488355328 * 140737488355328) *
            (2 * 140737488355328 * 140737488355328) / 2 := by decide
        have hs_le : Nat.sqrt A ≤
            (2 * 140737488355328 * 140737488355328) *
            (2 * 140737488355328 * 140737488355328) / 2 := by omega
        have hss : Nat.sqrt A * Nat.sqrt A ≤
            Nat.sqrt A *
            ((2 * 140737488355328 * 140737488355328) *
            (2 * 140737488355328 * 140737488355328) / 2) :=
          Nat.mul_le_mul_left _ hs_le
        sorry
      exact Nat.le_trans h1 hbound
    exact Nat.le_of_mul_le_mul_right hle_sq (by decide)
  exact hsq6

theorem iterate_succ_apply_aux (f : U256 → U256) (n : Nat) (x : U256) :
    iterate f (n + 1) x = f (iterate f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have e1 : iterate f (n + 1 + 1) x = iterate f (n + 1) (f x) := rfl
    have e2 : iterate f (n + 1) x = iterate f n (f x) := rfl
    rw [e1, e2, ih]

theorem exact_iter (a : U256) (h0 : a.toNat ≠ 0) (n : Nat) :
    (iterate (newtonStep a) n ((1 : U256) <<< (log2 a >>> 1))).toNat =
      nx a.toNat (Nat.log2 a.toNat / 2) n := by
  induction n with
  | zero => exact init_val a
  | succ n ih =>
    have hov : (iterate (newtonStep a) n ((1 : U256) <<< (log2 a >>> 1))).toNat +
        a.toNat / (iterate (newtonStep a) n ((1 : U256) <<< (log2 a >>> 1))).toNat <
        2 ^ 256 := by
      rw [ih]
      exact nx_overflow a h0 n
    have e1 : iterate (newtonStep a) (n + 1) ((1 : U256) <<< (log2 a >>> 1)) =
        newtonStep a (iterate (newtonStep a) n ((1 : U256) <<< (log2 a >>> 1))) :=
      iterate_succ_apply_aux (newtonStep a) n _
    rw [e1, toNat_newtonStep _ _ hov, ih]
    rfl

theorem toNat_newtonSqrt7 (a : U256) (h0 : a.toNat ≠ 0) :
    (newtonSqrt 7 a).toNat =
      Nat.min (nx a.toNat (Nat.log2 a.toNat / 2) 7)
        (a.toNat / nx a.toNat (Nat.log2 a.toNat / 2) 7) := by
  have hne : ¬ a = 0 := by
    intro hc
    apply h0
    rw [hc]
    rfl
  unfold newtonSqrt
  rw [if_neg hne]
  have hex : (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat =
      nx a.toNat (Nat.log2 a.toNat / 2) 7 := exact_iter a h0 7
  have hmin : (OzSqrt.min
      (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
      (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))).toNat =
      Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
        (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat :=
    toNat_min _ _
  rw [hmin, hex, BitVec.toNat_udiv, hex]

theorem min_sq_le (A X : Nat) (hx : 0 < X) :
    Nat.min X (A / X) * Nat.min X (A / X) ≤ A := by
  have hle : A / X * X ≤ A := Nat.div_mul_le_self A X
  by_cases h : X ≤ A / X
  · have hmin : Nat.min X (A / X) = X := Nat.min_eq_left h
    rw [hmin]
    calc X * X ≤ (A / X) * X := Nat.mul_le_mul_right X h
      _ = A / X * X := by rw [Nat.mul_comm]
      _ ≤ A := hle
  · have hlt : A / X < X := by omega
    have hmin : Nat.min X (A / X) = A / X := Nat.min_eq_right (Nat.le_of_lt hlt)
    rw [hmin]
    calc A / X * (A / X) ≤ X * (A / X) :=
          Nat.mul_le_mul_right (A / X) (Nat.le_of_lt hlt)
      _ = A / X * X := by rw [Nat.mul_comm]
      _ ≤ A := hle

theorem sqrt_sq_le (a : U256) : (sqrt a).toNat * (sqrt a).toNat ≤ a.toNat := by
  by_cases h0 : a.toNat = 0
  · have ha0 : a = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
    subst ha0
    have hs0 : sqrt (0 : U256) = 0 := rfl
    have h1 : (sqrt (0 : U256)).toNat = 0 := by rw [hs0]; rfl
    have h2 : ((0 : U256)).toNat = 0 := rfl
    rw [h1, h2, Nat.zero_mul]
    exact Nat.le_refl _
  · have heq : sqrt a = newtonSqrt 7 a := sqrt_eq7 a
    have hto : (sqrt a).toNat =
        Nat.min (nx a.toNat (Nat.log2 a.toNat / 2) 7)
          (a.toNat / nx a.toNat (Nat.log2 a.toNat / 2) 7) := by
      rw [heq]
      exact toNat_newtonSqrt7 a h0
    rw [hto]
    have hpos : 0 < nx a.toNat (Nat.log2 a.toNat / 2) 7 := by
      have hlo := pow_le_nx a.toNat (Nat.log2 a.toNat / 2) h0 rfl 7
      have h2 : 0 < 2 ^ (Nat.log2 a.toNat / 2) := Nat.two_pow_pos _
      omega
    exact min_sq_le a.toNat _ hpos

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  exact sqrt_sq_le a

theorem req_newton_budget : NewtonBudget sqrt := by
  exact ⟨7, Nat.le_refl 7, sqrt_eq7⟩

theorem req_mint_backed : MintBacked sqrt := by
  intro a0 a1 l hl
  have h := firstMint_eq_some hl
  obtain ⟨hprod, _, hliqu⟩ := h
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat :=
    toNat_mul_of_lt hprod
  have hroot : (sqrt (a0 * a1)).toNat * (sqrt (a0 * a1)).toNat ≤
      (a0 * a1).toNat := sqrt_sq_le _
  rw [hmul, ← hliqu] at hroot
  exact hroot

theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry

end OzSqrt
