import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.Sqrt
/-!
# Reference solution A (build team; hidden from agents)

Port of `Math.sqrt(uint256 a)` of OpenZeppelin Contracts v4.9.6 (commit
dc44c9f1a4c3b10af99492eed84f83ed244203f6, `contracts/utils/math/Math.sol` lines 152 to 183; the
same function in v4.8.0 and v5.0.x):

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

The proof: the estimate `E = 2^(log2 a / 2)` satisfies `E ≤ s < 2 * E` for the root `s`
(`seed_bounds`); the first step leaves an error of at most `s / 4 + 2` (`seed_step`); each further
step turns an error bound `s / 2^k + 2` into `s / 2^(2k+1) + 2` (`err_step`, from the exact error
relation `ProofForgeFin.Sqrt.newton_err_above`), so after six steps the error is at most
`s / 2^95 + 2`, whose square is at most `s` (`sq_le_of_err`); the seventh step then gives the root,
or the root plus one when `s * (s + 1) ≤ a`, and `min(result, a / result)` returns the root
(`ProofForgeFin.Sqrt.newton_eq_or_succ`, `min_div_eq_sqrt`). No step wraps (`word_step`). Inputs
whose root is below 4 are checked by evaluation (`sqrt_small`).
-/
namespace OzSqrt

open ProofForgeFin.Sqrt (newton)

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

theorem req_newton_budget : NewtonBudget sqrt := ⟨7, by decide, fun _ => rfl⟩

/-! ## The error analysis on natural numbers -/

/-- One step with the error bound `s / 2^k + 2` gives the error bound `s / 2^(2k+1) + 2`. -/
theorem err_step {A x k : Nat} (hs4 : 4 ≤ Nat.sqrt A) (hk : 2 ≤ k) (hsx : Nat.sqrt A ≤ x)
    (hd : x - Nat.sqrt A ≤ Nat.sqrt A / 2 ^ k + 2) :
    newton A x - Nat.sqrt A ≤ Nat.sqrt A / 2 ^ (2 * k + 1) + 2 := by
  have hx : 0 < x := by omega
  have e := ProofForgeFin.Sqrt.newton_err_above (a := A) hx hsx
  generalize Nat.sqrt A = s at *
  generalize newton A x - s = m at *
  generalize hP : 2 ^ k = P at hd
  have hP4 : 4 ≤ P := by
    rw [← hP]; exact Nat.le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) hk)
  have hpow : 2 ^ (2 * k + 1) = 2 * P * P := by
    rw [← hP, show 2 * k + 1 = (k + k) + 1 by omega, Nat.pow_succ, Nat.pow_add, Nat.mul_comm, ← Nat.mul_assoc]
  rw [hpow]
  generalize hq : s / P = q at hd
  generalize hQ : s / (2 * P * P) = Q
  have hqP : q * P ≤ s := by rw [← hq]; exact Nat.div_mul_le_self s P
  have hPP : 0 < 2 * P * P := by
    have : 0 < P := by omega
    exact Nat.mul_pos (Nat.mul_pos (by decide) this) this
  have hQs : s < (Q + 1) * (2 * P * P) := by
    rw [← hQ, Nat.succ_mul]; exact Nat.lt_div_mul_add hPP
  apply Nat.le_of_not_lt
  intro hlt
  have h1 : 2 * s * (Q + 3) ≤ 2 * x * m := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (x - s) * (x - s) ≤ (q + 2) * (q + 2) := Nat.mul_le_mul hd hd
  have e1 : 2 * s * (Q + 3) = 2 * s * (Q + 1) + 2 * s + 2 * s := by grind
  have e2 : (q + 2) * (q + 2) = q * q + 4 * q + 4 := by grind
  have h4 : q * q * (P * P) ≤ s * s := by
    have := Nat.mul_le_mul hqP hqP
    have e : q * P * (q * P) = q * q * (P * P) := by grind
    omega
  have h5 : s * s < s * ((Q + 1) * (2 * P * P)) := Nat.mul_lt_mul_of_pos_left hQs (by omega)
  have h6 : q * q < 2 * s * (Q + 1) := by
    have e : s * ((Q + 1) * (2 * P * P)) = 2 * s * (Q + 1) * (P * P) := by grind
    have : q * q * (P * P) < 2 * s * (Q + 1) * (P * P) := by omega
    exact Nat.lt_of_mul_lt_mul_right this
  have h7 : 4 * q ≤ s := by
    have : q * 4 ≤ q * P := Nat.mul_le_mul_left q hP4
    omega
  omega

/-- The first step from the estimate `E ≤ s < 2 * E` has the error bound `s / 4 + 2`. -/
theorem seed_step {A E : Nat} (hE : 0 < E) (hEs : E ≤ Nat.sqrt A) (hs2 : Nat.sqrt A < 2 * E) :
    newton A E - Nat.sqrt A ≤ Nat.sqrt A / 2 ^ 2 + 2 := by
  have e := ProofForgeFin.Sqrt.newton_err_below (a := A) hE hEs
  generalize Nat.sqrt A = s at *
  generalize newton A E - s = m at *
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hEs
  simp only [Nat.add_sub_cancel_left] at e
  generalize hQ : (E + t) / 2 ^ 2 = Q
  have hQs : E + t < (Q + 1) * 4 := by
    rw [← hQ, Nat.succ_mul]; exact Nat.lt_div_mul_add (by decide)
  apply Nat.le_of_not_lt
  intro hlt
  have h1 : 2 * E * (Q + 3) ≤ 2 * E * m := Nat.mul_le_mul_left _ (by omega)
  have h2 : E * (E + t) ≤ E * (4 * Q + 3) := Nat.mul_le_mul_left _ (by omega)
  have h3 : t * (t + 1) ≤ t * E := Nat.mul_le_mul_left _ (by omega)
  have h4 : (t + 1) * E ≤ E * E := Nat.mul_le_mul_right _ (by omega)
  have e1 : 2 * E * (Q + 3) = 2 * (E * Q) + 6 * E := by grind
  have e2 : E * (E + t) = E * E + t * E := by grind
  have e3 : E * (4 * Q + 3) = 4 * (E * Q) + 3 * E := by grind
  have e4 : t * (t + 1) = t * t + t := by grind
  have e5 : (t + 1) * E = t * E + E := by grind
  omega

/-- `err_step` with the lower bound of the next iterate. -/
theorem next_bound {A x k : Nat} (hs4 : 4 ≤ Nat.sqrt A) (hk : 2 ≤ k) (hsx : Nat.sqrt A ≤ x)
    (hd : x - Nat.sqrt A ≤ Nat.sqrt A / 2 ^ k + 2) :
    Nat.sqrt A ≤ newton A x ∧ newton A x - Nat.sqrt A ≤ Nat.sqrt A / 2 ^ (2 * k + 1) + 2 :=
  ⟨ProofForgeFin.Sqrt.sqrt_le_newton (by omega), err_step hs4 hk hsx hd⟩

/-- After six steps the square of the error is at most the root. -/
theorem sq_le_of_err {s d : Nat} (hs4 : 4 ≤ s) (hs : s < 2 ^ 128) (hd : d ≤ s / 2 ^ 95 + 2) :
    d * d ≤ s := by
  generalize hq : s / 2 ^ 95 = q at hd
  have hqs : q * 2 ^ 95 ≤ s := by rw [← hq]; exact Nat.div_mul_le_self s _
  have hq33 : q < 2 ^ 33 := by
    rw [← hq]; exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
      rw [← Nat.pow_add]; exact hs)
  have h1 : d * d ≤ (q + 2) * (q + 2) := Nat.mul_le_mul hd hd
  rcases Nat.eq_zero_or_pos q with h0 | h0
  · subst h0
    have : (0 + 2) * (0 + 2) = 4 := rfl
    clear hs hq33 hqs hq
    omega
  · generalize hP : (2 : Nat) ^ 33 = P at hq33
    have hP95 : (2 : Nat) ^ 95 = P * 2 ^ 62 := by rw [← hP, ← Nat.pow_add]
    rw [hP95] at hqs
    generalize hR : (2 : Nat) ^ 62 = R at hqs
    have hR' : 16 ≤ R := by rw [← hR]; decide
    clear hP95 hR hP hs hq hd
    have h2 : q * q ≤ q * P := Nat.mul_le_mul_left q (by omega)
    have h3 : q * P * 16 ≤ q * P * R := Nat.mul_le_mul_left _ hR'
    have e : (q + 2) * (q + 2) = q * q + 4 * q + 4 := by grind
    have e2 : q * (P * R) = q * P * R := by rw [Nat.mul_assoc]
    have h4 : q ≤ q * P := Nat.le_mul_of_pos_right q (by omega)
    omega

/-- Above the root by at most `s + 2` (and `s < 2^128`), a Newton line does not wrap. -/
theorem word_step {a r : U256} (hs : 0 < Nat.sqrt a.toNat) (hs128 : Nat.sqrt a.toNat < 2 ^ 128)
    (h1 : Nat.sqrt a.toNat ≤ r.toNat) (h2 : r.toNat ≤ 2 * Nat.sqrt a.toNat + 2) :
    ((r + a / r) >>> 1).toNat = newton a.toNat r.toNat := by
  have hlt := Nat.lt_succ_sqrt a.toNat
  generalize Nat.sqrt a.toNat = s at *
  have hr : 0 < r.toNat := by omega
  have hdiv : a.toNat / r.toNat ≤ a.toNat / s := Nat.div_le_div_left h1 hs
  have hdiv2 : a.toNat / s < s + 3 := by
    apply (Nat.div_lt_iff_lt_mul hs).mpr
    simp only [Nat.succ_eq_add_one] at hlt
    grind
  exact toNat_newtonStep a r (by omega)

/-- The estimate `1 << (log2(a) >> 1)` is `2^(log2 a / 2)`. -/
theorem toNat_seed (a : U256) : ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (Nat.log2 a.toNat / 2) := by
  have hL : Nat.log2 a.toNat < 256 := by
    rcases Nat.eq_zero_or_pos a.toNat with h | h
    · rw [h]; decide
    · exact (Nat.log2_lt (by omega)).mpr a.isLt
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, toNat_log2,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have : ((1 : U256)).toNat = 1 := rfl
  rw [this, Nat.one_mul, Nat.pow_one]
  apply Nat.mod_eq_of_lt
  exact Nat.pow_lt_pow_right (by decide) (by omega)

/-- The estimate is within a factor of two below the root. -/
theorem seed_bounds {A : Nat} (hA : 0 < A) :
    2 ^ (Nat.log2 A / 2) ≤ Nat.sqrt A ∧ Nat.sqrt A < 2 * 2 ^ (Nat.log2 A / 2) := by
  have h1 := Nat.log2_self_le (n := A) (by omega)
  have h2 := Nat.lt_log2_self (n := A)
  generalize Nat.log2 A = L at *
  constructor
  · apply ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le
    rw [← Nat.pow_add]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) h1
  · apply ProofForgeFin.Sqrt.sqrt_lt_of_lt_mul_self
    have e : 2 * 2 ^ (L / 2) * (2 * 2 ^ (L / 2)) = 2 ^ (L / 2 + 1 + (L / 2 + 1)) := by
      rw [Nat.pow_add, Nat.pow_succ]; grind
    rw [e]
    exact Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega))

/-- The routine returns the root for every input whose root is at least 4. -/
theorem toNat_sqrt_large (a : U256) (h0 : a ≠ 0) (hs4 : 4 ≤ Nat.sqrt a.toNat) :
    (sqrt a).toNat = Nat.sqrt a.toNat := by
  have hA : 0 < a.toNat := by
    rcases Nat.eq_zero_or_pos a.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
    · exact h
  have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
    ProofForgeFin.Sqrt.sqrt_lt_two_pow (k := 128) (by simpa using a.isLt)
  obtain ⟨hEs, hs2⟩ := seed_bounds hA
  have hseed := toNat_seed a
  unfold sqrt
  rw [ite_eq_right h0]
  simp only
  generalize (1 : U256) <<< (log2 a >>> 1) = r0 at hseed ⊢
  generalize hE : 2 ^ (Nat.log2 a.toNat / 2) = E at hEs hs2 hseed
  have hE0 : 0 < E := by rw [← hE]; exact Nat.two_pow_pos _
  -- step 1, from the estimate
  have b0 : r0.toNat + a.toNat / r0.toNat < 2 ^ 256 := by
    rw [hseed]
    have : a.toNat / E < 4 * E := by
      apply (Nat.div_lt_iff_lt_mul hE0).mpr
      have := Nat.lt_succ_sqrt a.toNat
      have h2 : Nat.sqrt a.toNat + 1 ≤ 2 * E := hs2
      have := ProofForgeFin.Sqrt.mul_self_le_mul_self h2
      simp only [Nat.succ_eq_add_one] at *
      grind
    have : E < 2 ^ 128 := by omega
    omega
  have v1 : ((r0 + a / r0) >>> 1).toNat = newton a.toNat E := by
    rw [← hseed]; exact toNat_newtonStep a r0 b0
  generalize (r0 + a / r0) >>> 1 = r1 at v1 ⊢
  have d1 := seed_step (A := a.toNat) hE0 hEs hs2
  have l1 : Nat.sqrt a.toNat ≤ newton a.toNat E := ProofForgeFin.Sqrt.sqrt_le_newton hE0
  rw [← v1] at d1 l1
  -- steps 2 to 6
  have hspos : 0 < Nat.sqrt a.toNat := by omega
  have v2 := word_step (r := r1) hspos hs128 l1 (by omega)
  have ⟨l2, d2⟩ := next_bound hs4 (by decide) l1 d1
  rw [← v2] at l2 d2
  generalize (r1 + a / r1) >>> 1 = r2 at l2 d2 ⊢
  have v3 := word_step (r := r2) hspos hs128 l2 (by omega)
  have ⟨l3, d3⟩ := next_bound hs4 (by decide) l2 d2
  rw [← v3] at l3 d3
  generalize (r2 + a / r2) >>> 1 = r3 at l3 d3 ⊢
  have v4 := word_step (r := r3) hspos hs128 l3 (by omega)
  have ⟨l4, d4⟩ := next_bound hs4 (by decide) l3 d3
  rw [← v4] at l4 d4
  generalize (r3 + a / r3) >>> 1 = r4 at l4 d4 ⊢
  have v5 := word_step (r := r4) hspos hs128 l4 (by omega)
  have ⟨l5, d5⟩ := next_bound hs4 (by decide) l4 d4
  rw [← v5] at l5 d5
  generalize (r4 + a / r4) >>> 1 = r5 at l5 d5 ⊢
  have v6 := word_step (r := r5) hspos hs128 l5 (by omega)
  have ⟨l6, d6⟩ := next_bound hs4 (by decide) l5 d5
  rw [← v6] at l6 d6
  generalize (r5 + a / r5) >>> 1 = r6 at l6 d6 ⊢
  -- step 7 and the final `min`
  have v7 := word_step (r := r6) hspos hs128 l6 (by omega)
  have sq := sq_le_of_err hs4 hs128 d6
  have hr6 : 0 < r6.toNat := by omega
  have t7 := ProofForgeFin.Sqrt.newton_eq_or_succ (a := a.toNat) hr6 l6 sq
  rw [← v7] at t7
  generalize (r6 + a / r6) >>> 1 = r7 at t7 ⊢
  have hr7 : 0 < r7.toNat := by omega
  rw [toNat_min, BitVec.toNat_udiv]
  exact ProofForgeFin.Sqrt.min_div_eq_sqrt hr7 t7

/-- The routine returns the root on the inputs below 16, checked by evaluation. -/
theorem sqrt_small : ∀ n, n < 16 →
    (sqrt (BitVec.ofNat 256 n)).toNat * (sqrt (BitVec.ofNat 256 n)).toNat ≤ n ∧
      n < ((sqrt (BitVec.ofNat 256 n)).toNat + 1) * ((sqrt (BitVec.ofNat 256 n)).toNat + 1) := by
  decide

/-- `Math.sqrt` returns the floor of the square root on every `uint256`. -/
theorem toNat_sqrt (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  by_cases h0 : a = 0
  · subst h0
    exact (ProofForgeFin.Sqrt.sqrt_eq_of_bounds (r := 0) (by decide) (by decide)).symm
  by_cases hs4 : 4 ≤ Nat.sqrt a.toNat
  · exact toNat_sqrt_large a h0 hs4
  · have h16 : a.toNat < 16 := by
      have := Nat.lt_succ_sqrt a.toNat
      have := ProofForgeFin.Sqrt.mul_self_le_mul_self (show Nat.sqrt a.toNat + 1 ≤ 4 by omega)
      simp only [Nat.succ_eq_add_one] at *
      omega
    have hb := sqrt_small a.toNat h16
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
    exact (ProofForgeFin.Sqrt.sqrt_eq_of_bounds hb.1 hb.2).symm

theorem req_sqrt_not_above : SqrtNotAbove sqrt := fun a => by
  rw [toNat_sqrt]; exact Nat.sqrt_le _

theorem req_sqrt_not_below : SqrtNotBelow sqrt := fun a => by
  rw [toNat_sqrt]; exact Nat.lt_succ_sqrt _

/-- The root rounded up, on values. -/
theorem toNat_sqrtUp (a : U256) :
    (sqrtUp sqrt a).toNat = Nat.sqrt a.toNat + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  have hs : Nat.sqrt a.toNat < 2 ^ 128 :=
    ProofForgeFin.Sqrt.sqrt_lt_two_pow (k := 128) (by simpa using a.isLt)
  have hsq : Nat.sqrt a.toNat * Nat.sqrt a.toNat < 2 ^ 256 := by
    have := Nat.mul_lt_mul_of_lt_of_lt hs hs
    rw [← Nat.pow_add] at this; exact this
  unfold sqrtUp
  simp only
  have hmul : (sqrt a * sqrt a).toNat = Nat.sqrt a.toNat * Nat.sqrt a.toNat := by
    rw [BitVec.toNat_mul, toNat_sqrt, Nat.mod_eq_of_lt hsq]
  by_cases h : sqrt a * sqrt a < a
  · have h' : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
      have := BitVec.lt_def.mp h; rw [hmul] at this; exact this
    rw [ite_eq_left h, ite_eq_left h', BitVec.toNat_add, toNat_sqrt]
    have : (1 : U256).toNat = 1 := rfl
    rw [this, Nat.mod_eq_of_lt (by omega)]
  · have h' : ¬ Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := fun c =>
      h (BitVec.lt_def.mpr (by rw [hmul]; exact c))
    rw [ite_eq_right h, ite_eq_right h']
    simp [toNat_sqrt]

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := fun a => by
  rw [toNat_sqrtUp]
  have h1 := Nat.lt_succ_sqrt a.toNat
  by_cases h : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat
  · rw [ite_eq_left h]; exact Nat.le_of_lt h1
  · rw [ite_eq_right h, Nat.add_zero]; omega

theorem req_sqrt_up_tight : SqrtUpTight sqrt := fun a hpos => by
  rw [toNat_sqrtUp] at hpos ⊢
  have h0 := Nat.sqrt_le a.toNat
  by_cases h : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat
  · rw [ite_eq_left h, Nat.add_sub_cancel]; exact h
  · rw [ite_eq_right h, Nat.add_zero] at hpos ⊢
    have : Nat.sqrt a.toNat - 1 < Nat.sqrt a.toNat := by omega
    have := Nat.mul_self_lt_mul_self this
    omega

theorem req_mint_backed : MintBacked sqrt := fun a0 a1 l h => by
  obtain ⟨h1, _, h3⟩ := firstMint_eq_some h
  rw [h3, toNat_sqrt, toNat_mul_of_lt h1]
  exact Nat.sqrt_le _

theorem req_mint_full : MintFull sqrt := fun a0 a1 l h => by
  obtain ⟨h1, _, h3⟩ := firstMint_eq_some h
  rw [show l.toNat + 1001 = l.toNat + 1000 + 1 by omega, h3, toNat_sqrt, toNat_mul_of_lt h1]
  exact Nat.lt_succ_sqrt _

theorem req_mint_live : MintLive sqrt := fun a0 a1 h1 h2 => by
  apply firstMint_isSome h1
  rw [toNat_sqrt, toNat_mul_of_lt h1]
  have := ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le h2
  omega

end OzSqrt
