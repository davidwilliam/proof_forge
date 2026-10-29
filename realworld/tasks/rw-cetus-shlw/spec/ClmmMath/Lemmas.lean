import ClmmMath.Spec
/-!
# Helper lemmas and sanity theorems (protected, agent-visible)

Proved facts about the protected definitions `fullMul`, `absDiff`, `divRound` and `getDeltaA`.
They say nothing about any shift routine; a candidate may use them.

The two sanity theorems at the end show that the requirements are not vacuous:

* `attack_rejected`: every shift routine that meets REQ-SHLW-EXACT makes `getDeltaA` abort on
  the deposit of the May 2025 attack, instead of charging 1 unit of token A;
* `nonvacuous`: every shift routine that meets REQ-SHLW-EXACT and REQ-SHLW-COMPLETE makes
  `getDeltaA` return the exact rounded-up amount, 3045910951 units, on an ordinary deposit over
  the same price range. So REQ-DELTA-A-COVERS and REQ-DELTA-A-TIGHT constrain a real output and
  cannot be met by aborting.
-/

namespace ClmmMath

theorem two_pow_128_mul : (2 : Nat) ^ 128 * 2 ^ 128 = 2 ^ 256 := by decide

theorem toNat_fullMul (a b : BitVec 128) : (fullMul a b).toNat = a.toNat * b.toNat := by
  unfold fullMul
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 256 :=
    two_pow_128_mul ▸ Nat.mul_lt_mul_of_lt_of_lt ha hb
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans ha (by decide)), Nat.mod_eq_of_lt (Nat.lt_trans hb (by decide)),
    Nat.mod_eq_of_lt hab]

theorem toNat_absDiff (a b : BitVec 128) : (absDiff a b).toNat = priceDiff a b := by
  unfold absDiff priceDiff
  have ha := a.isLt
  have hb := b.isLt
  by_cases h : a > b
  · rw [ite_eq_left h, BitVec.toNat_sub]
    have h' : b.toNat < a.toNat := h
    rw [ite_eq_left (Nat.le_of_lt h')]
    omega
  · rw [ite_eq_right h, BitVec.toNat_sub]
    have h' : ¬ b.toNat < a.toNat := h
    by_cases h2 : b.toNat ≤ a.toNat
    · rw [ite_eq_left h2]; omega
    · rw [ite_eq_right h2]; omega

theorem absDiff_eq_zero (a b : BitVec 128) : absDiff a b = 0 ↔ priceDiff a b = 0 := by
  rw [← toNat_absDiff, BitVec.toNat_eq]
  simp

theorem divRound_eq_none (num denom : BitVec 256) (up : Bool) :
    divRound num denom up = none ↔ denom = 0 := by
  unfold divRound
  by_cases h : denom = 0
  · simp [h]
  · simp only [h, ite_false, iff_false]
    split <;> simp

/-- Rounding up: the result covers `num`, and one unit less does not. -/
theorem divRound_up (num denom q : BitVec 256) (h : divRound num denom true = some q) :
    num.toNat ≤ q.toNat * denom.toNat ∧ (0 < q.toNat → (q.toNat - 1) * denom.toNat < num.toNat) := by
  unfold divRound at h
  have hn := num.isLt
  by_cases h0 : denom = 0
  · simp [h0] at h
  have hd : 0 < denom.toNat := by
    rcases Nat.eq_zero_or_pos denom.toNat with h' | h'
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h')) h0
    · exact h'
  rw [ite_eq_right h0] at h
  have hdiv : (num / denom).toNat = num.toNat / denom.toNat := BitVec.toNat_udiv
  have hle : num.toNat / denom.toNat * denom.toNat ≤ num.toNat := Nat.div_mul_le_self _ _
  have hmul : (num / denom * denom).toNat = num.toNat / denom.toNat * denom.toNat := by
    rw [BitVec.toNat_mul, hdiv, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hn)]
  have hlt := Nat.lt_div_mul_add (a := num.toNat) hd
  simp only [Bool.true_and] at h
  split at h
  · rename_i hne
    cases h
    have hne' : num / denom * denom ≠ num := by simpa using hne
    have hne'' : num.toNat / denom.toNat * denom.toNat ≠ num.toNat := by
      intro e; exact hne' (BitVec.eq_of_toNat_eq (hmul.trans e))
    have hq : num.toNat / denom.toNat ≤ num.toNat / denom.toNat * denom.toNat :=
      Nat.le_mul_of_pos_right _ hd
    have hp1 : (num / denom + 1).toNat = num.toNat / denom.toNat + 1 := by
      have h1 : (1 : BitVec 256).toNat = 1 := rfl
      rw [BitVec.toNat_add, hdiv, h1]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hp1, Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
    omega
  · rename_i heq
    cases h
    have heq' : num / denom * denom = num := by simpa using heq
    have he : num.toNat / denom.toNat * denom.toNat = num.toNat := by
      rw [← hmul, heq']
    have hq : num.toNat / denom.toNat ≤ num.toNat / denom.toNat * denom.toNat :=
      Nat.le_mul_of_pos_right _ hd
    rw [hdiv]
    refine ⟨Nat.le_of_eq he.symm, fun hp => ?_⟩
    rw [Nat.sub_mul, Nat.one_mul]
    omega

/-- Rounding down: the result times `denom` is at most `num`. -/
theorem divRound_down (num denom q : BitVec 256) (h : divRound num denom false = some q) :
    q.toNat * denom.toNat ≤ num.toNat := by
  unfold divRound at h
  by_cases h0 : denom = 0
  · simp [h0] at h
  rw [ite_eq_right h0] at h
  simp only [Bool.false_and, Bool.false_eq_true, ite_false, Option.some.injEq] at h
  subst h
  rw [BitVec.toNat_udiv]
  exact Nat.div_mul_le_self _ _

/-- `getDeltaA` depends on the shift routine only through its value at
`fullMul liquidity (absDiff sp0 sp1)`. -/
theorem getDeltaA_congr (s t : Shlw) (sp0 sp1 liquidity : BitVec 128) (up : Bool)
    (h : s (fullMul liquidity (absDiff sp0 sp1)) = t (fullMul liquidity (absDiff sp0 sp1))) :
    getDeltaA s sp0 sp1 liquidity up = getDeltaA t sp0 sp1 liquidity up := by
  unfold getDeltaA
  simp only [h]

/-- The outcomes of `getDeltaA`: zero for an empty range or no liquidity, an abort when the
shift reports overflow, and otherwise the rounded quotient if it fits in 64 bits. -/
theorem getDeltaA_cases (shlw : Shlw) (sp0 sp1 liquidity : BitVec 128) (up : Bool)
    (amount : BitVec 64) (h : getDeltaA shlw sp0 sp1 liquidity up = some amount) :
    (priceDiff sp0 sp1 = 0 ∨ liquidity.toNat = 0) ∧ amount = 0 ∨
    (priceDiff sp0 sp1 ≠ 0 ∧ liquidity.toNat ≠ 0 ∧
      (shlw (fullMul liquidity (absDiff sp0 sp1))).2 = false ∧
      ∃ q, divRound (shlw (fullMul liquidity (absDiff sp0 sp1))).1 (fullMul sp0 sp1) up = some q ∧
        q.toNat < 2 ^ 64 ∧ amount.toNat = q.toNat) := by
  unfold getDeltaA at h
  simp only at h
  by_cases hz : absDiff sp0 sp1 = 0 ∨ liquidity = 0
  · rw [ite_eq_left hz] at h
    cases h
    left
    refine ⟨?_, rfl⟩
    rcases hz with hz | hz
    · exact Or.inl ((absDiff_eq_zero _ _).mp hz)
    · exact Or.inr (by rw [hz]; rfl)
  · rw [ite_eq_right hz] at h
    have hd : priceDiff sp0 sp1 ≠ 0 := fun e => hz (Or.inl ((absDiff_eq_zero _ _).mpr e))
    have hl : liquidity.toNat ≠ 0 := fun e => hz (Or.inr (BitVec.eq_of_toNat_eq (by simpa using e)))
    right
    refine ⟨hd, hl, ?_⟩
    split at h
    · cases h
    · rename_i hf
      refine ⟨by simpa using hf, ?_⟩
      split at h
      · cases h
      · rename_i q hq
        split at h
        · rename_i hfit
          cases h
          refine ⟨q, hq, hfit, ?_⟩
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hfit]
        · cases h

/-- With a shift that reports overflow, `getDeltaA` aborts on a nonempty range with liquidity. -/
theorem getDeltaA_overflow (shlw : Shlw) (sp0 sp1 liquidity : BitVec 128) (up : Bool)
    (hd : absDiff sp0 sp1 ≠ 0) (hl : liquidity ≠ 0)
    (h : (shlw (fullMul liquidity (absDiff sp0 sp1))).2 = true) :
    getDeltaA shlw sp0 sp1 liquidity up = none := by
  unfold getDeltaA
  simp only
  rw [ite_eq_right (by intro h'; rcases h' with h' | h' <;> contradiction), ite_eq_left h]

/-! ## Sanity theorems: the requirements are not vacuous -/

/-- Every shift routine that meets REQ-SHLW-EXACT makes `get_delta_a` abort on the attack deposit
(tick range [300000, 300200], liquidity 10365647984364446732462244378333008). The original
`checked_shlw` charged 1 unit of token A for it (`witnesses/buggy_original.lean`). -/
theorem attack_rejected (shlw : Shlw) (hexact : ShlwExact shlw) (up : Bool) :
    getDeltaA shlw 60257519765924248467716150 60863087478126617965993239
      10365647984364446732462244378333008 up = none := by
  apply getDeltaA_overflow _ _ _ _ _ (by decide) (by decide)
  cases hf : (shlw (fullMul 10365647984364446732462244378333008
      (absDiff 60257519765924248467716150 60863087478126617965993239))).2 with
  | true => rfl
  | false =>
    have e := hexact _ hf
    have big : 2 ^ 256 ≤ (fullMul 10365647984364446732462244378333008
        (absDiff 60257519765924248467716150 60863087478126617965993239)).toNat * 2 ^ 64 := by
      decide
    have := (shlw (fullMul 10365647984364446732462244378333008
        (absDiff 60257519765924248467716150 60863087478126617965993239))).1.isLt
    omega

/-- Every shift routine that meets REQ-SHLW-EXACT and REQ-SHLW-COMPLETE makes `get_delta_a`
return 3045910951 units of token A, the exact amount rounded up, for liquidity 10^18 over the
attack's price range. -/
theorem nonvacuous (shlw : Shlw) (hexact : ShlwExact shlw) (hcomplete : ShlwComplete shlw) :
    getDeltaA shlw 60257519765924248467716150 60863087478126617965993239
      1000000000000000000 true = some 3045910951 := by
  have hf := hcomplete (fullMul 1000000000000000000
      (absDiff 60257519765924248467716150 60863087478126617965993239)) (by decide)
  have hv := hexact _ hf
  have hval : shlw (fullMul 1000000000000000000
      (absDiff 60257519765924248467716150 60863087478126617965993239)) =
      (11170752606298910867689489418975114715725824000000000000000000, false) := by
    refine Prod.ext (BitVec.eq_of_toNat_eq ?_) hf
    rw [hv]
    decide
  rw [getDeltaA_congr shlw (fun _ => (11170752606298910867689489418975114715725824000000000000000000, false))
    _ _ _ _ hval]
  decide

end ClmmMath
