import BalancerSwap.Spec
/-!
Fixed swap wrapper: every conversion rounds in the pool's favour.

* given-in: price the exact net amount in (`netInDown`), pay out rounded down.
* given-out: price the exact amount out rounded up (`scaleUp`), charge rounded up
  (single ceiling division by `(ONE - fee) * rateIn`).

Both directions refuse the boundary cases that the pool math does not cover
(`rateOut = 0`, `Q = 0`, `x >= balanceOut`), so every successful swap is covered
by `WellBehaved` and never lowers `value`.
-/
namespace BalancerSwap

theorem ONE_pos : 0 < ONE := by decide

theorem ONE_ne_zero : ONE ≠ 0 := Nat.ne_of_gt ONE_pos

theorem ONEONE_pos : 0 < ONE * ONE := Nat.mul_pos ONE_pos ONE_pos

theorem ceil_ge (a d : Nat) (hd : 0 < d) : a ≤ (a + (d - 1)) / d * d := by
  have h1 := Nat.div_add_mod (a + (d - 1)) d
  have h2 := Nat.mod_lt (a + (d - 1)) hd
  rw [Nat.mul_comm]
  omega

theorem ceil_le {a d q : Nat} (hd : 0 < d) (h : a ≤ q * d) : (a + (d - 1)) / d ≤ q := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hd).2
  rw [Nat.succ_mul]
  omega

theorem floor_lt_succ_mul (a r : Nat) (hr : 0 < r) :
    a < (a / r + 1) * r := by
  have h1 := Nat.div_add_mod a r
  have h2 := Nat.mod_lt a hr
  have e : (a / r + 1) * r = r * (a / r) + r := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (a / r) r]
  rw [e]
  omega

theorem floor_mul_le (a r : Nat) : a / r * r ≤ a := Nat.div_mul_le_self _ _

theorem sub_mul_eq (c q : Nat) : (c - 1) * q = c * q - q := by
  rw [Nat.sub_mul, Nat.one_mul]

theorem ceil_mul_ge_of_pos (P Q : Nat) (hQ : 0 < Q) :
    P ≤ (P + Q - 1) / Q * Q := by
  have h : P + (Q - 1) = P + Q - 1 := by omega
  rw [← h]
  exact ceil_ge P Q hQ

theorem div_pos_of_le (a b : Nat) (h : b ≤ a) (hb : 0 < b) : 0 < a / b :=
  Nat.div_pos h hb

/-! ## Implementation -/

/-- Round down back to raw units; fails on zero scaling factor. -/
def downscaleDown (amount rate : Nat) : Option Nat :=
  if rate = 0 then none else some (amount * ONE / rate)

/-- Given-in: price `netInDown`, pay out rounded down. -/
def swapGivenIn (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s))
    (p.rate s.tokenOut)

/-- Given-out: price `scaleUp`, charge rounded up in one ceiling division. -/
def swapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  if scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) then none
  else if (ONE - p.fee) * p.rate s.tokenIn = 0 then none
  else some ((m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
      (ONE - p.fee) * p.rate s.tokenIn - 1) /
      ((ONE - p.fee) * p.rate s.tokenIn))

/-- `onSwap` for a regular swap. -/
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn => swapGivenIn m p s
  | .givenOut => swapGivenOut m p s

theorem downscaleDown_some {a r y : Nat} (h : downscaleDown a r = some y) :
    r ≠ 0 ∧ y = a * ONE / r := by
  unfold downscaleDown at h
  by_cases hr : r = 0
  · rw [if_pos hr] at h
    cases h
  · rw [if_neg hr] at h
    cases h
    exact ⟨hr, rfl⟩

theorem swapGivenIn_eq {m : PoolMath} {p : Pool} {s : Swap} {y : Nat}
    (h : swapGivenIn m p s = some y) :
    p.rate s.tokenOut ≠ 0 ∧
    y = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut := by
  unfold swapGivenIn at h
  exact downscaleDown_some h

theorem swapGivenOut_eq {m : PoolMath} {p : Pool} {s : Swap} {c : Nat}
    (h : swapGivenOut m p s = some c) :
    scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut ∧
    (ONE - p.fee) * p.rate s.tokenIn ≠ 0 ∧
    c = (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
      (ONE - p.fee) * p.rate s.tokenIn - 1) /
      ((ONE - p.fee) * p.rate s.tokenIn) := by
  unfold swapGivenOut at h
  by_cases hle : scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut)
  · rw [if_pos hle] at h
    cases h
  · rw [if_neg hle] at h
    have hlt : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut := by
      omega
    refine ⟨hlt, ?_, ?_⟩
    · by_cases hQ : (ONE - p.fee) * p.rate s.tokenIn = 0
      · rw [if_pos hQ] at h
        cases h
      · rw [if_neg hQ] at h
        cases h
        exact hQ
    · by_cases hQ : (ONE - p.fee) * p.rate s.tokenIn = 0
      · rw [if_pos hQ] at h
        cases h
      · rw [if_neg hQ] at h
        cases h
        rfl

theorem scaledBalances_eq (p : Pool) (k : Nat) :
    scaledBalances p k = p.balance k * p.rate k / ONE := rfl

theorem scaleUp_eq (a r : Nat) : scaleUp a r = (a * r + (ONE - 1)) / ONE := rfl

theorem netInDown_eq (p : Pool) (s : Swap) :
    netInDown p s = s.amount * (ONE - p.fee) * p.rate s.tokenIn / (ONE * ONE) := rfl

theorem netLess_le_net (p : Pool) (s : Swap) :
    netInLessOneDown p s ≤ netInDown p s := by
  unfold netInLessOneDown netInDown
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_right
  exact Nat.sub_le _ _

theorem scaleUp_ge_mul (a r : Nat) :
    a * r ≤ scaleUp a r * ONE := by
  unfold scaleUp
  by_cases hr0 : r = 0
  · subst hr0
    rw [Nat.mul_zero]
    exact Nat.zero_le _
  · exact ceil_ge (a * r) ONE ONE_pos

theorem scaleDown_mul_le (a r : Nat) : scaleDown a r * ONE ≤ a * r := by
  unfold scaleDown
  exact Nat.div_mul_le_self _ _

theorem scaleDown_le_scaleUp_of_le {a b r : Nat} (hba : b ≤ a) :
    scaleDown b r ≤ scaleUp a r := by
  unfold scaleDown scaleUp
  by_cases hr0 : r = 0
  · subst hr0
    rw [Nat.mul_zero, Nat.mul_zero, Nat.zero_add]
    exact Nat.div_le_div_right (Nat.zero_le _)
  · have h1 : b * r ≤ a * r := Nat.mul_le_mul_right r hba
    have h2 : (b * r / ONE) * ONE ≤ b * r := Nat.div_mul_le_self _ _
    have h3 : a * r ≤ (a * r + (ONE - 1)) / ONE * ONE := ceil_ge _ _ ONE_pos
    have hle : (b * r / ONE) * ONE ≤ (a * r + (ONE - 1)) / ONE * ONE := by
      calc (b * r / ONE) * ONE ≤ b * r := h2
        _ ≤ a * r := h1
        _ ≤ (a * r + (ONE - 1)) / ONE * ONE := h3
    have h6 : b * r / ONE ≤ (a * r + (ONE - 1)) / ONE :=
      Nat.le_of_mul_le_mul_right hle ONE_pos
    exact h6

theorem scaleUp_lt_of_le_balance {a b r : Nat}
    (h : scaleUp a r < scaleDown b r) : a ≤ b := by
  have hnb : ¬ b ≤ a := by
    intro hba
    have hle := scaleDown_le_scaleUp_of_le (a := a) (b := b) (r := r) hba
    omega
  omega

theorem div_mul_le_self' (a b : Nat) : a / b * b ≤ a := Nat.div_mul_le_self _ _

theorem le_of_mul_le_mul_right' {a b c : Nat} (h : a * c ≤ b * c) (hc : 0 < c) :
    a ≤ b := Nat.le_of_mul_le_mul_right h hc

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s hwb hkind hvalid hrate hfee
  have hne : s.tokenIn ≠ s.tokenOut := hvalid.1
  have htin : s.tokenIn < p.n := hvalid.2.1
  have htout : s.tokenOut < p.n := hvalid.2.2
  have hRne : p.rate s.tokenOut ≠ 0 := Nat.ne_of_gt hrate
  have hon : onSwap m p s = swapGivenIn m p s := by
    unfold onSwap
    rw [hkind]
  unfold step
  rw [if_pos hvalid, hon]
  unfold swapGivenIn downscaleDown
  rw [if_neg hRne]
  simp only
  unfold settle amountOut
  rw [hkind]
  simp only
  have hMle : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
      ≤ scaledBalances p s.tokenOut := (hwb.outGivenIn _ _ _ _ hne htin htout).1
  rw [scaledBalances_eq] at hMle
  have hy_le : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) *
      ONE / p.rate s.tokenOut ≤ p.balance s.tokenOut := by
    have h1 : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE /
        p.rate s.tokenOut) * p.rate s.tokenOut ≤
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
      Nat.div_mul_le_self _ _
    have h2 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE ≤
        p.balance s.tokenOut * p.rate s.tokenOut := by
      have ha : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE ≤
          (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE :=
        Nat.mul_le_mul_right ONE hMle
      have hb : (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE ≤
          p.balance s.tokenOut * p.rate s.tokenOut :=
        Nat.div_mul_le_self _ _
      exact Nat.le_trans ha hb
    have h3 : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE /
        p.rate s.tokenOut) * p.rate s.tokenOut ≤
        p.balance s.tokenOut * p.rate s.tokenOut :=
      Nat.le_trans h1 h2
    exact Nat.le_of_mul_le_mul_right h3 hrate
  rw [if_pos hy_le]
  rfl

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  intro m p s hwb hkind hvalid hrate hfee hx
  have hne : s.tokenIn ≠ s.tokenOut := hvalid.1
  have htin : s.tokenIn < p.n := hvalid.2.1
  have htout : s.tokenOut < p.n := hvalid.2.2
  have hon : onSwap m p s = swapGivenOut m p s := by
    unfold onSwap
    rw [hkind]
  have hQpos : 0 < (ONE - p.fee) * p.rate s.tokenIn :=
    Nat.mul_pos (by omega) hrate
  have hQne : (ONE - p.fee) * p.rate s.tokenIn ≠ 0 := Nat.ne_of_gt hQpos
  have heq : scaledBalances p s.tokenOut =
      scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := rfl
  have hlt : ¬ scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) := by
    omega
  unfold step
  rw [if_pos hvalid, hon]
  unfold swapGivenOut
  rw [if_neg hlt, if_neg hQne]
  simp only
  unfold settle amountOut
  rw [hkind]
  simp only
  have hab : s.amount ≤ p.balance s.tokenOut :=
    scaleUp_lt_of_le_balance hx
  rw [if_pos hab]
  rfl

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y hmono hkind hvalid himpl
  have hon : onSwap m p s = swapGivenIn m p s := by
    unfold onSwap
    rw [hkind]
  rw [hon] at himpl
  have hspec := swapGivenIn_eq himpl
  have hRne := hspec.1
  have hy : y = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) *
      ONE / p.rate s.tokenOut := hspec.2
  rw [hy]
  have hle : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE /
      p.rate s.tokenOut) * p.rate s.tokenOut ≤
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
    Nat.div_mul_le_self _ _
  calc (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE /
        p.rate s.tokenOut) * p.rate s.tokenOut
      ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := hle
    _ = ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by
      rw [Nat.mul_comm]

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s y hmono hkind hvalid himpl
  have hon : onSwap m p s = swapGivenIn m p s := by
    unfold onSwap
    rw [hkind]
  rw [hon] at himpl
  have hspec := swapGivenIn_eq himpl
  have hRne := hspec.1
  have hy : y = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) *
      ONE / p.rate s.tokenOut := hspec.2
  have hRpos : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hRne
  have hle_net := netLess_le_net p s
  have hmono_out := hmono.1
  have hMle : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
    hmono_out _ _ _ _ _ hle_net
  have hlt : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE <
      (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE /
        p.rate s.tokenOut + 1) * p.rate s.tokenOut :=
    floor_lt_succ_mul _ _ hRpos
  rw [hy]
  have hle2 : ONE *
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤
        ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
    Nat.mul_le_mul_left ONE hMle
  have heq : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) =
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
    rw [Nat.mul_comm]
  omega

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c hmono hkind hvalid himpl
  have hon : onSwap m p s = swapGivenOut m p s := by
    unfold onSwap
    rw [hkind]
  rw [hon] at himpl
  have hspec := swapGivenOut_eq himpl
  have hQne := hspec.2.1
  have hc : c = (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
      (ONE - p.fee) * p.rate s.tokenIn - 1) /
      ((ONE - p.fee) * p.rate s.tokenIn) := hspec.2.2
  have hQpos : 0 < (ONE - p.fee) * p.rate s.tokenIn := Nat.pos_of_ne_zero hQne
  unfold outPrice
  rw [hc]
  have hP : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE ≤
      (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
        (ONE - p.fee) * p.rate s.tokenIn - 1) /
        ((ONE - p.fee) * p.rate s.tokenIn) * ((ONE - p.fee) * p.rate s.tokenIn) :=
    ceil_mul_ge_of_pos _ _ hQpos
  have heqL : ONE * ONE *
      m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) =
      m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE := by
    calc ONE * ONE *
          m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
            (scaleUp s.amount (p.rate s.tokenOut))
        = (ONE * ONE) *
          m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
            (scaleUp s.amount (p.rate s.tokenOut)) := rfl
      _ = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
            (scaleUp s.amount (p.rate s.tokenOut)) * (ONE * ONE) :=
        Nat.mul_comm _ _
      _ = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
            (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE :=
        (Nat.mul_assoc _ _ _).symm
  have heqR : (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
          (ONE - p.fee) * p.rate s.tokenIn - 1) /
          ((ONE - p.fee) * p.rate s.tokenIn) * (ONE - p.fee) * p.rate s.tokenIn =
        (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
          (ONE - p.fee) * p.rate s.tokenIn - 1) /
          ((ONE - p.fee) * p.rate s.tokenIn) * ((ONE - p.fee) * p.rate s.tokenIn) := by
    rw [Nat.mul_assoc]
  rw [heqL, heqR]
  exact hP

theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := by
  intro m p s c hmono hkind hvalid himpl
  have hon : onSwap m p s = swapGivenOut m p s := by
    unfold onSwap
    rw [hkind]
  rw [hon] at himpl
  have hspec := swapGivenOut_eq himpl
  have hQne := hspec.2.1
  have hc : c = (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
      (ONE - p.fee) * p.rate s.tokenIn - 1) /
      ((ONE - p.fee) * p.rate s.tokenIn) := hspec.2.2
  have hQpos : 0 < (ONE - p.fee) * p.rate s.tokenIn := Nat.pos_of_ne_zero hQne
  unfold outPrice
  rw [hc]
  have hQle : (ONE - p.fee) * p.rate s.tokenIn ≤ ONE * p.rate s.tokenIn := by
    apply Nat.mul_le_mul_right
    omega
  have hRpos : 0 < p.rate s.tokenIn := by
    by_cases hr0 : p.rate s.tokenIn = 0
    · rw [hr0, Nat.mul_zero] at hQpos
      omega
    · exact Nat.pos_of_ne_zero hr0
  have hONE_Rpos : 0 < ONE * p.rate s.tokenIn := Nat.mul_pos ONE_pos hRpos
  have hcmul : (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
          (ONE - p.fee) * p.rate s.tokenIn - 1) /
          ((ONE - p.fee) * p.rate s.tokenIn) * ((ONE - p.fee) * p.rate s.tokenIn) ≤
      m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
        (ONE - p.fee) * p.rate s.tokenIn - 1 :=
    Nat.div_mul_le_self _ _
  have hsub : ((m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
          (ONE - p.fee) * p.rate s.tokenIn - 1) /
          ((ONE - p.fee) * p.rate s.tokenIn) - 1) *
        ((ONE - p.fee) * p.rate s.tokenIn) =
      (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
          (ONE - p.fee) * p.rate s.tokenIn - 1) /
          ((ONE - p.fee) * p.rate s.tokenIn) * ((ONE - p.fee) * p.rate s.tokenIn) -
        (ONE - p.fee) * p.rate s.tokenIn := by
    rw [sub_mul_eq]
  have heqR : ONE * (ONE *
        m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn) =
      m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE + ONE * p.rate s.tokenIn := by
    rw [Nat.mul_add, ← Nat.mul_assoc ONE ONE
      (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut))),
      Nat.mul_comm (ONE * ONE)
        (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut))),
      ← Nat.mul_assoc]
  have heqL : ((m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
            (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
            (ONE - p.fee) * p.rate s.tokenIn - 1) /
            ((ONE - p.fee) * p.rate s.tokenIn) - 1) * (ONE - p.fee) * p.rate s.tokenIn =
      ((m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
            (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
            (ONE - p.fee) * p.rate s.tokenIn - 1) /
            ((ONE - p.fee) * p.rate s.tokenIn) - 1) *
          ((ONE - p.fee) * p.rate s.tokenIn) := by
    rw [Nat.mul_assoc]
  omega

theorem step_some_valid {impl : Impl} {m : PoolMath} {p : Pool} {s : Swap} {p' : Pool}
    (h : step impl m p s = some p') : Valid p s :=
  Classical.byContradiction (fun hVn => by
    unfold step at h
    rw [if_neg hVn] at h
    cases h)

theorem step_some_impl {impl : Impl} {m : PoolMath} {p : Pool} {s : Swap} {p' : Pool}
    (h : step impl m p s = some p') :
    ∃ c, impl m p s = some c ∧ settle p s c = some p' := by
  have hV : Valid p s := step_some_valid h
  unfold step at h
  rw [if_pos hV] at h
  have hDec : impl m p s = none ∨ impl m p s ≠ none := Decidable.em _
  cases hDec with
  | inl hnone =>
    rw [hnone] at h
    simp at h
  | inr hne =>
    have ⟨c, hc⟩ : ∃ x, some x = impl m p s := Option.ne_none_iff_exists.mp hne
    have himpl : impl m p s = some c := hc.symm
    have hset : settle p s c = some p' := by
      rw [himpl] at h
      simpa using h
    exact ⟨c, himpl, hset⟩

theorem givenIn_in_le (B A R F : Nat)
    (x : Nat) (hx : x = A * (ONE - F) * R / (ONE * ONE)) :
    B * R / ONE + x ≤ (B + A) * R / ONE := by
  have hdiv1 : (B * R / ONE) * ONE ≤ B * R := Nat.div_mul_le_self _ _
  have hdivx : x * (ONE * ONE) ≤ A * (ONE - F) * R := by
    rw [hx]
    exact Nat.div_mul_le_self _ _
  have hQF : A * (ONE - F) * R ≤ A * R * ONE := by
    have hle : A * (ONE - F) ≤ A * ONE := Nat.mul_le_mul_left A (Nat.sub_le ONE F)
    have h1 : A * (ONE - F) * R ≤ A * ONE * R :=
      Nat.mul_le_mul_right R hle
    calc A * (ONE - F) * R ≤ A * ONE * R := h1
      _ = A * R * ONE := by
        rw [Nat.mul_assoc A ONE R, Nat.mul_comm ONE R, ← Nat.mul_assoc A R ONE]
  have hxONE : x * ONE ≤ A * R := by
    have h1 : (x * ONE) * ONE ≤ A * R * ONE := by
      calc (x * ONE) * ONE = x * (ONE * ONE) := Nat.mul_assoc _ _ _
        _ ≤ A * (ONE - F) * R := hdivx
        _ ≤ A * R * ONE := hQF
    exact Nat.le_of_mul_le_mul_right h1 ONE_pos
  have hsum : (B * R / ONE + x) * ONE ≤ (B + A) * R := by
    calc (B * R / ONE + x) * ONE
        = (B * R / ONE) * ONE + x * ONE := Nat.add_mul _ _ _
      _ ≤ B * R + A * R := Nat.add_le_add hdiv1 hxONE
      _ = (B + A) * R := (Nat.add_mul _ _ _).symm
  exact (Nat.le_div_iff_mul_le ONE_pos).mpr hsum

theorem givenIn_out_le (B R M y : Nat) (hR : 0 < R)
    (hy : y = M * ONE / R) (hMle : M ≤ B * R / ONE) (hyB : y ≤ B) :
    B * R / ONE - M ≤ (B - y) * R / ONE := by
  have h1 : (B * R / ONE) * ONE ≤ B * R := Nat.div_mul_le_self _ _
  have h2 : y * R ≤ M * ONE := by
    rw [hy]
    exact Nat.div_mul_le_self _ _
  have e1 : (B * R / ONE - M) * ONE = (B * R / ONE) * ONE - M * ONE := Nat.sub_mul _ _ _
  have e2 : (B - y) * R = B * R - y * R := Nat.sub_mul _ _ _
  have hle : (B * R / ONE - M) * ONE ≤ (B - y) * R := by
    rw [e1, e2]
    omega
  exact (Nat.le_div_iff_mul_le ONE_pos).mpr hle

theorem givenOut_in_le (B R M c F : Nat) (hR : 0 < R)
    (Qpos : 0 < (ONE - F) * R)
    (hc : c = (M * ONE * ONE + (ONE - F) * R - 1) / ((ONE - F) * R)) :
    B * R / ONE + M ≤ (B + c) * R / ONE := by
  have h1 : (B * R / ONE) * ONE ≤ B * R := Nat.div_mul_le_self _ _
  have hceil : M * ONE * ONE ≤ c * ((ONE - F) * R) := by
    rw [hc]
    exact ceil_mul_ge_of_pos _ _ Qpos
  have hQle : (ONE - F) * R ≤ ONE * R := Nat.mul_le_mul_right R (Nat.sub_le ONE F)
  have hMONE : M * ONE ≤ c * R := by
    have h2 : (M * ONE) * ONE ≤ (c * R) * ONE := by
      calc (M * ONE) * ONE = M * ONE * ONE := rfl
        _ ≤ c * ((ONE - F) * R) := hceil
        _ ≤ c * (ONE * R) := Nat.mul_le_mul_left c hQle
        _ = (c * R) * ONE := by
          rw [Nat.mul_comm ONE R, ← Nat.mul_assoc c R ONE]
    exact Nat.le_of_mul_le_mul_right h2 ONE_pos
  have hsum : (B * R / ONE + M) * ONE ≤ (B + c) * R := by
    calc (B * R / ONE + M) * ONE
        = (B * R / ONE) * ONE + M * ONE := Nat.add_mul _ _ _
      _ ≤ B * R + c * R := Nat.add_le_add h1 hMONE
      _ = (B + c) * R := (Nat.add_mul _ _ _).symm
  exact (Nat.le_div_iff_mul_le ONE_pos).mpr hsum

theorem givenOut_out_le (B R A x : Nat)
    (hx : x = (A * R + (ONE - 1)) / ONE)
    (hAle : A ≤ B) (hxe : x ≤ B * R / ONE) :
    B * R / ONE - x ≤ (B - A) * R / ONE := by
  have h1 : (B * R / ONE) * ONE ≤ B * R := Nat.div_mul_le_self _ _
  have h2 : A * R ≤ x * ONE := by
    rw [hx]
    exact ceil_ge _ _ ONE_pos
  have e1 : (B * R / ONE - x) * ONE = (B * R / ONE) * ONE - x * ONE := Nat.sub_mul _ _ _
  have e2 : (B - A) * R = B * R - A * R := Nat.sub_mul _ _ _
  have hle : (B * R / ONE - x) * ONE ≤ (B - A) * R := by
    rw [e1, e2]
    omega
  exact (Nat.le_div_iff_mul_le ONE_pos).mpr hle

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  intro m p s p' hwb hstep
  have hV : Valid p s := step_some_valid hstep
  have hne : s.tokenIn ≠ s.tokenOut := hV.1
  have htin : s.tokenIn < p.n := hV.2.1
  have htout : s.tokenOut < p.n := hV.2.2
  have hEx : ∃ c, onSwap m p s = some c ∧ settle p s c = some p' := step_some_impl hstep
  have hDesc := Classical.indefiniteDescription
    (fun c => onSwap m p s = some c ∧ settle p s c = some p') hEx
  let c := hDesc.val
  have hEx2 := hDesc.property
  have himpl : onSwap m p s = some c := hEx2.1
  have hsettle : settle p s c = some p' := hEx2.2
  have hKindDec : s.kind = Kind.givenIn ∨ s.kind = Kind.givenOut := by
    cases s.kind with
    | givenIn => exact Or.inl rfl
    | givenOut => exact Or.inr rfl
  cases hKindDec with
  | inl hkind =>
    have hon : onSwap m p s = swapGivenIn m p s := by
      unfold onSwap
      rw [hkind]
    rw [hon] at himpl
    have hspec := swapGivenIn_eq himpl
    have hRne := hspec.1
    have hy : c = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) *
        ONE / p.rate s.tokenOut := hspec.2
    have hRpos : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hRne
    have hMle : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) ≤
        scaledBalances p s.tokenOut := (hwb.outGivenIn _ _ _ _ hne htin htout).1
    have hsound2 : m.invariant (scaledBalances p) ≤
        m.invariant (update2 (scaledBalances p) s.tokenIn
          (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut
          (scaledBalances p s.tokenOut -
            m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s))) :=
      (hwb.outGivenIn _ _ _ _ hne htin htout).2
    have hSetDec : amountOut s c ≤ p.balance s.tokenOut ∨
        ¬ amountOut s c ≤ p.balance s.tokenOut := Decidable.em _
    cases hSetDec with
    | inl hle =>
      have hamout : amountOut s c = c := by
        unfold amountOut
        rw [hkind]
      have hamin : amountIn s c = s.amount := by
        unfold amountIn
        rw [hkind]
      unfold settle at hsettle
      rw [if_pos hle] at hsettle
      rw [hamin, hamout] at hsettle
      have hp' : p' = { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - c) } := (Option.some_inj.mp hsettle).symm
      rw [hp']
      have hle_c : c ≤ p.balance s.tokenOut := by
        rw [← hamout]
        exact hle
      unfold value
      apply Nat.le_trans hsound2
      apply hwb.monotone
      intro k hk
      have hK1 : k = s.tokenIn ∨ k ≠ s.tokenIn := Decidable.em _
      cases hK1 with
      | inl hki =>
        have hx : netInDown p s =
            s.amount * (ONE - p.fee) * p.rate s.tokenIn / (ONE * ONE) := rfl
        have hle2 := givenIn_in_le (p.balance s.tokenIn) s.amount
          (p.rate s.tokenIn) (p.fee) (netInDown p s) hx
        simp only [hki, update2, scaledBalances_eq] at hle2 ⊢
        exact hle2
      | inr hki =>
        have hK2 : k = s.tokenOut ∨ k ≠ s.tokenOut := Decidable.em _
        cases hK2 with
        | inl hkj =>
          have hle2 := givenIn_out_le (p.balance s.tokenOut) (p.rate s.tokenOut)
            (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) c hRpos hy hMle hle_c
          simp only [hki, hkj, update2, scaledBalances_eq] at hle2 ⊢
          exact hle2
        | inr hkj =>
          simp only [hki, hkj, update2, scaledBalances_eq] at ⊢
          exact Nat.le_refl _
    | inr hlt =>
      unfold settle at hsettle
      rw [if_neg hlt] at hsettle
      cases hsettle
  | inr hkind =>
    have hon : onSwap m p s = swapGivenOut m p s := by
      unfold onSwap
      rw [hkind]
    rw [hon] at himpl
    have hspec := swapGivenOut_eq himpl
    have hx_lt := hspec.1
    have hQne := hspec.2.1
    have hc : c = (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE +
        (ONE - p.fee) * p.rate s.tokenIn - 1) /
        ((ONE - p.fee) * p.rate s.tokenIn) := hspec.2.2
    have hQpos : 0 < (ONE - p.fee) * p.rate s.tokenIn := Nat.pos_of_ne_zero hQne
    have hRpos : 0 < p.rate s.tokenIn := by
      have hDecR : p.rate s.tokenIn = 0 ∨ p.rate s.tokenIn ≠ 0 := Decidable.em _
      cases hDecR with
      | inl hr0 =>
        rw [hr0, Nat.mul_zero] at hQpos
        omega
      | inr hrne =>
        exact Nat.pos_of_ne_zero hrne
    have hsound2 : m.invariant (scaledBalances p) ≤
        m.invariant (update2 (scaledBalances p) s.tokenIn
          (scaledBalances p s.tokenIn +
            m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
              (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
          (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut))) :=
      (hwb.inGivenOut _ _ _ _ hne htin htout) hx_lt |>.2
    have hSetDec : amountOut s c ≤ p.balance s.tokenOut ∨
        ¬ amountOut s c ≤ p.balance s.tokenOut := Decidable.em _
    cases hSetDec with
    | inl hle =>
      have hamout : amountOut s c = s.amount := by
        unfold amountOut
        rw [hkind]
      have hamin : amountIn s c = c := by
        unfold amountIn
        rw [hkind]
      unfold settle at hsettle
      rw [if_pos hle] at hsettle
      rw [hamin, hamout] at hsettle
      have hp' : p' = { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) } := (Option.some_inj.mp hsettle).symm
      rw [hp']
      have hle_a : s.amount ≤ p.balance s.tokenOut := by
        rw [← hamout]
        exact hle
      unfold value
      apply Nat.le_trans hsound2
      apply hwb.monotone
      intro k hk
      have hK1 : k = s.tokenIn ∨ k ≠ s.tokenIn := Decidable.em _
      cases hK1 with
      | inl hki =>
        have hmid : update2 (scaledBalances p) s.tokenIn
            (scaledBalances p s.tokenIn +
              m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
            (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k =
            scaledBalances p s.tokenIn +
              m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                (scaleUp s.amount (p.rate s.tokenOut)) := by
          unfold update2
          rw [if_pos hki]
        have hsc : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) } k =
            (p.balance s.tokenIn + c) * p.rate s.tokenIn / ONE := by
          rw [scaledBalances_eq]
          have hb : (({ p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) }.balance k) =
              p.balance s.tokenIn + c := by
            show update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) k = _
            unfold update2
            rw [if_pos hki]
          have hr : (({ p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) }.rate k) = p.rate s.tokenIn := by
            show p.rate k = p.rate s.tokenIn
            rw [hki]
          rw [hb, hr]
        rw [hmid, hsc]
        exact givenOut_in_le (p.balance s.tokenIn) (p.rate s.tokenIn)
          (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
            (scaleUp s.amount (p.rate s.tokenOut))) c (p.fee) hRpos hQpos hc
      | inr hki =>
        have hK2 : k = s.tokenOut ∨ k ≠ s.tokenOut := Decidable.em _
        cases hK2 with
        | inl hkj =>
          have hmid : update2 (scaledBalances p) s.tokenIn
              (scaledBalances p s.tokenIn +
                m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                  (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
              (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k =
              scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) := by
            unfold update2
            rw [if_neg hki, if_pos hkj]
          have hsc : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) } k =
              (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut / ONE := by
            rw [scaledBalances_eq]
            have hb : (({ p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) }.balance k) =
                p.balance s.tokenOut - s.amount := by
              show update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) k = _
              unfold update2
              rw [if_neg hki, if_pos hkj]
            have hr : (({ p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) }.rate k) = p.rate s.tokenOut := by
              show p.rate k = p.rate s.tokenOut
              rw [hkj]
            rw [hb, hr]
          rw [hmid, hsc]
          have hx_eq : scaleUp s.amount (p.rate s.tokenOut) =
              (s.amount * p.rate s.tokenOut + (ONE - 1)) / ONE := rfl
          have hxe : scaleUp s.amount (p.rate s.tokenOut) ≤
              scaledBalances p s.tokenOut := Nat.le_of_lt hx_lt
          rw [scaledBalances_eq] at hxe
          exact givenOut_out_le (p.balance s.tokenOut) (p.rate s.tokenOut)
            s.amount (scaleUp s.amount (p.rate s.tokenOut)) hx_eq hle_a hxe
        | inr hkj =>
          have hmid : update2 (scaledBalances p) s.tokenIn
              (scaledBalances p s.tokenIn +
                m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                  (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
              (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k =
              scaledBalances p k := by
            unfold update2
            rw [if_neg hki, if_neg hkj]
          have hsc : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) } k =
              scaledBalances p k := by
            rw [scaledBalances_eq, scaledBalances_eq]
            have hb : (({ p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) }.balance k) = p.balance k := by
              show update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) k = p.balance k
              unfold update2
              rw [if_neg hki, if_neg hkj]
            have hr : (({ p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) }.rate k) = p.rate k := rfl
            rw [hb, hr]
          rw [hmid, hsc]
    | inr hlt =>
      unfold settle at hsettle
      rw [if_neg hlt] at hsettle
      cases hsettle

theorem step_preserves_n {impl : Impl} {m : PoolMath} {p : Pool} {s : Swap} {p' : Pool}
    (h : step impl m p s = some p') : p'.n = p.n := by
  have hEx : ∃ c, impl m p s = some c ∧ settle p s c = some p' := step_some_impl h
  have hDesc := Classical.indefiniteDescription
    (fun c => impl m p s = some c ∧ settle p s c = some p') hEx
  let c := hDesc.val
  have hEx2 := hDesc.property
  have hsettle : settle p s c = some p' := hEx2.2
  have hDec : amountOut s c ≤ p.balance s.tokenOut ∨
      ¬ amountOut s c ≤ p.balance s.tokenOut := Decidable.em _
  cases hDec with
  | inl hle =>
    unfold settle at hsettle
    rw [if_pos hle] at hsettle
    have hp' : p' = { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } := (Option.some_inj.mp hsettle).symm
    rw [hp']
    rfl
  | inr hlt =>
    unfold settle at hsettle
    rw [if_neg hlt] at hsettle
    cases hsettle

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  intro m p ss p' hwb hrun
  induction ss generalizing p p' with
  | nil =>
    unfold run at hrun
    cases hrun
    exact Nat.le_refl _
  | cons s ss ih =>
    have hDec : step onSwap m p s = none ∨ step onSwap m p s ≠ none := Decidable.em _
    cases hDec with
    | inl hnone =>
      have hrun2 : (match step onSwap m p s with
          | some p1 => run onSwap m p1 ss
          | none => none) = some p' := by
        unfold run at hrun
        exact hrun
      rw [hnone] at hrun2
      simp at hrun2
    | inr hne =>
      have hExP : ∃ x, some x = step onSwap m p s := Option.ne_none_iff_exists.mp hne
      have hDescP := Classical.indefiniteDescription
        (fun x => some x = step onSwap m p s) hExP
      let p1 := hDescP.val
      have hExP2 := hDescP.property
      have hStep : step onSwap m p s = some p1 := hExP2.symm
      have hRun2 : run onSwap m p1 ss = some p' := by
        have hrun2 : (match step onSwap m p s with
            | some p1 => run onSwap m p1 ss
            | none => none) = some p' := by
          unfold run at hrun
          exact hrun
        rw [hStep] at hrun2
        simpa using hrun2
      have hle1 : value m p ≤ value m p1 := req_swap_keeps_value m p s p1 hwb hStep
      have hn : p1.n = p.n := step_preserves_n hStep
      have hwb1 : WellBehaved m p1.n := by
        rw [hn]
        exact hwb
      have hle2 : value m p1 ≤ value m p' := ih p1 p' hwb1 hRun2
      exact Nat.le_trans hle1 hle2
