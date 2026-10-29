import ShareVault.Spec

namespace ShareVault

def vault : Impl := fun s c =>
  match c with
  | .deposit who x =>
    if s.supply = 0 then
      let t := initialSharesPerUnit * x
      some { assets := s.assets + x, supply := s.supply + t, balance := fun b => if b = who then s.balance b + t else s.balance b }
    else if s.assets = 0 then none
    else
      let t := (x * s.supply) / s.assets
      some { assets := s.assets + x, supply := s.supply + t, balance := fun b => if b = who then s.balance b + t else s.balance b }
  | .redeem who t =>
    if t ≤ s.balance who then
      if t ≤ s.supply then
        let y := if s.supply = 0 then 0 else (t * s.assets) / s.supply
        some { assets := s.assets - y, supply := s.supply - t, balance := fun b => if b = who then s.balance b - t else s.balance b }
      else none
    else none
  | .withdraw who x =>
    if 0 < s.supply then
      if 0 < s.assets then
        if x ≤ s.assets then
          let t := (x * s.supply + s.assets - 1) / s.assets
          if t ≤ s.balance who then
            if t ≤ s.supply then
              some { assets := s.assets - x, supply := s.supply - t, balance := fun b => if b = who then s.balance b - t else s.balance b }
            else none
          else none
        else none
      else none
    else none

theorem ceil_le_test (N D b : Nat) (hD : 0 < D) (hN : N ≤ b * D) : (N + D - 1) / D ≤ b := by
  have h1 : (N + D - 1) / D < b + 1 := by
    rw [Nat.div_lt_iff_lt_mul hD]
    have h2 : N + D - 1 < (b + 1) * D := by
      have e : (b + 1) * D = b * D + D := by rw [Nat.add_mul, Nat.one_mul]
      rw [e]
      omega
    exact h2
  omega

theorem foo_test2 (x A S : Nat) (h : x * S ≤ A * S) (hS : 0 < S) : x ≤ A := by
  exact Nat.le_of_mul_le_mul_right h hS

theorem probe_sig1 (B S A : Nat) (h : B ≤ S) : B * A ≤ S * A := by
  exact Nat.mul_le_mul_right A h

theorem req_redeem_effects_aux3 : RedeemEffects vault := by
  intro s s' who t h
  unfold vault at h
  by_cases hbal : t ≤ s.balance who
  · simp only [hbal, ↓reduceIte] at h
    by_cases hsup : t ≤ s.supply
    · simp only [hsup, ↓reduceIte] at h
      by_cases hsup0 : s.supply = 0
      · simp only [hsup0, ↓reduceIte] at h
        cases h
        have ht0 : t = 0 := by omega
        subst ht0
        refine ⟨0, by omega, by omega, Nat.zero_le _, rfl, ?_, ?_, ?_⟩
        · simp [hsup0]
        · simp
        · intro b hb
          simp [hb]
      · simp only [hsup0, ↓reduceIte] at h
        cases h
        refine ⟨(t * s.assets) / s.supply, hbal, hsup, ?_, rfl, rfl, ?_, ?_⟩
        · have hle : t * s.assets ≤ s.supply * s.assets :=
            Nat.mul_le_mul_right s.assets hsup
          have hdiv : (t * s.assets) / s.supply ≤ (s.supply * s.assets) / s.supply :=
            Nat.div_le_div_right hle
          have heq : (s.supply * s.assets) / s.supply = s.assets := by
            rw [Nat.mul_comm s.supply s.assets, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hsup0)]
          omega
        · simp
        · intro b hb
          simp [hb]
    · simp [hsup] at h
  · simp [hbal] at h

theorem req_withdraw_effects_tmp : WithdrawEffects vault := by
  intro s s' who x h
  unfold vault at h
  by_cases hsup : 0 < s.supply
  · simp only [hsup, ↓reduceIte] at h
    by_cases hassets : 0 < s.assets
    · simp only [hassets, ↓reduceIte] at h
      by_cases hx : x ≤ s.assets
      · simp only [hx, ↓reduceIte] at h
        by_cases hbal : (x * s.supply + s.assets - 1) / s.assets ≤ s.balance who
        · simp only [hbal, ↓reduceIte] at h
          by_cases hsup2 : (x * s.supply + s.assets - 1) / s.assets ≤ s.supply
          · simp only [hsup2, ↓reduceIte] at h
            cases h
            refine ⟨(x * s.supply + s.assets - 1) / s.assets, hbal, hsup2, hx, rfl, rfl, ?_, ?_⟩
            · simp
            · intro b hb
              simp [hb]
          · simp only [hsup2, ↓reduceIte] at h
            cases h
        · simp only [hbal, ↓reduceIte] at h
          cases h
      · simp only [hx, ↓reduceIte] at h
        cases h
    · simp only [hassets, ↓reduceIte] at h
      cases h
  · simp only [hsup, ↓reduceIte] at h
    cases h

theorem div_floor_aux4 (N A : Nat) (hA : 0 < A) :
    (N / A) * A ≤ N ∧ N < ((N / A) + 1) * A := by
  have h1 : A * (N / A) + N % A = N := Nat.div_add_mod N A
  have h2 : N % A < A := Nat.mod_lt N hA
  have hcomm : (N / A) * A = A * (N / A) := Nat.mul_comm _ _
  have heq : ((N / A) + 1) * A = (N / A) * A + A := by
    calc ((N / A) + 1) * A = (N / A) * A + 1 * A := by rw [Nat.add_mul]
      _ = (N / A) * A + A := by rw [Nat.one_mul]
  constructor
  · omega
  · omega

theorem probe_deposit_caseA (s s' : Vault) (who x t : Nat)
    (h : vault s (.deposit who x) = some s')
    (Hmint : Minted s who x t s') (hsup : s.supply = 0) :
    t = initialSharesPerUnit * x := by
  obtain ⟨hA', hS', hB', hO'⟩ := Hmint
  unfold vault at h
  simp only [hsup, ↓reduceIte] at h
  cases h
  case refl =>
    simp only at hS' ⊢
    omega

theorem probe_deposit_caseB (s s' : Vault) (who x t : Nat)
    (h : vault s (.deposit who x) = some s')
    (Hmint : Minted s who x t s') (hne : s.supply ≠ 0) (hA : s.assets ≠ 0) :
    t = (x * s.supply) / s.assets := by
  obtain ⟨hA', hS', hB', hO'⟩ := Hmint
  unfold vault at h
  simp only [hne, ↓reduceIte, hA, ↓reduceIte] at h
  cases h
  case refl =>
    simp only at hS' ⊢
    omega

theorem req_redeem_rounds_down_aux : RedeemRoundsDown vault := by
  intro s s' who t y h Hburn
  obtain ⟨htBal, htSup, hyA, hA', hS', hB', hO'⟩ := Hburn
  unfold vault at h
  by_cases hbal : t ≤ s.balance who
  · simp only [hbal, ↓reduceIte] at h
    by_cases hsup : t ≤ s.supply
    · simp only [hsup, ↓reduceIte] at h
      by_cases hsup0 : s.supply = 0
      · simp only [hsup0, ↓reduceIte] at h
        cases h
        constructor
        · intro _
          -- s'.assets = s.assets - y, but s' = {assets := s.assets - 0, ...}
          -- so s.assets - y = s.assets - 0
          simp only at hA' hyA ⊢
          omega
        · intro hpos
          omega
      · simp only [hsup0, ↓reduceIte] at h
        cases h
        -- y0 = (t * s.assets)/s.supply, s' assets = s.assets - y0
        -- Burned says s'.assets equation gives y = y0 via omega?
        have hYeq : y = (t * s.assets) / s.supply := by
          simp only at hA' hyA ⊢
          -- need y0 ≤ assets
          have hle : t * s.assets ≤ s.supply * s.assets :=
            Nat.mul_le_mul_right s.assets hsup
          have hdiv : (t * s.assets) / s.supply ≤ (s.supply * s.assets) / s.supply :=
            Nat.div_le_div_right hle
          have heq : (s.supply * s.assets) / s.supply = s.assets := by
            rw [Nat.mul_comm s.supply s.assets, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hsup0)]
          have hy0le : (t * s.assets) / s.supply ≤ s.assets := by omega
          omega
        have hApos : 0 < s.supply := Nat.pos_of_ne_zero hsup0
        have hfl := div_floor_aux4 (t * s.assets) s.supply hApos
        rw [hYeq] at *
        constructor
        · intro h0
          omega
        · intro hpos
          constructor
          · have := hfl.1
            -- (N/A)*A ≤ N ; need y * supply ≤ t*assets ; comm
            have hcomm : ((t * s.assets) / s.supply) * s.supply = s.supply * ((t * s.assets) / s.supply) := Nat.mul_comm _ _
            omega
          · have := hfl.2
            have hcomm2 : (((t * s.assets) / s.supply) + 1) * s.supply = s.supply * (((t * s.assets) / s.supply) + 1) := Nat.mul_comm _ _
            omega
    · simp only [hsup, ↓reduceIte] at h
      cases h
  · simp only [hbal, ↓reduceIte] at h
    cases h

theorem ceil_prop_withdraw (N A : Nat) (hA : 0 < A) :
    N ≤ ((N + A - 1) / A) * A ∧ ((N + A - 1) / A) * A < N + A := by
  have hM : (N + A - 1) + 1 = N + A := by omega
  have h1 : A * ((N + A - 1) / A) + (N + A - 1) % A = (N + A - 1) := Nat.div_add_mod _ _
  have h2 : (N + A - 1) % A < A := Nat.mod_lt _ hA
  have hcomm : A * ((N + A - 1) / A) = ((N + A - 1) / A) * A := Nat.mul_comm _ _
  omega

theorem probe_mul_sub_exists (a b c : Nat) : (a - b) * c = a * c - b * c := by exact Nat.sub_mul a b c

theorem probe_mul_sub_exists2 (a b c : Nat) : a * (b - c) = a * b - a * c := by exact Nat.mul_sub a b c

theorem probe_le_cancel (a b c : Nat) (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b := by exact Nat.le_of_mul_le_mul_right h hc
#check Nat.sub_mul
#check Nat.mul_sub
#check Nat.le_of_mul_le_mul_right
#check Nat.div_add_mod

theorem vnb_refl (s : Vault) : ValueNotBelow s s := by unfold ValueNotBelow; exact Nat.le_refl _

theorem vnb_trans_aux (A1 S1 A2 S2 A3 S3 : Nat)
  (h1 : A1 * S2 ≤ A2 * S1) (h2 : A2 * S3 ≤ A3 * S2) (hS2 : 0 < S2) :
  A1 * S3 ≤ A3 * S1 := by
  have e1 : (A1 * S2) * S3 ≤ (A2 * S1) * S3 := Nat.mul_le_mul_right S3 h1
  have e2 : (A2 * S3) * S1 ≤ (A3 * S2) * S1 := Nat.mul_le_mul_right S1 h2
  have r1 : (A1 * S2) * S3 = S2 * (A1 * S3) := by ac_rfl
  have r2 : (A2 * S1) * S3 = (A2 * S3) * S1 := by ac_rfl
  have r3 : (A3 * S2) * S1 = S2 * (A3 * S1) := by ac_rfl
  rw [r1] at e1
  rw [r2] at e1
  rw [r3] at e2
  have hcomb : S2 * (A1 * S3) ≤ S2 * (A3 * S1) := Nat.le_trans e1 e2
  exact Nat.le_of_mul_le_mul_left hcomb hS2

theorem vnb_trans (a b c : Vault) (h1 : ValueNotBelow a b) (h2 : ValueNotBelow b c) (h : 0 < b.supply) : ValueNotBelow a c := by
  unfold ValueNotBelow at *
  exact vnb_trans_aux a.assets a.supply b.assets b.supply c.assets c.supply h1 h2 h

theorem vnb_donate (s : Vault) (x : Nat) : ValueNotBelow s ({ s with assets := s.assets + x } : Vault) := by
  unfold ValueNotBelow
  simp only
  have h : s.assets * s.supply ≤ (s.assets + x) * s.supply := Nat.mul_le_mul_right s.supply (Nat.le_add_right s.assets x)
  exact h

theorem vnb_of_deposit_minted (s s' : Vault) (x t : Nat) (hm : Minted s who x t s')
  (hineq : t * s.assets ≤ x * s.supply) : ValueNotBelow s s' := by
  obtain ⟨hA, hS, _, _⟩ := hm
  unfold ValueNotBelow
  rw [hA, hS]
  have e1 : s.assets * (s.supply + t) = s.assets * s.supply + s.assets * t := Nat.mul_add _ _ _
  have e2 : (s.assets + x) * s.supply = s.assets * s.supply + x * s.supply := Nat.add_mul _ _ _
  have e3 : s.assets * t = t * s.assets := Nat.mul_comm _ _
  rw [e1, e2, e3]
  omega

theorem vnb_of_burned_general (s s' : Vault) (t y : Nat) (hm : Burned s who t y s')
  (hineq : y * s.supply ≤ t * s.assets) : ValueNotBelow s s' := by
  obtain ⟨_, htS, hyA, hA, hS, _, _⟩ := hm
  unfold ValueNotBelow
  rw [hA, hS]
  have e1 : s.assets * (s.supply - t) = s.assets * s.supply - s.assets * t := Nat.mul_sub _ _ _
  have e2 : (s.assets - y) * s.supply = s.assets * s.supply - y * s.supply := Nat.sub_mul _ _ _
  rw [e1, e2]
  have e3 : s.assets * t = t * s.assets := Nat.mul_comm _ _
  rw [e3]
  exact Nat.sub_le_sub_left hineq (s.assets * s.supply)

theorem probe_exec_none (s : Vault) (c : Call) (hvc : vault s c = none) :
    exec vault s (Op.call c) = s := by
  simp [exec, hvc]

theorem probe_exec_some (s s' : Vault) (c : Call) (hvc : vault s c = some s') :
    exec vault s (Op.call c) = s' := by
  simp [exec, hvc]

theorem req_deposit_succeeds    : DepositSucceeds vault := by
  intro s who x h
  unfold vault
  rcases h with h0 | hpos
  · simp [h0]
  · by_cases hsup : s.supply = 0
    · simp [hsup]
    · have hassets : s.assets ≠ 0 := by omega
      simp [hsup, hassets]

theorem req_redeem_succeeds    : RedeemSucceeds vault := by
  intro s who t hbal hsup
  unfold vault
  simp [hbal, hsup]

theorem req_withdraw_succeeds   : WithdrawSucceeds vault := by
  unfold WithdrawSucceeds
  intro s who x hsup hassets hbalS hval
  have hsup_ne : s.supply ≠ 0 := by omega
  have hassets_ne : s.assets ≠ 0 := by omega
  -- x ≤ assets
  have hbalA : s.balance who * s.assets ≤ s.supply * s.assets :=
    Nat.mul_le_mul_right s.assets hbalS
  have hxS_le : x * s.supply ≤ s.supply * s.assets := by
    calc x * s.supply ≤ s.balance who * s.assets := hval
      _ ≤ s.supply * s.assets := hbalA
  have hxS_le' : x * s.supply ≤ s.assets * s.supply := by
    rw [Nat.mul_comm s.supply s.assets] at hxS_le
    exact hxS_le
  have hxA : x ≤ s.assets := Nat.le_of_mul_le_mul_right hxS_le' hsup
  have hceil_bal : (x * s.supply + s.assets - 1) / s.assets ≤ s.balance who :=
    ceil_le_test (x * s.supply) s.assets (s.balance who) hassets hval
  have hceil_sup : (x * s.supply + s.assets - 1) / s.assets ≤ s.supply := by
    apply ceil_le_test (x * s.supply) s.assets s.supply hassets
    rw [Nat.mul_comm s.supply s.assets]
    exact hxS_le'
  unfold vault
  simp [hsup, hassets, hxA, hceil_bal, hceil_sup]

theorem req_deposit_effects : DepositEffects vault := by
  intro s s' who x h
  unfold vault at h
  by_cases hsup : s.supply = 0
  · simp [hsup] at h
    subst h
    refine ⟨initialSharesPerUnit * x, rfl, ?_, ?_, ?_⟩
    · simp [hsup]
    · simp
    · intro b hb
      simp [hb]
  · simp [hsup] at h
    by_cases hassets : s.assets = 0
    · simp [hassets] at h
    · simp [hassets] at h
      subst h
      refine ⟨(x * s.supply) / s.assets, rfl, rfl, ?_, ?_⟩
      · simp
      · intro b hb
        simp [hb]

theorem req_redeem_effects : RedeemEffects vault := req_redeem_effects_aux3

theorem req_withdraw_effects    : WithdrawEffects vault := by
  intro s s' who x h
  unfold vault at h
  by_cases hsup : 0 < s.supply
  · simp only [hsup, ↓reduceIte] at h
    by_cases hassets : 0 < s.assets
    · simp only [hassets, ↓reduceIte] at h
      by_cases hx : x ≤ s.assets
      · simp only [hx, ↓reduceIte] at h
        by_cases hbal : (x * s.supply + s.assets - 1) / s.assets ≤ s.balance who
        · simp only [hbal, ↓reduceIte] at h
          by_cases hsup2 : (x * s.supply + s.assets - 1) / s.assets ≤ s.supply
          · simp only [hsup2, ↓reduceIte] at h
            cases h
            refine ⟨(x * s.supply + s.assets - 1) / s.assets, hbal, hsup2, hx, rfl, rfl, ?_, ?_⟩
            · simp
            · intro b hb
              simp [hb]
          · simp only [hsup2, ↓reduceIte] at h
            cases h
        · simp only [hbal, ↓reduceIte] at h
          cases h
      · simp only [hx, ↓reduceIte] at h
        cases h
    · simp only [hassets, ↓reduceIte] at h
      cases h
  · simp only [hsup, ↓reduceIte] at h
    cases h

theorem req_deposit_rounds_down : DepositRoundsDown vault := by
  intro s s' who x t h Hmint
  by_cases hsup0 : s.supply = 0
  · have ht : t = initialSharesPerUnit * x := probe_deposit_caseA s s' who x t h Hmint hsup0
    constructor
    · intro _
      exact ht
    · intro hpos
      omega
  · have hne : s.supply ≠ 0 := hsup0
    have hAne : s.assets ≠ 0 := by
      intro hA0
      have h' := h
      unfold vault at h'
      simp only [hne, ↓reduceIte, hA0, ↓reduceIte] at h'
      cases h'
    have htEq : t = (x * s.supply) / s.assets :=
      probe_deposit_caseB s s' who x t h Hmint hne hAne
    have hApos : 0 < s.assets := Nat.pos_of_ne_zero hAne
    have hfl := div_floor_aux4 (x * s.supply) s.assets hApos
    rw [htEq] at *
    constructor
    · intro h0
      omega
    · intro hpos
      exact hfl

theorem req_redeem_rounds_down : RedeemRoundsDown vault := req_redeem_rounds_down_aux

theorem req_withdraw_rounds_up  : WithdrawRoundsUp vault := by
  intro s s' who x t h Hburn
  obtain ⟨htBal, htSup, hxA, hA', hS', hB', hO'⟩ := Hburn
  unfold vault at h
  by_cases hsup : 0 < s.supply
  · simp only [hsup, ↓reduceIte] at h
    by_cases hassets : 0 < s.assets
    · simp only [hassets, ↓reduceIte] at h
      by_cases hx : x ≤ s.assets
      · simp only [hx, ↓reduceIte] at h
        by_cases hbal : (x * s.supply + s.assets - 1) / s.assets ≤ s.balance who
        · simp only [hbal, ↓reduceIte] at h
          by_cases hsup2 : (x * s.supply + s.assets - 1) / s.assets ≤ s.supply
          · simp only [hsup2, ↓reduceIte] at h
            cases h
            have hApos : 0 < s.assets := hassets
            have hceil := ceil_prop_withdraw (x * s.supply) s.assets hApos
            have htEq : t = (x * s.supply + s.assets - 1) / s.assets := by
              simp only at hS' ⊢
              omega
            rw [htEq]
            refine ⟨hsup, ?_, ?_⟩
            · have := hceil.1
              calc x * s.supply ≤ ((x * s.supply + s.assets - 1) / s.assets) * s.assets := this
                _ = s.assets * (((x * s.supply + s.assets - 1) / s.assets)) := by rw [Nat.mul_comm]
                _ = ((x * s.supply + s.assets - 1) / s.assets) * s.assets := by rw [Nat.mul_comm s.assets _]
              -- need t * assets form: t = ceil, so x*S ≤ t * A ; rewrite comm
            · have h2 := hceil.2
              have hcomm : ((x * s.supply + s.assets - 1) / s.assets) * s.assets = s.assets * ((x * s.supply + s.assets - 1) / s.assets) := Nat.mul_comm _ _
              omega
          · simp only [hsup2, ↓reduceIte] at h
            cases h
        · simp only [hbal, ↓reduceIte] at h
          cases h
      · simp only [hx, ↓reduceIte] at h
        cases h
    · simp only [hassets, ↓reduceIte] at h
      cases h
  · simp only [hsup, ↓reduceIte] at h
    cases h

theorem req_share_value : ShareValueNeverFalls vault := by
  have step : ∀ (s : Vault) (op : Op), 0 < s.supply → 0 < (exec vault s op).supply →
      ValueNotBelow s (exec vault s op) := by
    intro s op h1 h2
    cases op with
    | donate x =>
      have heq : exec vault s (Op.donate x) = ({ s with assets := s.assets + x } : Vault) := rfl
      rw [heq]
      exact vnb_donate s x
    | call c =>
      cases c with
      | deposit who x =>
        cases heq : vault s (Call.deposit who x) with
        | none =>
          have hexec : exec vault s (Op.call (Call.deposit who x)) = s := by
            simp [exec, heq]
          rw [hexec]
          exact vnb_refl s
        | some s' =>
          have hexec : exec vault s (Op.call (Call.deposit who x)) = s' := by
            simp [exec, heq]
          rw [hexec]
          obtain ⟨t, hmint⟩ := req_deposit_effects s s' who x heq
          have hround := (req_deposit_rounds_down s s' who x t heq hmint).2 h1
          exact vnb_of_deposit_minted s s' x t hmint hround.1
      | redeem who t =>
        cases heq : vault s (Call.redeem who t) with
        | none =>
          have hexec : exec vault s (Op.call (Call.redeem who t)) = s := by
            simp [exec, heq]
          rw [hexec]
          exact vnb_refl s
        | some s' =>
          have hexec : exec vault s (Op.call (Call.redeem who t)) = s' := by
            simp [exec, heq]
          rw [hexec]
          obtain ⟨y, hburn⟩ := req_redeem_effects s s' who t heq
          have hround := (req_redeem_rounds_down s s' who t y heq hburn).2 h1
          exact vnb_of_burned_general s s' t y hburn hround.1
      | withdraw who x =>
        cases heq : vault s (Call.withdraw who x) with
        | none =>
          have hexec : exec vault s (Op.call (Call.withdraw who x)) = s := by
            simp [exec, heq]
          rw [hexec]
          exact vnb_refl s
        | some s' =>
          have hexec : exec vault s (Op.call (Call.withdraw who x)) = s' := by
            simp [exec, heq]
          rw [hexec]
          obtain ⟨tt, hburn⟩ := req_withdraw_effects s s' who x heq
          have hround := req_withdraw_rounds_up s s' who x tt heq hburn
          obtain ⟨_, hle, _⟩ := hround
          exact vnb_of_burned_general s s' tt x hburn hle
  have runVNB : ∀ (S : Vault) (ops : List Op),
      (∀ v ∈ trace vault S ops, 0 < v.supply) → ValueNotBelow S (run vault S ops) := by
    intro S ops
    induction ops generalizing S with
    | nil =>
      intro _
      simp [run]
      exact vnb_refl S
    | cons op rest ih =>
      intro hall
      have hS : 0 < S.supply := by
        have hmem : S ∈ trace vault S (op :: rest) := by simp [trace]
        exact hall S hmem
      have htail : ∀ v ∈ trace vault (exec vault S op) rest, 0 < v.supply := by
        intro v hv
        apply hall v
        simp [trace]
        exact Or.inr hv
      have hexec_pos : 0 < (exec vault S op).supply := by
        have hmem : (exec vault S op) ∈ trace vault (exec vault S op) rest := by
          cases rest with
          | nil => simp [trace]
          | cons r rs => simp [trace]
        exact htail _ hmem
      have hstep : ValueNotBelow S (exec vault S op) := step S op hS hexec_pos
      have hrest : ValueNotBelow (exec vault S op) (run vault (exec vault S op) rest) :=
        ih (exec vault S op) htail
      have hrun_eq : run vault S (op :: rest) = run vault (exec vault S op) rest := by
        simp [run]
      rw [hrun_eq]
      exact vnb_trans S (exec vault S op) _ hstep hrest hexec_pos
  intro history ops hall
  exact runVNB (run vault empty history) ops hall

end ShareVault
