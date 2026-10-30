import ShareVault.Spec

namespace ShareVault

def ceilDiv (a b : Nat) : Nat :=
  a / b + (if a % b = 0 then 0 else 1)

theorem mul_le_mul_right' (k : Nat) {a b : Nat} (h : a ≤ b) : a * k ≤ b * k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have e1 : a * (n + 1) = a * n + a := by rw [Nat.mul_add, Nat.mul_one]
    have e2 : b * (n + 1) = b * n + b := by rw [Nat.mul_add, Nat.mul_one]
    omega

theorem le_of_mul_le_mul_right' {a b k : Nat} (h : a * k ≤ b * k) (hk : 0 < k) : a ≤ b := by
  by_cases hle : a ≤ b
  · exact hle
  · have hlt : b < a := by omega
    have hle2 : b + 1 ≤ a := by omega
    have hmono : (b + 1) * k ≤ a * k := mul_le_mul_right' k hle2
    have e : (b + 1) * k = b * k + k := by rw [Nat.add_mul, Nat.one_mul]
    omega

theorem div_mul_le' (a b : Nat) : a / b * b ≤ a := by
  have h := Nat.div_add_mod a b
  have e : a / b * b = b * (a / b) := Nat.mul_comm _ _
  omega

theorem lt_succ_mul' (a b : Nat) (hb : 0 < b) : a < (a / b + 1) * b := by
  have h := Nat.div_add_mod a b
  have hm := Nat.mod_lt a hb
  have e1 : (a / b + 1) * b = a / b * b + 1 * b := by rw [Nat.add_mul]
  have e2 : (1 : Nat) * b = b := Nat.one_mul b
  have e3 : a / b * b = b * (a / b) := Nat.mul_comm _ _
  omega

theorem ceil_le {a b c : Nat} (hb : 0 < b) (h : a ≤ c * b) : ceilDiv a b ≤ c := by
  unfold ceilDiv
  by_cases hmod : a % b = 0
  · simp [hmod]
    have hdm := Nat.div_add_mod a b
    have e : a / b * b = b * (a / b) := Nat.mul_comm _ _
    have heq : b * (a / b) = a := by omega
    have hle2 : a / b * b ≤ c * b := by omega
    exact le_of_mul_le_mul_right' hle2 hb
  · simp [hmod]
    by_cases hle : a / b + 1 ≤ c
    · exact hle
    · have hle1 : c ≤ a / b := by omega
      have hmono : c * b ≤ a / b * b := mul_le_mul_right' b hle1
      have hdm := Nat.div_add_mod a b
      have hle2 : a / b * b ≤ a := div_mul_le' _ _
      have hle3 : c * b ≤ a := Nat.le_trans hmono hle2
      have heq : c * b = a := by omega
      have e : a / b * b = b * (a / b) := Nat.mul_comm _ _
      have hcontra : a % b = 0 := by omega
      omega

theorem le_ceil (a b : Nat) (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  by_cases hmod : a % b = 0
  · simp [hmod]
    have hdm := Nat.div_add_mod a b
    have e : a / b * b = b * (a / b) := Nat.mul_comm _ _
    omega
  · simp [hmod]
    have hdm := Nat.div_add_mod a b
    have hm := Nat.mod_lt a hb
    have e2a : (a / b + 1) * b = a / b * b + 1 * b := by rw [Nat.add_mul]
    have e2b : (1 : Nat) * b = b := Nat.one_mul b
    have e2c : a / b * b = b * (a / b) := Nat.mul_comm _ _
    omega

theorem ceil_lt (a b : Nat) (hb : 0 < b) : ceilDiv a b * b < a + b := by
  unfold ceilDiv
  by_cases hmod : a % b = 0
  · simp [hmod]
    have hdm := Nat.div_add_mod a b
    have e : a / b * b = b * (a / b) := Nat.mul_comm _ _
    omega
  · simp [hmod]
    have hdm := Nat.div_add_mod a b
    have hm := Nat.mod_lt a hb
    have hpos : 0 < a % b := by omega
    have e2a : (a / b + 1) * b = a / b * b + 1 * b := by rw [Nat.add_mul]
    have e2b : (1 : Nat) * b = b := Nat.one_mul b
    have e2c : a / b * b = b * (a / b) := Nat.mul_comm _ _
    omega

def vault : Impl := fun s c =>
  match c with
  | .deposit who x =>
    if s.supply = 0 then
      some { assets := s.assets + x, supply := s.supply + initialSharesPerUnit * x,
             balance := fun b => if b = who then s.balance b + initialSharesPerUnit * x else s.balance b }
    else if s.assets = 0 then none
    else
      some { assets := s.assets + x, supply := s.supply + x * s.supply / s.assets,
             balance := fun b => if b = who then s.balance b + x * s.supply / s.assets else s.balance b }
  | .redeem who t =>
    if s.supply = 0 then
      if t = 0 then some s else none
    else
      if t ≤ s.supply ∧ t ≤ s.balance who then
        some { assets := s.assets - t * s.assets / s.supply, supply := s.supply - t,
               balance := fun b => if b = who then s.balance b - t else s.balance b }
      else none
  | .withdraw who x =>
    if s.supply = 0 then none
    else if s.assets = 0 then none
    else
      if x ≤ s.assets ∧ ceilDiv (x * s.supply) s.assets ≤ s.supply ∧ ceilDiv (x * s.supply) s.assets ≤ s.balance who then
        some { assets := s.assets - x, supply := s.supply - ceilDiv (x * s.supply) s.assets,
               balance := fun b => if b = who then s.balance b - ceilDiv (x * s.supply) s.assets else s.balance b }
      else none

theorem req_deposit_succeeds : DepositSucceeds vault := by
  intro s who x h
  show Option.isSome (vault s (.deposit who x))
  unfold vault
  by_cases hsup : s.supply = 0
  · simp [hsup]
  · simp [hsup]
    have hassets : 0 < s.assets := by
      cases h with
      | inl h0 => exact absurd h0 hsup
      | inr h1 => exact h1
    have hne : ¬ s.assets = 0 := by omega
    simp [hne]

theorem req_redeem_succeeds : RedeemSucceeds vault := by
  intro s who t h1 h2
  show Option.isSome (vault s (.redeem who t))
  unfold vault
  by_cases hsup : s.supply = 0
  · simp [hsup]
    have ht : t = 0 := by omega
    simp [ht]
  · simp [hsup]
    have hc : t ≤ s.supply ∧ t ≤ s.balance who := ⟨h2, h1⟩
    simp [hc]

theorem req_withdraw_succeeds : WithdrawSucceeds vault := by
  intro s who x hsup hassets hbal hval
  show Option.isSome (vault s (.withdraw who x))
  unfold vault
  have hsupne : ¬ s.supply = 0 := by omega
  have hassetsne : ¬ s.assets = 0 := by omega
  simp [hsupne, hassetsne]
  have hmono : s.balance who * s.assets ≤ s.supply * s.assets :=
    mul_le_mul_right' s.assets hbal
  have htrans : x * s.supply ≤ s.supply * s.assets := Nat.le_trans hval hmono
  have htrans2 : x * s.supply ≤ s.assets * s.supply := by
    have e : s.supply * s.assets = s.assets * s.supply := Nat.mul_comm _ _
    omega
  have hx : x ≤ s.assets := le_of_mul_le_mul_right' htrans2 hsup
  have ht_bal : ceilDiv (x * s.supply) s.assets ≤ s.balance who :=
    ceil_le hassets hval
  have ht_sup : ceilDiv (x * s.supply) s.assets ≤ s.supply :=
    ceil_le hassets htrans
  have hc : x ≤ s.assets ∧ ceilDiv (x * s.supply) s.assets ≤ s.supply ∧ ceilDiv (x * s.supply) s.assets ≤ s.balance who :=
    ⟨hx, ht_sup, ht_bal⟩
  simp [hc]

theorem req_deposit_effects : DepositEffects vault := by
  intro s s' who x h
  unfold vault at h
  by_cases hsup : s.supply = 0
  · simp [hsup] at h
    cases h
    refine ⟨initialSharesPerUnit * x, rfl, by simp [hsup], if_pos rfl, fun b hb => if_neg hb⟩
  · simp [hsup] at h
    by_cases hassets : s.assets = 0
    · simp [hassets] at h
    · simp [hassets] at h
      cases h
      exact ⟨x * s.supply / s.assets, rfl, rfl, if_pos rfl, fun b hb => if_neg hb⟩

theorem req_redeem_effects : RedeemEffects vault := by
  intro s s' who t h
  unfold vault at h
  by_cases hsup : s.supply = 0
  · simp [hsup] at h
    by_cases ht : t = 0
    · simp [ht] at h
      cases h
      exact ⟨0, by omega, by omega, Nat.zero_le _, by simp, by simp [ht], by simp [ht], fun b _ => rfl⟩
    · simp [ht] at h
  · simp [hsup] at h
    by_cases hc : t ≤ s.supply ∧ t ≤ s.balance who
    · simp [hc] at h
      have hle1 : (t * s.assets / s.supply) * s.supply ≤ t * s.assets := div_mul_le' _ _
      have hle2 : t * s.assets ≤ s.supply * s.assets := mul_le_mul_right' s.assets hc.1
      have hle3 : (t * s.assets / s.supply) * s.supply ≤ s.supply * s.assets :=
        Nat.le_trans hle1 hle2
      have hle4 : (t * s.assets / s.supply) * s.supply ≤ s.assets * s.supply := by
        have e : s.supply * s.assets = s.assets * s.supply := Nat.mul_comm _ _
        omega
      have hpos : 0 < s.supply := by omega
      have hy : t * s.assets / s.supply ≤ s.assets := le_of_mul_le_mul_right' hle4 hpos
      cases h
      exact ⟨t * s.assets / s.supply, hc.2, hc.1, hy, rfl, rfl, if_pos rfl, fun b hb => if_neg hb⟩
    · simp [hc] at h

theorem req_withdraw_effects : WithdrawEffects vault := by
  intro s s' who x h
  unfold vault at h
  by_cases hsup : s.supply = 0
  · simp [hsup] at h
  · simp [hsup] at h
    by_cases hassets : s.assets = 0
    · simp [hassets] at h
    · simp [hassets] at h
      by_cases hc : x ≤ s.assets ∧ ceilDiv (x * s.supply) s.assets ≤ s.supply ∧ ceilDiv (x * s.supply) s.assets ≤ s.balance who
      · simp [hc] at h
        cases h
        exact ⟨ceilDiv (x * s.supply) s.assets, hc.2.2, hc.2.1, hc.1, rfl, rfl, if_pos rfl, fun b hb => if_neg hb⟩
      · simp [hc] at h

theorem req_deposit_rounds_down : DepositRoundsDown vault := by
  intro s s' who x t h1 h2
  have hs_t : s'.supply = s.supply + t := h2.2.1
  by_cases hsup : s.supply = 0
  · have hV : vault s (.deposit who x) =
      some { assets := s.assets + x, supply := s.supply + initialSharesPerUnit * x,
             balance := fun b => if b = who then s.balance b + initialSharesPerUnit * x else s.balance b } := by
      unfold vault; simp [hsup]
    rw [hV] at h1
    have heq := Option.some_inj.mp h1
    have hs_k : s'.supply = s.supply + initialSharesPerUnit * x := by rw [← heq]
    have ht : t = initialSharesPerUnit * x := by omega
    exact ⟨fun _ => ht, fun hpos => by omega⟩
  · by_cases hassets : s.assets = 0
    · have hV : vault s (.deposit who x) = none := by unfold vault; simp [hsup, hassets]
      rw [hV] at h1
      simp at h1
    · have hV : vault s (.deposit who x) =
        some { assets := s.assets + x, supply := s.supply + x * s.supply / s.assets,
               balance := fun b => if b = who then s.balance b + x * s.supply / s.assets else s.balance b } := by
        unfold vault; simp [hsup, hassets]
      rw [hV] at h1
      have heq := Option.some_inj.mp h1
      have hs_k : s'.supply = s.supply + x * s.supply / s.assets := by rw [← heq]
      have ht : t = x * s.supply / s.assets := by omega
      have hpos0 : 0 < s.assets := by omega
      have hle : t * s.assets ≤ x * s.supply := by
        rw [ht]
        exact div_mul_le' _ _
      have hlt : x * s.supply < (t + 1) * s.assets := by
        rw [ht]
        exact lt_succ_mul' _ _ hpos0
      exact ⟨fun h0 => by omega, fun _ => ⟨hle, hlt⟩⟩

theorem req_redeem_rounds_down : RedeemRoundsDown vault := by
  intro s s' who t y h1 h2
  obtain ⟨hb1, hs1, hy1, ha, hs, hbal, _⟩ := h2
  by_cases hsup : s.supply = 0
  · by_cases ht : t = 0
    · have hV : vault s (.redeem who t) = some s := by unfold vault; simp [hsup, ht]
      rw [hV] at h1
      have heq := Option.some_inj.mp h1
      have ha_k : s'.assets = s.assets := by rw [← heq]
      have hy0 : y = 0 := by omega
      exact ⟨fun _ => hy0, fun hpos => by omega⟩
    · have hV : vault s (.redeem who t) = none := by unfold vault; simp [hsup, ht]
      rw [hV] at h1
      simp at h1
  · by_cases hc : t ≤ s.supply ∧ t ≤ s.balance who
    · have hV : vault s (.redeem who t) =
        some { assets := s.assets - t * s.assets / s.supply, supply := s.supply - t,
               balance := fun b => if b = who then s.balance b - t else s.balance b } := by
        unfold vault; simp [hsup, hc]
      rw [hV] at h1
      have heq := Option.some_inj.mp h1
      have ha_k : s'.assets = s.assets - t * s.assets / s.supply := by rw [← heq]
      have hle1 : (t * s.assets / s.supply) * s.supply ≤ t * s.assets := div_mul_le' _ _
      have hle2 : t * s.assets ≤ s.supply * s.assets := mul_le_mul_right' s.assets hc.1
      have hle4 : (t * s.assets / s.supply) * s.supply ≤ s.assets * s.supply := by
        have e : s.supply * s.assets = s.assets * s.supply := Nat.mul_comm _ _
        omega
      have hpos : 0 < s.supply := by omega
      have he_le : t * s.assets / s.supply ≤ s.assets :=
        le_of_mul_le_mul_right' hle4 hpos
      have hy2 : y = t * s.assets / s.supply := by omega
      have hle : y * s.supply ≤ t * s.assets := by
        rw [hy2]
        exact div_mul_le' _ _
      have hlt : t * s.assets < (y + 1) * s.supply := by
        rw [hy2]
        exact lt_succ_mul' _ _ hpos
      exact ⟨fun h0 => by omega, fun _ => ⟨hle, hlt⟩⟩
    · have hV : vault s (.redeem who t) = none := by unfold vault; simp [hsup, hc]
      rw [hV] at h1
      simp at h1

theorem req_withdraw_rounds_up : WithdrawRoundsUp vault := by
  intro s s' who x t h1 h2
  obtain ⟨hb1, hs1, hy1, ha, hs, hbal, _⟩ := h2
  by_cases hsup : s.supply = 0
  · have hV : vault s (.withdraw who x) = none := by unfold vault; simp [hsup]
    rw [hV] at h1
    simp at h1
  · by_cases hassets : s.assets = 0
    · have hV : vault s (.withdraw who x) = none := by unfold vault; simp [hsup, hassets]
      rw [hV] at h1
      simp at h1
    · by_cases hc : x ≤ s.assets ∧ ceilDiv (x * s.supply) s.assets ≤ s.supply ∧ ceilDiv (x * s.supply) s.assets ≤ s.balance who
      · have hV : vault s (.withdraw who x) =
          some { assets := s.assets - x, supply := s.supply - ceilDiv (x * s.supply) s.assets,
                 balance := fun b => if b = who then s.balance b - ceilDiv (x * s.supply) s.assets else s.balance b } := by
          unfold vault; simp [hsup, hassets, hc]
        rw [hV] at h1
        have heq := Option.some_inj.mp h1
        have hs_k : s'.supply = s.supply - ceilDiv (x * s.supply) s.assets := by rw [← heq]
        have ht : t = ceilDiv (x * s.supply) s.assets := by omega
        have hpos : 0 < s.supply := by omega
        have hposA : 0 < s.assets := by omega
        have hle : x * s.supply ≤ t * s.assets := by
          rw [ht]
          have hcc := le_ceil (x * s.supply) s.assets hposA
          omega
        have hlt : t * s.assets < x * s.supply + s.assets := by
          rw [ht]
          exact ceil_lt _ _ hposA
        exact ⟨hpos, hle, hlt⟩
      · have hV : vault s (.withdraw who x) = none := by unfold vault; simp [hsup, hassets, hc]
        rw [hV] at h1
        simp at h1

theorem helper_value_refl (s : Vault) : ValueNotBelow s s := by
  unfold ValueNotBelow
  omega

theorem helper_value_trans {s m e : Vault} (hm : 0 < m.supply)
    (h1 : ValueNotBelow s m) (h2 : ValueNotBelow m e) : ValueNotBelow s e := by
  unfold ValueNotBelow at h1 h2 ⊢
  have e1 : (s.assets * m.supply) * e.supply ≤ (m.assets * s.supply) * e.supply :=
    mul_le_mul_right' e.supply h1
  have e2 : (m.assets * e.supply) * s.supply ≤ (e.assets * m.supply) * s.supply :=
    mul_le_mul_right' s.supply h2
  have r1 : (s.assets * m.supply) * e.supply = (s.assets * e.supply) * m.supply := by
    calc (s.assets * m.supply) * e.supply = s.assets * (m.supply * e.supply) := by rw [Nat.mul_assoc]
      _ = s.assets * (e.supply * m.supply) := by rw [Nat.mul_comm m.supply e.supply]
      _ = (s.assets * e.supply) * m.supply := by rw [← Nat.mul_assoc]
  have r2 : (m.assets * s.supply) * e.supply = (m.assets * e.supply) * s.supply := by
    calc (m.assets * s.supply) * e.supply = m.assets * (s.supply * e.supply) := by rw [Nat.mul_assoc]
      _ = m.assets * (e.supply * s.supply) := by rw [Nat.mul_comm s.supply e.supply]
      _ = (m.assets * e.supply) * s.supply := by rw [← Nat.mul_assoc]
  have r3 : (e.assets * m.supply) * s.supply = (e.assets * s.supply) * m.supply := by
    calc (e.assets * m.supply) * s.supply = e.assets * (m.supply * s.supply) := by rw [Nat.mul_assoc]
      _ = e.assets * (s.supply * m.supply) := by rw [Nat.mul_comm m.supply s.supply]
      _ = (e.assets * s.supply) * m.supply := by rw [← Nat.mul_assoc]
  have hle : (s.assets * e.supply) * m.supply ≤ (e.assets * s.supply) * m.supply := by omega
  exact le_of_mul_le_mul_right' hle hm

theorem helper_deposit_value (s : Vault) (who : Actor) (x : Nat) (v : Vault)
    (hv : vault s (.deposit who x) = some v) (h1 : 0 < s.supply) :
    ValueNotBelow s v := by
  unfold vault at hv
  by_cases hsup : s.supply = 0
  · omega
  · simp [hsup] at hv
    by_cases hassets : s.assets = 0
    · simp [hassets] at hv
    · simp [hassets] at hv
      cases hv
      show ValueNotBelow s _
      unfold ValueNotBelow
      show s.assets * (s.supply + x * s.supply / s.assets) ≤ (s.assets + x) * s.supply
      have hle : x * s.supply / s.assets * s.assets ≤ x * s.supply := div_mul_le' _ _
      have e1 : s.assets * (s.supply + x * s.supply / s.assets) = s.assets * s.supply + s.assets * (x * s.supply / s.assets) := Nat.mul_add _ _ _
      have e2 : (s.assets + x) * s.supply = s.assets * s.supply + x * s.supply := Nat.add_mul _ _ _
      have e3 : s.assets * (x * s.supply / s.assets) = (x * s.supply / s.assets) * s.assets := Nat.mul_comm _ _
      omega

theorem helper_redeem_value (s : Vault) (who : Actor) (t : Nat) (v : Vault)
    (hv : vault s (.redeem who t) = some v) (h1 : 0 < s.supply) :
    ValueNotBelow s v := by
  unfold vault at hv
  by_cases hsup : s.supply = 0
  · omega
  · simp [hsup] at hv
    by_cases hc : t ≤ s.supply ∧ t ≤ s.balance who
    · simp [hc] at hv
      cases hv
      show ValueNotBelow s _
      unfold ValueNotBelow
      show s.assets * (s.supply - t) ≤ (s.assets - t * s.assets / s.supply) * s.supply
      have hle : t * s.assets / s.supply * s.supply ≤ t * s.assets := div_mul_le' _ _
      have e1 : s.assets * (s.supply - t) = s.assets * s.supply - s.assets * t := Nat.mul_sub _ _ _
      have e2 : (s.assets - t * s.assets / s.supply) * s.supply = s.assets * s.supply - (t * s.assets / s.supply) * s.supply := Nat.sub_mul _ _ _
      have e3 : s.assets * t = t * s.assets := Nat.mul_comm _ _
      omega
    · simp [hc] at hv

theorem helper_withdraw_value (s : Vault) (who : Actor) (x : Nat) (v : Vault)
    (hv : vault s (.withdraw who x) = some v) :
    ValueNotBelow s v := by
  unfold vault at hv
  by_cases hsup : s.supply = 0
  · simp [hsup] at hv
  · simp [hsup] at hv
    by_cases hassets : s.assets = 0
    · simp [hassets] at hv
    · simp [hassets] at hv
      by_cases hc : x ≤ s.assets ∧ ceilDiv (x * s.supply) s.assets ≤ s.supply ∧ ceilDiv (x * s.supply) s.assets ≤ s.balance who
      · simp [hc] at hv
        cases hv
        show ValueNotBelow s _
        unfold ValueNotBelow
        show s.assets * (s.supply - ceilDiv (x * s.supply) s.assets) ≤ (s.assets - x) * s.supply
        have hApos : 0 < s.assets := by omega
        have hcc := le_ceil (x * s.supply) s.assets hApos
        have e1 : s.assets * (s.supply - ceilDiv (x * s.supply) s.assets) = s.assets * s.supply - s.assets * ceilDiv (x * s.supply) s.assets := Nat.mul_sub _ _ _
        have e2 : (s.assets - x) * s.supply = s.assets * s.supply - x * s.supply := Nat.sub_mul _ _ _
        have e3 : s.assets * ceilDiv (x * s.supply) s.assets = ceilDiv (x * s.supply) s.assets * s.assets := Nat.mul_comm _ _
        omega
      · simp [hc] at hv

theorem helper_step_mono (s : Vault) (op : Op) (h1 : 0 < s.supply)
    (h2 : 0 < (exec vault s op).supply) : ValueNotBelow s (exec vault s op) := by
  cases op with
  | donate x =>
    have hE : exec vault s (.donate x) = { s with assets := s.assets + x } := rfl
    rw [hE]
    unfold ValueNotBelow
    show s.assets * s.supply ≤ (s.assets + x) * s.supply
    have e : (s.assets + x) * s.supply = s.assets * s.supply + x * s.supply := Nat.add_mul _ _ _
    omega
  | call c =>
    cases c with
    | deposit who x =>
      cases hv : vault s (.deposit who x) with
      | none =>
        have hexec : exec vault s (.call (.deposit who x)) = s := by simp [exec, hv]
        rw [hexec]
        exact helper_value_refl s
      | some v =>
        have hexec : exec vault s (.call (.deposit who x)) = v := by simp [exec, hv]
        rw [hexec]
        exact helper_deposit_value s who x v hv h1
    | redeem who t =>
      cases hv : vault s (.redeem who t) with
      | none =>
        have hexec : exec vault s (.call (.redeem who t)) = s := by simp [exec, hv]
        rw [hexec]
        exact helper_value_refl s
      | some v =>
        have hexec : exec vault s (.call (.redeem who t)) = v := by simp [exec, hv]
        rw [hexec]
        exact helper_redeem_value s who t v hv h1
    | withdraw who x =>
      cases hv : vault s (.withdraw who x) with
      | none =>
        have hexec : exec vault s (.call (.withdraw who x)) = s := by simp [exec, hv]
        rw [hexec]
        exact helper_value_refl s
      | some v =>
        have hexec : exec vault s (.call (.withdraw who x)) = v := by simp [exec, hv]
        rw [hexec]
        exact helper_withdraw_value s who x v hv

theorem helper_mem_head (s : Vault) (ops : List Op) : s ∈ trace vault s ops := by
  cases ops with
  | nil => show s ∈ [s]; exact List.Mem.head _
  | cons op rest => show s ∈ s :: trace vault (exec vault s op) rest; exact List.Mem.head _

theorem helper_run_mono (s : Vault) (ops : List Op)
    (hall : ∀ v ∈ trace vault s ops, 0 < v.supply) : ValueNotBelow s (run vault s ops) := by
  induction ops generalizing s with
  | nil =>
    have heq : run vault s [] = s := rfl
    rw [heq]
    exact helper_value_refl s
  | cons op rest ih =>
    have hspos : 0 < s.supply := hall s (helper_mem_head s (op :: rest))
    have heq_trace : trace vault s (op :: rest) = s :: trace vault (exec vault s op) rest := rfl
    have hs1pos : 0 < (exec vault s op).supply := by
      have hmem_exec : (exec vault s op) ∈ trace vault (exec vault s op) rest :=
        helper_mem_head _ _
      have hmem : (exec vault s op) ∈ trace vault s (op :: rest) := by
        rw [heq_trace]
        exact List.Mem.tail _ hmem_exec
      exact hall _ hmem
    have hall_rest : ∀ v ∈ trace vault (exec vault s op) rest, 0 < v.supply := by
      intro v hv
      have hmem : v ∈ trace vault s (op :: rest) := by
        rw [heq_trace]
        exact List.Mem.tail _ hv
      exact hall v hmem
    have hstep : ValueNotBelow s (exec vault s op) := helper_step_mono s op hspos hs1pos
    have hrest : ValueNotBelow (exec vault s op) (run vault (exec vault s op) rest) := ih _ hall_rest
    have heq_run : run vault s (op :: rest) = run vault (exec vault s op) rest := rfl
    rw [heq_run]
    exact helper_value_trans hs1pos hstep hrest

theorem req_share_value : ShareValueNeverFalls vault := by
  intro history ops hall
  exact helper_run_mono (run vault empty history) ops hall

end ShareVault
