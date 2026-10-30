import ShareVault.Spec

namespace ShareVault

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
    if t ≤ s.balance who then
      if t ≤ s.supply then
        if s.supply = 0 then
          some { assets := s.assets - 0, supply := s.supply - t,
                 balance := fun b => if b = who then s.balance b - t else s.balance b }
        else
          some { assets := s.assets - t * s.assets / s.supply, supply := s.supply - t,
                 balance := fun b => if b = who then s.balance b - t else s.balance b }
      else none
    else none
  | .withdraw who x =>
    if s.supply = 0 then none
    else if s.assets = 0 then none
    else if x ≤ s.assets then
      if (x * s.supply + s.assets - 1) / s.assets ≤ s.balance who then
        if (x * s.supply + s.assets - 1) / s.assets ≤ s.supply then
          some { assets := s.assets - x, supply := s.supply - (x * s.supply + s.assets - 1) / s.assets,
                 balance := fun b => if b = who then s.balance b - (x * s.supply + s.assets - 1) / s.assets else s.balance b }
        else none
      else none
    else none

theorem my_mul_le_mul_right {a b : Nat} (h : a ≤ b) (k : Nat) : a * k ≤ b * k := by
  induction k with
  | zero => simp
  | succ k _ih =>
    have e1 : a * (k + 1) = a * k + a := by rw [Nat.mul_add, Nat.mul_one]
    have e2 : b * (k + 1) = b * k + b := by rw [Nat.mul_add, Nat.mul_one]
    omega

theorem my_le_of_mul_le_mul_right {a b k : Nat} (_hk : 0 < k) (h : a * k ≤ b * k) : a ≤ b := by
  by_cases hle : a ≤ b
  · exact hle
  · have h1 : b + 1 ≤ a := by omega
    have hm := my_mul_le_mul_right h1 k
    have e : (b + 1) * k = b * k + k := by rw [Nat.add_mul, Nat.one_mul]
    omega

theorem floor_le (a b : Nat) : (a / b) * b ≤ a := by
  have h := Nat.div_add_mod a b
  have hc : (a / b) * b = b * (a / b) := Nat.mul_comm _ _
  omega

theorem floor_lt (a b : Nat) (hb : 0 < b) : a < ((a / b) + 1) * b := by
  have h := Nat.div_add_mod a b
  have hm : a % b < b := Nat.mod_lt a hb
  have he : ((a / b) + 1) * b = (a / b) * b + b := by rw [Nat.add_mul, Nat.one_mul]
  have hc : (a / b) * b = b * (a / b) := Nat.mul_comm _ _
  omega

theorem ceil_le_mul (a b : Nat) (hb : 0 < b) : a ≤ ((a + b - 1) / b) * b := by
  have h := Nat.div_add_mod (a + b - 1) b
  have hm : (a + b - 1) % b < b := Nat.mod_lt _ hb
  have he : (((a + b - 1) / b) + 1) * b = ((a + b - 1) / b) * b + b := by rw [Nat.add_mul, Nat.one_mul]
  have hc : ((a + b - 1) / b) * b = b * ((a + b - 1) / b) := Nat.mul_comm _ _
  omega

theorem ceil_mul_lt (a b : Nat) (hb : 0 < b) : ((a + b - 1) / b) * b < a + b := by
  have h := Nat.div_add_mod (a + b - 1) b
  have hm : (a + b - 1) % b < b := Nat.mod_lt _ hb
  have hc : ((a + b - 1) / b) * b = b * ((a + b - 1) / b) := Nat.mul_comm _ _
  omega

theorem ceil_le_bound {a B b : Nat} (hb : 0 < b) (h : a ≤ B * b) :
    (a + b - 1) / b ≤ B := by
  by_cases hle : (a + b - 1) / b ≤ B
  · exact hle
  · have h2 : B + 1 ≤ (a + b - 1) / b := by omega
    have hmono := my_mul_le_mul_right h2 b
    have hfl := floor_le (a + b - 1) b
    have he : (B + 1) * b = B * b + b := by rw [Nat.add_mul, Nat.one_mul]
    omega

theorem y_le_assets_of {t assets supply : Nat} (hs : 0 < supply)
    (hts : t ≤ supply) : t * assets / supply ≤ assets := by
  have hmono := my_mul_le_mul_right hts assets
  have hfl := floor_le (t * assets) supply
  have hle : (t * assets / supply) * supply ≤ assets * supply := by
    have h1 : supply * assets = assets * supply := Nat.mul_comm _ _
    omega
  exact my_le_of_mul_le_mul_right hs hle

theorem req_deposit_succeeds : DepositSucceeds vault := by
  unfold DepositSucceeds
  intro s who x h
  show (vault s (.deposit who x)).isSome
  unfold vault
  by_cases hs : s.supply = 0
  · simp [hs]
  · have hane : s.assets ≠ 0 := by
      cases h with
      | inl h0 => contradiction
      | inr h1 => omega
    simp [hs, hane]

theorem req_redeem_succeeds : RedeemSucceeds vault := by
  unfold RedeemSucceeds
  intro s who t h1 h2
  show (vault s (.redeem who t)).isSome
  unfold vault
  simp only [h1, h2, ↓reduceIte]
  by_cases hs0 : s.supply = 0 <;> simp [hs0]

theorem req_withdraw_succeeds : WithdrawSucceeds vault := by
  unfold WithdrawSucceeds
  intro s who x hs ha hbal hle
  have hsne : ¬ s.supply = 0 := by omega
  have hane : ¬ s.assets = 0 := by omega
  have hx : x ≤ s.assets := by
    have hmono := my_mul_le_mul_right hbal s.assets
    have h4' : x * s.supply ≤ s.assets * s.supply := by
      have c1 : s.balance who * s.assets = s.assets * s.balance who := Nat.mul_comm _ _
      have c2 : s.supply * s.assets = s.assets * s.supply := Nat.mul_comm _ _
      omega
    exact my_le_of_mul_le_mul_right hs h4'
  have ht : (x * s.supply + s.assets - 1) / s.assets ≤ s.balance who := by
    apply ceil_le_bound ha
    have c : s.balance who * s.assets = s.assets * s.balance who := Nat.mul_comm _ _
    omega
  have htsup : (x * s.supply + s.assets - 1) / s.assets ≤ s.supply := by omega
  show (vault s (.withdraw who x)).isSome
  unfold vault
  simp [hsne, hane, hx, ht, htsup]

theorem req_deposit_effects : DepositEffects vault := by
  unfold DepositEffects
  intro s s' who x h
  by_cases hs : s.supply = 0
  · have hv : vault s (.deposit who x) =
        some { assets := s.assets + x, supply := s.supply + initialSharesPerUnit * x,
               balance := fun b => if b = who then s.balance b + initialSharesPerUnit * x else s.balance b } := by
      simp [vault, hs]
    rw [hv] at h
    cases h
    exact ⟨initialSharesPerUnit * x, rfl, by simp, by simp, fun b hb => by simp [hb]⟩
  · by_cases ha : s.assets = 0
    · have hv : vault s (.deposit who x) = none := by simp [vault, hs, ha]
      rw [hv] at h
      cases h
    · have hv : vault s (.deposit who x) =
          some { assets := s.assets + x, supply := s.supply + x * s.supply / s.assets,
                 balance := fun b => if b = who then s.balance b + x * s.supply / s.assets else s.balance b } := by
        simp [vault, hs, ha]
      rw [hv] at h
      cases h
      exact ⟨x * s.supply / s.assets, rfl, by simp, by simp, fun b hb => by simp [hb]⟩

theorem req_redeem_effects : RedeemEffects vault := by
  unfold RedeemEffects
  intro s s' who t h
  by_cases h1 : t ≤ s.balance who
  · by_cases h2 : t ≤ s.supply
    · by_cases hs0 : s.supply = 0
      · have ht0 : t = 0 := by omega
        subst ht0
        have hv : vault s (.redeem who 0) =
            some { assets := s.assets - 0, supply := s.supply - 0,
                   balance := fun b => if b = who then s.balance b - 0 else s.balance b } := by
          simp [vault, hs0]
        rw [hv] at h
        cases h
        exact ⟨0, by omega, by omega, by simp, rfl, by simp, by simp, fun b hb => by simp [hb]⟩
      · have hv : vault s (.redeem who t) =
            some { assets := s.assets - t * s.assets / s.supply, supply := s.supply - t,
                   balance := fun b => if b = who then s.balance b - t else s.balance b } := by
          simp [vault, h1, h2, hs0]
        rw [hv] at h
        cases h
        refine ⟨t * s.assets / s.supply, h1, h2, ?_, rfl, rfl, by simp, fun b hb => by simp [hb]⟩
        exact y_le_assets_of (by omega) h2
    · have hv : vault s (.redeem who t) = none := by simp [vault, h1, h2]
      rw [hv] at h
      cases h
  · have hv : vault s (.redeem who t) = none := by simp [vault, h1]
    rw [hv] at h
    cases h

theorem req_withdraw_effects : WithdrawEffects vault := by
  unfold WithdrawEffects
  intro s s' who x h
  by_cases hs0 : s.supply = 0
  · have hv : vault s (.withdraw who x) = none := by simp [vault, hs0]
    rw [hv] at h
    cases h
  · by_cases ha0 : s.assets = 0
    · have hv : vault s (.withdraw who x) = none := by simp [vault, hs0, ha0]
      rw [hv] at h
      cases h
    · by_cases hx : x ≤ s.assets
      · by_cases ht1 : (x * s.supply + s.assets - 1) / s.assets ≤ s.balance who
        · by_cases ht2 : (x * s.supply + s.assets - 1) / s.assets ≤ s.supply
          · have hv : vault s (.withdraw who x) =
                some { assets := s.assets - x, supply := s.supply - (x * s.supply + s.assets - 1) / s.assets,
                       balance := fun b => if b = who then s.balance b - (x * s.supply + s.assets - 1) / s.assets else s.balance b } := by
              simp [vault, hs0, ha0, hx, ht1, ht2]
            rw [hv] at h
            cases h
            exact ⟨(x * s.supply + s.assets - 1) / s.assets, ht1, ht2, hx, rfl, rfl, by simp, fun b hb => by simp [hb]⟩
          · have hv : vault s (.withdraw who x) = none := by simp [vault, hs0, ha0, hx, ht1, ht2]
            rw [hv] at h
            cases h
        · have hv : vault s (.withdraw who x) = none := by simp [vault, hs0, ha0, hx, ht1]
          rw [hv] at h
          cases h
      · have hv : vault s (.withdraw who x) = none := by simp [vault, hs0, ha0, hx]
        rw [hv] at h
        cases h

theorem req_deposit_rounds_down : DepositRoundsDown vault := by
  unfold DepositRoundsDown Minted
  intro s s' who x t h hm
  obtain ⟨hass, hsup, hbal, hoth⟩ := hm
  constructor
  · intro hs0
    have hv : vault s (.deposit who x) =
        some { assets := s.assets + x, supply := s.supply + initialSharesPerUnit * x,
               balance := fun b => if b = who then s.balance b + initialSharesPerUnit * x else s.balance b } := by
      simp [vault, hs0]
    rw [hv] at h
    cases h
    simp at hsup
    omega
  · intro hspos
    have hsne : ¬ s.supply = 0 := by omega
    by_cases ha0 : s.assets = 0
    · have hv : vault s (.deposit who x) = none := by simp [vault, hsne, ha0]
      rw [hv] at h
      cases h
    · have hv : vault s (.deposit who x) =
          some { assets := s.assets + x, supply := s.supply + x * s.supply / s.assets,
                 balance := fun b => if b = who then s.balance b + x * s.supply / s.assets else s.balance b } := by
        simp [vault, hsne, ha0]
      rw [hv] at h
      cases h
      simp at hsup
      have hteq : t = x * s.supply / s.assets := by omega
      subst hteq
      have hbpos : 0 < s.assets := by omega
      constructor
      · have hfl := floor_le (x * s.supply) s.assets
        omega
      · have hlt := floor_lt (x * s.supply) s.assets hbpos
        have he : ((x * s.supply / s.assets) + 1) * s.assets = (x * s.supply / s.assets) * s.assets + s.assets := by
          rw [Nat.add_mul, Nat.one_mul]
        omega

theorem req_redeem_rounds_down : RedeemRoundsDown vault := by
  unfold RedeemRoundsDown Burned
  intro s s' who t y h hb
  obtain ⟨hbt, hst, hyass, hass, hsup, hbal, hoth⟩ := hb
  constructor
  · intro hs0
    have ht0 : t = 0 := by omega
    subst ht0
    have hv : vault s (.redeem who 0) =
        some { assets := s.assets - 0, supply := s.supply - 0,
               balance := fun b => if b = who then s.balance b - 0 else s.balance b } := by
      simp [vault, hs0]
    rw [hv] at h
    cases h
    simp at hass
    omega
  · intro hspos
    have hsne : ¬ s.supply = 0 := by omega
    have hv : vault s (.redeem who t) =
        some { assets := s.assets - t * s.assets / s.supply, supply := s.supply - t,
               balance := fun b => if b = who then s.balance b - t else s.balance b } := by
      simp [vault, hbt, hst, hsne]
    rw [hv] at h
    cases h
    simp at hass
    have hXle : t * s.assets / s.supply ≤ s.assets := y_le_assets_of hspos hst
    have hyeq : y = t * s.assets / s.supply := by omega
    subst hyeq
    constructor
    · have hfl := floor_le (t * s.assets) s.supply
      omega
    · have hlt := floor_lt (t * s.assets) s.supply hspos
      have he : ((t * s.assets / s.supply) + 1) * s.supply = (t * s.assets / s.supply) * s.supply + s.supply := by
        rw [Nat.add_mul, Nat.one_mul]
      omega

theorem req_withdraw_rounds_up : WithdrawRoundsUp vault := by
  unfold WithdrawRoundsUp Burned
  intro s s' who x t h hb
  obtain ⟨hbt, hst, hxass, hass, hsup, hbal, hoth⟩ := hb
  by_cases hs0 : s.supply = 0
  · have hv : vault s (.withdraw who x) = none := by simp [vault, hs0]
    rw [hv] at h
    cases h
  · by_cases ha0 : s.assets = 0
    · have hv : vault s (.withdraw who x) = none := by simp [vault, hs0, ha0]
      rw [hv] at h
      cases h
    · by_cases hx : x ≤ s.assets
      · by_cases ht1 : (x * s.supply + s.assets - 1) / s.assets ≤ s.balance who
        · by_cases ht2 : (x * s.supply + s.assets - 1) / s.assets ≤ s.supply
          · have hv : vault s (.withdraw who x) =
                some { assets := s.assets - x, supply := s.supply - (x * s.supply + s.assets - 1) / s.assets,
                       balance := fun b => if b = who then s.balance b - (x * s.supply + s.assets - 1) / s.assets else s.balance b } := by
              simp [vault, hs0, ha0, hx, ht1, ht2]
            rw [hv] at h
            cases h
            simp at hass hsup
            have hspos : 0 < s.supply := by omega
            have hapos : 0 < s.assets := by omega
            have hteq : t = (x * s.supply + s.assets - 1) / s.assets := by omega
            subst hteq
            refine ⟨hspos, ?_, ?_⟩
            · have hcl := ceil_le_mul (x * s.supply) s.assets hapos
              have hcomm : ((x * s.supply + s.assets - 1) / s.assets) * s.assets = s.assets * ((x * s.supply + s.assets - 1) / s.assets) := Nat.mul_comm _ _
              omega
            · have hcu := ceil_mul_lt (x * s.supply) s.assets hapos
              omega
          · have hv : vault s (.withdraw who x) = none := by simp [vault, hs0, ha0, hx, ht1, ht2]
            rw [hv] at h
            cases h
        · have hv : vault s (.withdraw who x) = none := by simp [vault, hs0, ha0, hx, ht1]
          rw [hv] at h
          cases h
      · have hv : vault s (.withdraw who x) = none := by simp [vault, hs0, ha0, hx]
        rw [hv] at h
        cases h

theorem ValueNotBelow_refl (s : Vault) : ValueNotBelow s s := by
  unfold ValueNotBelow
  exact Nat.le_refl _

theorem ValueNotBelow_trans {a b c : Vault} (h1 : ValueNotBelow a b) (h2 : ValueNotBelow b c)
    (hb : 0 < b.supply) : ValueNotBelow a c := by
  unfold ValueNotBelow at h1 h2 ⊢
  have p1 : (a.assets * b.supply) * c.supply ≤ (b.assets * a.supply) * c.supply :=
    my_mul_le_mul_right h1 c.supply
  have p2 : (b.assets * c.supply) * a.supply ≤ (c.assets * b.supply) * a.supply :=
    my_mul_le_mul_right h2 a.supply
  have eA : (a.assets * b.supply) * c.supply = (a.assets * c.supply) * b.supply := by ac_rfl
  have eB : (b.assets * a.supply) * c.supply = (b.assets * c.supply) * a.supply := by ac_rfl
  have eC : (c.assets * b.supply) * a.supply = (c.assets * a.supply) * b.supply := by ac_rfl
  have q1 : (a.assets * c.supply) * b.supply ≤ (b.assets * c.supply) * a.supply := by
    rw [← eA, ← eB]
    exact p1
  have q2 : (b.assets * c.supply) * a.supply ≤ (c.assets * a.supply) * b.supply := by
    rw [← eC]
    exact p2
  have hchain : (a.assets * c.supply) * b.supply ≤ (c.assets * a.supply) * b.supply :=
    Nat.le_trans q1 q2
  exact my_le_of_mul_le_mul_right hb hchain

theorem deposit_value {s s' : Vault} {who x : Nat}
    (h : vault s (.deposit who x) = some s') (hs : 0 < s.supply) :
    ValueNotBelow s s' := by
  have hex : ∃ t, Minted s who x t s' := req_deposit_effects _ _ _ _ h
  obtain ⟨t, hm⟩ := hex
  have hround := (req_deposit_rounds_down _ _ _ _ _ h hm).2 hs
  obtain ⟨hass, hsup, _hbal, _hoth⟩ := hm
  obtain ⟨hle, _hlt⟩ := hround
  unfold ValueNotBelow
  rw [hsup, hass]
  have e1 : s.assets * (s.supply + t) = s.assets * s.supply + s.assets * t :=
    Nat.mul_add _ _ _
  have e2 : (s.assets + x) * s.supply = s.assets * s.supply + x * s.supply :=
    Nat.add_mul _ _ _
  have hc : s.assets * t = t * s.assets := Nat.mul_comm _ _
  omega

theorem redeem_value {s s' : Vault} {who t : Nat}
    (h : vault s (.redeem who t) = some s') :
    ValueNotBelow s s' := by
  have hex : ∃ y, Burned s who t y s' := req_redeem_effects _ _ _ _ h
  obtain ⟨y, hb⟩ := hex
  have hround := req_redeem_rounds_down _ _ _ _ _ h hb
  have hbound : y * s.supply ≤ t * s.assets := by
    by_cases hs0 : s.supply = 0
    · have hy0 := hround.1 hs0
      simp [hy0]
    · exact (hround.2 (by omega)).1
  obtain ⟨_hbt, hst, hyass, hass, hsup, _hbal, _hoth⟩ := hb
  unfold ValueNotBelow
  rw [hsup, hass]
  have hSt : s.supply - t + t = s.supply := Nat.sub_add_cancel hst
  have hAy : s.assets - y + y = s.assets := Nat.sub_add_cancel hyass
  have e1 : s.assets * (s.supply - t) + s.assets * t = s.assets * s.supply := by
    rw [← Nat.mul_add, hSt]
  have e2 : (s.assets - y) * s.supply + y * s.supply = s.assets * s.supply := by
    rw [← Nat.add_mul, hAy]
  have hc : s.assets * t = t * s.assets := Nat.mul_comm _ _
  omega

theorem withdraw_value {s s' : Vault} {who x : Nat}
    (h : vault s (.withdraw who x) = some s') :
    ValueNotBelow s s' := by
  have hex : ∃ t, Burned s who t x s' := req_withdraw_effects _ _ _ _ h
  obtain ⟨t, hb⟩ := hex
  have hround := req_withdraw_rounds_up _ _ _ _ _ h hb
  obtain ⟨_hspos, hle, _hlt⟩ := hround
  obtain ⟨_hbt, hst, hxass, hass, hsup, _hbal, _hoth⟩ := hb
  unfold ValueNotBelow
  rw [hsup, hass]
  have hSt : s.supply - t + t = s.supply := Nat.sub_add_cancel hst
  have hAx : s.assets - x + x = s.assets := Nat.sub_add_cancel hxass
  have e1 : s.assets * (s.supply - t) + s.assets * t = s.assets * s.supply := by
    rw [← Nat.mul_add, hSt]
  have e2 : (s.assets - x) * s.supply + x * s.supply = s.assets * s.supply := by
    rw [← Nat.add_mul, hAx]
  have hc : s.assets * t = t * s.assets := Nat.mul_comm _ _
  omega

theorem step_value (s : Vault) (op : Op) (hs : 0 < s.supply)
    (hs' : 0 < (exec vault s op).supply) : ValueNotBelow s (exec vault s op) := by
  cases op with
  | donate x =>
    have hdef : exec vault s (Op.donate x) = { s with assets := s.assets + x } := rfl
    rw [hdef]
    unfold ValueNotBelow
    simp
    have h2 := my_mul_le_mul_right (Nat.le_add_right s.assets x) s.supply
    have c2 : (s.assets + x) * s.supply = s.supply * (s.assets + x) := Nat.mul_comm _ _
    have c1 : s.assets * s.supply = s.supply * s.assets := Nat.mul_comm _ _
    omega
  | call c =>
    cases c with
    | deposit who x =>
      have hdef : exec vault s (Op.call (Call.deposit who x)) = (vault s (Call.deposit who x)).getD s := rfl
      cases heq : vault s (Call.deposit who x) with
      | none =>
        have hexec : exec vault s (Op.call (Call.deposit who x)) = s := by
          simp [exec, heq]
        rw [hexec]
        exact ValueNotBelow_refl s
      | some s' =>
        have hexec : exec vault s (Op.call (Call.deposit who x)) = s' := by
          simp [exec, heq]
        rw [hexec]
        exact deposit_value heq hs
    | redeem who tt =>
      have hdef : exec vault s (Op.call (Call.redeem who tt)) = (vault s (Call.redeem who tt)).getD s := rfl
      cases heq : vault s (Call.redeem who tt) with
      | none =>
        have hexec : exec vault s (Op.call (Call.redeem who tt)) = s := by
          simp [exec, heq]
        rw [hexec]
        exact ValueNotBelow_refl s
      | some s' =>
        have hexec : exec vault s (Op.call (Call.redeem who tt)) = s' := by
          simp [exec, heq]
        rw [hexec]
        exact redeem_value heq
    | withdraw who x =>
      have hdef : exec vault s (Op.call (Call.withdraw who x)) = (vault s (Call.withdraw who x)).getD s := rfl
      cases heq : vault s (Call.withdraw who x) with
      | none =>
        have hexec : exec vault s (Op.call (Call.withdraw who x)) = s := by
          simp [exec, heq]
        rw [hexec]
        exact ValueNotBelow_refl s
      | some s' =>
        have hexec : exec vault s (Op.call (Call.withdraw who x)) = s' := by
          simp [exec, heq]
        rw [hexec]
        exact withdraw_value heq

theorem trace_head_mem (impl : Impl) (s : Vault) (ops : List Op) :
    s ∈ trace impl s ops := by
  cases ops with
  | nil => simp [trace]
  | cons op rest => simp [trace]

theorem run_value_mono (s0 : Vault) (ops : List Op)
    (h : ∀ v ∈ trace vault s0 ops, 0 < v.supply) :
    ValueNotBelow s0 (run vault s0 ops) := by
  induction ops generalizing s0 with
  | nil =>
    have heq : run vault s0 [] = s0 := rfl
    rw [heq]
    exact ValueNotBelow_refl s0
  | cons op rest ih =>
    have heq_trace : trace vault s0 (op :: rest) = s0 :: trace vault (exec vault s0 op) rest := rfl
    have heq_run : run vault s0 (op :: rest) = run vault (exec vault s0 op) rest := rfl
    have hs0 : 0 < s0.supply := by
      apply h
      rw [heq_trace]
      simp
    have hrest : ∀ v ∈ trace vault (exec vault s0 op) rest, 0 < v.supply := by
      intro v hv
      apply h
      rw [heq_trace]
      simp [hv]
    have hs1 : 0 < (exec vault s0 op).supply := by
      apply hrest
      exact trace_head_mem _ _ _
    have hstep : ValueNotBelow s0 (exec vault s0 op) := step_value s0 op hs0 hs1
    have htail : ValueNotBelow (exec vault s0 op) (run vault (exec vault s0 op) rest) := ih _ hrest
    rw [heq_run]
    exact ValueNotBelow_trans hstep htail hs1

theorem req_share_value : ShareValueNeverFalls vault := by
  unfold ShareValueNeverFalls
  intro history ops h
  exact run_value_mono (run vault empty history) ops h

end ShareVault
