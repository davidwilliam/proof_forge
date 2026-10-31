import ShareVault.Spec
namespace ShareVault

def vault : Impl := fun s c =>
  match c with
  | .deposit who x =>
    if s.supply = 0 then
      let t := initialSharesPerUnit * x
      some { assets := s.assets + x, supply := s.supply + t,
             balance := fun b => if b = who then s.balance b + t else s.balance b }
    else if s.assets = 0 then none
    else
      let t := x * s.supply / s.assets
      some { assets := s.assets + x, supply := s.supply + t,
             balance := fun b => if b = who then s.balance b + t else s.balance b }
  | .redeem who t =>
    let y := if s.supply = 0 then 0 else t * s.assets / s.supply
    if t ≤ s.balance who ∧ t ≤ s.supply ∧ y ≤ s.assets then
      some { assets := s.assets - y, supply := s.supply - t,
             balance := fun b => if b = who then s.balance b - t else s.balance b }
    else none
  | .withdraw who x =>
    if s.supply = 0 then none
    else if s.assets = 0 then none
    else
      let t := (x * s.supply + s.assets - 1) / s.assets
      if t ≤ s.balance who ∧ t ≤ s.supply ∧ x ≤ s.assets then
        some { assets := s.assets - x, supply := s.supply - t,
               balance := fun b => if b = who then s.balance b - t else s.balance b }
      else none

theorem helper_redeem_y_le : ∀ (s : Vault) (t : Nat), t ≤ s.supply → (if s.supply = 0 then 0 else t * s.assets / s.supply) ≤ s.assets := by
  intro s t h
  by_cases hs : s.supply = 0
  · simp [hs]
  · simp [hs]
    have hpos : 0 < s.supply := Nat.pos_of_ne_zero hs
    have h1 : t * s.assets ≤ s.supply * s.assets := Nat.mul_le_mul_right s.assets h
    have h2 : t * s.assets / s.supply ≤ s.supply * s.assets / s.supply := Nat.div_le_div_right h1
    have h3 : s.supply * s.assets / s.supply = s.assets := by
      rw [Nat.mul_comm s.supply s.assets]
      exact Nat.mul_div_cancel s.assets hpos
    omega

theorem test_names : True := by trivial
#check @Nat.le_of_mul_le_mul_right
#check @Nat.div_le_iff_le_mul_add_pred
#check @Nat.le_div_iff_mul_le
#check @Nat.div_eq_of_lt_le

theorem tmp_probe1 : ∀ (S A : Nat), (S + 1) * A = S * A + A := by
  intro S A; exact Nat.succ_mul S A
#check @Nat.succ_mul
#check @Nat.add_mul
#check @Nat.mul_add
#check @Nat.mul_comm
#check @Nat.mul_le_mul_right
#check @Nat.le_of_mul_le_mul_left
#check @Nat.div_add_mod
#check @Nat.mod_lt

theorem tmp_div_lemma_test (x k y : Nat) (hk : 0 < k) : x / k ≤ y ↔ x ≤ k * y + (k - 1) :=
  Nat.div_le_iff_le_mul_add_pred hk

theorem tmp_check_order (a b c : Nat) (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b :=
  Nat.le_of_mul_le_mul_right h hc

theorem tmp_check_order2 (a b c : Nat) (h : c * a ≤ c * b) (hc : 0 < c) : a ≤ b :=
  Nat.le_of_mul_le_mul_left h hc

theorem req_deposit_effects_aux3 : DepositEffects vault := by
  intro s s' who x h
  unfold vault at h
  by_cases hsup : s.supply = 0
  · simp only [hsup, ↓reduceIte] at h
    cases h
    refine ⟨initialSharesPerUnit * x, rfl, ?_, ?_, ?_⟩
    · simp [hsup]
    · simp
    · intro b hb
      simp [hb]
  · simp only [hsup, ↓reduceIte] at h
    by_cases hassets : s.assets = 0
    · simp [hassets] at h
    · simp only [hassets, ↓reduceIte] at h
      cases h
      exact ⟨_, rfl, rfl, by simp, fun b hb => by simp [hb]⟩

theorem tmp_dep_aux2b (N D : Nat) (hD : 0 < D) : N < (N / D + 1) * D := by
  have h1 : D * (N / D) + N % D = N := Nat.div_add_mod N D
  have h2 : N % D < D := Nat.mod_lt N hD
  have h3 : D * (N / D) = (N / D) * D := Nat.mul_comm _ _
  have h4 : (N / D + 1) * D = (N / D) * D + D := by rw [Nat.add_mul, Nat.one_mul]
  omega

theorem tmp_dep_auxA (N D : Nat) : N / D * D ≤ N := Nat.div_mul_le_self N D

theorem tmp_probe_subst2 : ∀ (s s' : Vault) (who : Actor) (x t : Nat),
    s'.supply = s.supply + t →
    (vault s (.deposit who x) = some s') →
    s.supply = 0 → t = initialSharesPerUnit * x := by
  intro s s' who x t hsup' hv h0
  unfold vault at hv
  simp only [h0, ↓reduceIte] at hv
  cases hv
  simp at hsup'
  omega

theorem ceil_le_mulW (N D : Nat) (hD : 0 < D) : N ≤ ((N + D - 1) / D) * D := by
  have h1 : D * ((N + D - 1) / D) + (N + D - 1) % D = N + D - 1 := Nat.div_add_mod (N + D - 1) D
  have h2 : (N + D - 1) % D < D := Nat.mod_lt _ hD
  have h3 : D * ((N + D - 1) / D) = ((N + D - 1) / D) * D := Nat.mul_comm _ _
  omega

theorem ceil_mul_ltW (N D : Nat) (hD : 0 < D) : ((N + D - 1) / D) * D < N + D := by
  have h1 : D * ((N + D - 1) / D) + (N + D - 1) % D = N + D - 1 := Nat.div_add_mod (N + D - 1) D
  have h3 : D * ((N + D - 1) / D) = ((N + D - 1) / D) * D := Nat.mul_comm _ _
  omega

theorem probe_sub_mul (a b c : Nat) : (a - b) * c = a * c - b * c := by
  exact Nat.sub_mul a b c

theorem probe_mul_sub (a b c : Nat) : a * (b - c) = a * b - a * c := by
  exact Nat.mul_sub a b c

theorem probe_add_mul2 (a b c : Nat) : (a + b) * c = a * c + b * c := by
  exact Nat.add_mul a b c

theorem probe_mul_add2 (a b c : Nat) : a * (b + c) = a * b + a * c := by
  exact Nat.mul_add a b c

theorem vnb_trans_aux (A1 S1 A2 S2 A3 S3 : Nat) (h2pos : 0 < S2)
    (h1 : A1 * S2 ≤ A2 * S1) (h2 : A2 * S3 ≤ A3 * S2) : A1 * S3 ≤ A3 * S1 := by
  have e1 : (A1 * S3) * S2 = (A1 * S2) * S3 := by
    calc (A1 * S3) * S2 = A1 * (S3 * S2) := by rw [Nat.mul_assoc]
      _ = A1 * (S2 * S3) := by rw [Nat.mul_comm S3 S2]
      _ = (A1 * S2) * S3 := by rw [← Nat.mul_assoc]
  have e2 : (A3 * S1) * S2 = (A3 * S2) * S1 := by
    calc (A3 * S1) * S2 = A3 * (S1 * S2) := by rw [Nat.mul_assoc]
      _ = A3 * (S2 * S1) := by rw [Nat.mul_comm S1 S2]
      _ = (A3 * S2) * S1 := by rw [← Nat.mul_assoc]
  have e3 : (A2 * S1) * S3 = (A2 * S3) * S1 := by
    calc (A2 * S1) * S3 = A2 * (S1 * S3) := by rw [Nat.mul_assoc]
      _ = A2 * (S3 * S1) := by rw [Nat.mul_comm S1 S3]
      _ = (A2 * S3) * S1 := by rw [← Nat.mul_assoc]
  have h1' : (A1 * S2) * S3 ≤ (A2 * S1) * S3 := Nat.mul_le_mul_right S3 h1
  have h2' : (A2 * S3) * S1 ≤ (A3 * S2) * S1 := Nat.mul_le_mul_right S1 h2
  have hchain : (A1 * S3) * S2 ≤ (A3 * S1) * S2 := by omega
  exact Nat.le_of_mul_le_mul_right hchain h2pos

theorem sub_value_mono3 (A S y t : Nat)
    (h : y * S ≤ t * A) : A * (S - t) ≤ (A - y) * S := by
  have e1 : A * (S - t) = A * S - A * t := Nat.mul_sub A S t
  have e2 : (A - y) * S = A * S - y * S := Nat.sub_mul A y S
  have hAt : t * A = A * t := Nat.mul_comm t A
  have h1 : y * S ≤ A * t := by omega
  rw [e1, e2]
  exact Nat.sub_le_sub_left h1 (A * S)

theorem donate_vnb (s : Vault) (x : Nat) :
    ValueNotBelow s ({ s with assets := s.assets + x } : Vault) := by
  unfold ValueNotBelow
  simp only
  have h : s.assets * s.supply ≤ s.assets * s.supply + x * s.supply :=
    Nat.le_add_right _ _
  have heq : (s.assets + x) * s.supply = s.assets * s.supply + x * s.supply :=
    Nat.add_mul s.assets x s.supply
  omega

theorem vnb_refl (s : Vault) : ValueNotBelow s s := by
  unfold ValueNotBelow
  exact Nat.le_refl _

theorem deposit_some_vnb (s s' : Vault) (who : Actor) (x : Nat)
    (hpos : 0 < s.supply) (hsome : vault s (.deposit who x) = some s') :
    ValueNotBelow s s' := by
  unfold ValueNotBelow
  unfold vault at hsome
  have hsup : s.supply ≠ 0 := by omega
  simp only [hsup, ↓reduceIte] at hsome
  by_cases hA : s.assets = 0
  · simp only [hA, ↓reduceIte] at hsome
    cases hsome
  · simp only [hA, ↓reduceIte] at hsome
    cases hsome
    simp only
    have hApos : 0 < s.assets := Nat.pos_of_ne_zero hA
    have hfloor : (x * s.supply / s.assets) * s.assets ≤ x * s.supply :=
      Nat.div_mul_le_self _ _
    have hcomm1 : s.assets * (s.supply + x * s.supply / s.assets)
        = s.assets * s.supply + s.assets * (x * s.supply / s.assets) := by
      rw [Nat.mul_add]
    have hcomm2 : (s.assets + x) * s.supply
        = s.assets * s.supply + x * s.supply := by
      rw [Nat.add_mul]
    have hAt : s.assets * (x * s.supply / s.assets)
        = (x * s.supply / s.assets) * s.assets := Nat.mul_comm _ _
    omega

theorem redeem_some_vnb (s s' : Vault) (who : Actor) (t : Nat)
    (hsome : vault s (.redeem who t) = some s') :
    ValueNotBelow s s' := by
  unfold ValueNotBelow
  unfold vault at hsome
  simp only at hsome
  by_cases hcond : (t ≤ s.balance who ∧ t ≤ s.supply ∧ (if s.supply = 0 then 0 else t * s.assets / s.supply) ≤ s.assets)
  · simp only [hcond] at hsome
    cases hsome
    simp only
    by_cases h0 : s.supply = 0
    · have ht : t = 0 := by
        have := hcond.2.1
        omega
      subst ht
      simp [h0]
    · have hSpos : 0 < s.supply := Nat.pos_of_ne_zero h0
      simp only [h0, ↓reduceIte] at hcond ⊢
      have hfloor : (t * s.assets / s.supply) * s.supply ≤ t * s.assets :=
        Nat.div_mul_le_self _ _
      exact sub_value_mono3 s.assets s.supply (t * s.assets / s.supply) t hfloor
  · simp only [hcond] at hsome
    cases hsome

theorem withdraw_some_vnb (s s' : Vault) (who : Actor) (x : Nat)
    (hsome : vault s (.withdraw who x) = some s') :
    ValueNotBelow s s' := by
  unfold ValueNotBelow
  unfold vault at hsome
  simp only at hsome
  by_cases hsup : s.supply = 0
  · simp only [hsup, ↓reduceIte] at hsome
    cases hsome
  · simp only [hsup, ↓reduceIte] at hsome
    by_cases hA : s.assets = 0
    · simp only [hA, ↓reduceIte] at hsome
      cases hsome
    · simp only [hA, ↓reduceIte] at hsome
      by_cases hcond : ((x * s.supply + s.assets - 1) / s.assets ≤ s.balance who ∧ (x * s.supply + s.assets - 1) / s.assets ≤ s.supply ∧ x ≤ s.assets)
      · simp only [hcond] at hsome
        cases hsome
        simp only
        have hApos : 0 < s.assets := Nat.pos_of_ne_zero hA
        have hlb : x * s.supply ≤ ((x * s.supply + s.assets - 1) / s.assets) * s.assets :=
          ceil_le_mulW _ _ hApos
        exact sub_value_mono3 s.assets s.supply x ((x * s.supply + s.assets - 1) / s.assets) hlb
      · simp only [hcond] at hsome
        cases hsome

theorem vnb_trans_thm2 (s1 s2 s3 : Vault) (h2pos : 0 < s2.supply)
    (h1 : ValueNotBelow s1 s2) (h2 : ValueNotBelow s2 s3) : ValueNotBelow s1 s3 := by
  unfold ValueNotBelow at *
  exact vnb_trans_aux s1.assets s1.supply s2.assets s2.supply s3.assets s3.supply h2pos h1 h2

theorem step_vnb_thm2 (s : Vault) (op : Op) (hpos : 0 < s.supply) :
    ValueNotBelow s (exec vault s op) := by
  cases op with
  | donate amount =>
    simp only [exec]
    exact donate_vnb s amount
  | call c =>
    cases h : vault s c with
    | none =>
      have he : exec vault s (Op.call c) = s := by simp [exec, h]
      rw [he]
      exact vnb_refl s
    | some s' =>
      have he : exec vault s (Op.call c) = s' := by simp [exec, h]
      rw [he]
      cases c with
      | deposit who x =>
        exact deposit_some_vnb s s' who x hpos h
      | redeem who t =>
        exact redeem_some_vnb s s' who t h
      | withdraw who x =>
        exact withdraw_some_vnb s s' who x h

theorem mem_trace_head_aux (s : Vault) (ops : List Op) : s ∈ trace vault s ops := by
  cases ops with
  | nil => simp [trace]
  | cons op ops => simp [trace]

theorem mem_trace_tail_aux (s : Vault) (op : Op) (ops : List Op) (v : Vault)
    (hv : v ∈ trace vault (exec vault s op) ops) :
    v ∈ trace vault s (op :: ops) := by
  simp only [trace]
  exact List.Mem.tail _ hv

theorem run_vnb_chain2 (s : Vault) (ops : List Op)
    (hall : ∀ v ∈ trace vault s ops, 0 < v.supply) :
    ValueNotBelow s (run vault s ops) := by
  induction ops generalizing s with
  | nil =>
    simp only [run]
    exact vnb_refl s
  | cons op ops ih =>
    simp only [run]
    have hs : 0 < s.supply := hall s (mem_trace_head_aux s (op :: ops))
    have hstep : ValueNotBelow s (exec vault s op) := step_vnb_thm2 s op hs
    have hmid : 0 < (exec vault s op).supply :=
      hall _ (mem_trace_tail_aux s op ops _ (mem_trace_head_aux _ _))
    have hall' : ∀ v ∈ trace vault (exec vault s op) ops, 0 < v.supply := by
      intro v hv
      exact hall v (mem_trace_tail_aux s op ops v hv)
    have hrest : ValueNotBelow (exec vault s op) (run vault (exec vault s op) ops) :=
      ih _ hall'
    exact vnb_trans_thm2 s _ _ hmid hstep hrest

theorem req_deposit_succeeds    : DepositSucceeds vault := by
  intro s who x h
  unfold vault
  by_cases hsup : s.supply = 0
  · simp [hsup]
  · have hpos : 0 < s.assets := by
      rcases h with h0 | hp
      · exact absurd h0 hsup
      · exact hp
    have hassets : s.assets ≠ 0 := by omega
    simp [hsup, hassets]

theorem req_redeem_succeeds     : RedeemSucceeds vault := by
  intro s who t h1 h2
  unfold vault
  simp only
  have hy : (if s.supply = 0 then 0 else t * s.assets / s.supply) ≤ s.assets :=
    helper_redeem_y_le s t h2
  simp [h1, h2, hy]

theorem req_withdraw_succeeds   : WithdrawSucceeds vault := by
  intro s who x hS hA hbal hworth
  unfold vault
  have hsup : s.supply ≠ 0 := by omega
  have hass : s.assets ≠ 0 := by omega
  simp only [hsup, ↓reduceIte, hass]
  have hSpos : 0 < s.supply := hS
  have hDpos : 0 < s.assets := hA
  have hmul_comm1 : s.balance who * s.assets = s.assets * s.balance who := Nat.mul_comm _ _
  have hmul_comm2 : x * s.supply = s.supply * x := Nat.mul_comm _ _
  have hmul_comm3 : s.supply * s.assets = s.assets * s.supply := Nat.mul_comm _ _
  -- x ≤ assets from x*S ≤ B*A ≤ S*A
  have hBmul : s.balance who * s.assets ≤ s.supply * s.assets :=
    Nat.mul_le_mul_right s.assets hbal
  have hXle : x * s.supply ≤ s.supply * s.assets := by omega
  have hx_le : x ≤ s.assets := by
    have h1 : s.supply * x ≤ s.supply * s.assets := by omega
    exact Nat.le_of_mul_le_mul_left h1 hSpos
  have hceil_bal : (x * s.supply + s.assets - 1) / s.assets ≤ s.balance who := by
    rw [Nat.div_le_iff_le_mul_add_pred hDpos]
    have h1 : x * s.supply ≤ s.assets * s.balance who := by omega
    omega
  have hceil_sup : (x * s.supply + s.assets - 1) / s.assets ≤ s.supply := by
    rw [Nat.div_le_iff_le_mul_add_pred hDpos]
    have h1 : s.supply * x ≤ s.supply * s.assets := by omega
    have h2 : s.assets * s.supply = s.supply * s.assets := Nat.mul_comm _ _
    omega
  simp [hceil_bal, hceil_sup, hx_le]

theorem req_deposit_effects     : DepositEffects vault := by
  intro s s' who x h
  unfold vault at h
  by_cases hsup : s.supply = 0
  · simp only [hsup, ↓reduceIte] at h
    cases h
    refine ⟨initialSharesPerUnit * x, rfl, ?_, ?_, ?_⟩
    · simp [hsup]
    · simp
    · intro b hb
      simp [hb]
  · simp only [hsup, ↓reduceIte] at h
    by_cases hassets : s.assets = 0
    · simp [hassets] at h
    · simp only [hassets, ↓reduceIte] at h
      cases h
      exact ⟨_, rfl, rfl, by simp, fun b hb => by simp [hb]⟩

theorem req_redeem_effects      : RedeemEffects vault := by
  intro s s' who t h
  unfold vault at h
  simp only at h
  by_cases hcond : (t ≤ s.balance who ∧ t ≤ s.supply ∧ (if s.supply = 0 then 0 else t * s.assets / s.supply) ≤ s.assets)
  · simp only [hcond] at h
    cases h
    exact ⟨(if s.supply = 0 then 0 else t * s.assets / s.supply), hcond.1, hcond.2.1, hcond.2.2, rfl, rfl, by simp, fun b hb => by simp [hb]⟩
  · simp only [hcond] at h
    simp at h

theorem req_withdraw_effects    : WithdrawEffects vault := by
  intro s s' who x h
  unfold vault at h
  simp only at h
  by_cases hsup : s.supply = 0
  · simp only [hsup, ↓reduceIte] at h
    simp at h
  · simp only [hsup, ↓reduceIte] at h
    by_cases hassets : s.assets = 0
    · simp only [hassets, ↓reduceIte] at h
      simp at h
    · simp only [hassets, ↓reduceIte] at h
      by_cases hcond : ((x * s.supply + s.assets - 1) / s.assets ≤ s.balance who ∧ (x * s.supply + s.assets - 1) / s.assets ≤ s.supply ∧ x ≤ s.assets)
      · simp only [hcond] at h
        cases h
        exact ⟨(x * s.supply + s.assets - 1) / s.assets, hcond.1, hcond.2.1, hcond.2.2, rfl, rfl, by simp, fun b hb => by simp [hb]⟩
      · simp only [hcond] at h
        simp at h

theorem req_deposit_rounds_down : DepositRoundsDown vault := by
  intro s s' who x t hv hm
  unfold vault at hv
  by_cases h0 : s.supply = 0
  · simp only [h0, ↓reduceIte] at hv
    cases hv
    obtain ⟨hass', hsup', _, _⟩ := hm
    simp at hsup'
    constructor
    · intro _; omega
    · intro hpos; omega
  · simp only [h0, ↓reduceIte] at hv
    by_cases hA : s.assets = 0
    · simp only [hA, ↓reduceIte] at hv
      cases hv
    · simp only [hA, ↓reduceIte] at hv
      cases hv
      obtain ⟨hass', hsup', _, _⟩ := hm
      simp at hsup'
      have hApos : 0 < s.assets := Nat.pos_of_ne_zero hA
      have ht : t = x * s.supply / s.assets := by omega
      subst ht
      have hN1 : x * s.supply / s.assets * s.assets ≤ x * s.supply := Nat.div_mul_le_self _ _
      have hN2 : x * s.supply < (x * s.supply / s.assets + 1) * s.assets := tmp_dep_aux2b _ _ hApos
      constructor
      · intro h00; omega
      · intro hpos
        exact ⟨hN1, hN2⟩

theorem req_redeem_rounds_down  : RedeemRoundsDown vault := by
  intro s s' who t y hv hb
  unfold vault at hv
  simp only at hv
  by_cases hcond : (t ≤ s.balance who ∧ t ≤ s.supply ∧ (if s.supply = 0 then 0 else t * s.assets / s.supply) ≤ s.assets)
  · simp only [hcond] at hv
    cases hv
    obtain ⟨ht_bal, ht_sup, hy_assets, hass', hsup', hbal', hoth⟩ := hb
    simp only at hass'
    have hy0_le : (if s.supply = 0 then 0 else t * s.assets / s.supply) ≤ s.assets := hcond.2.2
    have hy_eq : (if s.supply = 0 then 0 else t * s.assets / s.supply) = y := by omega
    constructor
    · intro h0
      simp [h0] at hy_eq
      omega
    · intro hpos
      have hne : s.supply ≠ 0 := by omega
      simp [hne] at hy_eq
      have hdiv : y = t * s.assets / s.supply := by omega
      have h1 : y * s.supply ≤ t * s.assets := by
        rw [hdiv]
        exact Nat.div_mul_le_self _ _
      have h2 : t * s.assets < (y + 1) * s.supply := by
        rw [hdiv]
        exact tmp_dep_aux2b _ _ hpos
      exact ⟨h1, h2⟩
  · simp only [hcond] at hv
    cases hv

theorem req_withdraw_rounds_up  : WithdrawRoundsUp vault := by
  intro s s' who x t hv hb
  unfold vault at hv
  simp only at hv
  by_cases hsup : s.supply = 0
  · simp only [hsup, ↓reduceIte] at hv
    simp at hv
  · simp only [hsup, ↓reduceIte] at hv
    by_cases hassets : s.assets = 0
    · simp only [hassets, ↓reduceIte] at hv
      simp at hv
    · simp only [hassets, ↓reduceIte] at hv
      by_cases hcond : ((x * s.supply + s.assets - 1) / s.assets ≤ s.balance who ∧ (x * s.supply + s.assets - 1) / s.assets ≤ s.supply ∧ x ≤ s.assets)
      · simp only [hcond] at hv
        cases hv
        obtain ⟨ht_bal, ht_sup, hx_assets, hass', hsup', hbal', hoth⟩ := hb
        simp only at hass' hsup' hbal'
        have hSpos : 0 < s.supply := Nat.pos_of_ne_zero hsup
        have hDpos : 0 < s.assets := Nat.pos_of_ne_zero hassets
        have hceil_le : (x * s.supply + s.assets - 1) / s.assets ≤ s.supply := hcond.2.1
        have ht_eq : t = (x * s.supply + s.assets - 1) / s.assets := by omega
        subst ht_eq
        refine ⟨hSpos, ceil_le_mulW _ _ hDpos, ceil_mul_ltW _ _ hDpos⟩
      · simp only [hcond] at hv
        simp at hv

theorem req_share_value : ShareValueNeverFalls vault := by
  intro history ops h
  exact run_vnb_chain2 _ _ h

end ShareVault
