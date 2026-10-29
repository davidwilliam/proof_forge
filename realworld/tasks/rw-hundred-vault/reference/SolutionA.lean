import ShareVault.Spec
/-!
# Reference solution (build team; hidden from agents)

Shares are priced from the exact ratio `assets / supply`, never from a truncated exchange
rate: a deposit mints `x * supply / assets` rounded down, a redemption of `t` shares pays
`t * assets / supply` rounded down, and a withdrawal of `x` underlying burns
`x * supply / assets` rounded up.
-/

namespace ShareVault

/-- `s` after `who` paid in `x` and received `t` new shares. -/
def mintTo (s : Vault) (who : Actor) (x t : Nat) : Vault :=
  { assets := s.assets + x, supply := s.supply + t,
    balance := fun b => if b = who then s.balance b + t else s.balance b }

/-- `s` after `who` gave back `t` shares and received `y`. -/
def burnFrom (s : Vault) (who : Actor) (t y : Nat) : Vault :=
  { assets := s.assets - y, supply := s.supply - t,
    balance := fun b => if b = who then s.balance b - t else s.balance b }

/-- Shares burned for a withdrawal of `x`: `x * supply / assets` rounded up. -/
def sharesUp (s : Vault) (x : Nat) : Nat :=
  (x * s.supply + s.assets - 1) / s.assets

def vault : Impl := fun s c =>
  match c with
  | .deposit who x =>
    if s.supply = 0 then some (mintTo s who x (initialSharesPerUnit * x))
    else if s.assets = 0 then none
    else some (mintTo s who x (x * s.supply / s.assets))
  | .redeem who t =>
    if t ≤ s.balance who ∧ t ≤ s.supply then
      some (burnFrom s who t (t * s.assets / s.supply))
    else none
  | .withdraw who x =>
    if 0 < s.supply ∧ 0 < s.assets ∧ sharesUp s x ≤ s.balance who ∧ sharesUp s x ≤ s.supply ∧
        x ≤ s.assets then
      some (burnFrom s who (sharesUp s x) x)
    else none

/-! ## Arithmetic facts -/

theorem floor_spec (a b : Nat) (hb : 0 < b) : a / b * b ≤ a ∧ a < (a / b + 1) * b := by
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.mod_lt a hb
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (a / b) b]
  omega

theorem ceil_spec (a b : Nat) (hb : 0 < b) :
    a ≤ (a + b - 1) / b * b ∧ (a + b - 1) / b * b < a + b := by
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  rw [Nat.mul_comm ((a + b - 1) / b) b]
  omega

theorem mul_div_le_self {t a s : Nat} (h : t ≤ s) : t * a / s ≤ a := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp
  · exact Nat.div_le_of_le_mul (Nat.mul_le_mul_right a h)

theorem value_trans {a0 s0 a1 s1 a2 s2 : Nat} (h1 : a0 * s1 ≤ a1 * s0) (h2 : a1 * s2 ≤ a2 * s1)
    (hs : 0 < s1) : a0 * s2 ≤ a2 * s0 := by
  apply Nat.le_of_mul_le_mul_right _ hs
  calc a0 * s2 * s1 = (a0 * s1) * s2 := by rw [Nat.mul_right_comm]
    _ ≤ (a1 * s0) * s2 := Nat.mul_le_mul_right _ h1
    _ = (a1 * s2) * s0 := by rw [Nat.mul_right_comm]
    _ ≤ (a2 * s1) * s0 := Nat.mul_le_mul_right _ h2
    _ = a2 * s0 * s1 := by rw [Nat.mul_right_comm]

/-! ## Shape of each call -/

theorem deposit_some {s s' : Vault} {who x : Nat} (h : vault s (.deposit who x) = some s') :
    (s.supply = 0 ∧ s' = mintTo s who x (initialSharesPerUnit * x)) ∨
    (0 < s.supply ∧ 0 < s.assets ∧ s' = mintTo s who x (x * s.supply / s.assets)) := by
  simp only [vault] at h
  split at h
  · exact Or.inl ⟨by assumption, (Option.some.inj h).symm⟩
  · split at h
    · contradiction
    · exact Or.inr ⟨by omega, by omega, (Option.some.inj h).symm⟩

theorem redeem_some {s s' : Vault} {who t : Nat} (h : vault s (.redeem who t) = some s') :
    t ≤ s.balance who ∧ t ≤ s.supply ∧ s' = burnFrom s who t (t * s.assets / s.supply) := by
  simp only [vault] at h
  split at h
  · exact ⟨by omega, by omega, (Option.some.inj h).symm⟩
  · contradiction

theorem withdraw_some {s s' : Vault} {who x : Nat} (h : vault s (.withdraw who x) = some s') :
    0 < s.supply ∧ 0 < s.assets ∧ sharesUp s x ≤ s.balance who ∧ sharesUp s x ≤ s.supply ∧
      x ≤ s.assets ∧ s' = burnFrom s who (sharesUp s x) x := by
  simp only [vault] at h
  split at h
  · rename_i hc
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, (Option.some.inj h).symm⟩
  · contradiction

theorem mintTo_minted (s : Vault) (who x t : Nat) : Minted s who x t (mintTo s who x t) := by
  refine ⟨rfl, rfl, by simp [mintTo], fun b hb => by simp [mintTo, hb]⟩

theorem burnFrom_burned {s : Vault} {who t y : Nat} (h1 : t ≤ s.balance who) (h2 : t ≤ s.supply)
    (h3 : y ≤ s.assets) : Burned s who t y (burnFrom s who t y) :=
  ⟨h1, h2, h3, rfl, rfl, by simp [burnFrom], fun b hb => by simp [burnFrom, hb]⟩

/-! ## Requirements -/

theorem req_deposit_succeeds : DepositSucceeds vault := by
  intro s who x h
  simp only [vault]
  split
  · rfl
  · split
    · omega
    · rfl

theorem req_redeem_succeeds : RedeemSucceeds vault := by
  intro s who t h1 h2
  simp only [vault]
  split
  · rfl
  · rename_i hc; exact absurd ⟨h1, h2⟩ hc

theorem req_withdraw_succeeds : WithdrawSucceeds vault := by
  intro s who x hs ha hb hx
  have hc := ceil_spec (x * s.supply) s.assets ha
  have hup : sharesUp s x ≤ s.balance who := by
    unfold sharesUp
    apply Nat.le_of_lt_succ
    apply Nat.lt_of_mul_lt_mul_right (a := s.assets)
    rw [Nat.succ_mul]
    omega
  have hxa : x ≤ s.assets := by
    apply Nat.le_of_mul_le_mul_right _ hs
    calc x * s.supply ≤ s.balance who * s.assets := hx
      _ ≤ s.supply * s.assets := Nat.mul_le_mul_right _ hb
      _ = s.assets * s.supply := Nat.mul_comm _ _
  simp only [vault]
  split
  · rfl
  · rename_i hn; exact absurd ⟨hs, ha, hup, Nat.le_trans hup hb, hxa⟩ hn

theorem req_deposit_effects : DepositEffects vault := by
  intro s s' who x h
  rcases deposit_some h with ⟨_, rfl⟩ | ⟨_, _, rfl⟩
  · exact ⟨_, mintTo_minted s who x _⟩
  · exact ⟨_, mintTo_minted s who x _⟩

theorem req_redeem_effects : RedeemEffects vault := by
  intro s s' who t h
  obtain ⟨h1, h2, rfl⟩ := redeem_some h
  exact ⟨_, burnFrom_burned h1 h2 (mul_div_le_self h2)⟩

theorem req_withdraw_effects : WithdrawEffects vault := by
  intro s s' who x h
  obtain ⟨_, _, h1, h2, h3, rfl⟩ := withdraw_some h
  exact ⟨_, burnFrom_burned h1 h2 h3⟩

theorem req_deposit_rounds_down : DepositRoundsDown vault := by
  intro s s' who x t h hm
  have ht : t = s'.supply - s.supply := by have := hm.2.1; omega
  rcases deposit_some h with ⟨h0, rfl⟩ | ⟨hs, ha, rfl⟩
  · refine ⟨fun _ => ?_, fun h' => by omega⟩
    simp only [mintTo] at ht; omega
  · refine ⟨fun h' => by omega, fun _ => ?_⟩
    simp only [mintTo] at ht
    have hf := floor_spec (x * s.supply) s.assets ha
    rw [ht, Nat.add_sub_cancel_left]
    exact hf

theorem req_redeem_rounds_down : RedeemRoundsDown vault := by
  intro s s' who t y h hb
  obtain ⟨_, h2, rfl⟩ := redeem_some h
  have hy : y = t * s.assets / s.supply := by
    have := hb.2.2.2.1; simp only [burnFrom] at this
    have := mul_div_le_self (a := s.assets) h2
    have := hb.2.2.1
    omega
  subst hy
  refine ⟨fun h0 => by simp [h0], fun hs => floor_spec (t * s.assets) s.supply hs⟩

theorem req_withdraw_rounds_up : WithdrawRoundsUp vault := by
  intro s s' who x t h hb
  obtain ⟨hs, ha, _, h2, _, rfl⟩ := withdraw_some h
  have ht : t = sharesUp s x := by
    have := hb.2.2.2.2.1; simp only [burnFrom] at this
    have := hb.2.1
    omega
  subst ht
  exact ⟨hs, ceil_spec (x * s.supply) s.assets ha⟩

/-! ## Share value -/

theorem exec_value (s : Vault) (op : Op) (hs : 0 < s.supply) :
    ValueNotBelow s (exec vault s op) := by
  unfold ValueNotBelow
  cases op with
  | donate x =>
    simp only [exec]
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  | call c =>
    simp only [exec]
    cases h : vault s c with
    | none => simp
    | some s' =>
      simp only [Option.getD_some]
      cases c with
      | deposit who x =>
        rcases deposit_some h with ⟨h0, _⟩ | ⟨_, ha, rfl⟩
        · omega
        · have hf := (floor_spec (x * s.supply) s.assets ha).1
          simp only [mintTo]
          rw [Nat.mul_add, Nat.add_mul, Nat.mul_comm s.assets (x * s.supply / s.assets)]
          omega
      | redeem who t =>
        obtain ⟨_, h2, rfl⟩ := redeem_some h
        have hf := (floor_spec (t * s.assets) s.supply hs).1
        have hy := mul_div_le_self (a := s.assets) h2
        simp only [burnFrom]
        rw [Nat.mul_sub, Nat.sub_mul, Nat.mul_comm s.assets t, Nat.mul_comm s.assets s.supply]
        exact Nat.sub_le_sub_left hf _
      | withdraw who x =>
        obtain ⟨_, ha, _, h2, hx, rfl⟩ := withdraw_some h
        have hc := (ceil_spec (x * s.supply) s.assets ha).1
        simp only [burnFrom]
        rw [Nat.mul_sub, Nat.sub_mul, Nat.mul_comm s.assets (sharesUp s x),
          Nat.mul_comm s.assets s.supply]
        exact Nat.sub_le_sub_left hc _

theorem run_value : ∀ (ops : List Op) (s : Vault),
    (∀ v ∈ trace vault s ops, 0 < v.supply) → ValueNotBelow s (run vault s ops)
  | [], s, _ => Nat.le_refl _
  | op :: ops, s, h => by
    have h0 : 0 < s.supply := h s (by simp [trace])
    have h1 : ∀ v ∈ trace vault (exec vault s op) ops, 0 < v.supply :=
      fun v hv => h v (by simp [trace, hv])
    have hs1 : 0 < (exec vault s op).supply := by
      cases ops <;> exact h1 _ (by simp [trace])
    exact value_trans (exec_value s op h0) (run_value ops _ h1) hs1

theorem req_share_value : ShareValueNeverFalls vault := by
  intro history ops h
  exact run_value ops _ h

end ShareVault
