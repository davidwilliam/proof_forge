import ShareVault.Spec
/-!
# The requirements are not vacuous (protected, proved)

A vault that refuses every call would never lower the value of a share. The success, effects
and rounding requirements rule that out: `honest_sequence` shows that every implementation
meeting them runs this honest sequence from the empty vault, with exactly these results:

1. actor 0 deposits 100 and receives 5,000 shares (50 per unit, the initial price);
2. actor 1 deposits 300 and receives 15,000 shares;
3. someone donates 40 (or interest accrues): one share is now worth 440 / 20,000;
4. actor 0 withdraws 110, its deposit plus a quarter of the donation, for its 5,000 shares;
5. actor 1 redeems its 15,000 shares and receives 330, its deposit plus three quarters of the
   donation. The vault is empty again.

No actor withdraws more than it deposited plus its share of the donation, and every honest
call succeeds.
-/

namespace ShareVault

section
variable {vault : Impl}

theorem exec_deposit (h1 : DepositSucceeds vault) (h4 : DepositEffects vault)
    (h7 : DepositRoundsDown vault) (s : Vault) (who x : Nat) (hp : s.supply = 0 ∨ 0 < s.assets) :
    ∃ t, Minted s who x t (exec vault s (.call (.deposit who x))) ∧
      (s.supply = 0 → t = initialSharesPerUnit * x) ∧
      (0 < s.supply → t * s.assets ≤ x * s.supply ∧ x * s.supply < (t + 1) * s.assets) := by
  obtain ⟨s', hs⟩ := Option.isSome_iff_exists.mp (h1 s who x hp)
  obtain ⟨t, hm⟩ := h4 s s' who x hs
  refine ⟨t, ?_, h7 s s' who x t hs hm⟩
  simp only [exec, hs, Option.getD_some]
  exact hm

theorem exec_redeem (h2 : RedeemSucceeds vault) (h5 : RedeemEffects vault)
    (h8 : RedeemRoundsDown vault) (s : Vault) (who t : Nat) (hb : t ≤ s.balance who)
    (hs : t ≤ s.supply) :
    ∃ y, Burned s who t y (exec vault s (.call (.redeem who t))) ∧
      (0 < s.supply → y * s.supply ≤ t * s.assets ∧ t * s.assets < (y + 1) * s.supply) := by
  obtain ⟨s', h⟩ := Option.isSome_iff_exists.mp (h2 s who t hb hs)
  obtain ⟨y, hm⟩ := h5 s s' who t h
  refine ⟨y, ?_, (h8 s s' who t y h hm).2⟩
  simp only [exec, h, Option.getD_some]
  exact hm

theorem exec_withdraw (h3 : WithdrawSucceeds vault) (h6 : WithdrawEffects vault)
    (h9 : WithdrawRoundsUp vault) (s : Vault) (who x : Nat) (hs : 0 < s.supply)
    (ha : 0 < s.assets) (hb : s.balance who ≤ s.supply)
    (hx : x * s.supply ≤ s.balance who * s.assets) :
    ∃ t, Burned s who t x (exec vault s (.call (.withdraw who x))) ∧
      x * s.supply ≤ t * s.assets ∧ t * s.assets < x * s.supply + s.assets := by
  obtain ⟨s', h⟩ := Option.isSome_iff_exists.mp (h3 s who x hs ha hb hx)
  obtain ⟨t, hm⟩ := h6 s s' who x h
  refine ⟨t, ?_, (h9 s s' who x t h hm).2⟩
  simp only [exec, h, Option.getD_some]
  exact hm

theorem honest_sequence
    (h1 : DepositSucceeds vault) (h2 : RedeemSucceeds vault) (h3 : WithdrawSucceeds vault)
    (h4 : DepositEffects vault) (h5 : RedeemEffects vault) (h6 : WithdrawEffects vault)
    (h7 : DepositRoundsDown vault) (h8 : RedeemRoundsDown vault) (h9 : WithdrawRoundsUp vault) :
    let s := run vault empty [.call (.deposit 0 100), .call (.deposit 1 300), .donate 40]
    let a := run vault s [.call (.withdraw 0 110)]
    let b := run vault a [.call (.redeem 1 15000)]
    s.balance 0 = 5000 ∧ s.balance 1 = 15000 ∧ s.supply = 20000 ∧ s.assets = 440 ∧
    a.balance 0 = 0 ∧ a.balance 1 = 15000 ∧ a.supply = 15000 ∧ a.assets = 330 ∧
    b.balance 1 = 0 ∧ b.supply = 0 ∧ b.assets = 0 := by
  intro s a b
  -- 1. actor 0 deposits 100 into the empty vault
  obtain ⟨t1, m1, r1, -⟩ := exec_deposit h1 h4 h7 empty 0 100 (Or.inl rfl)
  generalize hs1 : exec vault empty (.call (.deposit 0 100)) = s1 at m1
  obtain ⟨m1a, m1s, m1w, m1o⟩ := m1
  have e1 : t1 = 5000 := by have := r1 rfl; simp only [initialSharesPerUnit] at this; omega
  simp only [empty] at m1a m1s m1w
  have m1o1 : s1.balance 1 = 0 := m1o 1 (by decide)
  -- 2. actor 1 deposits 300
  obtain ⟨t2, m2, -, r2⟩ := exec_deposit h1 h4 h7 s1 1 300 (Or.inr (by omega))
  generalize hs2 : exec vault s1 (.call (.deposit 1 300)) = s2 at m2
  obtain ⟨m2a, m2s, m2w, m2o⟩ := m2
  have e2 := r2 (by omega)
  rw [m1a, m1s, e1] at e2
  have ht2 : t2 = 15000 := by omega
  have m2o0 : s2.balance 0 = s1.balance 0 := m2o 0 (by decide)
  -- 3. a donation of 40
  have hs3 : s = { s2 with assets := s2.assets + 40 } := by
    show run vault empty _ = _
    simp only [run]
    rw [hs1, hs2]
    rfl
  have s3a : s.assets = 440 := by rw [hs3]; simp only; omega
  have s3s : s.supply = 20000 := by rw [hs3]; simp only; omega
  have s30 : s.balance 0 = 5000 := by rw [hs3]; simp only; omega
  have s31 : s.balance 1 = 15000 := by rw [hs3]; simp only; omega
  -- 4. actor 0 withdraws 110
  obtain ⟨t4, ⟨-, -, -, w4a, w4s, w4w, w4o⟩, r4a, r4b⟩ :=
    exec_withdraw h3 h6 h9 s 0 110 (by omega) (by omega) (by omega) (by rw [s3s, s30, s3a]; omega)
  have ha : exec vault s (.call (.withdraw 0 110)) = a := rfl
  rw [ha] at w4a w4s w4w w4o
  rw [s3s, s3a] at r4a r4b
  have ht4 : t4 = 5000 := by omega
  have w4o1 : a.balance 1 = s.balance 1 := w4o 1 (by decide)
  -- 5. actor 1 redeems 15000
  obtain ⟨y5, ⟨-, -, -, b5a, b5s, b5w, -⟩, r5⟩ :=
    exec_redeem h2 h5 h8 a 1 15000 (by omega) (by omega)
  have hb : exec vault a (.call (.redeem 1 15000)) = b := rfl
  rw [hb] at b5a b5s b5w
  have e5 := r5 (by omega)
  have a1 : a.supply = 15000 := by omega
  have a2 : a.assets = 330 := by omega
  rw [a1, a2] at e5
  have hy5 : y5 = 330 := by omega
  omega

end

end ShareVault
