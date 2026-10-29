import EulerLending.Spec
/-!
Port of the market logic of Euler Finance v1 (euler-xyz/euler-contracts, commit
b1ee3265853628d5a529081d7908c38404201b4e), single asset, exchange rate 1, no interest.

* `deposit`: `EToken.deposit` (lines 139 to 175); checks liquidity when the account has debt.
* `withdraw`: `EToken.withdraw` (lines 180 to 200); `e/insufficient-pool-size`, then
  `checkLiquidity(account)`.
* `borrow`, `repay`: `DToken.borrow` (lines 98 to 121) and `DToken.repay` (lines 126 to 148);
  repay pays at most the amount owed.
* `mint`, `burn`: `EToken.mint` (lines 206 to 229) and `EToken.burn` (lines 234 to 264).
* `transfer`: `EToken.transferFrom` (lines 323 to 354); checks the sender, and the receiver
  when it has debt.
* `donate`: `EToken.donateToReserves` (lines 359 to 386): `e/insufficient-balance`, then the
  balance moves to the reserves.
* `liquidate`: `Liquidation.liquidate`, `computeLiqOpp` and `executeLiquidation` (lines 55 to
  283), same asset as debt and collateral.
-/
namespace EulerLending

/-- Replace the position of account `u`. -/
def setAcct (s : St) (u : Nat) (a : Acct) : St :=
  { s with acct := fun w => if w = u then a else s.acct w }

def step : Impl := fun s op =>
  match op with
  | .deposit u x =>
    let a : Acct := ⟨(s.acct u).e + x, (s.acct u).d⟩
    if (s.acct u).d = 0 ∨ Healthy a then some { setAcct s u a with cash := s.cash + x } else none
  | .withdraw u x =>
    let a : Acct := ⟨(s.acct u).e - x, (s.acct u).d⟩
    if x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy a then
      some { setAcct s u a with cash := s.cash - x } else none
  | .borrow u x =>
    let a : Acct := ⟨(s.acct u).e, (s.acct u).d + x⟩
    if x ≤ s.cash ∧ Healthy a then some { setAcct s u a with cash := s.cash - x } else none
  | .repay u x =>
    let y := min x (s.acct u).d
    some { setAcct s u ⟨(s.acct u).e, (s.acct u).d - y⟩ with cash := s.cash + y }
  | .mint u x =>
    let a : Acct := ⟨(s.acct u).e + x, (s.acct u).d + x⟩
    if Healthy a then some (setAcct s u a) else none
  | .burn u x =>
    let y := min x (s.acct u).d
    let a : Acct := ⟨(s.acct u).e - y, (s.acct u).d - y⟩
    if y ≤ (s.acct u).e ∧ Healthy a then some (setAcct s u a) else none
  | .transfer u v x =>
    let a : Acct := ⟨(s.acct u).e - x, (s.acct u).d⟩
    let b : Acct := ⟨(s.acct v).e + x, (s.acct v).d⟩
    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ ((s.acct v).d = 0 ∨ Healthy b) then
      some (setAcct (setAcct s u a) v b) else none
  | .donate u x =>
    let a : Acct := ⟨(s.acct u).e - x, (s.acct u).d⟩
    if x ≤ (s.acct u).e ∧ Healthy a then
      some { setAcct s u a with reserves := s.reserves + x }
    else none
  | .liquidate l v r =>
    let y := liqYield (s.acct v) r
    let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
      some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
        reserves := s.reserves + liqFee r } else none

theorem req_honest_flow_aux : HonestFlow step := by unfold HonestFlow honestOutcome runAll step setAcct Healthy genesis; rfl

theorem mytest_thm : True := trivial

theorem mytest_thm2 : True := trivial

theorem actorWithdrawHelper2 : ∀ (s : St) (q x : Nat) (s' : St) (w : Nat), step s (.withdraw q x) = some s' → Checked (.withdraw q x) w → Healthy (s'.acct w) := by
  intro s q x s' w h hc
  simp only [Checked] at hc
  rw [hc]
  unfold step at h
  simp only at h
  by_cases hcond : (x ≤ (s.acct q).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct q).e - x, (s.acct q).d⟩)
  · rw [if_pos hcond] at h
    obtain rfl := Option.some_inj.mp h
    have hEq : (({ setAcct s q ⟨(s.acct q).e - x, (s.acct q).d⟩ with cash := s.cash - x } : St).acct q) = ⟨(s.acct q).e - x, (s.acct q).d⟩ := by
      unfold setAcct
      simp
    rw [hEq]
    exact hcond.2.2
  · rw [if_neg hcond] at h
    nomatch h

theorem stays_tmp1 : ∀ (s : St) (u v w : Nat) (a b : Acct), u ≠ v → w = u → ((setAcct (setAcct s u a) v b : St).acct w) = a := by
  intro s u v w a b h1 heq
  unfold setAcct
  simp [heq, h1]

theorem stays_tmp2 : ∀ (s : St) (u v w : Nat) (a b : Acct), w = v → ((setAcct (setAcct s u a) v b : St).acct w) = b := by
  intro s u v w a b heq
  unfold setAcct
  simp [heq]

theorem stays_tmp3 : ∀ (s : St) (u v w : Nat) (a b : Acct), w ≠ u → w ≠ v → ((setAcct (setAcct s u a) v b : St).acct w) = s.acct w := by
  intro s u v w a b h1 h2
  unfold setAcct
  simp [h1, h2]

theorem stays_rw_test : ∀ (s : St) (u w : Nat) (a : Acct), w = u → ((setAcct s u a : St).acct w) = a := by
  intro s u w a h
  subst h
  unfold setAcct
  simp

theorem stays_single_eq : ∀ (s : St) (u : Nat) (a : Acct), (setAcct s u a).acct u = a := by
  intro s u a
  unfold setAcct
  simp

theorem stays_single_ne : ∀ (s : St) (u w : Nat) (a : Acct), w ≠ u → (setAcct s u a).acct w = s.acct w := by
  intro s u w a h
  unfold setAcct
  simp [h]

theorem healthy_deposit_mono : ∀ (e d x : Nat), Healthy ⟨e, d⟩ → Healthy ⟨e + x, d⟩ := by
  intro e d x h
  unfold Healthy at h ⊢
  simp only at h ⊢
  exact Nat.le_trans h (Nat.le_add_right e x)

theorem healthy_repay_mono : ∀ (e d y : Nat), Healthy ⟨e, d⟩ → Healthy ⟨e, d - y⟩ := by
  intro e d y h
  unfold Healthy at h ⊢
  simp only at h ⊢
  apply Nat.le_trans _ h
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_right
  exact Nat.sub_le d y

theorem stays_dep_case : ∀ (s : St) (u x w : Nat), ∀ (s' : St), step s (.deposit u x) = some s' → Healthy (s.acct w) → Healthy (s'.acct w) := by
  intro s u x w s' h hw
  simp only [step] at h
  by_cases hc : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩)
  · rw [if_pos hc] at h
    obtain rfl := Option.some_inj.mp h
    by_cases heq : w = u
    · rw [heq] at hw ⊢
      rw [stays_single_eq]
      exact healthy_deposit_mono _ _ _ hw
    · have hEq : ((({ setAcct s u ⟨(s.acct u).e + x, (s.acct u).d⟩ with cash := s.cash + x } : St)).acct w) = s.acct w := by
        have h1 : ((({ setAcct s u ⟨(s.acct u).e + x, (s.acct u).d⟩ with cash := s.cash + x } : St)).acct w) = (setAcct s u ⟨(s.acct u).e + x, (s.acct u).d⟩).acct w := rfl
        rw [h1, stays_single_ne _ _ _ _ heq]
      rw [hEq]
      exact hw
  · rw [if_neg hc] at h
    nomatch h

theorem req_honest_flow : HonestFlow step := by unfold HonestFlow honestOutcome runAll step setAcct Healthy genesis; rfl

theorem req_allowed_succeeds : AllowedSucceeds step := by
  intro s op h
  cases op with
  | deposit u x =>
    unfold Allowed at h
    unfold step
    simp only
    rw [if_pos h]
    rfl
  | withdraw u x =>
    unfold Allowed at h
    unfold step
    simp only
    rw [if_pos h]
    rfl
  | borrow u x =>
    unfold Allowed at h
    unfold step
    simp only
    rw [if_pos h]
    rfl
  | repay u x =>
    unfold step
    simp only
    rfl
  | mint u x =>
    unfold Allowed at h
    unfold step
    simp only
    rw [if_pos h]
    rfl
  | burn u x =>
    unfold Allowed at h
    unfold step
    simp only
    rw [if_pos h]
    rfl
  | transfer u v x =>
    unfold Allowed at h
    unfold step
    simp only
    rw [if_pos h]
    rfl
  | donate u x =>
    unfold Allowed at h
    unfold step
    simp only
    rw [if_pos h]
    rfl
  | liquidate l v r =>
    unfold Allowed at h
    unfold step
    simp only
    rw [if_pos h]
    rfl

theorem req_effects : Effects step := by
  intro s op s' h
  cases op with
  | deposit u x =>
    simp only [step] at h
    by_cases hc : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩)
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      unfold EffectOn
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold setAcct; simp
      · intro w hw; unfold setAcct; simp [hw]
      · rfl
      · rfl
    · rw [if_neg hc] at h
      nomatch h
  | withdraw u x =>
    simp only [step] at h
    by_cases hc : (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨h1, h2, h3⟩ := hc
      unfold EffectOn
      refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
      · unfold setAcct; simp
      · intro w hw; unfold setAcct; simp [hw]
      · rfl
      · rfl
    · rw [if_neg hc] at h
      nomatch h
  | borrow u x =>
    simp only [step] at h
    by_cases hc : (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩)
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨h1, h2⟩ := hc
      unfold EffectOn
      refine ⟨h1, ?_, ?_, ?_, ?_⟩
      · unfold setAcct; simp
      · intro w hw; unfold setAcct; simp [hw]
      · rfl
      · rfl
    · rw [if_neg hc] at h
      nomatch h
  | repay u x =>
    simp only [step] at h
    obtain rfl := Option.some_inj.mp h
    unfold EffectOn
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold setAcct; simp
    · intro w hw; unfold setAcct; simp [hw]
    · rfl
    · rfl
  | mint u x =>
    simp only [step] at h
    by_cases hc : Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      unfold EffectOn
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold setAcct; simp
      · intro w hw; unfold setAcct; simp [hw]
      · rfl
      · rfl
    · rw [if_neg hc] at h
      nomatch h
  | burn u x =>
    simp only [step] at h
    by_cases hc : (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩)
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨h1, h2⟩ := hc
      unfold EffectOn
      refine ⟨h1, ?_, ?_, ?_, ?_⟩
      · unfold setAcct; simp
      · intro w hw; unfold setAcct; simp [hw]
      · rfl
      · rfl
    · rw [if_neg hc] at h
      nomatch h
  | transfer u v x =>
    simp only [step] at h
    by_cases hc : (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩))
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨h1, h2, h3, h4⟩ := hc
      unfold EffectOn
      refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_⟩
      · unfold setAcct; simp [h1]
      · unfold setAcct; simp
      · intro w hw1 hw2; unfold setAcct; simp [hw1, hw2]
      · rfl
      · rfl
    · rw [if_neg hc] at h
      nomatch h
  | donate u x =>
    simp only [step] at h
    by_cases hc : (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨h1, h2⟩ := hc
      unfold EffectOn
      refine ⟨h1, ?_, ?_, ?_, ?_⟩
      · unfold setAcct; simp
      · intro w hw; unfold setAcct; simp [hw]
      · rfl
      · rfl
    · rw [if_neg hc] at h
      nomatch h
  | liquidate l v r =>
    simp only [step] at h
    by_cases hc : (l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩)
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨h1, h2, h3, h4⟩ := hc
      unfold EffectOn
      refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_, ?_⟩
      · unfold setAcct; simp [Ne.symm h1]
      · unfold setAcct; simp
      · intro w hw1 hw2; unfold setAcct; simp [hw1, hw2]
      · rfl
      · rfl
    · rw [if_neg hc] at h
      nomatch h

theorem req_actor_healthy : ActorHealthy step := by
  intro s op s' w h hc
  cases op with
  | deposit u x =>
    simp only [Checked] at hc
  | withdraw q x =>
    simp only [Checked] at hc
    rw [hc]
    simp only [step] at h
    by_cases hcond : (x ≤ (s.acct q).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct q).e - x, (s.acct q).d⟩)
    · rw [if_pos hcond] at h
      obtain rfl := Option.some_inj.mp h
      have hEq : ((({ setAcct s q ⟨(s.acct q).e - x, (s.acct q).d⟩ with cash := s.cash - x } : St)).acct q) = (⟨(s.acct q).e - x, (s.acct q).d⟩ : Acct) := stays_single_eq _ _ _
      rw [hEq]
      exact hcond.2.2
    · rw [if_neg hcond] at h
      nomatch h
  | borrow q x =>
    simp only [Checked] at hc
    rw [hc]
    simp only [step] at h
    by_cases hcond : (x ≤ s.cash ∧ Healthy ⟨(s.acct q).e, (s.acct q).d + x⟩)
    · rw [if_pos hcond] at h
      obtain rfl := Option.some_inj.mp h
      have hEq : ((({ setAcct s q ⟨(s.acct q).e, (s.acct q).d + x⟩ with cash := s.cash - x } : St)).acct q) = (⟨(s.acct q).e, (s.acct q).d + x⟩ : Acct) := stays_single_eq _ _ _
      rw [hEq]
      exact hcond.2
    · rw [if_neg hcond] at h
      nomatch h
  | repay u x =>
    simp only [Checked] at hc
  | mint q x =>
    simp only [Checked] at hc
    rw [hc]
    simp only [step] at h
    by_cases hcond : Healthy ⟨(s.acct q).e + x, (s.acct q).d + x⟩
    · rw [if_pos hcond] at h
      obtain rfl := Option.some_inj.mp h
      rw [stays_single_eq]
      exact hcond
    · rw [if_neg hcond] at h
      nomatch h
  | burn q x =>
    simp only [Checked] at hc
    rw [hc]
    simp only [step] at h
    by_cases hcond : (min x (s.acct q).d ≤ (s.acct q).e ∧ Healthy ⟨(s.acct q).e - min x (s.acct q).d, (s.acct q).d - min x (s.acct q).d⟩)
    · rw [if_pos hcond] at h
      obtain rfl := Option.some_inj.mp h
      rw [stays_single_eq]
      exact hcond.2
    · rw [if_neg hcond] at h
      nomatch h
  | transfer q v x =>
    simp only [Checked] at hc
    rw [hc]
    simp only [step] at h
    by_cases hcond : (q ≠ v ∧ x ≤ (s.acct q).e ∧ Healthy ⟨(s.acct q).e - x, (s.acct q).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩))
    · rw [if_pos hcond] at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨h1, h2, h3, h4⟩ := hcond
      rw [stays_tmp1 _ _ _ _ _ _ h1 rfl]
      exact h3
    · rw [if_neg hcond] at h
      nomatch h
  | donate q x =>
    simp only [Checked] at hc
    rw [hc]
    simp only [step] at h
    by_cases hcond : (x ≤ (s.acct q).e ∧ Healthy ⟨(s.acct q).e - x, (s.acct q).d⟩)
    · rw [if_pos hcond] at h
      obtain rfl := Option.some_inj.mp h
      have hEq : ((({ setAcct s q ⟨(s.acct q).e - x, (s.acct q).d⟩ with reserves := s.reserves + x } : St)).acct q) = (⟨(s.acct q).e - x, (s.acct q).d⟩ : Acct) := stays_single_eq _ _ _
      rw [hEq]
      exact hcond.2
    · rw [if_neg hcond] at h
      nomatch h
  | liquidate l v r =>
    simp only [Checked] at hc
    rw [hc]
    simp only [step] at h
    by_cases hcond : (l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩)
    · rw [if_pos hcond] at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨h1, h2, h3, h4⟩ := hcond
      have hEq : ((({ setAcct (setAcct s v ⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩) l ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ with reserves := s.reserves + liqFee r } : St)).acct l) = (⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ : Acct) := by
        have h0 : ((({ setAcct (setAcct s v ⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩) l ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ with reserves := s.reserves + liqFee r } : St)).acct l) = ((setAcct (setAcct s v ⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩) l ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ : St).acct l) := rfl
        rw [h0]
        exact stays_tmp2 s v l l (⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩ : Acct) (⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ : Acct) rfl
      rw [hEq]
      exact h4
    · rw [if_neg hcond] at h
      nomatch h

theorem req_stays_healthy : StaysHealthy step := by
  intro s op s' w h hw
  cases op with
  | deposit u x =>
    simp only [step] at h
    by_cases hc : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩)
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      by_cases heq : w = u
      · rw [heq] at hw ⊢
        have hEq : ((({ setAcct s u ⟨(s.acct u).e + x, (s.acct u).d⟩ with cash := s.cash + x } : St)).acct u) = (⟨(s.acct u).e + x, (s.acct u).d⟩ : Acct) := stays_single_eq _ _ _
        rw [hEq]
        exact healthy_deposit_mono _ _ _ hw
      · have hEq : ((({ setAcct s u ⟨(s.acct u).e + x, (s.acct u).d⟩ with cash := s.cash + x } : St)).acct w) = s.acct w := by
          have h1 : ((({ setAcct s u ⟨(s.acct u).e + x, (s.acct u).d⟩ with cash := s.cash + x } : St)).acct w) = (setAcct s u ⟨(s.acct u).e + x, (s.acct u).d⟩).acct w := rfl
          rw [h1, stays_single_ne _ _ _ _ heq]
        rw [hEq]
        exact hw
    · rw [if_neg hc] at h
      nomatch h
  | withdraw u x =>
    simp only [step] at h
    by_cases hc : (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      by_cases heq : w = u
      · rw [heq] at hw ⊢
        have hEq : ((({ setAcct s u ⟨(s.acct u).e - x, (s.acct u).d⟩ with cash := s.cash - x } : St)).acct u) = (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) := stays_single_eq _ _ _
        rw [hEq]
        exact hc.2.2
      · have hEq : ((({ setAcct s u ⟨(s.acct u).e - x, (s.acct u).d⟩ with cash := s.cash - x } : St)).acct w) = s.acct w := by
          have h1 : ((({ setAcct s u ⟨(s.acct u).e - x, (s.acct u).d⟩ with cash := s.cash - x } : St)).acct w) = (setAcct s u ⟨(s.acct u).e - x, (s.acct u).d⟩).acct w := rfl
          rw [h1, stays_single_ne _ _ _ _ heq]
        rw [hEq]
        exact hw
    · rw [if_neg hc] at h
      nomatch h
  | borrow u x =>
    simp only [step] at h
    by_cases hc : (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩)
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      by_cases heq : w = u
      · rw [heq] at hw ⊢
        have hEq : ((({ setAcct s u ⟨(s.acct u).e, (s.acct u).d + x⟩ with cash := s.cash - x } : St)).acct u) = (⟨(s.acct u).e, (s.acct u).d + x⟩ : Acct) := stays_single_eq _ _ _
        rw [hEq]
        exact hc.2
      · have hEq : ((({ setAcct s u ⟨(s.acct u).e, (s.acct u).d + x⟩ with cash := s.cash - x } : St)).acct w) = s.acct w := by
          have h1 : ((({ setAcct s u ⟨(s.acct u).e, (s.acct u).d + x⟩ with cash := s.cash - x } : St)).acct w) = (setAcct s u ⟨(s.acct u).e, (s.acct u).d + x⟩).acct w := rfl
          rw [h1, stays_single_ne _ _ _ _ heq]
        rw [hEq]
        exact hw
    · rw [if_neg hc] at h
      nomatch h
  | repay u x =>
    simp only [step] at h
    obtain rfl := Option.some_inj.mp h
    by_cases heq : w = u
    · rw [heq] at hw ⊢
      have hEq : ((({ setAcct s u ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ with cash := s.cash + min x (s.acct u).d } : St)).acct u) = (⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ : Acct) := stays_single_eq _ _ _
      rw [hEq]
      exact healthy_repay_mono _ _ _ hw
    · have hEq : ((({ setAcct s u ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ with cash := s.cash + min x (s.acct u).d } : St)).acct w) = s.acct w := by
        have h1 : ((({ setAcct s u ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ with cash := s.cash + min x (s.acct u).d } : St)).acct w) = (setAcct s u ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩).acct w := rfl
        rw [h1, stays_single_ne _ _ _ _ heq]
      rw [hEq]
      exact hw
  | mint u x =>
    simp only [step] at h
    by_cases hc : Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      by_cases heq : w = u
      · rw [heq] at hw ⊢
        rw [stays_single_eq]
        exact hc
      · rw [stays_single_ne _ _ _ _ heq]
        exact hw
    · rw [if_neg hc] at h
      nomatch h
  | burn u x =>
    simp only [step] at h
    by_cases hc : (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩)
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      by_cases heq : w = u
      · rw [heq] at hw ⊢
        rw [stays_single_eq]
        exact hc.2
      · rw [stays_single_ne _ _ _ _ heq]
        exact hw
    · rw [if_neg hc] at h
      nomatch h
  | transfer u v x =>
    simp only [step] at h
    by_cases hc : (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩))
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨h1, h2, h3, h4⟩ := hc
      by_cases heq1 : w = u
      · rw [heq1]
        rw [stays_tmp1 _ _ _ _ _ _ h1 rfl]
        exact h3
      · by_cases heq2 : w = v
        · rw [heq2]
          rw [stays_tmp2 _ _ _ _ _ _ rfl]
          cases h4 with
          | inl hz =>
            unfold Healthy
            simp only
            omega
          | inr hh => exact hh
        · rw [stays_tmp3 _ _ _ _ _ _ heq1 heq2]
          exact hw
    · rw [if_neg hc] at h
      nomatch h
  | donate u x =>
    simp only [step] at h
    by_cases hc : (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      by_cases heq : w = u
      · rw [heq] at hw ⊢
        have hEq : ((({ setAcct s u ⟨(s.acct u).e - x, (s.acct u).d⟩ with reserves := s.reserves + x } : St)).acct u) = (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) := stays_single_eq _ _ _
        rw [hEq]
        exact hc.2
      · have hEq : ((({ setAcct s u ⟨(s.acct u).e - x, (s.acct u).d⟩ with reserves := s.reserves + x } : St)).acct w) = s.acct w := by
          have h1 : ((({ setAcct s u ⟨(s.acct u).e - x, (s.acct u).d⟩ with reserves := s.reserves + x } : St)).acct w) = (setAcct s u ⟨(s.acct u).e - x, (s.acct u).d⟩).acct w := rfl
          rw [h1, stays_single_ne _ _ _ _ heq]
        rw [hEq]
        exact hw
    · rw [if_neg hc] at h
      nomatch h
  | liquidate l v r =>
    simp only [step] at h
    by_cases hc : (l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩)
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨h1, h2, h3, h4⟩ := hc
      by_cases heq1 : w = l
      · rw [heq1]
        have hEq : ((({ setAcct (setAcct s v ⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩) l ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ with reserves := s.reserves + liqFee r } : St)).acct l) = (⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ : Acct) := by
          have h0 : ((({ setAcct (setAcct s v ⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩) l ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ with reserves := s.reserves + liqFee r } : St)).acct l) = ((setAcct (setAcct s v ⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩) l ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ : St).acct l) := rfl
          rw [h0]
          exact stays_tmp2 s v l l (⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩ : Acct) (⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ : Acct) rfl
        rw [hEq]
        exact h4
      · by_cases heq2 : w = v
        · exfalso
          rw [heq2] at hw
          exact h2 hw
        · have hEq : ((({ setAcct (setAcct s v ⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩) l ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ with reserves := s.reserves + liqFee r } : St)).acct w) = s.acct w := by
            have h0 : ((({ setAcct (setAcct s v ⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩) l ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ with reserves := s.reserves + liqFee r } : St)).acct w) = ((setAcct (setAcct s v ⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩) l ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ : St).acct w) := rfl
            rw [h0]
            exact stays_tmp3 s v l w (⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩ : Acct) (⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ : Acct) heq2 heq1
          rw [hEq]
          exact hw
    · rw [if_neg hc] at h
      nomatch h

theorem req_no_bad_debt : NoBadDebt step := by
  intro s hr u
  induction hr with
  | genesis =>
    unfold genesis Healthy
    simp
  | @step s s' op hreach heq ih =>
    exact req_stays_healthy s op s' u heq ih

end EulerLending
