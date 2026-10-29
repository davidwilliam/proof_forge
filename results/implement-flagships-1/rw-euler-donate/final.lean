import EulerLending.Spec

namespace EulerLending

def step : Impl
  | s, .deposit u x =>
    if decide ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩) then
      some ⟨fun w => if w == u then ⟨(s.acct u).e + x, (s.acct u).d⟩ else s.acct w, s.cash + x, s.reserves⟩
    else none
  | s, .withdraw u x =>
    if decide (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) then
      some ⟨fun w => if w == u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct w, s.cash - x, s.reserves⟩
    else none
  | s, .borrow u x =>
    if decide (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩) then
      some ⟨fun w => if w == u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct w, s.cash - x, s.reserves⟩
    else none
  | s, .repay u x =>
    some ⟨fun w => if w == u then ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ else s.acct w, s.cash + min x (s.acct u).d, s.reserves⟩
  | s, .mint u x =>
    if decide (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩) then
      some ⟨fun w => if w == u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct w, s.cash, s.reserves⟩
    else none
  | s, .burn u x =>
    if decide (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩) then
      some ⟨fun w => if w == u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct w, s.cash, s.reserves⟩
    else none
  | s, .transfer u v x =>
    if decide (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩)) then
      some ⟨fun w => if w == u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else if w == v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else s.acct w, s.cash, s.reserves⟩
    else none
  | s, .donate u x =>
    if decide (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) then
      some ⟨fun w => if w == u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct w, s.cash, s.reserves + x⟩
    else none
  | s, .liquidate l v r =>
    if decide (l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩) then
      some ⟨fun w => if w == v then ⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩ else if w == l then ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ else s.acct w, s.cash, s.reserves + liqFee r⟩
    else none

theorem helper_test_allowed : True := trivial

theorem aux_allowed_withdraw (s : St) (u x : Nat)
    (h : x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) :
    (step s (.withdraw u x)).isSome := by
  unfold step
  simp [h]

theorem probe_dep_full3 (s : St) (u x : Nat) (s' : St)
    (h : step s (.deposit u x) = some s') :
    EffectOn s (.deposit u x) s' := by
  unfold step at h
  by_cases hc : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩)
  · simp only [hc, decide_true] at h
    cases h
    simp only [EffectOn]
    refine ⟨?_, ?_, trivial, trivial⟩
    · simp
    · intro w hw
      simp [hw]
  · simp only [hc, decide_false] at h
    simp at h

def fooTest : Nat := 1

def fooTest3 : Nat := 2

theorem fooTestThm : True := trivial

theorem beqSelfTest (u : Nat) : (u == u) = true := by simp

theorem beqNeTest (l v : Nat) (h : l ≠ v) : (l == v) = false := by simp [h]

theorem beqEqTest (w u : Nat) (h : w = u) : (w == u) = true := by simp [h]

theorem req_actor_healthyAuxWithdraw : True := trivial

theorem healthy_zero_test (e : Nat) : Healthy ⟨e, 0⟩ := by unfold Healthy; simp

theorem healthy_mono_debt_test (e d k : Nat) (h : Healthy ⟨e, d⟩) : Healthy ⟨e, d - k⟩ := by
  unfold Healthy at h ⊢
  simp at h ⊢
  -- need (d - k)*20/19 ≤ e from d*20/19 ≤ e
  have hle : (d - k) * 20 ≤ d * 20 := by
    have h1 : d - k ≤ d := Nat.sub_le d k
    exact Nat.mul_le_mul_right 20 h1
  exact Nat.le_trans (Nat.div_le_div_right hle) h

theorem healthy_add_coll_test2 (e d x : Nat) (h : Healthy ⟨e, d⟩) : Healthy ⟨e + x, d⟩ := by
  unfold Healthy at h ⊢
  simp at h ⊢
  exact Nat.le_trans h (Nat.le_add_right e x)

theorem healthy_zero_test2 (e : Nat) : Healthy ⟨e, 0⟩ := by unfold Healthy; simp

theorem staysAuxA (s : St) (u x w : Nat) (h : w = u) :
    ((fun w => if w == u then (⟨(s.acct u).e + x, (s.acct u).d⟩ : Acct) else s.acct w) w) = ⟨(s.acct w).e + x, (s.acct w).d⟩ := by
  simp [h]

theorem staysDepositAux (s : St) (u x w : Nat) (s' : St)
    (hstep : step s (.deposit u x) = some s')
    (hhealth : Healthy (s.acct w)) : Healthy (s'.acct w) := by
  unfold step at hstep
  by_cases hc : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩)
  · simp [hc] at hstep
    subst hstep
    by_cases hw : w = u
    · simp [hw]
      have h0 : Healthy (s.acct u) := by
        rw [← hw]
        exact hhealth
      have h1 := healthy_add_coll_test2 (s.acct u).e (s.acct u).d x h0
      exact h1
    · simp [hw]
      exact hhealth
  · simp [hc] at hstep

theorem nbd_healthy_add (e d x : Nat) (h : Healthy ⟨e, d⟩) : Healthy ⟨e + x, d⟩ :=
  healthy_add_coll_test2 e d x h

theorem nbd_healthy_sub_debt (e d k : Nat) (h : Healthy ⟨e, d⟩) : Healthy ⟨e, d - k⟩ :=
  healthy_mono_debt_test e d k h

theorem nbd_healthy_zero (e : Nat) : Healthy ⟨e, 0⟩ := healthy_zero_test e

theorem nbd_beq_true (w u : Nat) (h : w = u) : (w == u) = true := by simp [h]

theorem nbd_beq_false (w u : Nat) (h : w ≠ u) : (w == u) = false := by simp [h]

theorem nbd_genesis_healthy (u : Nat) : Healthy (genesis.acct u) := by
  unfold genesis Healthy
  simp

theorem nbd_dep_ok2 (s s' : St) (u x w : Nat)
    (hall : ∀ u, Healthy (s.acct u))
    (hstep : step s (.deposit u x) = some s') : Healthy (s'.acct w) := by
  unfold step at hstep
  by_cases hc : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩)
  · simp [hc] at hstep
    subst hstep
    by_cases hw : w = u
    · simp [hw]
      rcases hc with hd0 | hH
      · have h2 : Healthy (⟨(s.acct u).e + x, (s.acct u).d⟩ : Acct) := by
          rw [hd0]; exact healthy_zero_test _
        simpa using h2
      · simpa using hH
    · simp [hw]
      exact hall w
  · simp [hc] at hstep

theorem req_effects_tmp2 : Effects step := by
  intro s op s' h
  cases op with
  | deposit u x =>
    unfold step at h
    by_cases hc : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      refine ⟨by simp, ?_, trivial, trivial⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | withdraw u x =>
    unfold step at h
    by_cases hc : (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      refine ⟨hc.1, hc.2.1, by simp, ?_, trivial, trivial⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | borrow u x =>
    unfold step at h
    by_cases hc : (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      refine ⟨hc.1, by simp, ?_, trivial, trivial⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | repay u x =>
    unfold step at h
    cases h
    simp only [EffectOn]
    refine ⟨by simp, ?_, trivial, trivial⟩
    intro w hw
    simp [hw]
  | mint u x =>
    unfold step at h
    by_cases hc : (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      refine ⟨by simp, ?_, trivial, trivial⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | burn u x =>
    unfold step at h
    by_cases hc : (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      refine ⟨hc.1, by simp, ?_, trivial, trivial⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | transfer u v x =>
    unfold step at h
    by_cases hc : (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩))
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      obtain ⟨hne, hle, _, _⟩ := hc
      refine ⟨hne, hle, by simp, by simp [Ne.symm hne], ?_, trivial, trivial⟩
      intro w hw1 hw2
      simp [hw1, hw2]
    · simp [hc] at h
  | donate u x =>
    unfold step at h
    by_cases hc : (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      refine ⟨hc.1, by simp, ?_, trivial, trivial⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | liquidate l v r =>
    unfold step at h
    by_cases hc : (l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      obtain ⟨hne, hnh, hle, _⟩ := hc
      refine ⟨hne, hnh, hle, by simp, by simp [hne], ?_, trivial, trivial⟩
      intro w hw1 hw2
      simp [hw1, hw2]
    · simp [hc] at h

theorem stays_healthy_aux1 (e d x : Nat) (h : Healthy ⟨e + x, d⟩) : Healthy ⟨e + x, d⟩ := h

theorem stays_rep_mono (e d k : Nat) (h : Healthy ⟨e, d⟩) : Healthy ⟨e, d - k⟩ :=
  healthy_mono_debt_test e d k h

theorem stays_coll_mono (e d x : Nat) (h : Healthy ⟨e, d⟩) : Healthy ⟨e + x, d⟩ :=
  healthy_add_coll_test2 e d x h

theorem stays_dep_probe2 (s : St) (u x w : Nat) (s' : St)
    (hstep : step s (.deposit u x) = some s')
    (hhealth : Healthy (s.acct w)) : Healthy (s'.acct w) := by
  unfold step at hstep
  by_cases hc : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩)
  · simp [hc] at hstep
    subst hstep
    by_cases hw : w = u
    · subst hw
      simp
      rcases hc with hd0 | hH
      · rw [hd0]; exact healthy_zero_test _
      · exact hH
    · simp [hw]
      exact hhealth
  · simp [hc] at hstep

theorem req_actor_healthy_auxA : True := trivial

theorem actor_probe_withdraw (s : St) (u x w : Nat) (s' : St)
    (hstep : step s (.withdraw u x) = some s')
    (hcheck : w = u) : Healthy (s'.acct w) := by
  unfold step at hstep
  by_cases hc : (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
  · simp [hc] at hstep
    subst hstep
    simp [hcheck]
    exact hc.2.2
  · simp [hc] at hstep

theorem actorLiqAux2 (s : St) (liq viol rr w : Nat) (s' : St)
    (hcheck : w = liq)
    (hstep : step s (.liquidate liq viol rr) = some s') : Healthy (s'.acct w) := by
  unfold step at hstep
  by_cases hc : (liq ≠ viol ∧ ¬ Healthy (s.acct viol) ∧ rr ≤ maxRepay (s.acct viol) ∧ Healthy ⟨(s.acct liq).e + liqYield (s.acct viol) rr, (s.acct liq).d + rr + liqFee rr⟩)
  · simp [hc] at hstep
    cases hstep
    rw [hcheck]
    simp [hc.1]
    exact hc.2.2.2
  · simp [hc] at hstep

theorem actorWithdrawAux (s : St) (u x w : Nat) (s' : St)
    (hcheck : w = u)
    (hstep : step s (.withdraw u x) = some s') : Healthy (s'.acct w) := by
  unfold step at hstep
  by_cases hc : (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
  · simp [hc] at hstep
    cases hstep
    rw [hcheck]
    simp
    exact hc.2.2
  · simp [hc] at hstep

theorem actorBorrowAux (s : St) (u x w : Nat) (s' : St)
    (hcheck : w = u)
    (hstep : step s (.borrow u x) = some s') : Healthy (s'.acct w) := by
  unfold step at hstep
  by_cases hc : (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩)
  · simp [hc] at hstep
    cases hstep
    rw [hcheck]
    simp
    exact hc.2
  · simp [hc] at hstep

theorem actorMintAux (s : St) (u x w : Nat) (s' : St)
    (hcheck : w = u)
    (hstep : step s (.mint u x) = some s') : Healthy (s'.acct w) := by
  unfold step at hstep
  by_cases hc : (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩)
  · simp [hc] at hstep
    cases hstep
    rw [hcheck]
    simp
    exact hc
  · simp [hc] at hstep

theorem actorBurnAux (s : St) (u x w : Nat) (s' : St)
    (hcheck : w = u)
    (hstep : step s (.burn u x) = some s') : Healthy (s'.acct w) := by
  unfold step at hstep
  by_cases hc : (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩)
  · simp [hc] at hstep
    cases hstep
    rw [hcheck]
    simp
    exact hc.2
  · simp [hc] at hstep

theorem actorTransferAux (s : St) (u v x w : Nat) (s' : St)
    (hcheck : w = u)
    (hstep : step s (.transfer u v x) = some s') : Healthy (s'.acct w) := by
  unfold step at hstep
  by_cases hc : (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩))
  · simp [hc] at hstep
    cases hstep
    rw [hcheck]
    simp
    exact hc.2.2.1
  · simp [hc] at hstep

theorem actorDonateAux (s : St) (u x w : Nat) (s' : St)
    (hcheck : w = u)
    (hstep : step s (.donate u x) = some s') : Healthy (s'.acct w) := by
  unfold step at hstep
  by_cases hc : (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
  · simp [hc] at hstep
    cases hstep
    rw [hcheck]
    simp
    exact hc.2
  · simp [hc] at hstep

theorem req_honest_flow : HonestFlow step := by rfl

theorem req_allowed_succeeds : AllowedSucceeds step := by
  intro s op h
  cases op with
  | deposit u x => simp only [Allowed] at h; unfold step; simp [h]
  | withdraw u x => simp only [Allowed] at h; unfold step; simp [h]
  | borrow u x => simp only [Allowed] at h; unfold step; simp [h]
  | repay u x => unfold step; simp
  | mint u x => simp only [Allowed] at h; unfold step; simp [h]
  | burn u x => simp only [Allowed] at h; unfold step; simp [h]
  | transfer u v x => simp only [Allowed] at h; unfold step; simp [h]
  | donate u x => simp only [Allowed] at h; unfold step; simp [h]
  | liquidate l v r => simp only [Allowed] at h; unfold step; simp [h]

theorem req_effects : Effects step := by
  intro s op s' h
  cases op with
  | deposit u x =>
    unfold step at h
    by_cases hc : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      refine ⟨by simp, ?_, trivial, trivial⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | withdraw u x =>
    unfold step at h
    by_cases hc : (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      refine ⟨hc.1, hc.2.1, by simp, ?_, trivial, trivial⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | borrow u x =>
    unfold step at h
    by_cases hc : (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      refine ⟨hc.1, by simp, ?_, trivial, trivial⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | repay u x =>
    unfold step at h
    cases h
    simp only [EffectOn]
    refine ⟨by simp, ?_, trivial, trivial⟩
    intro w hw
    simp [hw]
  | mint u x =>
    unfold step at h
    by_cases hc : (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      refine ⟨by simp, ?_, trivial, trivial⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | burn u x =>
    unfold step at h
    by_cases hc : (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      refine ⟨hc.1, by simp, ?_, trivial, trivial⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | transfer u v x =>
    unfold step at h
    by_cases hc : (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩))
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      obtain ⟨hne, hle, _, _⟩ := hc
      refine ⟨hne, hle, by simp, by simp [Ne.symm hne], ?_, trivial, trivial⟩
      intro w hw1 hw2
      simp [hw1, hw2]
    · simp [hc] at h
  | donate u x =>
    unfold step at h
    by_cases hc : (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      refine ⟨hc.1, by simp, ?_, trivial, trivial⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | liquidate l v r =>
    unfold step at h
    by_cases hc : (l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩)
    · simp [hc] at h
      cases h
      simp only [EffectOn]
      obtain ⟨hne, hnh, hle, _⟩ := hc
      refine ⟨hne, hnh, hle, by simp, by simp [hne], ?_, trivial, trivial⟩
      intro w hw1 hw2
      simp [hw1, hw2]
    · simp [hc] at h

theorem req_actor_healthy : ActorHealthy step := by
  intro s op s' w hstep hcheck
  cases op with
  | deposit u x => simp only [Checked] at hcheck
  | withdraw u x => simp only [Checked] at hcheck; exact actorWithdrawAux s u x w s' hcheck hstep
  | borrow u x => simp only [Checked] at hcheck; exact actorBorrowAux s u x w s' hcheck hstep
  | repay u x => simp only [Checked] at hcheck
  | mint u x => simp only [Checked] at hcheck; exact actorMintAux s u x w s' hcheck hstep
  | burn u x => simp only [Checked] at hcheck; exact actorBurnAux s u x w s' hcheck hstep
  | transfer u v x => simp only [Checked] at hcheck; exact actorTransferAux s u v x w s' hcheck hstep
  | donate u x => simp only [Checked] at hcheck; exact actorDonateAux s u x w s' hcheck hstep
  | liquidate liq viol rr => simp only [Checked] at hcheck; exact actorLiqAux2 s liq viol rr w s' hcheck hstep

theorem req_stays_healthy : StaysHealthy step := by
  intro s op s' w hstep hhealth
  cases op with
  | deposit u x =>
    unfold step at hstep
    by_cases hc : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩)
    · simp [hc] at hstep
      subst hstep
      by_cases hw : w = u
      · subst hw
        simp
        rcases hc with hd0 | hH
        · rw [hd0]; exact healthy_zero_test _
        · exact hH
      · simp [hw]
        exact hhealth
    · simp [hc] at hstep
  | withdraw u x =>
    unfold step at hstep
    by_cases hc : (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · simp [hc] at hstep
      subst hstep
      by_cases hw : w = u
      · subst hw
        simp
        exact hc.2.2
      · simp [hw]
        exact hhealth
    · simp [hc] at hstep
  | borrow u x =>
    unfold step at hstep
    by_cases hc : (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩)
    · simp [hc] at hstep
      subst hstep
      by_cases hw : w = u
      · subst hw
        simp
        exact hc.2
      · simp [hw]
        exact hhealth
    · simp [hc] at hstep
  | repay u x =>
    unfold step at hstep
    simp at hstep
    subst hstep
    by_cases hw : w = u
    · subst hw
      simp
      exact healthy_mono_debt_test _ _ _ hhealth
    · simp [hw]
      exact hhealth
  | mint u x =>
    unfold step at hstep
    by_cases hc : (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩)
    · simp [hc] at hstep
      subst hstep
      by_cases hw : w = u
      · subst hw
        simp
        exact hc
      · simp [hw]
        exact hhealth
    · simp [hc] at hstep
  | burn u x =>
    unfold step at hstep
    by_cases hc : (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩)
    · simp [hc] at hstep
      subst hstep
      by_cases hw : w = u
      · subst hw
        simp
        exact hc.2
      · simp [hw]
        exact hhealth
    · simp [hc] at hstep
  | transfer u v x =>
    unfold step at hstep
    by_cases hc : (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩))
    · simp [hc] at hstep
      subst hstep
      by_cases hw : w = u
      · subst hw
        simp
        exact hc.2.2.1
      · by_cases hw2 : w = v
        · subst hw2
          simp [hw]
          exact healthy_add_coll_test2 _ _ _ hhealth
        · simp [hw, hw2]
          exact hhealth
    · simp [hc] at hstep
  | donate u x =>
    unfold step at hstep
    by_cases hc : (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · simp [hc] at hstep
      subst hstep
      by_cases hw : w = u
      · subst hw
        simp
        exact hc.2
      · simp [hw]
        exact hhealth
    · simp [hc] at hstep
  | liquidate liq viol rr =>
    unfold step at hstep
    by_cases hc : (liq ≠ viol ∧ ¬ Healthy (s.acct viol) ∧ rr ≤ maxRepay (s.acct viol) ∧ Healthy ⟨(s.acct liq).e + liqYield (s.acct viol) rr, (s.acct liq).d + rr + liqFee rr⟩)
    · simp [hc] at hstep
      subst hstep
      by_cases hw : w = viol
      · subst hw
        exfalso
        exact hc.2.1 hhealth
      · by_cases hw2 : w = liq
        · subst hw2
          simp [hw]
          exact hc.2.2.2
        · simp [hw, hw2]
          exact hhealth
    · simp [hc] at hstep

theorem req_no_bad_debt : NoBadDebt step := by
  intro s hs u
  induction hs with
  | genesis =>
    show Healthy ((genesis.acct u))
    unfold genesis Healthy
    simp
  | step op hreach hstep ih =>
    exact req_stays_healthy _ op _ u hstep ih

end EulerLending
