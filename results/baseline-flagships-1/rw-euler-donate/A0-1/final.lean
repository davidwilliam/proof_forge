import EulerLending.Spec
namespace EulerLending

def step : Impl := fun s op =>
  match op with
  | .deposit u x =>
    if (s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩ then
      some ⟨(fun w => if w = u then ⟨(s.acct u).e + x, (s.acct u).d⟩ else s.acct w), s.cash + x, s.reserves⟩
    else none
  | .withdraw u x =>
    if x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ then
      some ⟨(fun w => if w = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct w), s.cash - x, s.reserves⟩
    else none
  | .borrow u x =>
    if x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩ then
      some ⟨(fun w => if w = u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct w), s.cash - x, s.reserves⟩
    else none
  | .repay u x =>
    some ⟨(fun w => if w = u then ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ else s.acct w), s.cash + min x (s.acct u).d, s.reserves⟩
  | .mint u x =>
    if Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩ then
      some ⟨(fun w => if w = u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct w), s.cash, s.reserves⟩
    else none
  | .burn u x =>
    if min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ then
      some ⟨(fun w => if w = u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct w), s.cash, s.reserves⟩
    else none
  | .transfer u v x =>
    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩) then
      some ⟨(fun w => if w = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else if w = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else s.acct w), s.cash, s.reserves⟩
    else none
  | .donate u x =>
    if x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ then
      some ⟨(fun w => if w = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct w), s.cash, s.reserves + x⟩
    else none
  | .liquidate l v r =>
    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ then
      some ⟨(fun w => if w = v then ⟨(s.acct v).e - liqYield (s.acct v) r, (s.acct v).d - r⟩ else if w = l then ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩ else s.acct w), s.cash, s.reserves + liqFee r⟩
    else none

theorem req_honest_flow : HonestFlow step := rfl

theorem req_allowed_succeeds : AllowedSucceeds step := by
  intro s op h
  cases op with
  | deposit u x =>
    simp only [Allowed] at h
    unfold step
    simp [h]
  | withdraw u x =>
    simp only [Allowed] at h
    unfold step
    simp [h]
  | borrow u x =>
    simp only [Allowed] at h
    unfold step
    simp [h]
  | repay u x =>
    unfold step
    simp
  | mint u x =>
    simp only [Allowed] at h
    unfold step
    simp [h]
  | burn u x =>
    simp only [Allowed] at h
    unfold step
    simp [h]
  | transfer u v x =>
    simp only [Allowed] at h
    unfold step
    simp [h]
  | donate u x =>
    simp only [Allowed] at h
    unfold step
    simp [h]
  | liquidate l v r =>
    simp only [Allowed] at h
    unfold step
    simp [h]

theorem req_effects : Effects step := by
  intro s op s' h
  cases op with
  | deposit u x =>
    simp only [step] at h
    by_cases hc : (s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩
    · simp [hc] at h
      cases h
      show _ ∧ _ ∧ _ ∧ _
      refine ⟨by simp, ?_, rfl, rfl⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | withdraw u x =>
    simp only [step] at h
    by_cases hc : x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩
    · simp [hc] at h
      cases h
      show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
      refine ⟨hc.left, hc.right.left, by simp, ?_, rfl, rfl⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | borrow u x =>
    simp only [step] at h
    by_cases hc : x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩
    · simp [hc] at h
      cases h
      show _ ∧ _ ∧ _ ∧ _ ∧ _
      refine ⟨hc.left, by simp, ?_, rfl, rfl⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | repay u x =>
    simp only [step] at h
    cases h
    show _ ∧ _ ∧ _ ∧ _
    refine ⟨by simp, ?_, rfl, rfl⟩
    intro w hw
    simp [hw]
  | mint u x =>
    simp only [step] at h
    by_cases hc : Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩
    · simp [hc] at h
      cases h
      show _ ∧ _ ∧ _ ∧ _
      refine ⟨by simp, ?_, rfl, rfl⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | burn u x =>
    simp only [step] at h
    by_cases hc : min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩
    · simp [hc] at h
      cases h
      show _ ∧ _ ∧ _ ∧ _ ∧ _
      refine ⟨hc.left, by simp, ?_, rfl, rfl⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | transfer u v x =>
    simp only [step] at h
    by_cases hc : u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩)
    · simp [hc] at h
      cases h
      have hne : u ≠ v := hc.left
      show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
      refine ⟨hne, hc.right.left, by simp, by simp [Ne.symm hne], ?_, rfl, rfl⟩
      intro w hw1 hw2
      simp [hw1, hw2]
    · simp [hc] at h
  | donate u x =>
    simp only [step] at h
    by_cases hc : x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩
    · simp [hc] at h
      cases h
      show _ ∧ _ ∧ _ ∧ _ ∧ _
      refine ⟨hc.left, by simp, ?_, rfl, rfl⟩
      intro w hw
      simp [hw]
    · simp [hc] at h
  | liquidate l v r =>
    simp only [step] at h
    by_cases hc : l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩
    · simp [hc] at h
      cases h
      have hne : l ≠ v := hc.left
      show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
      refine ⟨hne, hc.right.left, hc.right.right.left, by simp, by simp [hne], ?_, rfl, rfl⟩
      intro w hw1 hw2
      simp [hw1, hw2]
    · simp [hc] at h

theorem req_actor_healthy : ActorHealthy step := by
  intro s op s' w h_step h_check
  cases op with
  | deposit u x =>
    simp only [Checked] at h_check
  | withdraw u x =>
    simp only [Checked] at h_check
    simp only [step] at h_step
    by_cases hc : x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩
    · simp [hc] at h_step
      cases h_step
      simpa [h_check] using hc.right.right
    · simp [hc] at h_step
  | borrow u x =>
    simp only [Checked] at h_check
    simp only [step] at h_step
    by_cases hc : x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩
    · simp [hc] at h_step
      cases h_step
      simpa [h_check] using hc.right
    · simp [hc] at h_step
  | repay u x =>
    simp only [Checked] at h_check
  | mint u x =>
    simp only [Checked] at h_check
    simp only [step] at h_step
    by_cases hc : Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩
    · simp [hc] at h_step
      cases h_step
      simpa [h_check] using hc
    · simp [hc] at h_step
  | burn u x =>
    simp only [Checked] at h_check
    simp only [step] at h_step
    by_cases hc : min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩
    · simp [hc] at h_step
      cases h_step
      simpa [h_check] using hc.right
    · simp [hc] at h_step
  | transfer u v x =>
    simp only [Checked] at h_check
    simp only [step] at h_step
    by_cases hc : u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩)
    · simp [hc] at h_step
      cases h_step
      simpa [h_check] using hc.right.right.left
    · simp [hc] at h_step
  | donate u x =>
    simp only [Checked] at h_check
    simp only [step] at h_step
    by_cases hc : x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩
    · simp [hc] at h_step
      cases h_step
      simpa [h_check] using hc.right
    · simp [hc] at h_step
  | liquidate l v r =>
    simp only [Checked] at h_check
    simp only [step] at h_step
    by_cases hc : l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy ⟨(s.acct l).e + liqYield (s.acct v) r, (s.acct l).d + r + liqFee r⟩
    · simp [hc] at h_step
      cases h_step
      have hne : l ≠ v := hc.left
      have hH := hc.right.right.right
      rw [h_check]
      simpa [hne] using hH
    · simp [hc] at h_step

theorem req_stays_healthy : StaysHealthy step := by
  intro s op s' w h_step h_healthy
  cases op with
  | deposit u x =>
    have heff : EffectOn s (Op.deposit u x) s' := req_effects s (Op.deposit u x) s' h_step
    unfold EffectOn at heff
    obtain ⟨h_acct, h_others, _, _⟩ := heff
    by_cases heq : w = u
    · rw [heq, h_acct] at ⊢
      rw [heq] at h_healthy
      exact Nat.le_trans h_healthy (Nat.le_add_right _ _)
    · have heqw : s'.acct w = s.acct w := h_others w heq
      rw [heqw]
      exact h_healthy
  | withdraw u x =>
    have heff : EffectOn s (Op.withdraw u x) s' := req_effects s (Op.withdraw u x) s' h_step
    unfold EffectOn at heff
    obtain ⟨_, _, _, h_others, _, _⟩ := heff
    by_cases heq : w = u
    · exact req_actor_healthy s (Op.withdraw u x) s' w h_step heq
    · have heqw : s'.acct w = s.acct w := h_others w heq
      rw [heqw]
      exact h_healthy
  | borrow u x =>
    have heff : EffectOn s (Op.borrow u x) s' := req_effects s (Op.borrow u x) s' h_step
    unfold EffectOn at heff
    obtain ⟨_, _, h_others, _, _⟩ := heff
    by_cases heq : w = u
    · exact req_actor_healthy s (Op.borrow u x) s' w h_step heq
    · have heqw : s'.acct w = s.acct w := h_others w heq
      rw [heqw]
      exact h_healthy
  | repay u x =>
    have heff : EffectOn s (Op.repay u x) s' := req_effects s (Op.repay u x) s' h_step
    unfold EffectOn at heff
    obtain ⟨h_acct, h_others, _, _⟩ := heff
    by_cases heq : w = u
    · rw [heq, h_acct] at ⊢
      rw [heq] at h_healthy
      have hle : (s.acct u).d - min x (s.acct u).d ≤ (s.acct u).d := Nat.sub_le _ _
      have hmul : ((s.acct u).d - min x (s.acct u).d) * 20 ≤ (s.acct u).d * 20 :=
        Nat.mul_le_mul hle (Nat.le_refl 20)
      have hdiv : ((s.acct u).d - min x (s.acct u).d) * 20 / 19 ≤ (s.acct u).d * 20 / 19 :=
        Nat.div_le_div_right hmul
      exact Nat.le_trans hdiv h_healthy
    · have heqw : s'.acct w = s.acct w := h_others w heq
      rw [heqw]
      exact h_healthy
  | mint u x =>
    by_cases heq : w = u
    · exact req_actor_healthy s (Op.mint u x) s' w h_step heq
    · have heff : EffectOn s (Op.mint u x) s' := req_effects s (Op.mint u x) s' h_step
      unfold EffectOn at heff
      obtain ⟨_, h_others, _, _⟩ := heff
      have heqw : s'.acct w = s.acct w := h_others w heq
      rw [heqw]
      exact h_healthy
  | burn u x =>
    by_cases heq : w = u
    · exact req_actor_healthy s (Op.burn u x) s' w h_step heq
    · have heff : EffectOn s (Op.burn u x) s' := req_effects s (Op.burn u x) s' h_step
      unfold EffectOn at heff
      obtain ⟨_, _, h_others, _, _⟩ := heff
      have heqw : s'.acct w = s.acct w := h_others w heq
      rw [heqw]
      exact h_healthy
  | transfer u v x =>
    have heff : EffectOn s (Op.transfer u v x) s' := req_effects s (Op.transfer u v x) s' h_step
    unfold EffectOn at heff
    obtain ⟨_, _, h_acct_u, h_acct_v, h_others, _, _⟩ := heff
    by_cases heq1 : w = u
    · exact req_actor_healthy s (Op.transfer u v x) s' w h_step heq1
    · by_cases heq2 : w = v
      · rw [heq2, h_acct_v] at ⊢
        have h1 : s.acct v = s.acct w := by rw [heq2]
        rw [← h1] at h_healthy
        exact Nat.le_trans h_healthy (Nat.le_add_right _ _)
      · have heqw : s'.acct w = s.acct w := h_others w heq1 heq2
        rw [heqw]
        exact h_healthy
  | donate u x =>
    by_cases heq : w = u
    · exact req_actor_healthy s (Op.donate u x) s' w h_step heq
    · have heff : EffectOn s (Op.donate u x) s' := req_effects s (Op.donate u x) s' h_step
      unfold EffectOn at heff
      obtain ⟨_, _, h_others, _, _⟩ := heff
      have heqw : s'.acct w = s.acct w := h_others w heq
      rw [heqw]
      exact h_healthy
  | liquidate l v r =>
    have heff : EffectOn s (Op.liquidate l v r) s' := req_effects s (Op.liquidate l v r) s' h_step
    unfold EffectOn at heff
    obtain ⟨_, hnh, _, _, _, h_others, _, _⟩ := heff
    by_cases heq1 : w = v
    · rw [heq1] at h_healthy
      exact False.elim (hnh h_healthy)
    · by_cases heq2 : w = l
      · exact req_actor_healthy s (Op.liquidate l v r) s' w h_step heq2
      · have heqw : s'.acct w = s.acct w := h_others w heq2 heq1
        rw [heqw]
        exact h_healthy

theorem req_no_bad_debt : NoBadDebt step := by
  intro s hr
  induction hr with
  | genesis =>
    intro u
    simp [genesis, Healthy]
  | step op _ h_eq ih =>
    intro u
    exact req_stays_healthy _ _ _ u h_eq (ih u)

end EulerLending
