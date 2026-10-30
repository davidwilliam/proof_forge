import EulerLending.Spec

namespace EulerLending

def step : Impl := fun s op =>
  match op with
  | .deposit u x =>
    if (s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩ then
      some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d⟩ else s.acct a, s.cash + x, s.reserves⟩
    else none
  | .withdraw u x =>
    if x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ then
      some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash - x, s.reserves⟩
    else none
  | .borrow u x =>
    if x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩ then
      some ⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct a, s.cash - x, s.reserves⟩
    else none
  | .repay u x =>
    some ⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a,
      s.cash + min x (s.acct u).d, s.reserves⟩
  | .mint u x =>
    if Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩ then
      some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct a, s.cash, s.reserves⟩
    else none
  | .burn u x =>
    if min x (s.acct u).d ≤ (s.acct u).e ∧
        Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ then
      some ⟨fun a => if a = u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a,
        s.cash, s.reserves⟩
    else none
  | .transfer u v x =>
    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧
        ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩) then
      some ⟨fun a => if a = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a,
        s.cash, s.reserves⟩
    else none
  | .donate u x =>
    if x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ then
      some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves + x⟩
    else none
  | .liquidate liq viol r =>
    if liq ≠ viol ∧ ¬ Healthy (s.acct viol) ∧ r ≤ maxRepay (s.acct viol) ∧
        Healthy ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ then
      some ⟨fun a => if a = liq then ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩
          else if a = viol then ⟨(s.acct viol).e - liqYield (s.acct viol) r, (s.acct viol).d - r⟩ else s.acct a,
        s.cash, s.reserves + liqFee r⟩
    else none

theorem req_honest_flow : HonestFlow step := by
  unfold HonestFlow honestOutcome honestSession runAll step
  rfl

theorem req_allowed_succeeds : AllowedSucceeds step := by
  unfold AllowedSucceeds
  intro s op h
  cases op with
  | deposit u x =>
    have hc : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩) := h
    have e0 : step s (.deposit u x) =
      (if ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d⟩ else s.acct a, s.cash + x, s.reserves⟩ else none) := rfl
    rw [e0, if_pos hc]
    rfl
  | withdraw u x =>
    have hc : (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) := h
    have e0 : step s (.withdraw u x) =
      (if (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash - x, s.reserves⟩ else none) := rfl
    rw [e0, if_pos hc]
    rfl
  | borrow u x =>
    have hc : (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩) := h
    have e0 : step s (.borrow u x) =
      (if (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct a, s.cash - x, s.reserves⟩ else none) := rfl
    rw [e0, if_pos hc]
    rfl
  | repay u x =>
    have e0 : step s (.repay u x) =
      some ⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a,
        s.cash + min x (s.acct u).d, s.reserves⟩ := rfl
    rw [e0]
    rfl
  | mint u x =>
    have hc : (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩) := h
    have e0 : step s (.mint u x) =
      (if (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct a, s.cash, s.reserves⟩ else none) := rfl
    rw [e0, if_pos hc]
    rfl
  | burn u x =>
    have hc : (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩) := h
    have e0 : step s (.burn u x) =
      (if (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ else none) := rfl
    rw [e0, if_pos hc]
    rfl
  | transfer u v x =>
    have hc : (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩)) := h
    have e0 : step s (.transfer u v x) =
      (if (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩)) then
        some ⟨fun a => if a = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ else none) := rfl
    rw [e0, if_pos hc]
    rfl
  | donate u x =>
    have hc : (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) := h
    have e0 : step s (.donate u x) =
      (if (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves + x⟩ else none) := rfl
    rw [e0, if_pos hc]
    rfl
  | liquidate liq viol r =>
    have hc : (liq ≠ viol ∧ ¬ Healthy (s.acct viol) ∧ r ≤ maxRepay (s.acct viol) ∧ Healthy ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩) := h
    have e0 : step s (.liquidate liq viol r) =
      (if (liq ≠ viol ∧ ¬ Healthy (s.acct viol) ∧ r ≤ maxRepay (s.acct viol) ∧ Healthy ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩) then
        some ⟨fun a => if a = liq then ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ else if a = viol then ⟨(s.acct viol).e - liqYield (s.acct viol) r, (s.acct viol).d - r⟩ else s.acct a, s.cash, s.reserves + liqFee r⟩ else none) := rfl
    rw [e0, if_pos hc]
    rfl

theorem req_effects : Effects step := by
  unfold Effects
  intro s op s' h
  cases op with
  | deposit u x =>
    have e0 : step s (.deposit u x) =
      (if ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d⟩ else s.acct a, s.cash + x, s.reserves⟩ else none) := rfl
    by_cases hc : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩)
    · have hstep : step s (.deposit u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d⟩ else s.acct a, s.cash + x, s.reserves⟩ := by rw [e0, if_pos hc]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      unfold EffectOn OthersSame
      refine ⟨?_, ?_, rfl, rfl⟩
      · simp
      · intro w hw
        simp [hw]
    · have hstep : step s (.deposit u x) = none := by rw [e0, if_neg hc]
      rw [hstep] at h
      cases h
  | withdraw u x =>
    have e0 : step s (.withdraw u x) =
      (if (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash - x, s.reserves⟩ else none) := rfl
    by_cases hc : (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · have hstep : step s (.withdraw u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash - x, s.reserves⟩ := by rw [e0, if_pos hc]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      unfold EffectOn OthersSame
      refine ⟨hc.1, hc.2.1, ?_, ?_, rfl, rfl⟩
      · simp
      · intro w hw
        simp [hw]
    · have hstep : step s (.withdraw u x) = none := by rw [e0, if_neg hc]
      rw [hstep] at h
      cases h
  | borrow u x =>
    have e0 : step s (.borrow u x) =
      (if (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct a, s.cash - x, s.reserves⟩ else none) := rfl
    by_cases hc : (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩)
    · have hstep : step s (.borrow u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct a, s.cash - x, s.reserves⟩ := by rw [e0, if_pos hc]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      unfold EffectOn OthersSame
      refine ⟨hc.1, ?_, ?_, rfl, rfl⟩
      · simp
      · intro w hw
        simp [hw]
    · have hstep : step s (.borrow u x) = none := by rw [e0, if_neg hc]
      rw [hstep] at h
      cases h
  | repay u x =>
    have hstep : step s (.repay u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash + min x (s.acct u).d, s.reserves⟩ := rfl
    have hEq := Option.some_inj.mp (hstep.symm.trans h)
    subst hEq
    unfold EffectOn OthersSame
    refine ⟨?_, ?_, rfl, rfl⟩
    · simp
    · intro w hw
      simp [hw]
  | mint u x =>
    have e0 : step s (.mint u x) =
      (if (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct a, s.cash, s.reserves⟩ else none) := rfl
    by_cases hc : (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩)
    · have hstep : step s (.mint u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct a, s.cash, s.reserves⟩ := by rw [e0, if_pos hc]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      unfold EffectOn OthersSame
      refine ⟨?_, ?_, rfl, rfl⟩
      · simp
      · intro w hw
        simp [hw]
    · have hstep : step s (.mint u x) = none := by rw [e0, if_neg hc]
      rw [hstep] at h
      cases h
  | burn u x =>
    have e0 : step s (.burn u x) =
      (if (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ else none) := rfl
    by_cases hc : (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩)
    · have hstep : step s (.burn u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ := by rw [e0, if_pos hc]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      unfold EffectOn OthersSame
      refine ⟨hc.1, ?_, ?_, rfl, rfl⟩
      · simp
      · intro w hw
        simp [hw]
    · have hstep : step s (.burn u x) = none := by rw [e0, if_neg hc]
      rw [hstep] at h
      cases h
  | transfer u v x =>
    have e0 : step s (.transfer u v x) =
      (if (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩)) then
        some ⟨fun a => if a = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ else none) := rfl
    by_cases hc : (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩))
    · have hstep : step s (.transfer u v x) = some ⟨fun a => if a = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ := by rw [e0, if_pos hc]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      unfold EffectOn OthersSame2
      have hne2 : u ≠ v := hc.1
      refine ⟨hc.1, hc.2.1, ?_, ?_, ?_, rfl, rfl⟩
      · simp [hne2]
      · simp
      · intro w hw1 hw2
        simp [hw1, hw2]
    · have hstep : step s (.transfer u v x) = none := by rw [e0, if_neg hc]
      rw [hstep] at h
      cases h
  | donate u x =>
    have e0 : step s (.donate u x) =
      (if (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves + x⟩ else none) := rfl
    by_cases hc : (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · have hstep : step s (.donate u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves + x⟩ := by rw [e0, if_pos hc]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      unfold EffectOn OthersSame
      refine ⟨hc.1, ?_, ?_, rfl, rfl⟩
      · simp
      · intro w hw
        simp [hw]
    · have hstep : step s (.donate u x) = none := by rw [e0, if_neg hc]
      rw [hstep] at h
      cases h
  | liquidate liq viol r =>
    have e0 : step s (.liquidate liq viol r) =
      (if (liq ≠ viol ∧ ¬ Healthy (s.acct viol) ∧ r ≤ maxRepay (s.acct viol) ∧ Healthy ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩) then
        some ⟨fun a => if a = liq then ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ else if a = viol then ⟨(s.acct viol).e - liqYield (s.acct viol) r, (s.acct viol).d - r⟩ else s.acct a, s.cash, s.reserves + liqFee r⟩ else none) := rfl
    by_cases hc : (liq ≠ viol ∧ ¬ Healthy (s.acct viol) ∧ r ≤ maxRepay (s.acct viol) ∧ Healthy ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩)
    · have hstep : step s (.liquidate liq viol r) = some ⟨fun a => if a = liq then ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ else if a = viol then ⟨(s.acct viol).e - liqYield (s.acct viol) r, (s.acct viol).d - r⟩ else s.acct a, s.cash, s.reserves + liqFee r⟩ := by rw [e0, if_pos hc]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      unfold EffectOn OthersSame2
      have hne2 : viol ≠ liq := fun hh => hc.1 hh.symm
      refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_, ?_, ?_, rfl, rfl⟩
      · simp [hne2]
      · simp
      · intro w hw1 hw2
        simp [hw1, hw2]
    · have hstep : step s (.liquidate liq viol r) = none := by rw [e0, if_neg hc]
      rw [hstep] at h
      cases h

theorem req_actor_healthy : ActorHealthy step := by
  unfold ActorHealthy
  intro s op s' w h hc
  cases op with
  | deposit u x =>
    unfold Checked at hc
    cases hc
  | withdraw u x =>
    have hcw : w = u := hc
    have e0 : step s (.withdraw u x) =
      (if (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash - x, s.reserves⟩ else none) := rfl
    by_cases hcond : (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · have hstep : step s (.withdraw u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash - x, s.reserves⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash - x, s.reserves⟩ : St).acct w) = (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) := by
        show (if w = u then (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) else s.acct w) = _
        rw [if_pos hcw]
      rw [hg]
      exact hcond.2.2
    · have hstep : step s (.withdraw u x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | borrow u x =>
    have hcw : w = u := hc
    have e0 : step s (.borrow u x) =
      (if (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct a, s.cash - x, s.reserves⟩ else none) := rfl
    by_cases hcond : (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩)
    · have hstep : step s (.borrow u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct a, s.cash - x, s.reserves⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct a, s.cash - x, s.reserves⟩ : St).acct w) = (⟨(s.acct u).e, (s.acct u).d + x⟩ : Acct) := by
        show (if w = u then (⟨(s.acct u).e, (s.acct u).d + x⟩ : Acct) else s.acct w) = _
        rw [if_pos hcw]
      rw [hg]
      exact hcond.2
    · have hstep : step s (.borrow u x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | repay u x =>
    unfold Checked at hc
    cases hc
  | mint u x =>
    have hcw : w = u := hc
    have e0 : step s (.mint u x) =
      (if (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct a, s.cash, s.reserves⟩ else none) := rfl
    by_cases hcond : (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩)
    · have hstep : step s (.mint u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct a, s.cash, s.reserves⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct a, s.cash, s.reserves⟩ : St).acct w) = (⟨(s.acct u).e + x, (s.acct u).d + x⟩ : Acct) := by
        show (if w = u then (⟨(s.acct u).e + x, (s.acct u).d + x⟩ : Acct) else s.acct w) = _
        rw [if_pos hcw]
      rw [hg]
      exact hcond
    · have hstep : step s (.mint u x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | burn u x =>
    have hcw : w = u := hc
    have e0 : step s (.burn u x) =
      (if (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ else none) := rfl
    by_cases hcond : (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩)
    · have hstep : step s (.burn u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ : St).acct w) = (⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ : Acct) := by
        show (if w = u then (⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ : Acct) else s.acct w) = _
        rw [if_pos hcw]
      rw [hg]
      exact hcond.2
    · have hstep : step s (.burn u x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | transfer u v x =>
    have hcw : w = u := hc
    have e0 : step s (.transfer u v x) =
      (if (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩)) then
        some ⟨fun a => if a = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ else none) := rfl
    by_cases hcond : (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩))
    · have hstep : step s (.transfer u v x) = some ⟨fun a => if a = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      have hnev : w ≠ v := by rw [hcw]; exact hcond.1
      have hg : ((⟨fun a => if a = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ : St).acct w) = (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) := by
        show (if w = v then (⟨(s.acct v).e + x, (s.acct v).d⟩ : Acct) else if w = u then (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) else s.acct w) = _
        rw [if_neg hnev, if_pos hcw]
      rw [hg]
      exact hcond.2.2.1
    · have hstep : step s (.transfer u v x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | donate u x =>
    have hcw : w = u := hc
    have e0 : step s (.donate u x) =
      (if (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves + x⟩ else none) := rfl
    by_cases hcond : (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · have hstep : step s (.donate u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves + x⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves + x⟩ : St).acct w) = (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) := by
        show (if w = u then (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) else s.acct w) = _
        rw [if_pos hcw]
      rw [hg]
      exact hcond.2
    · have hstep : step s (.donate u x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | liquidate liq viol r =>
    have hcw : w = liq := hc
    have e0 : step s (.liquidate liq viol r) =
      (if (liq ≠ viol ∧ ¬ Healthy (s.acct viol) ∧ r ≤ maxRepay (s.acct viol) ∧ Healthy ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩) then
        some ⟨fun a => if a = liq then ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ else if a = viol then ⟨(s.acct viol).e - liqYield (s.acct viol) r, (s.acct viol).d - r⟩ else s.acct a, s.cash, s.reserves + liqFee r⟩ else none) := rfl
    by_cases hcond : (liq ≠ viol ∧ ¬ Healthy (s.acct viol) ∧ r ≤ maxRepay (s.acct viol) ∧ Healthy ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩)
    · have hstep : step s (.liquidate liq viol r) = some ⟨fun a => if a = liq then ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ else if a = viol then ⟨(s.acct viol).e - liqYield (s.acct viol) r, (s.acct viol).d - r⟩ else s.acct a, s.cash, s.reserves + liqFee r⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      have hg : ((⟨fun a => if a = liq then ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ else if a = viol then ⟨(s.acct viol).e - liqYield (s.acct viol) r, (s.acct viol).d - r⟩ else s.acct a, s.cash, s.reserves + liqFee r⟩ : St).acct w) = (⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ : Acct) := by
        show (if w = liq then (⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ : Acct) else _) = _
        rw [if_pos hcw]
      rw [hg]
      exact hcond.2.2.2
    · have hstep : step s (.liquidate liq viol r) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h

theorem req_stays_healthy : StaysHealthy step := by
  unfold StaysHealthy
  intro s op s' w h hh
  cases op with
  | deposit u x =>
    have e0 : step s (.deposit u x) =
      (if ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d⟩ else s.acct a, s.cash + x, s.reserves⟩ else none) := rfl
    by_cases hcond : ((s.acct u).d = 0 ∨ Healthy ⟨(s.acct u).e + x, (s.acct u).d⟩)
    · have hstep : step s (.deposit u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d⟩ else s.acct a, s.cash + x, s.reserves⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      by_cases hwu : w = u
      · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d⟩ else s.acct a, s.cash + x, s.reserves⟩ : St).acct w) = (⟨(s.acct u).e + x, (s.acct u).d⟩ : Acct) := by
          show (if w = u then (⟨(s.acct u).e + x, (s.acct u).d⟩ : Acct) else s.acct w) = _
          rw [if_pos hwu]
        rw [hg]
        cases hcond with
        | inl hd0 =>
          unfold Healthy
          simp only [hd0, Nat.zero_mul, Nat.zero_div]
          exact Nat.zero_le _
        | inr hh2 => exact hh2
      · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d⟩ else s.acct a, s.cash + x, s.reserves⟩ : St).acct w) = s.acct w := by
          show (if w = u then (⟨(s.acct u).e + x, (s.acct u).d⟩ : Acct) else s.acct w) = s.acct w
          rw [if_neg hwu]
        rw [hg]
        exact hh
    · have hstep : step s (.deposit u x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | withdraw u x =>
    have e0 : step s (.withdraw u x) =
      (if (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash - x, s.reserves⟩ else none) := rfl
    by_cases hcond : (x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · have hstep : step s (.withdraw u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash - x, s.reserves⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      by_cases hwu : w = u
      · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash - x, s.reserves⟩ : St).acct w) = (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) := by
          show (if w = u then (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) else s.acct w) = _
          rw [if_pos hwu]
        rw [hg]
        exact hcond.2.2
      · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash - x, s.reserves⟩ : St).acct w) = s.acct w := by
          show (if w = u then (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) else s.acct w) = s.acct w
          rw [if_neg hwu]
        rw [hg]
        exact hh
    · have hstep : step s (.withdraw u x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | borrow u x =>
    have e0 : step s (.borrow u x) =
      (if (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct a, s.cash - x, s.reserves⟩ else none) := rfl
    by_cases hcond : (x ≤ s.cash ∧ Healthy ⟨(s.acct u).e, (s.acct u).d + x⟩)
    · have hstep : step s (.borrow u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct a, s.cash - x, s.reserves⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      by_cases hwu : w = u
      · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct a, s.cash - x, s.reserves⟩ : St).acct w) = (⟨(s.acct u).e, (s.acct u).d + x⟩ : Acct) := by
          show (if w = u then (⟨(s.acct u).e, (s.acct u).d + x⟩ : Acct) else s.acct w) = _
          rw [if_pos hwu]
        rw [hg]
        exact hcond.2
      · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d + x⟩ else s.acct a, s.cash - x, s.reserves⟩ : St).acct w) = s.acct w := by
          show (if w = u then (⟨(s.acct u).e, (s.acct u).d + x⟩ : Acct) else s.acct w) = s.acct w
          rw [if_neg hwu]
        rw [hg]
        exact hh
    · have hstep : step s (.borrow u x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | repay u x =>
    have hstep : step s (.repay u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash + min x (s.acct u).d, s.reserves⟩ := rfl
    have hEq := Option.some_inj.mp (hstep.symm.trans h)
    subst hEq
    by_cases hwu : w = u
    · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash + min x (s.acct u).d, s.reserves⟩ : St).acct w) = (⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ : Acct) := by
        show (if w = u then (⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ : Acct) else s.acct w) = _
        rw [if_pos hwu]
      rw [hg]
      have hh_u : Healthy (s.acct u) := hwu ▸ hh
      unfold Healthy at hh_u ⊢
      simp only at hh_u ⊢
      have hle : (s.acct u).d - min x (s.acct u).d ≤ (s.acct u).d := Nat.sub_le _ _
      have hmul : ((s.acct u).d - min x (s.acct u).d) * 20 ≤ (s.acct u).d * 20 := Nat.mul_le_mul_right _ hle
      have hdiv : ((s.acct u).d - min x (s.acct u).d) * 20 / 19 ≤ (s.acct u).d * 20 / 19 := Nat.div_le_div_right hmul
      exact Nat.le_trans hdiv hh_u
    · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash + min x (s.acct u).d, s.reserves⟩ : St).acct w) = s.acct w := by
        show (if w = u then (⟨(s.acct u).e, (s.acct u).d - min x (s.acct u).d⟩ : Acct) else s.acct w) = s.acct w
        rw [if_neg hwu]
      rw [hg]
      exact hh
  | mint u x =>
    have e0 : step s (.mint u x) =
      (if (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct a, s.cash, s.reserves⟩ else none) := rfl
    by_cases hcond : (Healthy ⟨(s.acct u).e + x, (s.acct u).d + x⟩)
    · have hstep : step s (.mint u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct a, s.cash, s.reserves⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      by_cases hwu : w = u
      · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct a, s.cash, s.reserves⟩ : St).acct w) = (⟨(s.acct u).e + x, (s.acct u).d + x⟩ : Acct) := by
          show (if w = u then (⟨(s.acct u).e + x, (s.acct u).d + x⟩ : Acct) else s.acct w) = _
          rw [if_pos hwu]
        rw [hg]
        exact hcond
      · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e + x, (s.acct u).d + x⟩ else s.acct a, s.cash, s.reserves⟩ : St).acct w) = s.acct w := by
          show (if w = u then (⟨(s.acct u).e + x, (s.acct u).d + x⟩ : Acct) else s.acct w) = s.acct w
          rw [if_neg hwu]
        rw [hg]
        exact hh
    · have hstep : step s (.mint u x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | burn u x =>
    have e0 : step s (.burn u x) =
      (if (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ else none) := rfl
    by_cases hcond : (min x (s.acct u).d ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩)
    · have hstep : step s (.burn u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      by_cases hwu : w = u
      · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ : St).acct w) = (⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ : Acct) := by
          show (if w = u then (⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ : Acct) else s.acct w) = _
          rw [if_pos hwu]
        rw [hg]
        exact hcond.2
      · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ : St).acct w) = s.acct w := by
          show (if w = u then (⟨(s.acct u).e - min x (s.acct u).d, (s.acct u).d - min x (s.acct u).d⟩ : Acct) else s.acct w) = s.acct w
          rw [if_neg hwu]
        rw [hg]
        exact hh
    · have hstep : step s (.burn u x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | transfer u v x =>
    have e0 : step s (.transfer u v x) =
      (if (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩)) then
        some ⟨fun a => if a = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ else none) := rfl
    by_cases hcond : (u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩ ∧ ((s.acct v).d = 0 ∨ Healthy ⟨(s.acct v).e + x, (s.acct v).d⟩))
    · have hstep : step s (.transfer u v x) = some ⟨fun a => if a = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      by_cases hwu : w = u
      · have hnev : w ≠ v := by rw [hwu]; exact hcond.1
        have hg : ((⟨fun a => if a = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ : St).acct w) = (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) := by
          show (if w = v then (⟨(s.acct v).e + x, (s.acct v).d⟩ : Acct) else if w = u then (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) else s.acct w) = _
          rw [if_neg hnev, if_pos hwu]
        rw [hg]
        exact hcond.2.2.1
      · by_cases hwv : w = v
        · have hg : ((⟨fun a => if a = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ : St).acct w) = (⟨(s.acct v).e + x, (s.acct v).d⟩ : Acct) := by
            show (if w = v then (⟨(s.acct v).e + x, (s.acct v).d⟩ : Acct) else _) = _
            rw [if_pos hwv]
          rw [hg]
          have hwv' : w = v := hwv
          have heqv : s.acct w = s.acct v := by rw [hwv']
          cases hcond.2.2.2 with
          | inl hd0 =>
            unfold Healthy
            simp only [hd0, Nat.zero_mul, Nat.zero_div]
            exact Nat.zero_le _
          | inr hh2 => exact hh2
        · have hg : ((⟨fun a => if a = v then ⟨(s.acct v).e + x, (s.acct v).d⟩ else if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves⟩ : St).acct w) = s.acct w := by
            show (if w = v then (⟨(s.acct v).e + x, (s.acct v).d⟩ : Acct) else if w = u then (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) else s.acct w) = s.acct w
            rw [if_neg hwv, if_neg hwu]
          rw [hg]
          exact hh
    · have hstep : step s (.transfer u v x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | donate u x =>
    have e0 : step s (.donate u x) =
      (if (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩) then
        some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves + x⟩ else none) := rfl
    by_cases hcond : (x ≤ (s.acct u).e ∧ Healthy ⟨(s.acct u).e - x, (s.acct u).d⟩)
    · have hstep : step s (.donate u x) = some ⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves + x⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      by_cases hwu : w = u
      · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves + x⟩ : St).acct w) = (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) := by
          show (if w = u then (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) else s.acct w) = _
          rw [if_pos hwu]
        rw [hg]
        exact hcond.2
      · have hg : ((⟨fun a => if a = u then ⟨(s.acct u).e - x, (s.acct u).d⟩ else s.acct a, s.cash, s.reserves + x⟩ : St).acct w) = s.acct w := by
          show (if w = u then (⟨(s.acct u).e - x, (s.acct u).d⟩ : Acct) else s.acct w) = s.acct w
          rw [if_neg hwu]
        rw [hg]
        exact hh
    · have hstep : step s (.donate u x) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h
  | liquidate liq viol r =>
    have e0 : step s (.liquidate liq viol r) =
      (if (liq ≠ viol ∧ ¬ Healthy (s.acct viol) ∧ r ≤ maxRepay (s.acct viol) ∧ Healthy ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩) then
        some ⟨fun a => if a = liq then ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ else if a = viol then ⟨(s.acct viol).e - liqYield (s.acct viol) r, (s.acct viol).d - r⟩ else s.acct a, s.cash, s.reserves + liqFee r⟩ else none) := rfl
    by_cases hcond : (liq ≠ viol ∧ ¬ Healthy (s.acct viol) ∧ r ≤ maxRepay (s.acct viol) ∧ Healthy ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩)
    · have hstep : step s (.liquidate liq viol r) = some ⟨fun a => if a = liq then ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ else if a = viol then ⟨(s.acct viol).e - liqYield (s.acct viol) r, (s.acct viol).d - r⟩ else s.acct a, s.cash, s.reserves + liqFee r⟩ := by rw [e0, if_pos hcond]
      have hEq := Option.some_inj.mp (hstep.symm.trans h)
      subst hEq
      by_cases hwl : w = liq
      · have hg : ((⟨fun a => if a = liq then ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ else if a = viol then ⟨(s.acct viol).e - liqYield (s.acct viol) r, (s.acct viol).d - r⟩ else s.acct a, s.cash, s.reserves + liqFee r⟩ : St).acct w) = (⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ : Acct) := by
          show (if w = liq then (⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ : Acct) else _) = _
          rw [if_pos hwl]
        rw [hg]
        exact hcond.2.2.2
      · by_cases hwv : w = viol
        · have hhv : Healthy (s.acct viol) := hwv ▸ hh
          exact absurd hhv hcond.2.1
        · have hg : ((⟨fun a => if a = liq then ⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ else if a = viol then ⟨(s.acct viol).e - liqYield (s.acct viol) r, (s.acct viol).d - r⟩ else s.acct a, s.cash, s.reserves + liqFee r⟩ : St).acct w) = s.acct w := by
            show (if w = liq then (⟨(s.acct liq).e + liqYield (s.acct viol) r, (s.acct liq).d + r + liqFee r⟩ : Acct) else if w = viol then (⟨(s.acct viol).e - liqYield (s.acct viol) r, (s.acct viol).d - r⟩ : Acct) else s.acct w) = s.acct w
            rw [if_neg hwl, if_neg hwv]
          rw [hg]
          exact hh
    · have hstep : step s (.liquidate liq viol r) = none := by rw [e0, if_neg hcond]
      rw [hstep] at h
      cases h

theorem req_no_bad_debt : NoBadDebt step := by
  unfold NoBadDebt
  intro s hr
  induction hr with
  | genesis =>
    intro u
    unfold genesis Healthy
    simp
  | step op _ heq ih =>
    intro u
    exact req_stays_healthy _ _ _ _ heq (ih u)

end EulerLending
