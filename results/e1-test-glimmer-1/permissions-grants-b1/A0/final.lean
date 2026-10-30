import Grants.Spec

namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) :=
  by unfold ValidCommand OtherAdmin; infer_instance

def step : Impl :=
  fun s r =>
    if ValidCommand s r then
      (Outcome.ok, { users := s.users, has := fun u q => expectedHas s r u q })
    else
      (Outcome.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_authorization : AdminOnly step := by
  intro s r hok
  by_cases hv : ValidCommand s r
  · simp [step, hv] at hok
    rcases hv with ⟨ha, _, had, _, _⟩
    exact ⟨ha, had⟩
  · simp [step, hv] at hok

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hop
  by_cases hv : ValidCommand s r
  · simp [step, hv] at hok
    rcases hv with ⟨_, _, _, hgr, _⟩
    exact (hgr hop).1
  · simp [step, hv] at hok

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hneq
  by_cases hv : ValidCommand s r
  · simp [step, hv] at hok
    simp [expectedHas, hneq]
  · simp [step, hv] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : ValidCommand s r
  · simp [step, hv] at hok ⊢
    constructor
    · rfl
    · intro u q; rfl
  · simp [step, hv] at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hv : ValidCommand s r
  · simp [step, hv] at hok
    have hnot : ¬ ValidCommand { users := s.users, has := fun u q => expectedHas s r u q } r := by
      intro hval
      rcases hv with ⟨_, _, _, hgr, hre⟩
      rcases hval with ⟨_, _, _, hgr', hre'⟩
      cases r.op with
      | grant =>
        have hpre := (hgr rfl).2
        have hpost := (hgr' rfl).2
        simp [expectedHas] at hpost
        rw [decide_eq_true_eq] at hpost
        contradiction
      | revoke =>
        have hpre := (hre rfl).1
        have hpost := (hre' rfl).1
        simp [expectedHas] at hpost
        contradiction
    simp [step, hnot]
  · simp [step, hv] at hok

theorem req_last_admin : KeepsAdmin step := by
  intro s r had
  by_cases hv : ValidCommand s r
  · simp [step, hv]
    rcases hv with ⟨_, _, _, hgr, hre⟩
    rcases had with ⟨u0, hu0, had0⟩
    by_cases hsame : u0 = r.target ∧ Role.admin = r.role
    · cases r.op with
      | grant =>
        exact ⟨u0, by simp, by simp [expectedHas, hsame]⟩
      | revoke =>
        have hr : r.role = Role.admin := (hsame.2).symm
        rcases (hre rfl).2 hr with ⟨v, hv_mem, hv_ne, hv_admin⟩
        have : expectedHas s r v Role.admin = s.has v Role.admin := by
          simp [expectedHas, hv_ne, hr]
        exact ⟨v, by simp, by rw [this]; exact hv_admin⟩
    · have : expectedHas s r u0 Role.admin = s.has u0 Role.admin := by
        simp [expectedHas, hsame]
      exact ⟨u0, by simp, by rw [this]; exact had0⟩
  · simp [step, hv]
    exact had

end Grants
