import Grants.Spec

namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin
  infer_instance

def step : Impl := fun s r =>
  if _ : ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_authorization : AdminOnly step := by
  intro s r hOk
  by_cases h : ValidCommand s r
  · rcases h with ⟨h1, _, h3, _, _⟩
    exact ⟨h1, h3⟩
  · exfalso
    have : (step s r).1 = .rejected := by simp [step, h]
    rw [this] at hOk
    cases hOk

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hOk hOp
  by_cases h : ValidCommand s r
  · rcases h with ⟨_, _, _, hG, _⟩
    exact (hG hOp).1
  · exfalso
    have : (step s r).1 = .rejected := by simp [step, h]
    rw [this] at hOk
    cases hOk

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hOk u q hNe
  by_cases h : ValidCommand s r
  · have hs : (step s r).2 = { users := s.users, has := expectedHas s r } := by
      simp [step, h]
    rw [hs]
    unfold expectedHas
    have hNot : ¬(u = r.target ∧ q = r.role) := by
      intro hc
      rcases hc with ⟨hu, hq⟩
      rcases hNe with h1 | h1
      · exact h1 hu
      · exact h1 hq
    simp [hNot]
  · have : (step s r).1 = .rejected := by simp [step, h]
    rw [this] at hOk
    cases hOk

theorem req_effects : Effects step := by
  intro s r hOk
  by_cases h : ValidCommand s r
  · have hs : (step s r).2 = { users := s.users, has := expectedHas s r } := by
      simp [step, h]
    rw [hs]
    constructor
    · rfl
    · intro u q; rfl
  · have : (step s r).1 = .rejected := by simp [step, h]
    rw [this] at hOk
    cases hOk

theorem req_idempotency : Idempotent step := by
  intro s r hOk
  have h : ValidCommand s r := by
    by_cases hc : ValidCommand s r
    · exact hc
    · have : (step s r).1 = .rejected := by simp [step, hc]
      rw [this] at hOk
      cases hOk
  have sEq : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by
    simp [step, h]
  have hNot : ¬ ValidCommand ({ users := s.users, has := expectedHas s r } : State) r := by
    intro h2
    rcases h with ⟨_, _, _, hG, hR⟩
    rcases h2 with ⟨_, _, _, hG2, hR2⟩
    by_cases hop : r.op = .grant
    · have hg := hG hop
      have hg2 := hG2 hop
      -- hg.2 : s.has target role = false
      -- hg2.2 : expectedHas ... = false
      have exp_eq : expectedHas s r r.target r.role = true := by
        unfold expectedHas
        simp [hop]
      have hg2_false : expectedHas s r r.target r.role = false := hg2.2
      rw [exp_eq] at hg2_false
      cases hg2_false
    · have hopR : r.op = .revoke := by
        cases hOp : r.op with
        | grant => exact absurd hOp hop
        | revoke => rfl
      have hr2 := hR2 hopR
      have exp_eq : expectedHas s r r.target r.role = false := by
        unfold expectedHas
        simp [hop]
      have hr2_true : expectedHas s r r.target r.role = true := hr2.1
      rw [exp_eq] at hr2_true
      cases hr2_true
  have h1 : step (({ users := s.users, has := expectedHas s r } : State)) r = ((.rejected : Outcome), ({ users := s.users, has := expectedHas s r } : State)) := by
    simp [step, hNot]
  have goal_eq : step (step s r).2 r = step (({ users := s.users, has := expectedHas s r } : State)) r := by
    rw [sEq]
  have rhs_eq : ((.rejected : Outcome), (step s r).2) = ((.rejected : Outcome), ({ users := s.users, has := expectedHas s r } : State)) := by
    rw [sEq]
  rw [goal_eq, rhs_eq, h1]

theorem req_last_admin : KeepsAdmin step := by
  intro s r hEx
  rcases hEx with ⟨w, hwMem, hwAdmin⟩
  by_cases h : ValidCommand s r
  · have hs : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by
      simp [step, h]
    rw [hs]
    rcases h with ⟨haMem, htMem, haAdminMem, hG, hR⟩
    by_cases hop : r.op = .grant
    · refine ⟨w, hwMem, ?_⟩
      unfold expectedHas
      by_cases heq : w = r.target ∧ Role.admin = r.role
      · simp [heq, hop]
      · simp [heq, hwAdmin]
    · have hopR : r.op = .revoke := by
        cases hOp : r.op with
        | grant => exact absurd hOp hop
        | revoke => rfl
      have hr := hR hopR
      rcases hr with ⟨_, hOther⟩
      by_cases hwEq : w = r.target ∧ Role.admin = r.role
      · rcases hwEq with ⟨hwT, hAdmEq⟩
        have hOtherAdmin : OtherAdmin s r.target := hOther hAdmEq.symm
        unfold OtherAdmin at hOtherAdmin
        rcases hOtherAdmin with ⟨v, hvMem, hvNe, hvAdm⟩
        refine ⟨v, hvMem, ?_⟩
        unfold expectedHas
        have hNe : ¬(v = r.target ∧ (Role.admin = r.role)) := by
          intro hc
          rcases hc with ⟨h1, _⟩
          exact hvNe h1
        simp [hNe, hvAdm]
      · refine ⟨w, hwMem, ?_⟩
        unfold expectedHas
        simp [hwEq, hwAdmin]
  · have hs : (step s r).2 = s := by simp [step, h]
    rw [hs]
    exact ⟨w, hwMem, hwAdmin⟩

end Grants
