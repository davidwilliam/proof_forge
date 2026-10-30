import Grants.Spec

namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin
  infer_instance

def step : Impl := fun s r =>
  if _h : ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  show (step s r).1 = .ok
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  show step s r = (.rejected, s)
  unfold step
  simp [h]

theorem req_authorization : AdminOnly step := by
  intro s r hok
  unfold step at hok
  by_cases h : ValidCommand s r
  · simp [h] at hok
    exact ⟨h.1, h.2.2.1⟩
  · simp [h] at hok

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hgrant
  unfold step at hok
  by_cases h : ValidCommand s r
  · simp [h] at hok
    exact (h.2.2.2.1 hgrant).1
  · simp [h] at hok

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hor
  have hok' := hok
  unfold step at hok
  by_cases h : ValidCommand s r
  · simp [h] at hok
    have hEq : (step s r).2.has u q = expectedHas s r u q := by
      unfold step
      simp [h]
    rw [hEq]
    unfold expectedHas
    have hcond : ¬(u = r.target ∧ q = r.role) := by
      intro hc
      rcases hor with h1 | h1
      · exact h1 hc.1
      · exact h1 hc.2
    simp [hcond]
  · simp [h] at hok

theorem req_effects : Effects step := by
  intro s r hok
  have hok' := hok
  unfold step at hok
  by_cases h : ValidCommand s r
  · simp [h] at hok
    constructor
    · show (if h : ValidCommand s r then (Outcome.ok, ({ users := s.users, has := expectedHas s r } : State)) else (Outcome.rejected, s)).2.users = s.users
      simp [h]
    · intro u q
      show (if h : ValidCommand s r then (Outcome.ok, ({ users := s.users, has := expectedHas s r } : State)) else (Outcome.rejected, s)).2.has u q = expectedHas s r u q
      simp [h]
  · simp [h] at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hok' := hok
  unfold step at hok
  by_cases h : ValidCommand s r
  · simp [h] at hok
    have hNot : ¬ValidCommand { users := s.users, has := expectedHas s r } r := by
      intro hv
      have hGrant := hv.2.2.2.1
      have hRevoke := hv.2.2.2.2
      cases hop : r.op with
      | grant =>
        have hg := hGrant hop
        have hHas : expectedHas s r r.target r.role = decide (r.op = .grant) := by
          unfold expectedHas; simp
        rw [hop] at hHas
        simp at hHas
        have : (({ users := s.users, has := expectedHas s r } : State).has r.target r.role) = true := by
          show expectedHas s r r.target r.role = true
          rw [hHas]
        rw [this] at hg
        exact absurd hg.2 (by decide)
      | revoke =>
        have hr := hRevoke hop
        have hHas : expectedHas s r r.target r.role = decide (r.op = .grant) := by
          unfold expectedHas; simp
        rw [hop] at hHas
        simp at hHas
        have : (({ users := s.users, has := expectedHas s r } : State).has r.target r.role) = false := by
          show expectedHas s r r.target r.role = false
          rw [hHas]
        rw [this] at hr
        exact absurd hr.1 (by decide)
    have hStepEq : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by
      unfold step
      simp [h]
    rw [hStepEq]
    show step { users := s.users, has := expectedHas s r } r = (.rejected, { users := s.users, has := expectedHas s r })
    unfold step
    simp [hNot]
  · simp [h] at hok

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  show ∃ u ∈ (step s r).2.users, (step s r).2.has u .admin = true
  unfold step
  by_cases h : ValidCommand s r
  · simp [h]
    rcases hex with ⟨u, huMem, huAdmin⟩
    by_cases hop : r.op = .grant
    · refine ⟨u, huMem, ?_⟩
      show expectedHas s r u .admin = true
      unfold expectedHas
      by_cases hc : u = r.target ∧ (Role.admin = r.role)
      · rcases hc with ⟨h1, h2⟩
        simp [h1, h2, hop]
      · simp [hc, huAdmin]
    · have hopR : r.op = .revoke := by
        cases hr : r.op with
        | grant => exact absurd hr hop
        | revoke => rfl
      by_cases hrole : r.role = .admin
      · have hOther : OtherAdmin s r.target := (h.2.2.2.2 hopR).2 hrole
        rcases hOther with ⟨v, hvMem, hvNe, hvAdmin⟩
        refine ⟨v, hvMem, ?_⟩
        show expectedHas s r v .admin = true
        unfold expectedHas
        have hc : ¬(v = r.target ∧ (Role.admin = r.role)) := by
          intro hc
          exact hvNe hc.1
        simp [hc, hvAdmin]
      · refine ⟨u, huMem, ?_⟩
        show expectedHas s r u .admin = true
        unfold expectedHas
        have hc : ¬(u = r.target ∧ (Role.admin = r.role)) := by
          intro hc
          exact hrole hc.2.symm
        simp [hc, huAdmin]
  · simp [h]
    exact hex

end Grants
