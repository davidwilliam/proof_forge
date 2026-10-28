import Grants.Spec
namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin
  infer_instance

def step : Impl := fun s r =>
  if ValidCommand s r then (.ok, { users := s.users, has := expectedHas s r }) else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_authorization : AdminOnly step := by
  intro s r hok
  have hV : ValidCommand s r := by
    by_cases h : ValidCommand s r
    · exact h
    · have hEq : step s r = (.rejected, s) := by simp [step, h]
      rw [hEq] at hok
      simp at hok
  exact ⟨hV.1, hV.2.2.1⟩

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hop
  have hV : ValidCommand s r := by
    by_cases h : ValidCommand s r
    · exact h
    · have hEq : step s r = (.rejected, s) := by simp [step, h]
      rw [hEq] at hok
      simp at hok
  exact (hV.2.2.2.1 hop).1

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hor
  have hV : ValidCommand s r := by
    by_cases h : ValidCommand s r
    · exact h
    · have hEq : step s r = (.rejected, s) := by simp [step, h]
      rw [hEq] at hok
      simp at hok
  have hEq : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by simp [step, hV]
  rw [hEq]
  show expectedHas s r u q = s.has u q
  unfold expectedHas
  have hcond : ¬(u = r.target ∧ q = r.role) := by
    intro hC
    cases hor with
    | inl h => exact h hC.1
    | inr h => exact h hC.2
  simp [hcond]

theorem req_effects : Effects step := by
  intro s r hok
  have hV : ValidCommand s r := by
    by_cases h : ValidCommand s r
    · exact h
    · have hEq0 : step s r = (.rejected, s) := by simp [step, h]
      rw [hEq0] at hok
      simp at hok
  have hEq : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by simp [step, hV]
  rw [hEq]
  exact ⟨rfl, fun u q => rfl⟩

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hV : ValidCommand s r := by
    by_cases h : ValidCommand s r
    · exact h
    · have hEq0 : step s r = (.rejected, s) := by simp [step, h]
      rw [hEq0] at hok
      simp at hok
  have hEq : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by simp [step, hV]
  have hexp : expectedHas s r r.target r.role = decide (r.op = .grant) := by
    unfold expectedHas
    simp
  have hE2 : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by
    simp [step, hV]
  have hN' : ¬ ValidCommand ({ users := s.users, has := expectedHas s r } : State) r := by
    intro hV'
    by_cases hG : r.op = .grant
    · have hF := (hV'.2.2.2.1 hG).2
      have hFe : expectedHas s r r.target r.role = false := hF
      rw [hexp] at hFe
      have hDec : decide (r.op = .grant) = true := by simp [hG]
      rw [hDec] at hFe
      cases hFe
    · have hR : r.op = .revoke := by
        have hlem : ∀ o : Op, o ≠ .grant → o = .revoke := by
          intro o h
          cases o with
          | grant => exact absurd rfl h
          | revoke => rfl
        exact hlem _ hG
      have hT := (hV'.2.2.2.2 hR).1
      have hTe : expectedHas s r r.target r.role = true := hT
      rw [hexp] at hTe
      have hDecF : decide (r.op = .grant) = false := by simp [hG]
      rw [hDecF] at hTe
      cases hTe
  have hStep2 : step (step s r).2 r = (.rejected, (step s r).2) := by
    rw [hE2]
    simp [step, hN']
  exact hStep2

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  obtain ⟨u0, hu0mem, hu0admin⟩ := hex
  by_cases hV : ValidCommand s r
  · have hEq : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by simp [step, hV]
    rw [hEq]
    show ∃ u ∈ s.users, expectedHas s r u .admin = true
    by_cases hG : r.op = .grant
    · refine ⟨u0, hu0mem, ?_⟩
      unfold expectedHas
      by_cases hC : (u0 = r.target ∧ Role.admin = r.role)
      · simp [hC, hG]
      · simp [hC, hu0admin]
    · have hR : r.op = .revoke := by
        have hlem : ∀ o : Op, o ≠ .grant → o = .revoke := by
          intro o h
          cases o with
          | grant => exact absurd rfl h
          | revoke => rfl
        exact hlem _ hG
      by_cases hRole : r.role = .admin
      · have hRev := hV.2.2.2.2 hR
        have hOther := hRev.2 hRole
        obtain ⟨v, hv_mem, hv_ne, hv_admin⟩ := hOther
        refine ⟨v, hv_mem, ?_⟩
        unfold expectedHas
        have hcond : ¬(v = r.target ∧ Role.admin = r.role) := by
          intro hC
          exact hv_ne hC.1
        simp [hcond, hv_admin]
      · refine ⟨u0, hu0mem, ?_⟩
        unfold expectedHas
        have hcond : ¬(u0 = r.target ∧ Role.admin = r.role) := by
          intro hC
          exact hRole hC.2.symm
        simp [hcond, hu0admin]
  · have hEq : step s r = (.rejected, s) := by simp [step, hV]
    rw [hEq]
    exact ⟨u0, hu0mem, hu0admin⟩

end Grants
