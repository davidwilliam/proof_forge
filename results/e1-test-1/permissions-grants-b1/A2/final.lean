import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance
def step : Impl := fun s r =>
  if _h : ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop    : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization   : AdminOnly step := by
  intro s r h
  unfold step at h
  by_cases hv : ValidCommand s r
  · obtain ⟨ha, _, hc, _, _⟩ := hv
    exact ⟨ha, hc⟩
  · simp [hv] at h

theorem req_no_self_grant   : NoSelfGrant step := by
  intro s r h hop
  unfold step at h
  by_cases hv : ValidCommand s r
  · obtain ⟨_, _, _, hgr, _⟩ := hv
    exact (hgr hop).1
  · simp [hv] at h

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r h u q hneq
  unfold step at h ⊢
  by_cases hv : ValidCommand s r
  · simp only [hv, dite_true] at h ⊢
    -- h : (ok, ...) .1 = ok which is trivial, need second component
    -- goal about has
    show (expectedHas s r u q) = s.has u q
    unfold expectedHas
    have hcond : ¬ (u = r.target ∧ q = r.role) := by
      cases hneq with
      | inl hl => intro hc; exact hl hc.1
      | inr hr => intro hc; exact hr hc.2
    simp [hcond]
  · simp [hv] at h

theorem req_effects : Effects step := by
  intro s r h
  unfold step at h ⊢
  by_cases hv : ValidCommand s r
  · simp [hv]
  · simp [hv] at h

theorem req_idempotency : Idempotent step := by
  intro s r h
  have hv : ValidCommand s r := by
    by_cases hc : ValidCommand s r
    · exact hc
    · have e := req_invalid_noop s r hc
      rw [e] at h
      simp at h
  have hstep : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
    unfold step
    simp [hv]
  have h2 : (step s r).2 = { users := s.users, has := expectedHas s r } := by
    rw [hstep]
  have hnot : ¬ ValidCommand (step s r).2 r := by
    rw [h2]
    intro hc
    obtain ⟨hm1, hm2, hm3, hgr, hrev⟩ := hv
    obtain ⟨hn1, hn2, hn3, hngr, hnrev⟩ := hc
    cases hop : r.op with
    | grant =>
      have hng := (hngr hop).2
      simp only at hng
      unfold expectedHas at hng
      simp [hop] at hng
    | revoke =>
      have hng := (hnrev hop).1
      simp only at hng
      unfold expectedHas at hng
      simp [hop] at hng
  have e := req_invalid_noop (step s r).2 r hnot
  exact e

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  obtain ⟨u0, hu0mem, hu0admin⟩ := hex
  cases hop : r.op with
  | grant =>
    by_cases hv : ValidCommand s r
    · have hvcopy := hv
      obtain ⟨hact_mem, htgt_mem, hact_admin, hgr, hrev⟩ := hvcopy
      have hok : (step s r).1 = .ok := req_valid_succeeds s r hv
      have heff := req_effects s r hok
      obtain ⟨husers, hhas_eq⟩ := heff
      have hne : r.actor ≠ r.target := (hgr hop).1
      have hhas : (step s r).2.has r.actor .admin = true := by
        rw [hhas_eq]
        show expectedHas s r r.actor .admin = true
        unfold expectedHas
        have hcond : ¬ (r.actor = r.target ∧ (.admin : Role) = r.role) := by
          intro hc; exact hne hc.1
        simp [hcond, hact_admin]
      rw [husers]
      exact ⟨r.actor, hact_mem, hhas⟩
    · have e : step s r = (.rejected, s) := req_invalid_noop s r hv
      have h2 : (step s r).2 = s := by rw [e]
      rw [h2]
      exact ⟨u0, hu0mem, hu0admin⟩
  | revoke =>
    by_cases hv : ValidCommand s r
    · have hvcopy := hv
      obtain ⟨hact_mem, htgt_mem, hact_admin, hgr, hrev⟩ := hvcopy
      have hok : (step s r).1 = .ok := req_valid_succeeds s r hv
      have heff := req_effects s r hok
      obtain ⟨husers, hhas_eq⟩ := heff
      by_cases hrole : r.role = .admin
      · have hrevA := hrev hop
        obtain ⟨htrue, hother⟩ := hrevA
        obtain ⟨v, hvmem, hne_v, hvadmin⟩ := hother hrole
        have hhas : (step s r).2.has v .admin = true := by
          rw [hhas_eq]
          show expectedHas s r v .admin = true
          unfold expectedHas
          have hcond : ¬ (v = r.target ∧ (.admin : Role) = r.role) := by
            intro hc; exact hne_v hc.1
          simp only [hcond, ite_false]
          exact hvadmin
        rw [husers]
        exact ⟨v, hvmem, hhas⟩
      · have hhas : (step s r).2.has u0 .admin = true := by
          rw [hhas_eq]
          show expectedHas s r u0 .admin = true
          unfold expectedHas
          have hcond : ¬ (u0 = r.target ∧ (.admin : Role) = r.role) := by
            intro hc; exact hrole hc.2.symm
          simp only [hcond, ite_false]
          exact hu0admin
        rw [husers]
        exact ⟨u0, hu0mem, hhas⟩
    · have e : step s r = (.rejected, s) := req_invalid_noop s r hv
      have h2 : (step s r).2 = s := by rw [e]
      rw [h2]
      exact ⟨u0, hu0mem, hu0admin⟩

end Grants
