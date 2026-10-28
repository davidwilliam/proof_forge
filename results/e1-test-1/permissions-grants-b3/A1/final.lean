import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance
def step : Impl := fun s r =>
  if ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

theorem req_idempotency_aux_test : True := trivial

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
  · simp [hv] at h
    obtain ⟨h1, h2, h3, _, _⟩ := hv
    exact ⟨h1, h3⟩
  · simp [hv] at h

theorem req_no_self_grant   : NoSelfGrant step := by
  intro s r h hop
  unfold step at h
  by_cases hv : ValidCommand s r
  · simp [hv] at h
    obtain ⟨_, _, _, hg, _⟩ := hv
    exact (hg hop).1
  · simp [hv] at h

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hneq
  by_cases hv : ValidCommand s r
  · have hstep : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
      unfold step; simp [hv]
    have hhas : (step s r).2.has u q = expectedHas s r u q := by
      rw [hstep]
    rw [hhas]
    unfold expectedHas
    have hneg : ¬ (u = r.target ∧ q = r.role) := by
      cases hneq with
      | inl h => exact fun h2 => h h2.1
      | inr h => exact fun h2 => h h2.2
    simp [hneg]
  · unfold step at hok
    simp [hv] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : ValidCommand s r
  · have hstep : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
      unfold step; simp [hv]
    rw [hstep]
    exact ⟨rfl, fun u q => rfl⟩
  · unfold step at hok
    simp [hv] at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hv : ValidCommand s r
  · have hstep : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
      unfold step
      simp [hv]
    have h2eq : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by
      rw [hstep]
    have hneg : ¬ ValidCommand ({ users := s.users, has := expectedHas s r } : State) r := by
      intro hc
      obtain ⟨ha_mem, ht_mem, ha_admin, hg, hr⟩ := hc
      cases hop : r.op with
      | grant =>
        obtain ⟨hne, hfalse⟩ := hg hop
        change expectedHas s r r.target r.role = false at hfalse
        have hexp : expectedHas s r r.target r.role = true := by
          unfold expectedHas
          simp [hop]
        rw [hexp] at hfalse
        simp at hfalse
      | revoke =>
        obtain ⟨htrue, _⟩ := hr hop
        change expectedHas s r r.target r.role = true at htrue
        have hexp : expectedHas s r r.target r.role = false := by
          unfold expectedHas
          simp [hop]
        rw [hexp] at htrue
        simp at htrue
    have hrej : step ({ users := s.users, has := expectedHas s r } : State) r =
        (.rejected, ({ users := s.users, has := expectedHas s r } : State)) :=
      req_invalid_noop _ _ hneg
    rw [h2eq]
    exact hrej
  · unfold step at hok
    simp [hv] at hok

theorem req_last_admin : KeepsAdmin step := by
  intro s r H
  by_cases hv : ValidCommand s r
  · have hstep : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
      unfold step; simp [hv]
    obtain ⟨u0, hu0_mem, hu0_admin⟩ := H
    obtain ⟨ha_mem, ht_mem, ha_admin, hg, hr⟩ := hv
    by_cases hbad : (u0 = r.target ∧ r.role = .admin ∧ r.op = .revoke)
    · obtain ⟨h_eq_t, h_eq_role, h_eq_op⟩ := hbad
      obtain ⟨htrue, hother⟩ := hr h_eq_op
      have hOA : OtherAdmin s r.target := hother h_eq_role
      obtain ⟨v, hv_mem, hv_ne, hv_admin⟩ := hOA
      refine ⟨v, ?_, ?_⟩
      · have : (step s r).2.users = s.users := by rw [hstep]
        rw [this]; exact hv_mem
      · have hv_has : (step s r).2.has v .admin = expectedHas s r v .admin := by rw [hstep]
        rw [hv_has]
        unfold expectedHas
        have hneg : ¬ (v = r.target ∧ (.admin : Role) = r.role) := by
          intro hcon
          exact hv_ne hcon.1
        simp [hneg, hv_admin]
    · refine ⟨u0, ?_, ?_⟩
      · have : (step s r).2.users = s.users := by rw [hstep]
        rw [this]; exact hu0_mem
      · have hu_has : (step s r).2.has u0 .admin = expectedHas s r u0 .admin := by rw [hstep]
        rw [hu_has]
        unfold expectedHas
        by_cases hcon : (u0 = r.target ∧ (.admin : Role) = r.role)
        · have hop : r.op = .grant := by
            cases hop2 : r.op with
            | grant => rfl
            | revoke =>
              exfalso
              apply hbad
              exact ⟨hcon.1, hcon.2.symm, hop2⟩
          simp [hcon, hop]
        · simp [hcon, hu0_admin]
  · have hstep : step s r = (.rejected, s) := req_invalid_noop s r hv
    obtain ⟨u0, hu0_mem, hu0_admin⟩ := H
    refine ⟨u0, ?_, ?_⟩
    · have : (step s r).2.users = s.users := by rw [hstep]
      rw [this]; exact hu0_mem
    · have : (step s r).2.has u0 .admin = s.has u0 .admin := by rw [hstep]
      rw [this]; exact hu0_admin

end Grants
