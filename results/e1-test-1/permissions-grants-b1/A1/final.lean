import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance
def step : Impl := fun s r =>
  if ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

theorem test_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem myLastAdminAux3 : KeepsAdmin step := by
  intro s r hex
  obtain ⟨u0, hu0mem, hu0admin⟩ := hex
  by_cases hV : ValidCommand s r
  · have hVc := hV
    obtain ⟨ha_mem, ht_mem, ha_admin, hgrant, hrevoke⟩ := hVc
    have hstep : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step
      simp [hV]
    have h2eq : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by
      rw [hstep]
    cases hop : r.op with
    | grant =>
      by_cases hrole : r.role = Role.admin
      · refine ⟨r.target, ?_, ?_⟩
        · rw [h2eq]; exact ht_mem
        · rw [h2eq]
          show expectedHas s r r.target Role.admin = true
          have hr : r.role = Role.admin := hrole
          unfold expectedHas
          simp [hr, hop]
      · refine ⟨u0, ?_, ?_⟩
        · rw [h2eq]; exact hu0mem
        · rw [h2eq]
          show expectedHas s r u0 Role.admin = true
          unfold expectedHas
          have hcond : ¬ (u0 = r.target ∧ Role.admin = r.role) := by
            rintro ⟨_, hq⟩
            apply hrole
            exact hq.symm
          simp [hcond, hu0admin]
    | revoke =>
      have hop' : r.op = Op.revoke := by rw [hop]
      have hrev := hrevoke hop'
      by_cases hrole : r.role = Role.admin
      · have hOA : OtherAdmin s r.target := hrev.2 hrole
        obtain ⟨v, hv_mem, hv_ne, hv_admin⟩ := hOA
        refine ⟨v, ?_, ?_⟩
        · rw [h2eq]; exact hv_mem
        · rw [h2eq]
          show expectedHas s r v Role.admin = true
          unfold expectedHas
          have hcond : ¬ (v = r.target ∧ Role.admin = r.role) := by
            rintro ⟨hv_eq, _⟩
            exact hv_ne hv_eq
          simp [hcond, hv_admin]
      · refine ⟨u0, ?_, ?_⟩
        · rw [h2eq]; exact hu0mem
        · rw [h2eq]
          show expectedHas s r u0 Role.admin = true
          unfold expectedHas
          have hcond : ¬ (u0 = r.target ∧ Role.admin = r.role) := by
            rintro ⟨_, hq⟩
            apply hrole
            exact hq.symm
          simp [hcond, hu0admin]
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hV]
    have h2eq : (step s r).2 = s := by rw [hstep]
    exact ⟨u0, by rw [h2eq]; exact hu0mem, by rw [h2eq]; exact hu0admin⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization   : AdminOnly step := by
  intro s r h
  by_cases hV : ValidCommand s r
  · obtain ⟨ha_mem, _, ha_admin, _, _⟩ := hV
    exact ⟨ha_mem, ha_admin⟩
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hV]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [h1] at h
    contradiction

theorem req_no_self_grant   : NoSelfGrant step := by
  intro s r hok hop
  by_cases hV : ValidCommand s r
  · obtain ⟨_, _, _, hgrant, _⟩ := hV
    exact (hgrant hop).1
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hV]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [h1] at hok
    contradiction

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hne
  by_cases hV : ValidCommand s r
  · have h2 : (step s r).2.has u q = expectedHas s r u q := by
      unfold step
      simp [hV]
    rw [h2]
    unfold expectedHas
    have hcond : ¬ (u = r.target ∧ q = r.role) := by
      cases hne with
      | inl h => exact fun ⟨hu, _⟩ => h hu
      | inr h => exact fun ⟨_, hq⟩ => h hq
    simp [hcond]
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hV]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [h1] at hok
    contradiction

theorem req_effects         : Effects step := by
  intro s r hok
  by_cases hV : ValidCommand s r
  · have hstep : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step
      simp [hV]
    have husers : (step s r).2.users = s.users := by rw [hstep]
    have hhas : ∀ u q, (step s r).2.has u q = expectedHas s r u q := by
      intro u q
      rw [hstep]
    exact ⟨husers, hhas⟩
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hV]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [h1] at hok
    contradiction

theorem req_idempotency     : Idempotent step := by
  intro s r hok
  by_cases hV : ValidCommand s r
  · have hstep : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step
      simp [hV]
    have hs2 : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by
      rw [hstep]
    have hNot : ¬ ValidCommand ({ users := s.users, has := expectedHas s r } : State) r := by
      intro hC
      obtain ⟨ha_mem, ht_mem, ha_admin, hgrant, hrevoke⟩ := hV
      obtain ⟨ha_mem', ht_mem', ha_admin', hgrant', hrevoke'⟩ := hC
      cases hop : r.op with
      | grant =>
        have h2 : expectedHas s r r.target r.role = false := (hgrant' hop).2
        have hexp : expectedHas s r r.target r.role = true := by
          unfold expectedHas
          simp [hop]
        rw [hexp] at h2
        contradiction
      | revoke =>
        have hop' : r.op = Op.revoke := by rw [hop]
        have h2 : expectedHas s r r.target r.role = true := (hrevoke' hop').1
        have hexp : expectedHas s r r.target r.role = false := by
          unfold expectedHas
          simp [hop]
        rw [hexp] at h2
        contradiction
    have hstep2 : step ({ users := s.users, has := expectedHas s r } : State) r =
        (.rejected, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step
      simp [hNot]
    rw [hs2]
    exact hstep2
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hV]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [h1] at hok
    contradiction

theorem req_last_admin      : KeepsAdmin step := myLastAdminAux3

end Grants
