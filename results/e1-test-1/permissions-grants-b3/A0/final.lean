import Grants.Spec
namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin
  infer_instance

def step : Impl := fun s r =>
  if ValidCommand s r then (.ok, { users := s.users, has := expectedHas s r })
  else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : AdminOnly step := by
  intro s r hok
  by_cases h : ValidCommand s r
  · obtain ⟨ha_mem, _, ha_admin, _, _⟩ := h
    exact ⟨ha_mem, ha_admin⟩
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [h]
    rw [hrej] at hok
    exact absurd hok (by decide)

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hop
  by_cases h : ValidCommand s r
  · obtain ⟨_, _, _, hgrant, _⟩ := h
    have ⟨hne, _⟩ := hgrant hop
    exact hne
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [h]
    rw [hrej] at hok
    exact absurd hok (by decide)

theorem req_effects : Effects step := by
  intro s r hok
  by_cases h : ValidCommand s r
  · have hstep : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
      simp [step, h]
    rw [hstep]
    exact ⟨rfl, fun u q => rfl⟩
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [h]
    rw [hrej] at hok
    exact absurd hok (by decide)

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hne
  by_cases h : ValidCommand s r
  · have hstep : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
      simp [step, h]
    have hhas : (step s r).2.has u q = expectedHas s r u q := by rw [hstep]
    rw [hhas]
    unfold expectedHas
    have hcond : ¬ (u = r.target ∧ q = r.role) := by
      intro hc
      obtain ⟨hu, hq⟩ := hc
      cases hne with
      | inl hnu => exact hnu hu
      | inr hnq => exact hnq hq
    simp [hcond]
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [h]
    rw [hrej] at hok
    exact absurd hok (by decide)

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  obtain ⟨w, hw_mem, hw_has⟩ := hex
  by_cases h : ValidCommand s r
  · have hVC := h
    obtain ⟨ha_mem, ht_mem, ha_admin, hgrant, hrevoke⟩ := hVC
    have hstep : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
      simp [step, h]
    have hcases : r.op = Op.grant ∨ r.op = Op.revoke := by
      cases r.op <;> simp
    rcases hcases with hOp | hOp
    · refine ⟨w, ?_, ?_⟩
      · rw [hstep]; exact hw_mem
      · rw [hstep]
        show expectedHas s r w Role.admin = true
        unfold expectedHas
        by_cases hc : w = r.target ∧ Role.admin = r.role
        · simp [hc, hOp]
        · simp [hc, hw_has]
    · by_cases hRole : r.role = Role.admin
      · have hrev := hrevoke hOp
        have hOA := hrev.2 hRole
        obtain ⟨v, hv_mem, hv_ne, hv_has⟩ := hOA
        refine ⟨v, ?_, ?_⟩
        · rw [hstep]; exact hv_mem
        · rw [hstep]
          show expectedHas s r v Role.admin = true
          unfold expectedHas
          have hc : ¬ (v = r.target ∧ Role.admin = r.role) := by
            intro hc
            obtain ⟨hvu, _⟩ := hc
            exact hv_ne hvu
          simp [hc, hv_has]
      · refine ⟨w, ?_, ?_⟩
        · rw [hstep]; exact hw_mem
        · rw [hstep]
          show expectedHas s r w Role.admin = true
          unfold expectedHas
          have hc : ¬ (w = r.target ∧ Role.admin = r.role) := by
            intro hc
            obtain ⟨_, hq⟩ := hc
            exact hRole hq.symm
          simp [hc, hw_has]
  · have hstep : step s r = (.rejected, s) := by simp [step, h]
    rw [hstep]
    exact ⟨w, hw_mem, hw_has⟩

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases h : ValidCommand s r
  · have hstep : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
      simp [step, h]
    have hhas : ∀ u q, (step s r).2.has u q = expectedHas s r u q := by
      intro u q; rw [hstep]
    have hNot : ¬ ValidCommand (step s r).2 r := by
      intro h2
      have h2C := h2
      obtain ⟨_, _, _, hgrant2, hrevoke2⟩ := h2C
      have hcases : r.op = Op.grant ∨ r.op = Op.revoke := by
        cases r.op <;> simp
      rcases hcases with hOp | hOp
      · obtain ⟨_, hfalse⟩ := hgrant2 hOp
        have htrue : (step s r).2.has r.target r.role = true := by
          rw [hhas]
          unfold expectedHas
          simp [hOp]
        rw [htrue] at hfalse
        exact absurd hfalse (by decide)
      · obtain ⟨htrue2, _⟩ := hrevoke2 hOp
        have hfalse2 : (step s r).2.has r.target r.role = false := by
          rw [hhas]
          unfold expectedHas
          simp [hOp]
        rw [hfalse2] at htrue2
        exact absurd htrue2 (by decide)
    have hEq : step (step s r).2 r =
        (if ValidCommand (step s r).2 r then
          (.ok, ({ users := (step s r).2.users, has := expectedHas (step s r).2 r } : State))
        else (.rejected, (step s r).2)) := rfl
    rw [hEq, if_neg hNot]
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [h]
    rw [hrej] at hok
    exact absurd hok (by decide)

end Grants
