import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance
def step : Impl := fun s r =>
  if _h : ValidCommand s r then
    match r.op with
    | .grant => (.ok, { users := s.users, has := fun u q => if u = r.target ∧ q = r.role then true else s.has u q })
    | .revoke => (.ok, { users := s.users, has := fun u q => if u = r.target ∧ q = r.role then false else s.has u q })
  else (.rejected, s)

theorem req_idempotency_aux_test : True := trivial

theorem req_last_admin_aux1 : True := trivial

theorem req_last_admin_tmp2 : KeepsAdmin step := by
  intro s r hex
  obtain ⟨w, hw_mem, hw_admin⟩ := hex
  by_cases hvc : ValidCommand s r
  · have hcopy := hvc
    have ⟨h_actor_mem, h_target_mem, h_actor_admin, h_grant, h_rev⟩ := hcopy
    cases hop : r.op with
    | grant =>
      have hstep : step s r = (.ok, ({ users := s.users, has := fun u q => if u = r.target ∧ q = r.role then true else s.has u q } : State)) := by
        simp only [step, dif_pos hvc, hop]
      have husers : (step s r).2.users = s.users := by rw [hstep]
      by_cases hrole : r.role = .admin
      · refine ⟨r.target, by rw [husers]; exact h_target_mem, ?_⟩
        have hhas : (step s r).2.has r.target .admin = (if r.target = r.target ∧ (.admin : Role) = r.role then true else s.has r.target .admin) := by rw [hstep]
        have hcond : (r.target = r.target ∧ (.admin : Role) = r.role) := ⟨rfl, by rw [hrole]⟩
        rw [hhas, if_pos hcond]
      · refine ⟨w, by rw [husers]; exact hw_mem, ?_⟩
        have hhas : (step s r).2.has w .admin = (if w = r.target ∧ (.admin : Role) = r.role then true else s.has w .admin) := by rw [hstep]
        have hcond : ¬ (w = r.target ∧ (.admin : Role) = r.role) := by
          intro ⟨_, hq⟩
          exact hrole hq.symm
        rw [hhas, if_neg hcond, hw_admin]
    | revoke =>
      have hstep : step s r = (.ok, ({ users := s.users, has := fun u q => if u = r.target ∧ q = r.role then false else s.has u q } : State)) := by
        simp only [step, dif_pos hvc, hop]
      have husers : (step s r).2.users = s.users := by rw [hstep]
      have hrev := h_rev hop
      obtain ⟨htrue, hother⟩ := hrev
      by_cases hrole : r.role = .admin
      · have hOA := hother hrole
        unfold OtherAdmin at hOA
        obtain ⟨v, hv_mem, hv_ne, hv_admin⟩ := hOA
        refine ⟨v, by rw [husers]; exact hv_mem, ?_⟩
        have hhas : (step s r).2.has v .admin = (if v = r.target ∧ (.admin : Role) = r.role then false else s.has v .admin) := by rw [hstep]
        have hcond : ¬ (v = r.target ∧ (.admin : Role) = r.role) := by
          intro ⟨heq, _⟩
          exact hv_ne heq
        rw [hhas, if_neg hcond, hv_admin]
      · refine ⟨w, by rw [husers]; exact hw_mem, ?_⟩
        have hhas : (step s r).2.has w .admin = (if w = r.target ∧ (.admin : Role) = r.role then false else s.has w .admin) := by rw [hstep]
        have hcond : ¬ (w = r.target ∧ (.admin : Role) = r.role) := by
          intro ⟨_, hq⟩
          exact hrole hq.symm
        rw [hhas, if_neg hcond, hw_admin]
  · have hstep : step s r = (.rejected, s) := by simp only [step, dif_neg hvc]
    have husers : (step s r).2.users = s.users := by rw [hstep]
    have hhas : ∀ u q, (step s r).2.has u q = s.has u q := by intro u q; rw [hstep]
    refine ⟨w, by rw [husers]; exact hw_mem, ?_⟩
    rw [hhas w .admin, hw_admin]

theorem foo_test_thm : True := trivial

theorem idem_helper : ∀ s r, (step s r).1 = .ok → ¬ ValidCommand (step s r).2 r := by
  intro s r hok hvc'
  by_cases hvc : ValidCommand s r
  · have hvc0 := hvc
    obtain ⟨h_amem, h_tmem, h_aadmin, h_grant, h_rev⟩ := hvc0
    obtain ⟨h_amem', h_tmem', h_aadmin', h_grant', h_rev'⟩ := hvc'
    cases hop : r.op with
    | grant =>
      have hstep : step s r = (.ok, ({ users := s.users, has := fun u q => if u = r.target ∧ q = r.role then true else s.has u q } : State)) := by
        simp only [step, dif_pos hvc, hop]
      have h_has_new_eq : (step s r).2.has r.target r.role = (if r.target = r.target ∧ r.role = r.role then true else s.has r.target r.role) := by rw [hstep]
      have h_if : (if r.target = r.target ∧ r.role = r.role then true else s.has r.target r.role) = true := if_pos ⟨rfl, rfl⟩
      rw [h_if] at h_has_new_eq
      have hneed := (h_grant' hop).2
      rw [h_has_new_eq] at hneed
      contradiction
    | revoke =>
      have hstep : step s r = (.ok, ({ users := s.users, has := fun u q => if u = r.target ∧ q = r.role then false else s.has u q } : State)) := by
        simp only [step, dif_pos hvc, hop]
      have h_has_new_eq : (step s r).2.has r.target r.role = (if r.target = r.target ∧ r.role = r.role then false else s.has r.target r.role) := by rw [hstep]
      have h_if : (if r.target = r.target ∧ r.role = r.role then false else s.has r.target r.role) = false := if_pos ⟨rfl, rfl⟩
      rw [h_if] at h_has_new_eq
      have hneed := (h_rev' hop).1
      rw [h_has_new_eq] at hneed
      contradiction
  · have hrej : (step s r).1 = .rejected := by simp only [step, dif_neg hvc]
    rw [hrej] at hok
    contradiction

theorem req_valid_succeeds  : ValidSucceeds step := by
  intro s r h
  simp only [step, dif_pos h]
  cases r.op <;> rfl

theorem req_invalid_noop    : InvalidNoop step := by
  intro s r h
  simp only [step, dif_neg h]

theorem req_authorization   : AdminOnly step := by
  intro s r h
  by_cases hvc : ValidCommand s r
  · obtain ⟨ha, _, hadm, _, _⟩ := hvc
    exact ⟨ha, hadm⟩
  · have hrej : (step s r).1 = .rejected := by simp only [step, dif_neg hvc]
    rw [hrej] at h
    contradiction

theorem req_no_self_grant   : NoSelfGrant step := by
  intro s r h hg
  by_cases hvc : ValidCommand s r
  · obtain ⟨_, _, _, hgrant, _⟩ := hvc
    exact (hgrant hg).1
  · have hrej : (step s r).1 = .rejected := by simp only [step, dif_neg hvc]
    rw [hrej] at h
    contradiction

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hdiff
  by_cases hvc : ValidCommand s r
  · have hcond : ¬ (u = r.target ∧ q = r.role) := by
      intro ⟨hu, hq⟩
      cases hdiff with
      | inl hne => exact hne hu
      | inr hne => exact hne hq
    cases hop : r.op with
    | grant =>
      have hstep : step s r = (.ok, { users := s.users, has := fun u q => if u = r.target ∧ q = r.role then true else s.has u q }) := by
        simp only [step, dif_pos hvc, hop]
      have hhas : (step s r).2.has u q = (if u = r.target ∧ q = r.role then true else s.has u q) := by
        rw [hstep]
      rw [hhas, if_neg hcond]
    | revoke =>
      have hstep : step s r = (.ok, { users := s.users, has := fun u q => if u = r.target ∧ q = r.role then false else s.has u q }) := by
        simp only [step, dif_pos hvc, hop]
      have hhas : (step s r).2.has u q = (if u = r.target ∧ q = r.role then false else s.has u q) := by
        rw [hstep]
      rw [hhas, if_neg hcond]
  · have hrej : (step s r).1 = .rejected := by simp only [step, dif_neg hvc]
    rw [hrej] at hok
    contradiction

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hvc : ValidCommand s r
  · constructor
    · cases hop : r.op with
      | grant =>
        have hstep : step s r = (.ok, { users := s.users, has := fun u q => if u = r.target ∧ q = r.role then true else s.has u q }) := by
          simp only [step, dif_pos hvc, hop]
        have : (step s r).2.users = s.users := by rw [hstep]
        exact this
      | revoke =>
        have hstep : step s r = (.ok, { users := s.users, has := fun u q => if u = r.target ∧ q = r.role then false else s.has u q }) := by
          simp only [step, dif_pos hvc, hop]
        have : (step s r).2.users = s.users := by rw [hstep]
        exact this
    · intro u q
      cases hop : r.op with
      | grant =>
        have hstep : step s r = (.ok, { users := s.users, has := fun u q => if u = r.target ∧ q = r.role then true else s.has u q }) := by
          simp only [step, dif_pos hvc, hop]
        have hhas : (step s r).2.has u q = (if u = r.target ∧ q = r.role then true else s.has u q) := by rw [hstep]
        rw [hhas]
        unfold expectedHas
        simp only [hop]
        by_cases hcond : (u = r.target ∧ q = r.role)
        · simp [hcond]
        · simp [hcond]
      | revoke =>
        have hstep : step s r = (.ok, { users := s.users, has := fun u q => if u = r.target ∧ q = r.role then false else s.has u q }) := by
          simp only [step, dif_pos hvc, hop]
        have hhas : (step s r).2.has u q = (if u = r.target ∧ q = r.role then false else s.has u q) := by rw [hstep]
        rw [hhas]
        unfold expectedHas
        simp only [hop]
        by_cases hcond : (u = r.target ∧ q = r.role)
        · simp [hcond]
        · simp [hcond]
  · have hrej : (step s r).1 = .rejected := by simp only [step, dif_neg hvc]
    rw [hrej] at hok
    contradiction

theorem req_idempotency : Idempotent step := by
  intro s r hok
  exact req_invalid_noop _ _ (idem_helper s r hok)

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  obtain ⟨w, hw_mem, hw_admin⟩ := hex
  by_cases hvc : ValidCommand s r
  · have hcopy := hvc
    have ⟨h_actor_mem, h_target_mem, h_actor_admin, h_grant, h_rev⟩ := hcopy
    cases hop : r.op with
    | grant =>
      have hstep : step s r = (.ok, ({ users := s.users, has := fun u q => if u = r.target ∧ q = r.role then true else s.has u q } : State)) := by
        simp only [step, dif_pos hvc, hop]
      have husers : (step s r).2.users = s.users := by rw [hstep]
      by_cases hrole : r.role = .admin
      · refine ⟨r.target, by rw [husers]; exact h_target_mem, ?_⟩
        have hhas : (step s r).2.has r.target .admin = (if r.target = r.target ∧ (.admin : Role) = r.role then true else s.has r.target .admin) := by rw [hstep]
        have hcond : (r.target = r.target ∧ (.admin : Role) = r.role) := ⟨rfl, by rw [hrole]⟩
        rw [hhas, if_pos hcond]
      · refine ⟨w, by rw [husers]; exact hw_mem, ?_⟩
        have hhas : (step s r).2.has w .admin = (if w = r.target ∧ (.admin : Role) = r.role then true else s.has w .admin) := by rw [hstep]
        have hcond : ¬ (w = r.target ∧ (.admin : Role) = r.role) := by
          intro ⟨_, hq⟩
          exact hrole hq.symm
        rw [hhas, if_neg hcond, hw_admin]
    | revoke =>
      have hstep : step s r = (.ok, ({ users := s.users, has := fun u q => if u = r.target ∧ q = r.role then false else s.has u q } : State)) := by
        simp only [step, dif_pos hvc, hop]
      have husers : (step s r).2.users = s.users := by rw [hstep]
      have hrev := h_rev hop
      obtain ⟨htrue, hother⟩ := hrev
      by_cases hrole : r.role = .admin
      · have hOA := hother hrole
        unfold OtherAdmin at hOA
        obtain ⟨v, hv_mem, hv_ne, hv_admin⟩ := hOA
        refine ⟨v, by rw [husers]; exact hv_mem, ?_⟩
        have hhas : (step s r).2.has v .admin = (if v = r.target ∧ (.admin : Role) = r.role then false else s.has v .admin) := by rw [hstep]
        have hcond : ¬ (v = r.target ∧ (.admin : Role) = r.role) := by
          intro ⟨heq, _⟩
          exact hv_ne heq
        rw [hhas, if_neg hcond, hv_admin]
      · refine ⟨w, by rw [husers]; exact hw_mem, ?_⟩
        have hhas : (step s r).2.has w .admin = (if w = r.target ∧ (.admin : Role) = r.role then false else s.has w .admin) := by rw [hstep]
        have hcond : ¬ (w = r.target ∧ (.admin : Role) = r.role) := by
          intro ⟨_, hq⟩
          exact hrole hq.symm
        rw [hhas, if_neg hcond, hw_admin]
  · have hstep : step s r = (.rejected, s) := by simp only [step, dif_neg hvc]
    have husers : (step s r).2.users = s.users := by rw [hstep]
    have hhas : ∀ u q, (step s r).2.has u q = s.has u q := by intro u q; rw [hstep]
    refine ⟨w, by rw [husers]; exact hw_mem, ?_⟩
    rw [hhas w .admin, hw_admin]

end Grants
