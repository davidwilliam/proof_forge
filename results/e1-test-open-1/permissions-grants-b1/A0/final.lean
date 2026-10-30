import Grants.Spec
namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin
  infer_instance

def step : Impl := fun s r =>
  if _ : ValidCommand s r then (.ok, { users := s.users, has := expectedHas s r }) else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [ValidSucceeds, step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [InvalidNoop, step, h]

theorem req_authorization : AdminOnly step := by
  intro s r h
  unfold step at h
  split at h
  · next hv =>
    exact ⟨hv.1, hv.2.2.1⟩
  · next _ => simp at h

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r h hg
  have hv : ValidCommand s r := by
    unfold step at h
    split at h
    · assumption
    · simp at h
  exact hv.2.2.2.1 hg |>.1

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r h u q hu
  have hv : ValidCommand s r := by
    unfold step at h; split at h; assumption; simp at h
  unfold step
  simp [hv]
  unfold expectedHas
  have hcond : ¬(u = r.target ∧ q = r.role) := by
    intro ⟨e1, e2⟩
    subst e1; subst e2
    simp at hu
  simp [hcond]

theorem req_effects : Effects step := by
  intro s r h
  have hv : ValidCommand s r := by
    unfold step at h; split at h; assumption; simp at h
  unfold step
  simp [hv]

theorem req_idempotency : Idempotent step := by
  intro s r h
  have hv : ValidCommand s r := by
    unfold step at h; split at h; assumption; simp at h
  have h_eq : (step s r).2 = { users := s.users, has := expectedHas s r } := by
    unfold step; simp [hv]
  rw [h_eq]
  have h2 : ¬ ValidCommand { users := s.users, has := expectedHas s r } r := by
    intro hc
    cases hop : r.op with
    | grant =>
      have hgrant := hc.2.2.2.1 hop
      unfold expectedHas at hgrant
      simp [hop] at hgrant
    | revoke =>
      have hrev := hc.2.2.2.2 hop
      have hhas := hrev.1
      unfold expectedHas at hhas
      simp [hop] at hhas
  unfold step
  simp [h2]

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  unfold step
  split
  · next hv =>
    simp
    cases hop : r.op with
    | grant =>
      obtain ⟨u, hu_mem, hu_admin⟩ := hex
      refine ⟨u, hu_mem, ?_⟩
      unfold expectedHas
      by_cases heq : u = r.target ∧ Role.admin = r.role
      · obtain ⟨e1, e2⟩ := heq
        simp [e1, e2, hop]
      · simp [heq, hu_admin]
    | revoke =>
      by_cases hrole : r.role = .admin
      · have hrev := hv.2.2.2.2 hop
        have hother := hrev.2 hrole
        obtain ⟨v, hv_mem, hv_ne, hv_admin⟩ := hother
        refine ⟨v, hv_mem, ?_⟩
        unfold expectedHas
        have hneq : ¬(v = r.target ∧ Role.admin = r.role) := by
          intro ⟨e1, e2⟩
          subst e1
          exact hv_ne rfl
        simp [hneq, hv_admin]
      · obtain ⟨u, hu_mem, hu_admin⟩ := hex
        refine ⟨u, hu_mem, ?_⟩
        unfold expectedHas
        have hneq : ¬(u = r.target ∧ Role.admin = r.role) := by
          intro ⟨e1, e2⟩
          exact hrole e2.symm
        simp [hneq, hu_admin]
  · next _ =>
    simp
    exact hex

end Grants
