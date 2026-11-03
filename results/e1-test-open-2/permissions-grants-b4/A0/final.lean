import Grants.Spec
namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance

def step : Impl := fun s r =>
  if _h : ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

private theorem step_ok_iff (s : State) (r : Request) : (step s r).1 = .ok ↔ ValidCommand s r := by
  unfold step
  by_cases h : ValidCommand s r <;> simp [h]

private theorem step_eq_ok_branch (s : State) (r : Request) (h : ValidCommand s r) :
    step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
  unfold step; simp [h]

private theorem step_eq_rejected_branch (s : State) (r : Request) (h : ¬ValidCommand s r) :
    step s r = (.rejected, s) := by
  unfold step; simp [h]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hv
  have := step_eq_ok_branch s r hv
  simp [this]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hn
  exact step_eq_rejected_branch s r hn

theorem req_authorization : AdminOnly step := by
  intro s r hok
  have hv : ValidCommand s r := (step_ok_iff s r).mp hok
  unfold ValidCommand at hv
  rcases hv with ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h1, h3⟩

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hgrant
  have hv : ValidCommand s r := (step_ok_iff s r).mp hok
  unfold ValidCommand at hv
  rcases hv with ⟨h1, h2, h3, h4, h5⟩
  exact (h4 hgrant).1

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hneq
  have hv : ValidCommand s r := (step_ok_iff s r).mp hok
  have heq := step_eq_ok_branch s r hv
  have husers : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by
    simp [heq]
  have hhas : (step s r).2.has u q = (expectedHas s r u q) := by
    simp [husers]
  rw [hhas]
  unfold expectedHas
  have hcond : ¬(u = r.target ∧ q = r.role) := by
    intro h
    rcases h with ⟨hu, hq⟩
    rcases hneq with h1 | h1
    · exact h1 hu
    · exact h1 hq
  simp [hcond]

theorem req_effects : Effects step := by
  intro s r hok
  have hv : ValidCommand s r := (step_ok_iff s r).mp hok
  have heq := step_eq_ok_branch s r hv
  constructor
  · simp [heq]
  · intro u q
    have hhas : (step s r).2.has u q = expectedHas s r u q := by
      simp [heq]
    exact hhas

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv : ValidCommand s r := (step_ok_iff s r).mp hok
  have heq := step_eq_ok_branch s r hv
  have hs' : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by
    simp [heq]
  have hnot : ¬ValidCommand ({ users := s.users, has := expectedHas s r } : State) r := by
    intro h
    unfold ValidCommand at hv h
    rcases hv with ⟨hA1, hT1, hadm1, hg1, hr1⟩
    rcases h with ⟨hA2, hT2, hadm2, hg2, hr2⟩
    cases hop : r.op with
    | grant =>
      have hg2' := hg2 hop
      have h_has : (expectedHas s r r.target r.role) = true := by
        unfold expectedHas; simp [hop]
      have h1 : (expectedHas s r r.target r.role) = false := hg2'.2
      rw [h_has] at h1
      contradiction
    | revoke =>
      have h_has : (expectedHas s r r.target r.role) = false := by
        unfold expectedHas; simp [hop]
      have h1 : (expectedHas s r r.target r.role) = true := (hr2 hop).1
      rw [h_has] at h1
      contradiction
  have hstep' : step ({ users := s.users, has := expectedHas s r } : State) r = (.rejected, ({ users := s.users, has := expectedHas s r } : State)) :=
    step_eq_rejected_branch _ r hnot
  rw [hs', hstep']

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  by_cases hv : ValidCommand s r
  · have heq := step_eq_ok_branch s r hv
    have husers : (step s r).2.users = s.users := by simp [heq]
    cases hop : r.op with
    | grant =>
      rcases hex with ⟨u, hu, hadm⟩
      refine ⟨u, ?_, ?_⟩
      · rw [husers]; exact hu
      · have hhas : (step s r).2.has u .admin = expectedHas s r u .admin := by simp [heq]
        rw [hhas]
        unfold expectedHas
        by_cases hcond : u = r.target ∧ (Role.admin = r.role)
        · have _hrole_eq : Role.admin = r.role := hcond.2
          simp [hcond, hop]
        · simp [hcond, hadm]
    | revoke =>
      by_cases hrole : r.role = .admin
      · unfold ValidCommand at hv
        rcases hv with ⟨h1, h2, h3, h4, h5⟩
        have hother : OtherAdmin s r.target := (h5 hop).2 hrole
        rcases hother with ⟨v, hv_mem, hv_neq, hv_adm⟩
        refine ⟨v, ?_, ?_⟩
        · rw [husers]; exact hv_mem
        · have hhas : (step s r).2.has v .admin = expectedHas s r v .admin := by simp [heq]
          rw [hhas]
          unfold expectedHas
          have hcond : ¬(v = r.target ∧ Role.admin = r.role) := by
            intro h
            exact hv_neq h.1
          simp [hcond, hv_adm]
      · rcases hex with ⟨u, hu, hadm⟩
        refine ⟨u, ?_, ?_⟩
        · rw [husers]; exact hu
        · have hhas : (step s r).2.has u .admin = expectedHas s r u .admin := by simp [heq]
          rw [hhas]
          unfold expectedHas
          by_cases hcond : u = r.target ∧ Role.admin = r.role
          · exfalso; exact hrole hcond.2.symm
          · simp [hcond, hadm]
  · have heq := step_eq_rejected_branch s r hv
    rcases hex with ⟨u, hu, hadm⟩
    refine ⟨u, ?_, ?_⟩
    · simp [heq, hu]
    · simp [heq, hadm]

end Grants
