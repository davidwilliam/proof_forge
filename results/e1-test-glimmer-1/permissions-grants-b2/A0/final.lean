import Grants.Spec

namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) :=
  by unfold ValidCommand OtherAdmin; infer_instance

def step : Impl := fun s r =>
  if ValidCommand s r then
    (.ok, { users := s.users, has := fun u q => expectedHas s r u q })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_authorization : AdminOnly step := by
  intro s r hok
  by_cases hv : ValidCommand s r
  · simp [step, hv] at hok
    rcases hv with ⟨hact, _, hadmin, _, _⟩
    exact ⟨hact, hadmin⟩
  · simp [step, hv] at hok

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hop
  by_cases hv : ValidCommand s r
  · simp [step, hv] at hok
    rcases hv with ⟨_, _, _, hgrant, _⟩
    exact (hgrant hop).1
  · simp [step, hv] at hok

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hneq
  by_cases hv : ValidCommand s r
  · simp [step, hv] at hok
    simp [step, hv]
    unfold expectedHas
    by_cases h : u = r.target ∧ q = r.role
    · exfalso
      rcases h with ⟨hu, hq⟩
      rcases hneq with h1 | h2
      · rw [hu] at h1; contradiction
      · rw [hq] at h2; contradiction
    · simp [h]
  · simp [step, hv] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : ValidCommand s r
  · simp [step, hv] at hok ⊢
    constructor <;> rfl
  · simp [step, hv] at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hv : ValidCommand s r
  · simp [step, hv] at hok
    simp [step, hv]
    intro hvalid
    rcases hv with ⟨_, _, _, hgrant, hrev⟩
    rcases hvalid with ⟨_, _, _, hgrant', hrev'⟩
    by_cases hop : r.op = Op.grant
    · have h1 : (fun u q => expectedHas s r u q) r.target r.role = true := by
        simp [expectedHas, hop]
      have h2 : (fun u q => expectedHas s r u q) r.target r.role = false := (hgrant' hop).2
      rw [h1] at h2; contradiction
    · have h1 : (fun u q => expectedHas s r u q) r.target r.role = false := by
        simp [expectedHas, hop]
      have h2 : (fun u q => expectedHas s r u q) r.target r.role = true := by
        have hop' : r.op = Op.revoke := by
          cases r.op; simp [hop]
        exact (hrev' hop').1
      rw [h1] at h2; contradiction
  · simp [step, hv] at hok

theorem req_last_admin : KeepsAdmin step := by
  intro s r hadmin
  by_cases hv : ValidCommand s r
  · simp [step, hv]
    rcases hv with ⟨_, _, _, hgrant, hrev⟩
    obtain ⟨u, hu_mem, hu_admin⟩ := hadmin
    by_cases hop : r.op = Op.grant
    · have hne : ¬(u = r.target ∧ Role.admin = r.role) := by
        intro h
        rcases h with ⟨hu, hq⟩
        have hfalse : s.has r.target r.role = false := (hgrant hop).2
        rw [hu.symm, hq.symm] at hfalse
        exact hfalse hu_admin
      exact ⟨u, by simp, by
        unfold expectedHas
        by_cases h : u = r.target ∧ Role.admin = r.role
        · exfalso; exact hne h
        · simp [h, hu_admin]⟩
    · have hop' : r.op = Op.revoke := by
        cases r.op; simp [hop]
      by_cases hrole : r.role = Role.admin
      · rcases (hrev hop').2 hrole with ⟨v, hv_mem, hv_ne, hv_admin⟩
        have hne : ¬(v = r.target ∧ Role.admin = r.role) := by
          intro h; rcases h with ⟨hv_eq, _⟩; exact hv_ne hv_eq
        exact ⟨v, by simp, by
          unfold expectedHas
          by_cases h : v = r.target ∧ Role.admin = r.role
          · exfalso; exact hne h
          · simp [h, hv_admin]⟩
      · have hne : ¬(u = r.target ∧ Role.admin = r.role) := by
          intro h; rcases h with ⟨hu, hq⟩; rw [hq] at hrole; exact hrole rfl
        exact ⟨u, by simp, by
          unfold expectedHas
          by_cases h : u = r.target ∧ Role.admin = r.role
          · exfalso; exact hne h
          · simp [h, hu_admin]⟩
  · simp [step, hv]
    exact hadmin

end Grants
