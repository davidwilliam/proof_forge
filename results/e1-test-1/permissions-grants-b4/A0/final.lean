import Grants.Spec
namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance

def step : Impl := fun s r =>
  if ValidCommand s r then
    (.ok, { users := s.users, has := fun u q => expectedHas s r u q })
  else
    (.rejected, s)

private theorem valid_of_ok' (s : State) (r : Request) (h : (step s r).1 = .ok) : ValidCommand s r := by
  by_cases hv : ValidCommand s r
  case pos => exact hv
  case neg =>
    have hstep : step s r = (.rejected, s) := by unfold step; simp [hv]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    have heq : Outcome.ok = Outcome.rejected := h.symm.trans h1
    have hne : Outcome.ok ≠ Outcome.rejected := by decide
    exact absurd heq hne

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : AdminOnly step := by
  unfold AdminOnly
  intro s r hok
  have hv : ValidCommand s r := valid_of_ok' s r hok
  unfold ValidCommand at hv
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  exact ⟨h1, h3⟩

theorem req_no_self_grant : NoSelfGrant step := by
  unfold NoSelfGrant
  intro s r hok hop
  have hv : ValidCommand s r := valid_of_ok' s r hok
  unfold ValidCommand at hv
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  have hc := h4 hop
  exact hc.1

theorem req_others_unchanged : OthersUnchanged step := by
  unfold OthersUnchanged
  intro s r hok u q hneq
  have hv : ValidCommand s r := valid_of_ok' s r hok
  have h_has : (step s r).2.has u q = expectedHas s r u q := by unfold step; simp [hv]
  rw [h_has]
  have hcond : ¬ (u = r.target ∧ q = r.role) := by
    intro hcon
    cases hneq with
    | inl h => exact h hcon.1
    | inr h => exact h hcon.2
  unfold expectedHas
  rw [if_neg hcond]

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hok
  have hv : ValidCommand s r := valid_of_ok' s r hok
  constructor
  · unfold step; simp [hv]
  · intro u q
    have h_has : (step s r).2.has u q = expectedHas s r u q := by unfold step; simp [hv]
    exact h_has

theorem req_idempotency : Idempotent step := by
  unfold Idempotent
  intro s r hok
  have hv : ValidCommand s r := valid_of_ok' s r hok
  have hstep_eq : step s r = (.ok, { users := s.users, has := fun u q => expectedHas s r u q }) := by
    unfold step; simp [hv]
  have h_has : ∀ u q, (step s r).2.has u q = expectedHas s r u q := fun u q => by rw [hstep_eq]
  have h_target : (step s r).2.has r.target r.role = decide (r.op = .grant) := by
    rw [h_has]
    unfold expectedHas
    rw [if_pos]
    exact ⟨rfl, rfl⟩
  have hn2 : ¬ ValidCommand (step s r).2 r := by
    intro hc
    unfold ValidCommand at hv hc
    obtain ⟨ha1, ht1, had1, hg1, hr1⟩ := hv
    obtain ⟨ha2, ht2, had2, hg2, hr2⟩ := hc
    have hop_cases : r.op = .grant ∨ r.op = .revoke := by
      cases h_op : r.op with
      | grant => exact Or.inl rfl
      | revoke => exact Or.inr rfl
    cases hop_cases with
    | inl hopg =>
      have hcon := hg2 hopg
      rw [h_target, hopg] at hcon
      simp at hcon
    | inr hopr =>
      have hcon := hr2 hopr
      rw [h_target, hopr] at hcon
      simp at hcon
  have h_outer_def : step ((step s r).2) r =
      (if ValidCommand ((step s r).2) r then
        (.ok, { users := ((step s r).2).users, has := fun u qq => expectedHas ((step s r).2) r u qq })
       else (.rejected, (step s r).2)) := rfl
  rw [h_outer_def, if_neg hn2]

theorem req_last_admin : KeepsAdmin step := by
  unfold KeepsAdmin
  intro s r hex
  obtain ⟨u, hu_mem, hu_admin⟩ := hex
  by_cases hv : ValidCommand s r
  case pos =>
    have h_users : (step s r).2.users = s.users := by unfold step; simp [hv]
    have h_has : ∀ w q, (step s r).2.has w q = expectedHas s r w q := fun w q => by
      unfold step; simp [hv]
    have hv0 : ValidCommand s r := hv
    unfold ValidCommand at hv0
    obtain ⟨hAmem, hTmem, hAadmin, hGrant, hRevoke⟩ := hv0
    by_cases htr : (r.op = .revoke ∧ r.role = .admin ∧ u = r.target)
    case pos =>
      obtain ⟨hop_rev, hrole_admin, hu_eq⟩ := htr
      have hrev := hRevoke hop_rev
      have h_other := hrev.2 hrole_admin
      unfold OtherAdmin at h_other
      obtain ⟨v, hv_mem, hv_ne, hv_admin⟩ := h_other
      refine ⟨v, ?_, ?_⟩
      · rw [h_users]; exact hv_mem
      · rw [h_has]
        have hCneg : ¬ (v = r.target ∧ Role.admin = r.role) := by
          intro hcon
          exact hv_ne hcon.1
        unfold expectedHas
        rw [if_neg hCneg]
        exact hv_admin
    case neg =>
      have hcond_imp_grant : (u = r.target ∧ Role.admin = r.role) → r.op = .grant := by
        intro hcon
        obtain ⟨hu_eq, hrole_eq⟩ := hcon
        have hrole_sym : r.role = .admin := Eq.symm hrole_eq
        have hdisj : r.op = .grant ∨ r.op = .revoke := by
          cases r.op
          case grant => exact Or.inl rfl
          case revoke => exact Or.inr rfl
        cases hdisj with
        | inl h => exact h
        | inr h => exact absurd ⟨h, hrole_sym, hu_eq⟩ htr
      have h_final : expectedHas s r u Role.admin = true := by
        unfold expectedHas
        by_cases hC : (u = r.target ∧ Role.admin = r.role)
        case pos =>
          have hg := hcond_imp_grant hC
          simp [hC, hg]
        case neg =>
          simp [hC, hu_admin]
      refine ⟨u, ?_, ?_⟩
      · rw [h_users]; exact hu_mem
      · rw [h_has]; exact h_final
  case neg =>
    have h_users : (step s r).2.users = s.users := by unfold step; simp [hv]
    have h_has2 : ∀ w q, (step s r).2.has w q = s.has w q := fun w q => by
      unfold step; simp [hv]
    refine ⟨u, ?_, ?_⟩
    · rw [h_users]; exact hu_mem
    · rw [h_has2]; exact hu_admin

end Grants
