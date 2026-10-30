import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance
def step : Impl := fun s r =>
  if ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds step
  intro s r h
  simp [h]

theorem req_invalid_noop    : InvalidNoop step := by
  unfold InvalidNoop step
  intro s r h
  simp [h]

theorem req_authorization : AdminOnly step := by
  unfold AdminOnly step
  intro s r h
  by_cases hvc : ValidCommand s r
  · have h1 := hvc.1
    have h2 := hvc.2.2.1
    exact ⟨h1, h2⟩
  · simp [hvc] at h

theorem req_no_self_grant   : NoSelfGrant step := by
  unfold NoSelfGrant step
  intro s r hOk hGrant
  by_cases hvc : ValidCommand s r
  · have hP := hvc.2.2.2.1
    have hGr : r.op = Op.grant := hGrant
    have hneq := hP hGr
    exact hneq.1
  · simp [hvc] at hOk

theorem req_others_unchanged : OthersUnchanged step := by
  unfold OthersUnchanged step
  intro s r hOk u q h
  by_cases hvc : ValidCommand s r
  · simp only [hvc, ↓reduceIte] at hOk ⊢
    simp only [expectedHas]
    have hcond : ¬ (u = r.target ∧ q = r.role) := by
      intro hconj
      have : u ≠ r.target ∨ q ≠ r.role := h
      rcases h with h1 | h2
      · exact h1 hconj.1
      · exact h2 hconj.2
    simp [hcond]
  · simp [hvc] at hOk

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hOk
  unfold step at hOk ⊢
  by_cases hvc : ValidCommand s r
  · simp only [hvc, ↓reduceIte] at hOk ⊢
    constructor
    · trivial
    · intro u q; trivial
  · simp [hvc] at hOk

theorem req_idempotency : Idempotent step := by
  unfold Idempotent
  intro s r hOk
  have hValid : ValidCommand s r := by
    by_cases h : ValidCommand s r
    · exact h
    · unfold step at hOk; simp [h] at hOk
  have hNot : ¬ ValidCommand ({ users := s.users, has := expectedHas s r } : State) r := by
    intro hV'
    have hExp : expectedHas s r r.target r.role = decide (r.op = .grant) := by unfold expectedHas; simp
    cases hOp : r.op with
    | grant =>
      have h2 : (expectedHas s r r.target r.role) = false := (hV'.2.2.2.1 hOp).2
      rw [hExp] at h2
      simp [hOp] at h2
    | revoke =>
      have h2 : (expectedHas s r r.target r.role) = true := (hV'.2.2.2.2 hOp).1
      rw [hExp] at h2
      simp [hOp] at h2
  have hStepEq : step s r = (Outcome.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
    unfold step; simp [hValid]
  rw [hStepEq]
  unfold step
  simp [hNot]

theorem req_last_admin      : KeepsAdmin step := by
  unfold KeepsAdmin step
  intro s r hex
  by_cases hvc : ValidCommand s r
  · simp only [hvc, ↓reduceIte]
    cases hOp : r.op with
    | grant =>
      obtain ⟨w, hwmem, hwadmin⟩ := hex
      refine ⟨w, hwmem, ?_⟩
      have hNe : ¬ (w = r.target ∧ (Role.admin : Role) = r.role) ∨ (w = r.target ∧ (Role.admin : Role) = r.role) := by
        by_cases h : w = r.target ∧ (Role.admin : Role) = r.role
        · exact Or.inr h
        · exact Or.inl h
      by_cases h : w = r.target ∧ (Role.admin : Role) = r.role
      · simp [expectedHas, h, hOp]
      · simp [expectedHas, h, hwadmin]
    | revoke =>
      by_cases hRole : r.role = Role.admin
      · have hOther : OtherAdmin s r.target := (hvc.2.2.2.2 hOp).2 hRole
        obtain ⟨v, hvMem, hvNe, hvAdmin⟩ := hOther
        refine ⟨v, hvMem, ?_⟩
        have hNe : ¬ (v = r.target ∧ (Role.admin : Role) = r.role) := by
          intro hconj
          exact hvNe hconj.1
        simp [expectedHas, hNe, hvAdmin]
      · obtain ⟨w, hwmem, hwadmin⟩ := hex
        refine ⟨w, hwmem, ?_⟩
        have hNe : ¬ (w = r.target ∧ (Role.admin : Role) = r.role) := by
          intro hconj
          exact hRole hconj.2.symm
        simp [expectedHas, hNe, hwadmin]
  · simp only [hvc, ↓reduceIte]
    exact hex

end Grants
