import Grants.Spec
namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin
  infer_instance

def validB (s : State) (r : Request) : Bool := decide (ValidCommand s r)

theorem validB_iff (s : State) (r : Request) : ValidCommand s r ↔ validB s r = true := by
  simp [validB]

def step : Impl := fun s r =>
  if validB s r then (.ok, { users := s.users, has := expectedHas s r }) else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hV
  have hv : validB s r = true := (validB_iff s r).mp hV
  show (step s r).1 = .ok
  simp [step, hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hN
  have hv : validB s r = false := by
    cases hb : validB s r with
    | true => have hV : ValidCommand s r := (validB_iff s r).mpr hb; exact absurd hV hN
    | false => rfl
  show step s r = (.rejected, s)
  simp [step, hv]

theorem req_authorization : AdminOnly step := by
  intro s r hOk
  have hv : validB s r = true := by
    cases hb : validB s r with
    | true => rfl
    | false => simp [step, hb] at hOk
  have hV : ValidCommand s r := (validB_iff s r).mpr hv
  exact ⟨hV.1, hV.2.2.1⟩

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hOk hop
  have hv : validB s r = true := by
    cases hb : validB s r with
    | true => rfl
    | false => simp [step, hb] at hOk
  have hV : ValidCommand s r := (validB_iff s r).mpr hv
  exact (hV.2.2.2.1 hop).1

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hOk u q hNe
  have hv : validB s r = true := by
    cases hb : validB s r with
    | true => rfl
    | false => simp [step, hb] at hOk
  have hStep : (step s r).2.has u q = expectedHas s r u q := by simp [step, hv]
  rw [hStep]
  unfold expectedHas
  have hCondFalse : ¬(u = r.target ∧ q = r.role) := by
    intro hConj
    cases hNe with
    | inl h => exact h hConj.1
    | inr h => exact h hConj.2
  simp [hCondFalse]

theorem req_effects : Effects step := by
  intro s r hOk
  have hv : validB s r = true := by
    cases hb : validB s r with
    | true => rfl
    | false => simp [step, hb] at hOk
  have h1 : (step s r).2.users = s.users := by simp [step, hv]
  have h2 : ∀ u q, (step s r).2.has u q = expectedHas s r u q := by intro u q; simp [step, hv]
  exact ⟨h1, h2⟩

theorem req_idempotency : Idempotent step := by
  intro s r hOk
  have hv : validB s r = true := by
    cases hb : validB s r with
    | true => rfl
    | false => simp [step, hb] at hOk
  have hStepEq : (step s r).2 = { users := s.users, has := expectedHas s r } := by simp [step, hv]
  let s' : State := { users := s.users, has := expectedHas s r }
  have hEq : (step s r).2 = s' := hStepEq
  rw [hEq]
  have hV : ValidCommand s r := (validB_iff s r).mpr hv
  have hValidBFalse : validB s' r = false := by
    apply Decidable.byContradiction
    intro hNotFalse
    have hNotFalse' : validB s' r = true := by cases hb : validB s' r with | true => rfl | false => contradiction
    have hV' : ValidCommand s' r := (validB_iff s' r).mpr hNotFalse'
    cases hop : r.op with
    | grant =>
      have hHadNot : s.has r.target r.role = false := (hV.2.2.2.1 hop).2
      have hHasNow : s'.has r.target r.role = true := by simp [s', expectedHas, hop]
      have hNeedFalse : s'.has r.target r.role = false := (hV'.2.2.2.1 hop).2
      rw [hHasNow] at hNeedFalse
      contradiction
    | revoke =>
      have hHasNow : s'.has r.target r.role = false := by simp [s', expectedHas, hop]
      have hNeedTrue : s'.has r.target r.role = true := (hV'.2.2.2.2 hop).1
      rw [hHasNow] at hNeedTrue
      contradiction
  show step s' r = (.rejected, s')
  simp [step, hValidBFalse]

theorem req_last_admin : KeepsAdmin step := by
  intro s r hEx
  by_cases hv : validB s r = true
  · have hV : ValidCommand s r := (validB_iff s r).mpr hv
    have hs : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by simp [step, hv]
    have hStepUsers : (step s r).2.users = s.users := by simp [hs]
    have hStepHas : ∀ u q, (step s r).2.has u q = expectedHas s r u q := by intro u q; simp [hs]
    rcases hEx with ⟨w, hwMem, hwAdmin⟩
    cases hop : r.op with
    | grant =>
      refine ⟨w, ?_, ?_⟩
      · rw [hStepUsers]; exact hwMem
      · rw [hStepHas]
        show expectedHas s r w .admin = true
        unfold expectedHas
        by_cases hCond : w = r.target ∧ (Role.admin : Role) = r.role
        · simp [hCond, hop]
        · simp [hCond, hwAdmin]
    | revoke =>
      by_cases hRoleAdmin : r.role = .admin
      · have hOther : OtherAdmin s r.target := (hV.2.2.2.2 hop).2 hRoleAdmin
        rcases hOther with ⟨v, hvMem, hvNe, hvAdmin⟩
        refine ⟨v, ?_, ?_⟩
        · rw [hStepUsers]; exact hvMem
        · rw [hStepHas]
          show expectedHas s r v .admin = true
          have hCondV : ¬(v = r.target ∧ (Role.admin : Role) = r.role) := by
            intro hC
            exact hvNe hC.1
          simp [expectedHas, hCondV, hvAdmin]
      · refine ⟨w, ?_, ?_⟩
        · rw [hStepUsers]; exact hwMem
        · rw [hStepHas]
          show expectedHas s r w .admin = true
          have hCond : ¬(w = r.target ∧ (Role.admin : Role) = r.role) := by
            intro hC
            have : r.role = .admin := hC.2.symm
            contradiction
          simp [expectedHas, hCond, hwAdmin]
  · have hFalse : validB s r = false := by cases hb : validB s r with | true => contradiction | false => rfl
    have hs : step s r = (.rejected, s) := by simp [step, hFalse]
    rw [hs]
    exact hEx

end Grants
