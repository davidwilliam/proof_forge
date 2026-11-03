import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance
def isAdmin (s : State) (u : UserId) : Bool := s.users.contains u && s.has u .admin
def step : Impl := fun s r =>
  if !(s.users.contains r.actor && s.users.contains r.target) then (.rejected, s) else
  match r.op with
  | .grant =>
    if isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role then
      (.ok, { users := s.users, has := fun u q => if u == r.target && q == r.role then true else s.has u q })
    else (.rejected, s)
  | .revoke =>
    if isAdmin s r.actor && s.has r.target r.role &&
        (r.role != .admin || s.users.any (fun v => v != r.target && s.has v .admin)) then
      (.ok, { users := s.users, has := fun u q => if u == r.target && q == r.role then false else s.has u q })
    else (.rejected, s)

def test_contains (s : State) (r : Request) (h : r.actor ∈ s.users) : s.users.contains r.actor = true := by
  simp_all

theorem req_valid_succeeds  : ValidSucceeds step := sorry

theorem req_invalid_noop    : InvalidNoop step := sorry

theorem req_authorization : AdminOnly step := by
  intro s r hOk
  simp [Grants.step, isAdmin] at hOk
  split at hOk
  next h => simp at hOk
  next h =>
    simp at h
    cases hOp : r.op with
    | grant =>
      simp [hOp] at hOk
      split at hOk
      next h2 => simp at hOk; exact ⟨h2.1.1.1, h2.1.1.2⟩
      next h2 => simp at hOk
    | revoke =>
      simp [hOp] at hOk
      split at hOk
      next h2 => simp at hOk; exact ⟨h2.1.1.1, h2.1.1.2⟩
      next h2 => simp at hOk

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hOk hGrant
  cases r with | mk op actor target role =>
  simp at hGrant
  subst hGrant
  simp [Grants.step] at hOk
  by_cases hcA : actor ∈ s.users
  · by_cases hcT : target ∈ s.users
    · simp [hcA, hcT] at hOk
      by_cases hCond : (isAdmin s actor = true ∧ ¬actor = target) ∧ s.has target role = false
      · exact hCond.1.2
      · simp [hCond] at hOk
    · simp [hcT] at hOk
  · simp [hcA] at hOk

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hOk u q hNe
  have hNot : ¬(u = r.target ∧ q = r.role) := by
    intro ⟨hu, hq⟩
    cases hNe with | inl h => exact h hu | inr h => exact h hq
  simp [Grants.step] at hOk ⊢
  by_cases hcA : r.actor ∈ s.users
  · by_cases hcT : r.target ∈ s.users
    · simp [hcA, hcT] at hOk ⊢
      cases hOp : r.op
      · simp [hOp] at hOk ⊢
        by_cases hc : (isAdmin s r.actor = true ∧ ¬r.actor = r.target) ∧ s.has r.target r.role = false
        · simp [hc, hNot] at hOk ⊢
        · simp [hc] at hOk
      · simp [hOp] at hOk ⊢
        by_cases hc : (isAdmin s r.actor = true ∧ s.has r.target r.role = true) ∧ (¬r.role = Role.admin ∨ ∃ x, x ∈ s.users ∧ ¬x = r.target ∧ s.has x Role.admin = true)
        · simp [hc] at hOk ⊢
          by_cases hu : u = r.target
          · by_cases hq : q = r.role
            · exact absurd ⟨hu, hq⟩ hNot
            · simp [hu, hq]
          · simp [hu]
        · simp [hc] at hOk
    · simp [hcT] at hOk
  · simp [hcA] at hOk

theorem req_effects         : Effects step := sorry

theorem req_idempotency : Idempotent step := by
  intro s r h
  cases r with | mk op actor target role =>
  cases op with
  | grant =>
    by_cases hA : actor ∈ s.users
    · by_cases hT : target ∈ s.users
      · by_cases hAd : s.has actor .admin = true
        · by_cases hNe : actor ≠ target
          · by_cases hNh : s.has target role = false
            · have hEq : step s { op := Op.grant, actor := actor, target := target, role := role } =
                (.ok, { users := s.users, has := fun u q => if u == target && q == role then true else s.has u q }) := by
                simp [Grants.step, isAdmin, hA, hT, hAd, hNe, hNh]
              rw [hEq] at h ⊢
              have hNe_beq : (actor == target) = false := by
                simp [beq_iff_eq]
                exact hNe
              simp [Grants.step, isAdmin, hA, hT, hAd, hNe, hNe_beq]
            · simp [Grants.step, isAdmin, hA, hT, hAd, hNe, hNh] at h
          · simp [Grants.step, isAdmin, hA, hT, hAd, hNe] at h
        · simp [Grants.step, isAdmin, hA, hT, hAd] at h
      · simp [Grants.step, hA, hT] at h
    · simp [Grants.step, hA] at h
  | revoke =>
    by_cases hA : actor ∈ s.users
    · by_cases hT : target ∈ s.users
      · by_cases hAd : s.has actor .admin = true
        · by_cases hHas : s.has target role = true
          · by_cases hOther : (role != .admin || s.users.any (fun v => v != target && s.has v .admin)) = true
            · have hEq : step s { op := Op.revoke, actor := actor, target := target, role := role } =
                (.ok, { users := s.users, has := fun u q => if u == target && q == role then false else s.has u q }) := by
                simp [Grants.step, isAdmin, hA, hT, hAd, hHas, hOther]
              rw [hEq] at h ⊢
              simp [Grants.step, isAdmin, hA, hT]
            · simp [Grants.step, isAdmin, hA, hT, hAd, hHas, hOther] at h
          · simp [Grants.step, isAdmin, hA, hT, hAd, hHas] at h
        · simp [Grants.step, isAdmin, hA, hT, hAd] at h
      · simp [Grants.step, hA, hT] at h
    · simp [Grants.step, hA] at h

theorem req_last_admin      : KeepsAdmin step := sorry

end Grants
