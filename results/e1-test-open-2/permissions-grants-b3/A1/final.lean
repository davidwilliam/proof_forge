import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance
def isAdmin (s : State) (u : UserId) : Bool := s.users.contains u && s.has u .admin
def step : Impl := fun s r =>
  if !(s.users.contains r.actor && s.users.contains r.target) then (.rejected, s) else
  match r.op with
  | .grant =>
    if isAdmin s r.actor && decide (r.actor ≠ r.target) && !s.has r.target r.role then
      (.ok, { users := s.users, has := fun u q => if u == r.target && q == r.role then true else s.has u q })
    else (.rejected, s)
  | .revoke =>
    if isAdmin s r.actor && s.has r.target r.role &&
        (r.role != .admin || s.users.any (fun v => v != r.target && s.has v .admin)) then
      (.ok, { users := s.users, has := fun u q => if u == r.target && q == r.role then false else s.has u q })
    else (.rejected, s)

theorem req_valid_succeeds  : ValidSucceeds step := by
  intro s r hV
  obtain ⟨hmemA, hmemT, hIsAdmin, hGrant, hRevoke⟩ := hV
  unfold step
  have h1 : (s.users.contains r.actor && s.users.contains r.target) = true := by
    simp [hmemA, hmemT]
  simp only [h1]
  cases hOp : r.op with
  | grant =>
    have hNe : r.actor ≠ r.target := (hGrant hOp).1
    have hNotHas : s.has r.target r.role = false := (hGrant hOp).2
    have hIsAdminBool : isAdmin s r.actor = true := by
      unfold isAdmin
      simp [hmemA, hIsAdmin]
    have hNeBool : decide (r.actor ≠ r.target) = true := by simp [hNe]
    have hNotHasBool : (!s.has r.target r.role) = true := by simp [hNotHas]
    simp [hOp, hIsAdminBool, hNeBool, hNotHasBool]
  | revoke =>
    have hHas : s.has r.target r.role = true := (hRevoke hOp).1
    have hOther : r.role = Role.admin → OtherAdmin s r.target := fun heq => (hRevoke hOp).2 heq
    have hIsAdminBool : isAdmin s r.actor = true := by
      unfold isAdmin
      simp [hmemA, hIsAdmin]
    simp only [hOp, hIsAdminBool, hHas, Bool.true_and]
    by_cases hRole : r.role = Role.admin
    · have hOA := hOther hRole
      unfold OtherAdmin at hOA
      obtain ⟨v, hvMem, hvNe, hvAdmin⟩ := hOA
      have hAny : s.users.any (fun v => v != r.target && s.has v Role.admin) = true := by
        rw [List.any_eq_true]
        refine ⟨v, hvMem, ?_⟩
        simp [hvNe, hvAdmin]
      have hC : (r.role != Role.admin || s.users.any (fun v => v != r.target && s.has v Role.admin)) = true := by
        simp [hRole, hAny]
      simp [hC]
    · have hC : (r.role != Role.admin || s.users.any (fun v => v != r.target && s.has v Role.admin)) = true := by
        simp [hRole]
      simp [hC]

theorem req_invalid_noop    : InvalidNoop step := sorry

theorem req_authorization   : AdminOnly step := sorry

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hOk hOp
  have hOpG : r.op = Op.grant := hOp
  unfold step at hOk
  by_cases hCont : (s.users.contains r.actor && s.users.contains r.target) = true
  · simp only [hCont] at hOk
    rw [hOpG] at hOk
    simp only at hOk
    by_cases hAdmin : isAdmin s r.actor = true
    · simp only [hAdmin, Bool.true_and] at hOk
      by_cases hNe : decide (r.actor ≠ r.target) = true
      · exact of_decide_eq_true hNe
      · simp only [hNe, Bool.false_and] at hOk
        simp at hOk
    · simp only [hAdmin, Bool.false_and] at hOk
      simp at hOk
  · simp only [hCont] at hOk
    simp at hOk

theorem req_others_unchanged : OthersUnchanged step := sorry

theorem req_effects         : Effects step := sorry

theorem req_idempotency     : Idempotent step := sorry

theorem req_last_admin      : KeepsAdmin step := sorry

end Grants
