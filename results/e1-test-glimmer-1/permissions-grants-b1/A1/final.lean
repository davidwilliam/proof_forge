import Grants.Spec
namespace Grants

def step : Impl := fun s r =>
  if !(s.users.contains r.actor && s.users.contains r.target) then (.rejected, s) else
  if !s.has r.actor .admin then (.rejected, s) else
  match r.op with
  | .grant =>
    if r.actor != r.target && !s.has r.target r.role then
      (.ok, { users := s.users, has := fun u q => if u == r.target && q == r.role then true else s.has u q })
    else (.rejected, s)
  | .revoke =>
    let otherAdmin := s.users.any (fun v => v != r.target && s.has v .admin)
    if s.has r.target r.role && (r.role != .admin || otherAdmin) then
      (.ok, { users := s.users, has := fun u q => if u == r.target && q == r.role then false else s.has u q })
    else (.rejected, s)

theorem req_valid_succeeds  : ValidSucceeds step := sorry

theorem req_invalid_noop    : InvalidNoop step := sorry

theorem req_authorization : AdminOnly step := by
  intro s r hok
  unfold step at hok
  simp at hok
  have h1 : ¬(¬r.actor ∈ s.users ∨ ¬r.target ∈ s.users) := by
    intro h
    simp [h] at hok
  have hmem_actor : r.actor ∈ s.users := by
    have : ¬ ¬r.actor ∈ s.users := by
      intro hneg
      apply h1
      left; exact hneg
    simp at this
    exact this
  have hmem_target : r.target ∈ s.users := by
    have : ¬ ¬r.target ∈ s.users := by
      intro hneg
      apply h1
      right; exact hneg
    simp at this
    exact this
  have h2 : ¬(s.has r.actor Role.admin = false) := by
    intro h
    simp [h1, h] at hok
  have hadmin : s.has r.actor Role.admin = true := by
    cases h : s.has r.actor Role.admin
    · exfalso
      apply h2
      exact h
    · rfl
  exact ⟨hmem_actor, hadmin⟩

theorem req_no_self_grant   : NoSelfGrant step := sorry

theorem req_others_unchanged : OthersUnchanged step := sorry

theorem req_effects         : Effects step := sorry

theorem req_idempotency     : Idempotent step := sorry

theorem req_last_admin      : KeepsAdmin step := sorry

end Grants
