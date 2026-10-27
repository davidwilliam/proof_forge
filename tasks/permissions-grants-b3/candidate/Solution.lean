import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance
def isAdmin (s : State) (u : UserId) : Bool := s.users.contains u && s.has u .admin
def step : Impl := fun s r =>
  if !(s.users.contains r.actor && s.users.contains r.target) then (.rejected, s) else
  match r.op with
  | .grant =>
    if isAdmin s r.actor && !s.has r.target r.role then
      (.ok, { users := s.users, has := fun u q => if u == r.target && q == r.role then true else s.has u q })
    else (.rejected, s)
  | .revoke =>
    if isAdmin s r.actor && s.has r.target r.role &&
        (r.role != .admin || s.users.any (fun v => v != r.target && s.has v .admin)) then
      (.ok, { users := s.users, has := fun u q => if u == r.target && q == r.role then false else s.has u q })
    else (.rejected, s)
theorem req_valid_succeeds  : ValidSucceeds step := sorry
theorem req_invalid_noop    : InvalidNoop step := sorry
theorem req_authorization   : AdminOnly step := sorry
theorem req_no_self_grant   : NoSelfGrant step := sorry
theorem req_others_unchanged : OthersUnchanged step := sorry
theorem req_effects         : Effects step := sorry
theorem req_idempotency     : Idempotent step := sorry
theorem req_last_admin      : KeepsAdmin step := sorry
end Grants
