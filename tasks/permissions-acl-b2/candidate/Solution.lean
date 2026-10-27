import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance
def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def decision (l : List Entry) (r : Request) : Bool :=
  let ms := l.filter (matchesB · r)
  ms.any (·.effect == .allow) && !ms.any (·.effect == .deny)

def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := decision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)
theorem req_valid_answered     : ValidAnswered step := sorry
theorem req_invalid_noop       : InvalidNoop step := sorry
theorem req_effects            : Effects step := sorry
theorem req_default_deny       : DefaultDeny step := sorry
theorem req_deny_overrides     : DenyOverrides step := sorry
theorem req_specific_allow     : SpecificAllow step := sorry
theorem req_grant_justified    : GrantJustified step := sorry
theorem req_order_independent  : OrderIndependent step := sorry
theorem req_denial_explained   : DenialExplained step := sorry
end Acl
