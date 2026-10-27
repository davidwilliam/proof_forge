import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance
def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

/-- Depth of the most specific matching entry with effect `eff`. -/
def best (eff : Effect) (r : Request) (l : List Entry) : Option Nat :=
  (l.filter (fun e => matchesB e r && e.effect == eff)).foldl
    (fun m e => some (max (m.getD 0) (depth e))) none

def decision (l : List Entry) (r : Request) : Bool :=
  match best .allow r l, best .deny r l with
  | some _, none => true
  | some a, some d => d ≤ a
  | none, _ => false

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
