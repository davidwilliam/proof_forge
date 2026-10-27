import Acl.Spec
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`Acl.step` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace Acl

def step : Impl := sorry

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
