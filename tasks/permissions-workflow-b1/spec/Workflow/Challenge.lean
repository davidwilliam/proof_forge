import Workflow.Spec
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`Workflow.step` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace Workflow

def step : Impl := sorry

theorem req_valid_succeeds       : ValidSucceeds step := sorry
theorem req_invalid_noop         : InvalidNoop step := sorry
theorem req_authorization        : Authorized step := sorry
theorem req_single_doc           : SingleDoc step := sorry
theorem req_published_immutable  : PublishedImmutable step := sorry
theorem req_no_unpublish         : NoUnpublish step := sorry
theorem req_effects              : Effects step := sorry
theorem req_audit_append_only    : AuditAppendOnly step := sorry
theorem req_audit_consistent     : KeepsAuditConsistent step := sorry

end Workflow
