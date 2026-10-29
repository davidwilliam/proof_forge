import Workflow.Spec

namespace Workflow

-- Placeholder body; replace it with an implementation that meets the spec.
def step : Impl := fun s _ => (Outcome.rejected, s)

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
