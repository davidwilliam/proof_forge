import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

-- Placeholder body; replace it with an implementation that meets the spec.
def step : Impl := fun s _ => (Outcome.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_duplicate      : DuplicateReturnsOriginal step := sorry
theorem req_effects        : Effects step := sorry
theorem req_append_only    : AppendOnly step := sorry
theorem req_unique_ids     : UniqueIds step := sorry
theorem req_nonnegative    : NonNegative step := sorry
theorem req_consistent     : StaysConsistent step := sorry

end EntryLog
