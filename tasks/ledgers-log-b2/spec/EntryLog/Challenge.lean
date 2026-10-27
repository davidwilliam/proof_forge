import EntryLog.Spec
/-!
# Locked challenge (never imports candidate code)

`EntryLog.step` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace EntryLog

def step : Impl := sorry

theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_duplicate      : DuplicateReturnsOriginal step := sorry
theorem req_effects        : Effects step := sorry
theorem req_append_only    : AppendOnly step := sorry
theorem req_unique_ids     : UniqueIds step := sorry
theorem req_nonnegative    : NonNegative step := sorry
theorem req_consistent     : StaysConsistent step := sorry

end EntryLog
