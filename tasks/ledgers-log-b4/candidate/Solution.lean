import EntryLog.Spec
import EntryLog.Lemmas
namespace EntryLog
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance
/-- Acceptance check for an entry with a new ID. -/
def accepts (s : State) (e : Entry) : Bool :=
  s.accounts.contains e.account && e.amount != 0 && decide (0 < s.balance e.account + e.amount)
def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if accepts s e then
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)
theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_duplicate      : DuplicateReturnsOriginal step := sorry
theorem req_effects        : Effects step := sorry
theorem req_append_only    : AppendOnly step := sorry
theorem req_unique_ids     : UniqueIds step := sorry
theorem req_nonnegative    : NonNegative step := sorry
theorem req_consistent     : StaysConsistent step := sorry
end EntryLog
