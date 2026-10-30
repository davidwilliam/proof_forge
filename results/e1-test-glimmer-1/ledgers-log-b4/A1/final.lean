import EntryLog.Spec
import EntryLog.Lemmas
namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

/-- Acceptance check for an entry with a new ID. -/
def accepts (s : State) (e : Entry) : Bool :=
  s.accounts.contains e.account && e.amount != 0 && decide (0 ≤ s.balance e.account + e.amount)

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if accepts s e then
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnot hvalid
  unfold step
  simp [receiptOf_eq_none hnot]
  have hacc : accepts s e = true := by
    unfold accepts
    simp [hvalid.1, hvalid.2.1]
    -- hvalid.2 is e.amount ≠ 0 ∧ 0 ≤ ...
    have hle : 0 ≤ s.balance e.account + e.amount := hvalid.2.2
    simp [hle]
  simp [hacc]

theorem req_invalid_noop   : InvalidNoop step := sorry

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  simp [h]

theorem req_effects : Effects step := by
  intro s e hnot hvalid
  unfold step
  simp [receiptOf_eq_none hnot]
  have hacc : accepts s e = true := by
    unfold accepts
    simp [hvalid.1, hvalid.2.1]
    have hle : 0 ≤ s.balance e.account + e.amount := hvalid.2.2
    simp [hle]
  simp [hacc]
  -- explicit proof
  exact fun a => by
    by_cases ha : a = e.account
    · subst ha
      simp
    · simp [ha]

theorem req_append_only    : AppendOnly step := sorry

theorem req_unique_ids     : UniqueIds step := sorry

theorem req_nonnegative    : NonNegative step := sorry

theorem req_consistent     : StaysConsistent step := sorry

end EntryLog
