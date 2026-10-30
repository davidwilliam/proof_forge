import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (Outcome.ok n, s)
  | none =>
    if h : ValidEntry s e then
      (Outcome.ok s.log.length,
       { s with
         log := s.log ++ [e],
         balance := fun a => s.balance a + if a = e.account then e.amount else 0 })
    else
      (Outcome.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnid hvalid
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hnid
  simp [step, hr]
  rw [if_pos hvalid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnid hnot
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hnid
  simp [step, hr]
  rw [if_neg hnot]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hrec
  simp [step, hrec]

theorem req_effects : Effects step := by
  intro s e hnid hvalid
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hnid
  simp [step, hr]
  rw [if_pos hvalid]
  constructor
  · rfl
  · rfl
  · intro a; rfl

theorem req_append_only : AppendOnly step := by
  intro s e
  cases r : receiptOf s.log e.id
  · simp [step]
    exact ⟨[], rfl⟩
  · simp [step]
    split
    · exact ⟨[e], rfl⟩
    · exact ⟨[], rfl⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  cases r : receiptOf s.log e.id
  · simp [step]
    exact hnodup
  · simp [step]
    split
    · have hnid : e.id ∉ ids s.log := by
        intro hmem
        have ⟨n, hn⟩ := receiptOf_isSome hmem
        have : r = some n := by
          have : receiptOf s.log e.id = some n := hn
          rfl
        cases r
      rw [ids_append]
      exact List.Nodup.append hnodup (by simp [List.Nodup.cons, hnid])
    · exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hnn a ha
  cases r : receiptOf s.log e.id
  · simp [step] at ha ⊢
    exact hnn a ha
  · simp [step] at ha ⊢
    split at ha ⊢
    · have ha' : a ∈ s.accounts := by simpa using ha
      by_cases heq : a = e.account
      · subst heq
        simp at *
        exact (ValidEntry.mp ‹ValidEntry s e›).2.2
      · simp [heq]
        exact hnn a ha'
    · have ha' : a ∈ s.accounts := by simpa using ha
      exact hnn a ha'

theorem req_consistent : StaysConsistent step := by
  intro s e hcons
  cases r : receiptOf s.log e.id
  · simp [step]
    exact hcons
  · simp [step]
    split
    · intro a
      have hlog : logSum (s.log ++ [e]) a =
          logSum s.log a + if a = e.account then e.amount else 0 := by
        unfold logSum
        rw [sumOver_append]
        simp [sumOver_cons, sumOver_nil]
      rw [hcons a, hlog]
    · exact hcons

end EntryLog
