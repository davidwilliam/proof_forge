import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if ValidEntry s e then
      (.ok s.log.length,
       { s with
         log := s.log ++ [e],
         balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnid hvalid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none hnid
  simp [step, hnone, hvalid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnid hnot
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none hnid
  simp [step, hnone, hnot]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hrec
  simp [step, hrec]

theorem req_effects : Effects step := by
  intro s e hnid hvalid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none hnid
  simp [step, hnone, hvalid]
  constructor
  · rfl
  constructor
  · rfl
  · intro a
    by_cases ha : a = e.account
    · simp [ha]
    · simp [ha]

theorem req_append_only : AppendOnly step := by
  intro s e
  cases h : receiptOf s.log e.id with
  | some _ => exact ⟨[], by simp [step, h]⟩
  | none =>
    by_cases hv : ValidEntry s e
    · exact ⟨[e], by simp [step, h, hv]⟩
    · exact ⟨[], by simp [step, h, hv]⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  cases h : receiptOf s.log e.id with
  | some _ =>
    simp [step, h]
    exact hnodup
  | none =>
    by_cases hv : ValidEntry s e
    · have hnid : e.id ∉ ids s.log := by
        intro hin
        obtain ⟨n, hn⟩ := receiptOf_isSome hin
        rw [h] at hn
        cases hn
      simp [step, h, hv, ids_append]
      apply List.nodup_append.mpr
      refine ⟨hnodup, ?_, ?_⟩
      · simp
      · intro a ha1 ha2
        simp at ha2
        subst ha2
        exact hnid ha1
    · simp [step, h, hv]
      exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hnn a ha
  cases h : receiptOf s.log e.id with
  | some _ =>
    simp [step, h] at ha ⊢
    exact hnn a ha
  | none =>
    by_cases hv : ValidEntry s e
    · simp [step, h, hv] at ha ⊢
      have ha' : a ∈ s.accounts := by simpa using ha
      rcases hv with ⟨hacc, _, hge⟩
      by_cases haeq : a = e.account
      · subst haeq
        exact hge
      · simp [haeq]
        exact hnn a ha'
    · simp [step, h, hv] at ha ⊢
      exact hnn a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons
  cases h : receiptOf s.log e.id with
  | some _ =>
    simp [step, h]
    exact hcons
  | none =>
    by_cases hv : ValidEntry s e
    · simp [step, h, hv]
      intro a
      by_cases ha : a = e.account
      · subst ha
        have hlog : logSum (s.log ++ [e]) e.account = logSum s.log e.account + e.amount := by
          unfold logSum
          rw [sumOver_append, sumOver_cons]
          simp
        rw [hcons e.account, hlog]
      · have hlog : logSum (s.log ++ [e]) a = logSum s.log a := by
          unfold logSum
          rw [sumOver_append, sumOver_cons]
          simp [ha]
        rw [hcons a, hlog]
    · simp [step, h, hv]
      exact hcons

end EntryLog
