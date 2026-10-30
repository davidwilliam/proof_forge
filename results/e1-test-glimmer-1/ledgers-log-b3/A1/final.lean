import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def step (s : State) (e : Entry) : Outcome × State :=
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if ValidEntry s e then
      (.ok s.log.length,
        { s with
          log := s.log ++ [e],
          balance := fun a => s.balance a + if a = e.account then e.amount else 0 })
    else
      (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnotin hvalid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  simp [step, hnone, hvalid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnotin hinvalid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  simp [step, hnone, hinvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hrec
  simp [step, hrec]

theorem req_effects : Effects step := by
  intro s e hnotin hvalid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  simp [step, hnone, hvalid]

theorem req_append_only : AppendOnly step := by
  intro s e
  cases hrec : receiptOf s.log e.id with
  | some _ => exact ⟨[], by simp [step, hrec]⟩
  | none =>
    by_cases hvalid : ValidEntry s e
    · exact ⟨[e], by simp [step, hrec, hvalid]⟩
    · exact ⟨[], by simp [step, hrec, hvalid]⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  cases hrec : receiptOf s.log e.id with
  | some _ =>
    simp [step, hrec]
    exact hnodup
  | none =>
    by_cases hvalid : ValidEntry s e
    · have hnotin : e.id ∉ ids s.log := by
        intro hmem
        have ⟨n, hn⟩ := receiptOf_isSome hmem
        rw [hn] at hrec
        cases hrec
      simp [step, hrec, hvalid, ids_append, ids]
      apply List.nodup_append.mpr
      constructor
      · exact hnodup
      constructor
      · simp
      · intro a ha b hb
        simp at hb
        subst hb
        intro h
        rw [h] at ha
        exact hnotin ha
    · simp [step, hrec, hvalid]
      exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hnn a ha
  cases hrec : receiptOf s.log e.id with
  | some _ =>
    simp [step, hrec] at ha ⊢
    exact hnn a ha
  | none =>
    by_cases hvalid : ValidEntry s e
    · simp [step, hrec, hvalid] at ha ⊢
      have hacc : a ∈ s.accounts := by simpa using ha
      rcases hvalid with ⟨_, _, hge⟩
      by_cases h : a = e.account
      · subst h
        simpa using hge
      · simpa [h] using hnn a hacc
    · simp [step, hrec, hvalid] at ha ⊢
      exact hnn a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons a
  cases hrec : receiptOf s.log e.id with
  | some _ =>
    simp [step, hrec]
    exact hcons a
  | none =>
    by_cases hvalid : ValidEntry s e
    · simp [step, hrec, hvalid]
      have hlog : logSum (s.log ++ [e]) a = logSum s.log a + if e.account = a then e.amount else 0 := by
        unfold logSum; rw [sumOver_append]; simp
      rw [hcons a, hlog]
      by_cases h : a = e.account
      · simp [h]
      · have hsym : e.account ≠ a := by
          intro heq
          exact h (heq.symm)
        simp [h, hsym]
    · simp [step, hrec, hvalid]
      exact hcons a

end EntryLog
