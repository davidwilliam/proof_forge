import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

instance (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
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
    else
      (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h_id hvalid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none h_id
  simp [step, hnone, hvalid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h_id hnot
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none h_id
  simp [step, hnone, hnot]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  simp [step, h]

theorem req_effects : Effects step := by
  intro s e h_id hvalid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none h_id
  simp [step, hnone, hvalid]
  constructor
  · rfl
  constructor
  · rfl
  · intro a
    by_cases h : a = e.account
    · subst h; simp
    · simp [h]

theorem req_append_only : AppendOnly step := by
  intro s e
  cases r : receiptOf s.log e.id with
  | some _ => exact ⟨[], by simp [step, r]⟩
  | none =>
    by_cases hv : ValidEntry s e
    · exact ⟨[e], by simp [step, r, hv]⟩
    · exact ⟨[], by simp [step, r, hv]⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  cases r : receiptOf s.log e.id with
  | some _ => simp [step, r]; exact hnodup
  | none =>
    by_cases hv : ValidEntry s e
    · have h_id : e.id ∉ ids s.log := by
        intro hm
        have ⟨n, hn⟩ := receiptOf_isSome hm
        rw [hn] at r
        cases r
      simp [step, r, hv, ids_append]
      apply List.nodup_append.mpr
      constructor
      · exact hnodup
      constructor
      · simp
      · intro a ha b hb hab
        simp [ids] at ha hb
        have hb' : b = e.id := by
          simpa using hb
        subst hb'
        exact h_id (by simpa using ha)
    · simp [step, r, hv]; exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hpos a ha
  cases r : receiptOf s.log e.id with
  | some _ =>
    simp [step, r] at ha ⊢
    exact hpos a ha
  | none =>
    by_cases hv : ValidEntry s e
    · simp [step, r, hv] at ha
      have ha' : a ∈ s.accounts := by simpa using ha
      rcases hv with ⟨_, _, hge⟩
      by_cases heq : a = e.account
      · subst heq
        simp [step, r, hv]
        exact hge
      · simp [step, r, hv, heq]
        exact hpos a ha'
    · simp [step, r, hv] at ha ⊢
      exact hpos a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons
  cases r : receiptOf s.log e.id with
  | some _ =>
    intro a
    simp [step, r]
    exact hcons a
  | none =>
    by_cases hv : ValidEntry s e
    · intro a
      simp [step, r, hv]
      rw [hcons a]
      have hlog : logSum (s.log ++ [e]) a = logSum s.log a + if e.account = a then e.amount else 0 := by
        unfold logSum
        rw [sumOver_append]
        simp [sumOver_cons]
      rw [hlog]
      by_cases h : a = e.account
      · simp [h]
      · simp [h]
    · intro a
      simp [step, r, hv]
      exact hcons a

end EntryLog
