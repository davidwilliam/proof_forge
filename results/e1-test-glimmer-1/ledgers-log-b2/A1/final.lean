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
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h_notin hvalid
  unfold step
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none h_notin
  simp [hrec, hvalid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h_notin hnot
  unfold step
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none h_notin
  simp [hrec, hnot]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  simp [h]

theorem req_effects : Effects step := by
  intro s e h_notin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none h_notin
  simp [step, hrec, hvalid]
  intro a
  by_cases h_eq : a = e.account
  · simp [h_eq]
  · simp [h_eq]

theorem req_append_only : AppendOnly step := by
  intro s e
  simp [step]
  split
  next h =>
    exact ⟨[], by simp⟩
  next h =>
    split
    next hv =>
      exact ⟨[e], rfl⟩
    next hv =>
      exact ⟨[], by simp⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  unfold step
  cases h : receiptOf s.log e.id with
  | some n =>
      simp [h]
      exact hnodup
  | none =>
      by_cases hvalid : ValidEntry s e
      · simp [h, hvalid]
        have hnotin : e.id ∉ ids s.log := by
          intro hin
          have := receiptOf_isSome hin
          obtain ⟨n', hn'⟩ := this
          rw [hn'] at h
          cases h
        have h1 : (ids s.log).Nodup := hnodup
        have h2 : ([e.id]).Nodup := by simp [List.Nodup]
        have h3 : ∀ a ∈ ids s.log, ∀ b ∈ [e.id], a ≠ b := by
          intro a ha b hb
          simp at hb
          subst hb
          intro heq
          apply hnotin
          rw [← heq]
          exact ha
        rw [List.nodup_append]
        exact ⟨h1, h2, h3⟩
      · simp [h, hvalid]
        exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hpos a ha
  cases hrec : receiptOf s.log e.id with
  | some n =>
    simp [step, hrec] at ha ⊢
    exact hpos a ha
  | none =>
    by_cases hvalid : ValidEntry s e
    · simp [step, hrec, hvalid] at ha ⊢
      have ha' : a ∈ s.accounts := by simpa using ha
      by_cases h_eq : a = e.account
      · subst h_eq
        have hbal : 0 ≤ s.balance e.account + e.amount := (hvalid).2.2
        rw [if_pos rfl]
        exact hbal
      · simp [h_eq]
        exact hpos a ha'
    · simp [step, hrec, hvalid] at ha ⊢
      exact hpos a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons
  cases hrec : receiptOf s.log e.id with
  | some n =>
    simp [step, hrec]
    exact hcons
  | none =>
    by_cases hvalid : ValidEntry s e
    · simp [step, hrec, hvalid]
      intro a
      have hbal : s.balance a = logSum s.log a := hcons a
      simp [logSum, sumOver_append, sumOver_cons] at hbal ⊢
      rw [hbal]
      by_cases h_eq : a = e.account
      · simp [h_eq]
      · simp [h_eq, Ne.symm h_eq]
    · simp [step, hrec, hvalid]
      exact hcons

end EntryLog
