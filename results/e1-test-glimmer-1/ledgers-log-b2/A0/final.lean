import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) :=
  by unfold ValidEntry; infer_instance

def step : Impl := fun s e =>
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
  intro s e hnot hvalid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none hnot
  simp [step, hnone, hvalid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnot hnv
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none hnot
  simp [step, hnone, hnv]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hrec
  simp [step, hrec]

theorem req_effects : Effects step := by
  intro s e hnot hvalid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none hnot
  simp [step, hnone, hvalid]
  refine ⟨rfl, rfl, fun a => rfl⟩

theorem req_append_only : AppendOnly step := by
  intro s e
  cases h : receiptOf s.log e.id with
  | some _ => exact ⟨[], by simp [step, h]⟩
  | none =>
    by_cases hv : ValidEntry s e
    · simp [step, h, hv]; exact ⟨[e], rfl⟩
    · simp [step, h, hv]; exact ⟨[], rfl⟩

private theorem receiptOf_none_imp_notmem (log : List Entry) (i : EntryId)
    (h : receiptOf log i = none) : i ∉ ids log := by
  intro hmem
  have ⟨n, hn⟩ := receiptOf_isSome hmem
  rw [hn] at h; cases h

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  cases h : receiptOf s.log e.id with
  | some _ => simp [step, h]; exact hnodup
  | none =>
    by_cases hv : ValidEntry s e
    · simp [step, h, hv, ids_append]
      have hnotmem : e.id ∉ ids s.log := receiptOf_none_imp_notmem _ _ h
      apply List.nodup_append.mpr
      refine ⟨hnodup, by simp, fun a ha b hb hab => ?_⟩
      simp at hb
      cases hb
      subst b
      intro heq
      have : e.id ∈ ids s.log := by rw [← heq]; exact ha
      contradiction
    · simp [step, h, hv]; exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hnn a ha
  cases h : receiptOf s.log e.id with
  | some _ =>
    simp [step, h]
    have : (step s e).2.accounts = s.accounts := by simp [step, h]
    rw [this] at ha
    exact hnn a ha
  | none =>
    by_cases hv : ValidEntry s e
    · simp [step, h, hv]
      have ha' : a ∈ s.accounts := by
        have : (step s e).2.accounts = s.accounts := by simp [step, h, hv]
        rw [this] at ha; exact ha
      by_cases heq : a = e.account
      · subst heq
        have ⟨_, _, hpos⟩ := hv
        exact hpos
      · simp [heq]
        exact hnn a ha'
    · simp [step, h, hv]
      have : (step s e).2.accounts = s.accounts := by simp [step, h, hv]
      rw [this] at ha
      exact hnn a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons
  cases h : receiptOf s.log e.id with
  | some _ =>
    intro a
    simp [step, h]
    exact hcons a
  | none =>
    by_cases hv : ValidEntry s e
    · intro a
      simp [step, h, hv]
      have hlog : logSum (s.log ++ [e]) a = logSum s.log a + if e.account = a then e.amount else 0 := by
        simp [logSum, sumOver_append]
      rw [hcons a, hlog]
      by_cases ha : a = e.account
      · simp [ha]
        rw [if_pos rfl]
        omega
      · simp [ha]
        rw [if_neg ha]
        omega
    · intro a
      simp [step, h, hv]
      exact hcons a

end EntryLog
