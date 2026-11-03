import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

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
  intro s e hNotIn hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  show (step s e).1 = .ok s.log.length
  simp [step, hRec, hValid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hNotIn hInvalid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  show step s e = (.rejected, s)
  simp [step, hRec, hInvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hRec
  show step s e = (.ok n, s)
  simp [step, hRec]

theorem req_effects : Effects step := by
  intro s e hNotIn hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  show (step s e).2.accounts = s.accounts ∧ (step s e).2.log = s.log ++ [e] ∧ ∀ a, (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0)
  simp only [step, hRec, hValid]
  constructor
  · rfl
  constructor
  · rfl
  · intro a
    by_cases h : a = e.account
    · simp [h]
    · simp [h]

theorem req_append_only : AppendOnly step := by
  intro s e
  show ∃ t, (step s e).2.log = s.log ++ t
  by_cases hm : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hm
    exact ⟨[], by simp [step, hn]⟩
  · have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hm
    by_cases hv : ValidEntry s e
    · exact ⟨[e], by simp [step, hRec, hv]⟩
    · exact ⟨[], by simp [step, hRec, hv]⟩

private theorem nodup_append_singleton {α : Type} [DecidableEq α] (l : List α) (x : α) (hl : l.Nodup) (hx : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hl1 : hd ∉ tl := by
      simp [List.nodup_cons] at hl
      exact hl.1
    have hl2 : tl.Nodup := by
      simp [List.nodup_cons] at hl
      exact hl.2
    have hxTl : x ∉ tl := fun h => hx (List.Mem.tail hd h)
    have hne : hd ≠ x := fun heq => hx (heq ▸ List.Mem.head tl)
    have ih' := ih hl2 hxTl
    rw [List.cons_append]
    rw [List.nodup_cons]
    constructor
    · intro hIn
      rw [List.mem_append] at hIn
      rcases hIn with hInTl | hInSing
      · exact hl1 hInTl
      · simp at hInSing
        exact hne hInSing
    · exact ih'

theorem req_unique_ids : UniqueIds step := by
  intro s e hNodup
  show (ids (step s e).2.log).Nodup
  by_cases hm : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hm
    simp [step, hn, hNodup]
  · have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hm
    simp [step, hRec]
    by_cases hv : ValidEntry s e
    · simp [hv, ids_append]
      exact nodup_append_singleton (ids s.log) e.id hNodup hm
    · simp [hv, hNodup]

theorem req_nonnegative : NonNegative step := by
  intro s e hNonNeg a ha
  show 0 ≤ (step s e).2.balance a
  by_cases hm : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hm
    simp [step, hn] at ha ⊢
    exact hNonNeg a ha
  · have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hm
    simp [step, hRec] at ha ⊢
    by_cases hv : ValidEntry s e
    · simp [hv] at ha ⊢
      by_cases heq : a = e.account
      · subst heq
        simp
        exact hv.2.2
      · simp [heq]
        exact hNonNeg a ha
    · simp [hv] at ha ⊢
      exact hNonNeg a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hCons
  show Consistent (step s e).2
  intro a
  show (step s e).2.balance a = logSum (step s e).2.log a
  by_cases hm : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hm
    simp [step, hn]
    exact hCons a
  · have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hm
    simp [step, hRec]
    by_cases hv : ValidEntry s e
    · simp [hv]
      have hBal : s.balance a = logSum s.log a := hCons a
      have hSum : logSum (s.log ++ [e]) a = logSum s.log a + (if e.account = a then e.amount else 0) := by
        unfold logSum
        rw [sumOver_append]
        simp
      rw [hSum, <- hBal]
      by_cases heq : a = e.account
      · subst heq
        simp
      · have hne : e.account ≠ a := fun h => heq h.symm
        simp [heq, hne]
    · simp [hv]
      exact hCons a

end EntryLog
