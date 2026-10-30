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
  intro s e hNotIn hValid
  unfold step
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  simp only [hRec]
  have hAcc : accepts s e = true := by
    unfold accepts
    simp [hValid.1, hValid.2.1, hValid.2.2]
  simp [hAcc]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s e hNotIn hInvalid
  unfold step
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  simp only [hRec]
  have hAcc : accepts s e = false := by
    unfold accepts
    by_cases hT : (s.accounts.contains e.account && (e.amount != 0) && decide (0 ≤ s.balance e.account + e.amount)) = true
    · exfalso
      apply hInvalid
      have h1 : s.accounts.contains e.account = true := by
        have hh := hT
        simp only [Bool.and_eq_true] at hh
        exact hh.1.1
      have h2 : (e.amount != 0) = true := by
        have hh := hT
        simp only [Bool.and_eq_true] at hh
        exact hh.1.2
      have h3 : decide (0 ≤ s.balance e.account + e.amount) = true := by
        have hh := hT
        simp only [Bool.and_eq_true] at hh
        exact hh.2
      refine ⟨?_, ?_, ?_⟩
      · simp_all
      · intro heq
        simp [heq] at h2
      · simp_all
    · simp_all
  simp [hAcc]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  simp [h]

theorem req_effects : Effects step := by
  intro s e hNotIn hValid
  unfold step
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  rw [hRec]
  have hAcc : accepts s e = true := by
    unfold accepts
    simp [hValid.1, hValid.2.1, hValid.2.2]
  rw [hAcc]
  simp
  intro a
  by_cases h : a = e.account
  · simp [h]
  · simp [h]

theorem req_append_only : AppendOnly step := by
  intro s e
  simp only [step]
  split
  · rename_i n hn
    exact ⟨[], by simp⟩
  · rename_i hnone
    split
    · exact ⟨[e], rfl⟩
    · exact ⟨[], by simp⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hNodup
  unfold step
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    simp [hn, hNodup]
  · have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hMem
    simp only [hRec]
    split
    next heq =>
      have h1 : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by simp [ids]
      rw [h1]
      rw [List.nodup_append]
      refine ⟨hNodup, by simp, ?_⟩
      intro a ha b hb heq
      simp at hb
      subst hb
      subst heq
      exact hMem ha
    · exact hNodup

theorem req_nonnegative : NonNegative step := by
  intro s e hPos a ha
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hStep : (step s e).2 = s := by unfold step; simp [hn]
    rw [hStep] at ha ⊢
    exact hPos a ha
  · have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hMem
    by_cases hAcc : accepts s e = true
    · have hBal : (step s e).2.balance = fun x => if x = e.account then s.balance x + e.amount else s.balance x := by
          unfold step; simp [hRec, hAcc]
      have ha' : a ∈ s.accounts := by
        have hSt : (step s e).2.accounts = s.accounts := by unfold step; simp [hRec, hAcc]
        rw [hSt] at ha
        exact ha
      rw [hBal]
      by_cases heq : a = e.account
      · simp only [heq, ↓reduceIte]
        have hDec : decide (0 ≤ s.balance e.account + e.amount) = true := by
          unfold accepts at hAcc
          simp only [Bool.and_eq_true] at hAcc
          exact hAcc.2
        exact of_decide_eq_true hDec
      · simp only [heq, ↓reduceIte]
        exact hPos a ha'
    · have hAccF : accepts s e = false := by
        cases h : accepts s e <;> simp_all
      have hStep : (step s e).2 = s := by unfold step; simp [hRec, hAccF]
      rw [hStep] at ha ⊢
      exact hPos a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hCons a
  show (step s e).2.balance a = logSum (step s e).2.log a
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hStep : (step s e).2 = s := by unfold step; simp [hn]
    rw [hStep]
    exact hCons a
  · have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hMem
    by_cases hAcc : accepts s e = true
    · have hStepLog : (step s e).2.log = s.log ++ [e] := by
        simp [step, hRec, hAcc]
      have hStepBal : (step s e).2.balance a = if a = e.account then s.balance a + e.amount else s.balance a := by
        simp [step, hRec, hAcc]
      rw [hStepLog, hStepBal]
      have hLogSum : logSum (s.log ++ [e]) a = logSum s.log a + if e.account = a then e.amount else 0 := by
        unfold logSum
        rw [sumOver_append]
        simp
      rw [hLogSum]
      have hc : s.balance a = logSum s.log a := hCons a
      rw [hc]
      by_cases heq : a = e.account
      · subst heq; simp
      · have hne : e.account ≠ a := fun h => heq h.symm
        simp [heq, hne]
    · have hAccF : accepts s e = false := by cases h : accepts s e <;> simp_all
      have hStep : (step s e).2 = s := by unfold step; simp [hRec, hAccF]
      rw [hStep]
      exact hCons a

end EntryLog
