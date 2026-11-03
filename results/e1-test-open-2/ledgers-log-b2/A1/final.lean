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
                balance := fun a => s.balance a + (if a = e.account then e.amount else 0) })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hNotIn hValid
  have hNone : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  simp [step, hNone, hValid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hNotIn hInvalid
  have hNone : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  simp [step, hNone, hInvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hRec
  unfold step
  simp [hRec]

theorem req_effects : Effects step := by
  intro s e hNotIn hValid
  have hNone : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  simp [step, hNone, hValid]

theorem req_append_only : AppendOnly step := by
  intro s e
  show ∃ t, (step s e).2.log = s.log ++ t
  cases hrec : receiptOf s.log e.id
  · simp only [step, hrec]
    by_cases hv : ValidEntry s e
    · simp only [hv, ↓reduceIte]
      exact ⟨[e], rfl⟩
    · simp only [hv, ↓reduceIte]
      exact ⟨[], by simp⟩
  · simp only [step, hrec]
    exact ⟨[], by simp⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hNodup
  by_cases hRec : receiptOf s.log e.id = none
  · by_cases hv : ValidEntry s e
    · have hStep : (step s e).2.log = s.log ++ [e] := by
        simp [step, hRec, hv]
      rw [hStep]
      rw [ids_append]
      have hNotMem : e.id ∉ ids s.log := by
        intro hMem
        obtain ⟨n, hn⟩ := receiptOf_isSome hMem
        rw [hn] at hRec
        contradiction
      simp [ids]
      -- prove Nodup (ids s.log ++ [e.id])
      have h1 : List.Nodup (ids s.log ++ [e.id]) := by
        -- induction on ids s.log
        have hgen : ∀ (l : List EntryId), l.Nodup → e.id ∉ l → (l ++ [e.id]).Nodup := by
          intro l
          induction l with
          | nil => intro _ _; simp
          | cons x xs ih =>
            intro hNod hNotIn
            simp at hNod
            have hNotIn' : e.id ∉ xs := by
              intro hmem
              apply hNotIn
              simp [hmem]
            have hne : x ≠ e.id := by
              intro heq
              apply hNotIn
              rw [heq]; simp
            have hxsNod : (xs ++ [e.id]).Nodup := ih hNod.2 hNotIn'
            simp [hNod.1, hne, hxsNod]
        exact hgen (ids s.log) hNodup hNotMem
      exact h1
    · have hStep : (step s e).2.log = s.log := by
        simp [step, hRec, hv]
      rw [hStep]
      exact hNodup
  · have hSome : ∃ n, receiptOf s.log e.id = some n := by
        cases h : receiptOf s.log e.id with
        | none => contradiction
        | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := hSome
    have hStep : (step s e).2.log = s.log := by
      simp [step, hn]
    rw [hStep]
    exact hNodup

theorem req_nonnegative : NonNegative step := by
  intro s e hNonneg a ha
  by_cases hRec : receiptOf s.log e.id = none
  · by_cases hv : ValidEntry s e
    · have hStep : step s e = (.ok s.log.length,
           { s with log := s.log ++ [e],
                    balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
        simp [step, hRec, hv]
      have hAcc : (step s e).2.accounts = s.accounts := by simp [hStep]
      have hBal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := by simp [hStep]
      rw [hAcc] at ha
      rw [hBal]
      by_cases heq : a = e.account
      · simp [heq] at hBal ⊢
        have hle : 0 ≤ s.balance e.account + e.amount := hv.2.2
        -- a = e.account so show is same
        subst heq
        exact hle
      · simp [heq]
        exact hNonneg a ha
    · have hStep : step s e = (.rejected, s) := by simp [step, hRec, hv]
      have hAcc : (step s e).2.accounts = s.accounts := by simp [hStep]
      have hBal : (step s e).2.balance a = s.balance a := by simp [hStep]
      rw [hAcc] at ha
      rw [hBal]
      exact hNonneg a ha
  · have hSome : ∃ n, receiptOf s.log e.id = some n := by
        cases h : receiptOf s.log e.id with
        | none => contradiction
        | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := hSome
    have hStep : step s e = (.ok n, s) := by simp [step, hn]
    have hAcc : (step s e).2.accounts = s.accounts := by simp [hStep]
    have hBal : (step s e).2.balance a = s.balance a := by simp [hStep]
    rw [hAcc] at ha
    rw [hBal]
    exact hNonneg a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hCons a
  by_cases hRec : receiptOf s.log e.id = none
  · by_cases hv : ValidEntry s e
    · have hStepBal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := by
        simp [step, hRec, hv]
      have hStepLog : (step s e).2.log = s.log ++ [e] := by
        simp [step, hRec, hv]
      rw [hStepBal, hStepLog]
      have hOld : s.balance a = logSum s.log a := hCons a
      rw [hOld]
      unfold logSum
      rw [sumOver_append]
      have hSing : sumOver [e] (fun e2 : Entry => if e2.account = a then e2.amount else 0) = if e.account = a then e.amount else 0 := by
        simp [sumOver]
      rw [hSing]
      have hIfEq : (if a = e.account then e.amount else (0 : Int)) = (if e.account = a then e.amount else 0) := by
        by_cases heq : a = e.account
        · simp [heq]
        · have heq2 : ¬ e.account = a := fun h => heq h.symm
          simp [heq, heq2]
      rw [hIfEq]
    · have hStep : (step s e).2 = s := by simp [step, hRec, hv]
      have hOld : s.balance a = logSum s.log a := hCons a
      have : (step s e).2.balance a = s.balance a := by simp [hStep]
      rw [this, hStep]
      exact hOld
  · have hSome : ∃ n, receiptOf s.log e.id = some n := by
        cases h : receiptOf s.log e.id with
        | none => contradiction
        | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := hSome
    have hStep : (step s e).2 = s := by simp [step, hn]
    have : (step s e).2.balance a = s.balance a := by simp [hStep]
    rw [this, hStep]
    exact hCons a

end EntryLog
