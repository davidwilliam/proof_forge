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
  intro s e hNotMem hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotMem
  show (step s e).1 = .ok s.log.length
  simp [step, hRec, hValid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hNotMem hNotValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotMem
  show step s e = (.rejected, s)
  simp [step, hRec, hNotValid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hRec
  show step s e = (.ok n, s)
  simp [step, hRec]

theorem req_effects : Effects step := by
  intro s e hNotMem hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotMem
  show (step s e).2.accounts = s.accounts ∧ (step s e).2.log = s.log ++ [e] ∧ ∀ a, (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0)
  have hStep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    simp [step, hRec, hValid]
  rw [hStep]
  refine ⟨rfl, rfl, fun a => ?_⟩
  simp only
  by_cases heq : a = e.account
  · simp [heq]
  · simp [heq]

theorem req_append_only : AppendOnly step := by
  intro s e
  show ∃ t, (step s e).2.log = s.log ++ t
  simp only [step]
  split
  next h => exact ⟨[], by simp⟩
  next h =>
    split
    next hv => exact ⟨[e], by simp⟩
    next hv => exact ⟨[], by simp⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hNodup
  show (ids (step s e).2.log).Nodup
  simp only [step]
  split
  next h => simpa
  next hRec =>
    split
    next hv =>
      simp only [ids_append]
      have hNotMem : e.id ∉ ids s.log := by
        intro hmem
        obtain ⟨n, hn⟩ := receiptOf_isSome hmem
        rw [hn] at hRec
        simp at hRec
      have aux : ∀ (l : List EntryId), l.Nodup → e.id ∉ l → (l ++ [e.id]).Nodup := by
        intro l
        induction l with
        | nil => intro _ _; simp
        | cons hd tl ih =>
          intro hN hMem
          have hHeadNot : hd ∉ tl := (List.nodup_cons.mp hN).1
          have hTailNodup : tl.Nodup := (List.nodup_cons.mp hN).2
          have hNotMemTail : e.id ∉ tl := fun hm => hMem (List.mem_cons.mpr (Or.inr hm))
          have hNe : e.id ≠ hd := fun heq => hMem (heq ▸ List.mem_cons.mpr (Or.inl rfl))
          have ih' := ih hTailNodup hNotMemTail
          rw [List.cons_append]
          rw [List.nodup_cons]
          constructor
          · intro hm
            rw [List.mem_append] at hm
            rcases hm with hm1 | hm2
            · exact hHeadNot hm1
            · simp at hm2
              exact hNe hm2.symm
          · exact ih'
      exact aux (ids s.log) hNodup hNotMem
    next hv => simpa

theorem req_nonnegative : NonNegative step := by
  intro s e hNonNeg a ha
  show 0 ≤ (step s e).2.balance a
  cases hEq : receiptOf s.log e.id with
  | some n =>
    have hStep : step s e = (.ok n, s) := by simp [step, hEq]
    have hAcc : (step s e).2.accounts = s.accounts := by rw [hStep]
    have ha' : a ∈ s.accounts := hAcc ▸ ha
    have hBal : (step s e).2.balance a = s.balance a := by rw [hStep]
    rw [hBal]
    exact hNonNeg a ha'
  | none =>
    by_cases hv : ValidEntry s e
    · have hStep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by simp [step, hEq, hv]
      have hAcc : (step s e).2.accounts = s.accounts := by rw [hStep]
      have ha' : a ∈ s.accounts := hAcc ▸ ha
      have hBal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by rw [hStep]
      rw [hBal]
      by_cases heq : a = e.account
      · rw [if_pos heq]
        have h2 : s.balance a + e.amount = s.balance e.account + e.amount := by rw [heq]
        rw [h2]
        exact hv.2.2
      · rw [if_neg heq]
        exact hNonNeg a ha'
    · have hStep : step s e = ((.rejected : Outcome), s) := by simp [step, hEq, hv]
      have hAcc : (step s e).2.accounts = s.accounts := by rw [hStep]
      have ha' : a ∈ s.accounts := hAcc ▸ ha
      have hBal : (step s e).2.balance a = s.balance a := by rw [hStep]
      rw [hBal]
      exact hNonNeg a ha'

theorem req_consistent : StaysConsistent step := by
  intro s e hCons
  show Consistent (step s e).2
  intro a
  show (step s e).2.balance a = logSum (step s e).2.log a
  cases hEq : receiptOf s.log e.id with
  | some n =>
    have hStep : step s e = (.ok n, s) := by simp [step, hEq]
    have hBal : (step s e).2.balance = s.balance := by rw [hStep]
    have hLog : (step s e).2.log = s.log := by rw [hStep]
    rw [hBal, hLog]
    exact hCons a
  | none =>
    by_cases hv : ValidEntry s e
    · have hStep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by simp [step, hEq, hv]
      have hBal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by rw [hStep]
      have hLog : (step s e).2.log = s.log ++ [e] := by rw [hStep]
      rw [hBal, hLog]
      have hSum : logSum (s.log ++ [e]) a = logSum s.log a + (if e.account = a then e.amount else 0) := by
        unfold logSum
        rw [sumOver_append]
        simp only [sumOver_cons, sumOver_nil]
        omega
      have hIf : (if a = e.account then e.amount else (0 : Int)) = (if e.account = a then e.amount else (0 : Int)) := by
        by_cases heq : a = e.account
        · have h1 : e.account = a := heq.symm
          rw [if_pos heq, if_pos h1]
        · have h1 : ¬ e.account = a := fun h => heq h.symm
          rw [if_neg heq, if_neg h1]
      have h1 : (if a = e.account then s.balance a + e.amount else s.balance a) = s.balance a + (if a = e.account then e.amount else 0) := by
        by_cases heq : a = e.account
        · rw [if_pos heq, if_pos heq]
        · rw [if_neg heq, if_neg heq]; omega
      rw [h1, hCons a, hIf, hSum]
    · have hStep : step s e = ((.rejected : Outcome), s) := by simp [step, hEq, hv]
      have hBal : (step s e).2.balance = s.balance := by rw [hStep]
      have hLog : (step s e).2.log = s.log := by rw [hStep]
      rw [hBal, hLog]
      exact hCons a

end EntryLog
