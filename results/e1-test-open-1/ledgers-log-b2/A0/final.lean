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

private theorem nodup_append_singleton {α : Type} (l : List α) (x : α) (hNodup : l.Nodup) (hMem : x ∉ l) :
    (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    have hY : y ∉ ys := (List.nodup_cons.mp hNodup).1
    have hNodupYs : ys.Nodup := (List.nodup_cons.mp hNodup).2
    have hMemYs : x ∉ ys := fun h => hMem (List.Mem.tail y h)
    have hNe : y ≠ x := fun heq => hMem (heq ▸ List.Mem.head ys)
    have ih' := ih hNodupYs hMemYs
    have hNotMem : y ∉ ys ++ [x] := by
      intro h
      rw [List.mem_append] at h
      rcases h with h1 | h1
      · exact hY h1
      · simp at h1
        exact hNe h1
    exact List.nodup_cons.mpr ⟨hNotMem, ih'⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hNot hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNot
  show (step s e).1 = Outcome.ok s.log.length
  unfold step
  simp only [hRec, hValid, ↓reduceIte]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hNot hInval
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNot
  show step s e = (.rejected, s)
  unfold step
  simp only [hRec, hInval, ↓reduceIte]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hRec
  show step s e = (.ok n, s)
  unfold step
  simp only [hRec]

theorem req_effects : Effects step := by
  intro s e hNot hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNot
  have hEq : step s e = (.ok s.log.length,
          { s with log := s.log ++ [e],
                   balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    simp only [hRec, hValid, ↓reduceIte]
  refine ⟨?_, ?_, ?_⟩
  · show (step s e).2.accounts = s.accounts
    rw [hEq]
  · show (step s e).2.log = s.log ++ [e]
    rw [hEq]
  · intro a
    show (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0)
    rw [hEq]
    by_cases ha : a = e.account
    · simp only [ha, ↓reduceIte]
    · simp only [ha, ↓reduceIte, Int.add_zero]

theorem req_append_only : AppendOnly step := by
  intro s e
  show ∃ t, (step s e).2.log = s.log ++ t
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hStep : (step s e).2.log = s.log := by
      unfold step
      simp only [hn]
    exact ⟨[], by rw [hStep, List.append_nil]⟩
  · have hNot : e.id ∉ ids s.log := hMem
    have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNot
    by_cases hV : ValidEntry s e
    · have hStep : (step s e).2.log = s.log ++ [e] := by
        unfold step
        simp only [hRec, hV, ↓reduceIte]
      exact ⟨[e], hStep⟩
    · have hStep : (step s e).2.log = s.log := by
        unfold step
        simp only [hRec, hV, ↓reduceIte]
      exact ⟨[], by rw [hStep, List.append_nil]⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hNodup
  show (ids (step s e).2.log).Nodup
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hStep : (step s e).2.log = s.log := by
      unfold step; simp only [hn]
    rw [hStep]
    exact hNodup
  · have hNot : e.id ∉ ids s.log := hMem
    have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNot
    by_cases hV : ValidEntry s e
    · have hStep : (step s e).2.log = s.log ++ [e] := by
        unfold step; simp only [hRec, hV, ↓reduceIte]
      rw [hStep, ids_append]
      have : ids [e] = [e.id] := rfl
      rw [this]
      exact nodup_append_singleton (ids s.log) e.id hNodup hNot
    · have hStep : (step s e).2.log = s.log := by
        unfold step; simp only [hRec, hV, ↓reduceIte]
      rw [hStep]
      exact hNodup

theorem req_nonnegative : NonNegative step := by
  intro s e hNonNeg a ha
  show 0 ≤ (step s e).2.balance a
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hEq : step s e = (Outcome.ok n, s) := by unfold step; simp only [hn]
    have hBal : (step s e).2.balance a = s.balance a := by rw [hEq]
    have hAcc : (step s e).2.accounts = s.accounts := by rw [hEq]
    rw [hBal]
    have ha' : a ∈ s.accounts := hAcc ▸ ha
    exact hNonNeg a ha'
  · have hNot : e.id ∉ ids s.log := hMem
    have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNot
    by_cases hV : ValidEntry s e
    · have hEq : step s e = (.ok s.log.length,
          { s with log := s.log ++ [e],
                   balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        unfold step; simp only [hRec, hV, ↓reduceIte]
      have hBal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by
        rw [hEq]
      have hAcc : (step s e).2.accounts = s.accounts := by rw [hEq]
      have ha' : a ∈ s.accounts := hAcc ▸ ha
      rw [hBal]
      by_cases heq : a = e.account
      · simp only [heq, ↓reduceIte] at *
        exact hV.2.2
      · simp only [heq, ↓reduceIte] at *
        exact hNonNeg a ha'
    · have hEq : step s e = (.rejected, s) := by unfold step; simp only [hRec, hV, ↓reduceIte]
      have hBal : (step s e).2.balance a = s.balance a := by rw [hEq]
      have hAcc : (step s e).2.accounts = s.accounts := by rw [hEq]
      rw [hBal]
      have ha' : a ∈ s.accounts := hAcc ▸ ha
      exact hNonNeg a ha'

theorem req_consistent : StaysConsistent step := by
  intro s e hCons
  show Consistent (step s e).2
  intro a
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hEq : step s e = (Outcome.ok n, s) := by unfold step; simp only [hn]
    have hLog : (step s e).2.log = s.log := by rw [hEq]
    have hBal : (step s e).2.balance a = s.balance a := by rw [hEq]
    rw [hLog, hBal]
    exact hCons a
  · have hNot : e.id ∉ ids s.log := hMem
    have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNot
    by_cases hV : ValidEntry s e
    · have hEq : step s e = (.ok s.log.length,
          { s with log := s.log ++ [e],
                   balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        unfold step; simp only [hRec, hV, ↓reduceIte]
      have hStepLog : (step s e).2.log = s.log ++ [e] := by rw [hEq]
      have hStepBal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by
        rw [hEq]
      rw [hStepLog, hStepBal, hCons a]
      have hExpand : logSum (s.log ++ [e]) a = logSum s.log a + (if e.account = a then e.amount else 0) := by
        unfold logSum
        rw [sumOver_append]
        have h1 : sumOver [e] (fun e_1 => if e_1.account = a then e_1.amount else (0 : Int)) = (if e.account = a then e.amount else (0 : Int)) := by
          have : sumOver [e] (fun e_1 => if e_1.account = a then e_1.amount else (0 : Int)) =
               (if e.account = a then e.amount else (0 : Int)) + 0 := rfl
          rw [this, Int.add_zero]
        rw [h1]
      rw [hExpand]
      by_cases heq : a = e.account
      · have heq2 : e.account = a := heq.symm
        rw [if_pos heq, if_pos heq2]
      · have heq2 : ¬ e.account = a := fun h => heq h.symm
        rw [if_neg heq, if_neg heq2, Int.add_zero]
    · have hEq : step s e = (.rejected, s) := by unfold step; simp only [hRec, hV, ↓reduceIte]
      have hLog : (step s e).2.log = s.log := by rw [hEq]
      have hBal : (step s e).2.balance a = s.balance a := by rw [hEq]
      rw [hLog, hBal]
      exact hCons a

end EntryLog
