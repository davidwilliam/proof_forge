import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def step : Impl := fun s e =>
  match _h : receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if ValidEntry s e then
      (.ok s.log.length,
       { accounts := s.accounts, log := s.log ++ [e],
         balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hNotMem hValid
  have hNone : receiptOf s.log e.id = none := receiptOf_eq_none hNotMem
  unfold step
  rw [hNone]
  simp [hValid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hNotMem hInvalid
  have hNone : receiptOf s.log e.id = none := receiptOf_eq_none hNotMem
  unfold step
  rw [hNone]
  simp [hInvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hRec
  unfold step
  rw [hRec]

theorem req_effects : Effects step := by
  intro s e hNotMem hValid
  have hNone : receiptOf s.log e.id = none := receiptOf_eq_none hNotMem
  have hStep : step s e = (.ok s.log.length,
       { accounts := s.accounts, log := s.log ++ [e],
         balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    rw [hNone]
    simp [hValid]
  refine ⟨?_, ?_, ?_⟩
  · show (step s e).2.accounts = s.accounts
    rw [hStep]
  · show (step s e).2.log = s.log ++ [e]
    rw [hStep]
  · intro a
    show (step s e).2.balance a = s.balance a + if a = e.account then e.amount else 0
    rw [hStep]
    show (if a = e.account then s.balance a + e.amount else s.balance a) = s.balance a + if a = e.account then e.amount else 0
    by_cases heq : a = e.account
    · simp [heq]
    · simp [heq]

theorem req_append_only : AppendOnly step := by
  intro s e
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hEq : (step s e).2.log = s.log := by unfold step; rw [hn]
    exact ⟨[], by rw [hEq, List.append_nil]⟩
  · have hNone : receiptOf s.log e.id = none := receiptOf_eq_none hMem
    by_cases hv : ValidEntry s e
    · have hEq : (step s e).2.log = s.log ++ [e] := by
        have hStep : step s e = (.ok s.log.length,
          { accounts := s.accounts, log := s.log ++ [e],
            balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
          unfold step; rw [hNone]; simp [hv]
        rw [hStep]
      exact ⟨[e], hEq⟩
    · have hEq : (step s e).2.log = s.log := by
        have hStep : step s e = (.rejected, s) := by
          unfold step; rw [hNone]; simp [hv]
        rw [hStep]
      exact ⟨[], by rw [hEq, List.append_nil]⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hNodup
  have aux : ∀ (l : List Entry), (ids l).Nodup → e.id ∉ ids l → (ids (l ++ [e])).Nodup := by
    intro l
    induction l with
    | nil =>
      intro _ _
      simp [ids]
    | cons hd tl ih =>
      intro hNd hNot
      have hIdsCons : ids (hd :: tl) = hd.id :: ids tl := rfl
      have hNd' : (hd.id :: ids tl).Nodup := by rw [← hIdsCons]; exact hNd
      have hNotTl : e.id ∉ ids tl := fun hIn => hNot (List.mem_cons.mpr (Or.inr hIn))
      have hHdNe : hd.id ≠ e.id := by
        intro heq
        apply hNot
        rw [← heq]
        exact List.mem_cons.mpr (Or.inl rfl)
      have hHdNotInTl : hd.id ∉ ids tl := (List.nodup_cons.mp hNd').1
      have hNodupTl : (ids tl).Nodup := (List.nodup_cons.mp hNd').2
      have ih' := ih hNodupTl hNotTl
      have hIdsAppend : ids ((hd :: tl) ++ [e]) = hd.id :: ids (tl ++ [e]) := by
        simp [ids]
      rw [hIdsAppend]
      apply List.nodup_cons.mpr
      constructor
      · intro hIn
        have hIdsEq : ids (tl ++ [e]) = ids tl ++ [e.id] := by simp [ids]
        rw [hIdsEq] at hIn
        rw [List.mem_append] at hIn
        rcases hIn with hIn1 | hIn2
        · exact hHdNotInTl hIn1
        · rw [List.mem_singleton] at hIn2
          exact hHdNe hIn2
      · exact ih'
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hEq : (step s e).2.log = s.log := by unfold step; rw [hn]
    rw [hEq]
    exact hNodup
  · have hNone : receiptOf s.log e.id = none := receiptOf_eq_none hMem
    by_cases hv : ValidEntry s e
    · have hEq : (step s e).2.log = s.log ++ [e] := by
        have hStep : step s e = (.ok s.log.length,
          { accounts := s.accounts, log := s.log ++ [e],
            balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
          unfold step; rw [hNone]; simp [hv]
        rw [hStep]
      rw [hEq]
      exact aux s.log hNodup hMem
    · have hEq : (step s e).2.log = s.log := by
        have hStep : step s e = (.rejected, s) := by
          unfold step; rw [hNone]; simp [hv]
        rw [hStep]
      rw [hEq]
      exact hNodup

theorem req_nonnegative : NonNegative step := by
  intro s e hNonNeg a ha
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hEq : step s e = (.ok n, s) := by unfold step; rw [hn]
    have hAcc : (step s e).2.accounts = s.accounts := by rw [hEq]
    have hBal : (step s e).2.balance a = s.balance a := by rw [hEq]
    rw [hBal]
    have ha' : a ∈ s.accounts := by rw [← hAcc]; exact ha
    exact hNonNeg a ha'
  · have hNone : receiptOf s.log e.id = none := receiptOf_eq_none hMem
    by_cases hv : ValidEntry s e
    · have hStep : step s e = (.ok s.log.length,
            { accounts := s.accounts, log := s.log ++ [e],
              balance := fun a_2 => if a_2 = e.account then s.balance a_2 + e.amount else s.balance a_2 }) := by
        unfold step; rw [hNone]; simp [hv]
      have hAcc : (step s e).2.accounts = s.accounts := by rw [hStep]
      have hBal : (step s e).2.balance a = if a = e.account then s.balance a + e.amount else s.balance a := by
        rw [hStep]
      rw [hBal]
      have ha' : a ∈ s.accounts := by rw [← hAcc]; exact ha
      by_cases heq : a = e.account
      · simp [heq]
        subst heq
        exact hv.2.2
      · simp [heq]
        exact hNonNeg a ha'
    · have hStep : step s e = (.rejected, s) := by
        unfold step; rw [hNone]; simp [hv]
      have hAcc : (step s e).2.accounts = s.accounts := by rw [hStep]
      have hBal : (step s e).2.balance a = s.balance a := by rw [hStep]
      rw [hBal]
      have ha' : a ∈ s.accounts := by rw [← hAcc]; exact ha
      exact hNonNeg a ha'

theorem req_consistent : StaysConsistent step := by
  intro s e hCons
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hEq : (step s e).2 = s := by unfold step; rw [hn]
    rw [hEq]
    exact hCons
  · have hNone : receiptOf s.log e.id = none := receiptOf_eq_none hMem
    by_cases hv : ValidEntry s e
    · have hStep : step s e = (.ok s.log.length,
          { accounts := s.accounts, log := s.log ++ [e],
            balance := fun ac => if ac = e.account then s.balance ac + e.amount else s.balance ac }) := by
        unfold step; rw [hNone]; simp [hv]
      have hLogEq : (step s e).2.log = s.log ++ [e] := by rw [hStep]
      have hBalEq : ∀ x, (step s e).2.balance x = if x = e.account then s.balance x + e.amount else s.balance x := by
        intro x; rw [hStep]
      intro a
      rw [hBalEq a, hLogEq]
      have hConsA := hCons a
      have hSumAppend : logSum (s.log ++ [e]) a = logSum s.log a + logSum [e] a := by
        unfold logSum
        exact sumOver_append s.log [e] (fun e' => if e'.account = a then e'.amount else (0 : Int))
      have hSumSingle : logSum [e] a = if e.account = a then e.amount else 0 := by
        unfold logSum; simp
      rw [hSumAppend, hSumSingle, ← hConsA]
      by_cases heq : a = e.account
      · have heq' : e.account = a := heq.symm
        have h1 : (if a = e.account then s.balance a + e.amount else s.balance a) = s.balance a + e.amount := by rw [if_pos heq]
        have h2 : (if e.account = a then e.amount else (0:Int)) = e.amount := by rw [if_pos heq']
        rw [h1, h2]
      · have heq2 : ¬ e.account = a := fun h => heq h.symm
        have h1 : (if a = e.account then s.balance a + e.amount else s.balance a) = s.balance a := by rw [if_neg heq]
        have h2 : (if e.account = a then e.amount else (0:Int)) = 0 := by rw [if_neg heq2]
        rw [h1, h2]
        omega
    · have hStep : step s e = (.rejected, s) := by
        unfold step; rw [hNone]; simp [hv]
      have hEq : (step s e).2 = s := by rw [hStep]
      rw [hEq]
      exact hCons

end EntryLog
