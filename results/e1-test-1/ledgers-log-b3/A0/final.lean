import EntryLog.Spec
import EntryLog.Lemmas
namespace EntryLog
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance
def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (Outcome.ok n, s)
  | none =>
    if ValidEntry s e then
      (Outcome.ok s.log.length,
       { accounts := s.accounts,
         log := s.log ++ [e],
         balance := fun a => s.balance a + (if a = e.account then e.amount else 0) })
    else (Outcome.rejected, s)
theorem nodup_append_singleton_aux (l : List EntryId) (x : EntryId) (hN : l.Nodup) (hFresh : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil =>
    exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | cons a t ih =>
    have hNpair : a ∉ t ∧ t.Nodup := by simpa using hN
    have hFpair : x ≠ a ∧ x ∉ t := by simpa using hFresh
    obtain ⟨haT, hNt⟩ := hNpair
    obtain ⟨hxNe, hxT⟩ := hFpair
    have ih' := ih hNt hxT
    have haFresh : a ∉ t ++ [x] := by
      intro hMem
      have hOr : a ∈ t ∨ a = x := by simpa using hMem
      rcases hOr with hInT | hEq
      · exact haT hInT
      · exact hxNe hEq.symm
    have haNe : ∀ y ∈ t ++ [x], a ≠ y := fun y hy hEq => haFresh (hEq ▸ hy)
    exact List.Pairwise.cons haNe ih'
theorem logSum_append_singleton_aux (log : List Entry) (e : Entry) (a : AccountId) : logSum (log ++ [e]) a = logSum log a + (if a = e.account then e.amount else 0) := by
  unfold logSum
  rw [sumOver_append]
  have h1 : sumOver [e] (fun e_ => if e_.account = a then e_.amount else 0) = (if e.account = a then e.amount else 0) := by simp
  have hCond : (if e.account = a then e.amount else (0 : Int)) = (if a = e.account then e.amount else 0) := by
    by_cases heq : a = e.account
    · subst heq
      simp
    · simp [heq, Ne.symm heq]
  rw [h1, hCond]
theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s e hFresh hValid
  simp [step, receiptOf_eq_none hFresh, hValid]
theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s e hFresh hInv
  simp [step, receiptOf_eq_none hFresh, hInv]
theorem req_duplicate : DuplicateReturnsOriginal step := by
  unfold DuplicateReturnsOriginal
  intro s e n hRec
  simp [step, hRec]
theorem req_effects : Effects step := by
  unfold Effects
  intro s e hFresh hValid
  have hR : receiptOf s.log e.id = none := receiptOf_eq_none hFresh
  have hStep : step s e = (Outcome.ok s.log.length, { accounts := s.accounts, log := s.log ++ [e], balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by simp [step, hR, hValid]
  rw [hStep]
  exact ⟨rfl, rfl, fun a => rfl⟩
theorem req_append_only : AppendOnly step := by
  unfold AppendOnly
  intro s e
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hStep : step s e = (Outcome.ok n, s) := by simp [step, hn]
    exact ⟨[], by simp [hStep]⟩
  · have hR : receiptOf s.log e.id = none := receiptOf_eq_none hMem
    by_cases hV : ValidEntry s e
    · have hStep : step s e = (Outcome.ok s.log.length, { accounts := s.accounts, log := s.log ++ [e], balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by simp [step, hR, hV]
      exact ⟨[e], by simp [hStep]⟩
    · have hStep : step s e = (Outcome.rejected, s) := by simp [step, hR, hV]
      exact ⟨[], by simp [hStep]⟩
theorem req_unique_ids : UniqueIds step := by
  unfold UniqueIds
  intro s e hNodup
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hStep : step s e = (Outcome.ok n, s) := by simp [step, hn]
    simpa [hStep] using hNodup
  · have hR : receiptOf s.log e.id = none := receiptOf_eq_none hMem
    by_cases hV : ValidEntry s e
    · have hStep : step s e = (Outcome.ok s.log.length, { accounts := s.accounts, log := s.log ++ [e], balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by simp [step, hR, hV]
      have hLog : (step s e).2.log = s.log ++ [e] := by simp [hStep]
      have hEq : ids (step s e).2.log = ids s.log ++ [e.id] := by simp [hLog, ids]
      have hFresh : e.id ∉ ids s.log := hMem
      have hN' : (ids s.log ++ [e.id]).Nodup := nodup_append_singleton_aux _ _ hNodup hFresh
      rw [hEq]
      exact hN'
    · have hStep : step s e = (Outcome.rejected, s) := by simp [step, hR, hV]
      simpa [hStep] using hNodup
theorem req_nonnegative : NonNegative step := by
  unfold NonNegative
  intro s e hNonneg a ha
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hStep : step s e = (Outcome.ok n, s) := by simp [step, hn]
    have h2 : (step s e).2 = s := by simp [hStep]
    have ha' : a ∈ s.accounts := by simpa [h2] using ha
    have hLe := hNonneg a ha'
    simpa [h2] using hLe
  · have hR : receiptOf s.log e.id = none := receiptOf_eq_none hMem
    by_cases hV : ValidEntry s e
    · have hStep : step s e = (Outcome.ok s.log.length, { accounts := s.accounts, log := s.log ++ [e], balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by simp [step, hR, hV]
      have ha' : a ∈ s.accounts := by simpa [hStep] using ha
      have hOld : 0 ≤ s.balance a := hNonneg a ha'
      have hVpair : e.account ∈ s.accounts ∧ e.amount ≠ 0 ∧ 0 ≤ s.balance e.account + e.amount := hV
      obtain ⟨_, _, hBal⟩ := hVpair
      by_cases heq : a = e.account
      · subst heq
        have hEq : (step s e).2.balance e.account = s.balance e.account + e.amount := by simp [hStep]
        rw [hEq]
        exact hBal
      · have hEq : (step s e).2.balance a = s.balance a := by simp [hStep, heq]
        rw [hEq]
        exact hOld
    · have hStep : step s e = (Outcome.rejected, s) := by simp [step, hR, hV]
      have h2 : (step s e).2 = s := by simp [hStep]
      have ha' : a ∈ s.accounts := by simpa [h2] using ha
      have hLe := hNonneg a ha'
      simpa [h2] using hLe
theorem req_consistent : StaysConsistent step := by
  unfold StaysConsistent
  intro s e hCons a
  by_cases hMem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hMem
    have hStep : step s e = (Outcome.ok n, s) := by simp [step, hn]
    have h2 : (step s e).2 = s := by simp [hStep]
    simpa [h2] using hCons a
  · have hR : receiptOf s.log e.id = none := receiptOf_eq_none hMem
    by_cases hV : ValidEntry s e
    · have hStep : step s e = (Outcome.ok s.log.length, { accounts := s.accounts, log := s.log ++ [e], balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by simp [step, hR, hV]
      have hBal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := by simp [hStep]
      have hLog : (step s e).2.log = s.log ++ [e] := by simp [hStep]
      rw [hBal, hLog, hCons a, logSum_append_singleton_aux]
    · have hStep : step s e = (Outcome.rejected, s) := by simp [step, hR, hV]
      have h2 : (step s e).2 = s := by simp [hStep]
      simpa [h2] using hCons a
end EntryLog
