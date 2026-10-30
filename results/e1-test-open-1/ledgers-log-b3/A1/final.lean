import EntryLog.Spec
import EntryLog.Lemmas
namespace EntryLog
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance
def step : Impl := fun s e =>
  match h : receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if ValidEntry s e then
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem check_nodup_lemmas2 : True := by
  have h1 : ∀ (l₁ l₂ : List Nat), (l₁ ++ l₂).Nodup ↔ l₁.Nodup ∧ l₂.Nodup ∧ ∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y := by
    intro l₁ l₂
    exact List.nodup_append
  trivial

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hId hValid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hId
  unfold step
  -- try rw
  rw [hrec]
  simp [hValid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hId hValid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hId
  unfold step
  rw [hrec]
  simp [hValid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  rw [h]

theorem req_effects : Effects step := by
  intro s e hId hValid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hId
  have hstep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    rw [hrec]
    simp [hValid]
  refine ⟨?_, ?_, ?_⟩
  · rw [hstep]
  · rw [hstep]
  · intro a
    rw [hstep]
    simp only
    by_cases ha : a = e.account
    · simp [ha]
    · simp [ha]

theorem req_append_only : AppendOnly step := by
  intro s e
  by_cases h : receiptOf s.log e.id = none
  · by_cases hV : ValidEntry s e
    · have hstep : (step s e).2.log = s.log ++ [e] := by
        unfold step
        rw [h]
        simp [hV]
      exact ⟨[e], hstep⟩
    · have hstep : (step s e).2.log = s.log := by
        unfold step
        rw [h]
        simp [hV]
      exact ⟨[], by rw [hstep, List.append_nil]⟩
  · have hsome : ∃ n, receiptOf s.log e.id = some n := by
      cases hm : receiptOf s.log e.id with
      | none => contradiction
      | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := hsome
    have hstep : (step s e).2.log = s.log := by
      unfold step
      rw [hn]
    exact ⟨[], by rw [hstep, List.append_nil]⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hNodup
  by_cases hRec : receiptOf s.log e.id = none
  · by_cases hV : ValidEntry s e
    · have hLog : (step s e).2.log = s.log ++ [e] := by
        unfold step
        rw [hRec]
        simp [hV]
      rw [hLog]
      have hid : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by simp [ids]
      rw [hid]
      have hNotMem : e.id ∉ ids s.log := by
        intro hMem
        obtain ⟨n, hn⟩ := receiptOf_isSome hMem
        rw [hn] at hRec
        contradiction
      have h1 : (ids s.log ++ [e.id]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hNodup, by simp, ?_⟩
        intro x hx y hy
        simp at hy
        rcases hy with rfl
        intro heq
        rw [heq] at hx
        exact hNotMem hx
      exact h1
    · have hLog : (step s e).2.log = s.log := by
        unfold step
        rw [hRec]
        simp [hV]
      rw [hLog]
      exact hNodup
  · have hex : ∃ n, receiptOf s.log e.id = some n := by
      cases hm : receiptOf s.log e.id with
      | none => contradiction
      | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := hex
    have hLog : (step s e).2.log = s.log := by
      unfold step
      rw [hn]
    rw [hLog]
    exact hNodup

theorem req_nonnegative : NonNegative step := by
  intro s e hNonneg a ha
  by_cases hrec : receiptOf s.log e.id = none
  · by_cases hV : ValidEntry s e
    · have hstep : step s e = (Outcome.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        unfold step
        rw [hrec]
        simp [hV]
      rw [hstep] at ha ⊢
      simp at ha
      have : (({ s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a } : State).balance a) = (if a = e.account then s.balance a + e.amount else s.balance a) := rfl
      rw [this]
      by_cases heq : a = e.account
      · simp [heq]
        exact hV.2.2
      · simp [heq]; exact hNonneg a ha
    · have hstep : step s e = (Outcome.rejected, s) := by
        unfold step
        rw [hrec]
        simp [hV]
      rw [hstep] at ha ⊢
      simp at ha ⊢
      exact hNonneg a ha
  · have hex : ∃ n, receiptOf s.log e.id = some n := by
      cases hm : receiptOf s.log e.id
      · contradiction
      · exact ⟨_, rfl⟩
    obtain ⟨n, hn⟩ := hex
    have hstep : step s e = (Outcome.ok n, s) := by
      unfold step
      rw [hn]
    rw [hstep] at ha ⊢
    simp at ha ⊢
    exact hNonneg a ha

theorem req_consistent     : StaysConsistent step := by
  intro s e hCons a
  show (step s e).2.balance a = logSum (step s e).2.log a
  by_cases hRec : receiptOf s.log e.id = none
  · by_cases hV : ValidEntry s e
    · have hEq : (step s e).2 = ({ s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a } : State) := by
        unfold step
        rw [hRec]
        simp [hV]
      have hBal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by
        rw [hEq]
      have hLog : (step s e).2.log = s.log ++ [e] := by
        rw [hEq]
      rw [hBal, hLog]
      have hLogSum : logSum (s.log ++ [e]) a = logSum s.log a + (if e.account = a then e.amount else 0) := by
        unfold logSum
        rw [sumOver_append]
        have h1 : sumOver [e] (fun e => if e.account = a then e.amount else 0) = (if e.account = a then e.amount else 0) := by
          simp [sumOver_cons, sumOver_nil]
        rw [h1]
      rw [hLogSum, hCons a]
      by_cases heq : a = e.account
      · have heq2 : e.account = a := heq.symm
        rw [if_pos heq, if_pos heq2]
      · have heq2 : ¬ (e.account = a) := by intro h; exact heq h.symm
        rw [if_neg heq, if_neg heq2, Int.add_zero]
    · have hEq : (step s e).2 = s := by
        unfold step
        rw [hRec]
        simp [hV]
      rw [hEq]
      exact hCons a
  · have hex : ∃ n, receiptOf s.log e.id = some n := by
      cases hm : receiptOf s.log e.id
      · contradiction
      · exact ⟨_, rfl⟩
    obtain ⟨n, hn⟩ := hex
    have hEq : (step s e).2 = s := by
      unfold step
      rw [hn]
    rw [hEq]
    exact hCons a

end EntryLog
