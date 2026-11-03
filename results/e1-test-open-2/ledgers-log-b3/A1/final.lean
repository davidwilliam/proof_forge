import EntryLog.Spec
import EntryLog.Lemmas
namespace EntryLog
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance
def step : Impl := fun s e =>
  match hr : receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if h : ValidEntry s e then
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem aux_dup : DuplicateReturnsOriginal step := by
  intro s e n hRec
  unfold step
  -- use the hRec to rewrite the match
  have : (match hr : receiptOf s.log e.id with | some k => (Outcome.ok k, s) | none => (if h : ValidEntry s e then (Outcome.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) else (Outcome.rejected, s))) = (Outcome.ok n, s) := by
    have h_eq : receiptOf s.log e.id = some n := hRec
    cases h : receiptOf s.log e.id with
    | none => rw [h] at h_eq; contradiction
    | some m =>
      simp [h]
      rw [h] at h_eq
      injection h_eq
  exact this

private theorem step_accounts' (s : State) (e : Entry) : (step s e).2.accounts = s.accounts := by
  unfold step
  cases h : receiptOf s.log e.id with
  | some n => simp [h]
  | none =>
    simp only [h]
    by_cases hv : ValidEntry s e <;> simp [hv]

theorem logSum_append_single_aux3 (log : List Entry) (e : Entry) (a : AccountId) :
    logSum (log ++ [e]) a = logSum log a + if e.account = a then e.amount else 0 := by
  unfold logSum
  rw [sumOver_append]
  simp

theorem logSum_append_single_aux4 (log : List Entry) (e : Entry) (a : AccountId) :
    logSum (log ++ [e]) a = logSum log a + (if a = e.account then e.amount else 0) := by
  have h := logSum_append_single_aux3 log e a
  have heq : (if e.account = a then e.amount else (0 : Int)) = (if a = e.account then e.amount else 0) := by
    by_cases he : e.account = a
    · rw [if_pos he, if_pos he.symm]
    · rw [if_neg he, if_neg (fun hh => he hh.symm)]
  rw [heq] at h
  exact h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hNotIn hValid
  unfold step
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  -- rw the scrutinee
  have h1 : (match h : receiptOf s.log e.id with | some n => (Outcome.ok n, s) | none => if h : ValidEntry s e then (Outcome.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) else (Outcome.rejected, s)) = (if h : ValidEntry s e then (Outcome.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) else (Outcome.rejected, s)) := by rw [hRec]
  rw [h1]
  simp [hValid]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s e hNotIn hInvalid
  unfold step
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  have h1 : (match h : receiptOf s.log e.id with | some n => (Outcome.ok n, s) | none => if h : ValidEntry s e then (Outcome.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) else (Outcome.rejected, s)) = (if h : ValidEntry s e then (Outcome.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) else (Outcome.rejected, s)) := by rw [hRec]
  rw [h1]
  simp [hInvalid]

theorem req_duplicate      : DuplicateReturnsOriginal step := aux_dup

theorem req_effects : Effects step := by
  intro s e hNotIn hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  have hStep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    rw [hRec]
    simp [hValid]
  rw [hStep]
  refine ⟨rfl, rfl, fun a => ?_⟩
  by_cases ha : a = e.account
  · simp [ha]
  · simp [ha]

theorem req_append_only    : AppendOnly step := by
  intro s e
  unfold step
  cases h : receiptOf s.log e.id with
  | none =>
    by_cases hv : ValidEntry s e
    · simp only [h, hv, dite_true]
      exact ⟨[e], rfl⟩
    · simp only [h, hv, dite_false]
      exact ⟨[], by simp⟩
  | some n =>
    simp only [h]
    exact ⟨[], by simp⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hNodup
  unfold step
  cases h : receiptOf s.log e.id with
  | some n =>
    simp only [h]
    exact hNodup
  | none =>
    have hNotIn : e.id ∉ ids s.log := by
      intro hIn
      obtain ⟨n, hn⟩ := receiptOf_isSome hIn
      rw [hn] at h
      contradiction
    by_cases hv : ValidEntry s e
    · simp only [hv, dite_true]
      have hid : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by
        simp [ids]
      rw [hid]
      have aux : ∀ (l : List EntryId) (x : EntryId), l.Nodup → x ∉ l → (l ++ [x]).Nodup := by
        intro l x hl hx
        induction l with
        | nil => exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
        | cons hd tl ih =>
          have hl' : tl.Nodup := (List.nodup_cons.mp hl).2
          have hdNotInTl : hd ∉ tl := (List.nodup_cons.mp hl).1
          have xNotInTl : x ∉ tl := fun h => hx (List.mem_cons_of_mem hd h)
          have hdNeX : hd ≠ x := by
            intro heq
            apply hx
            rw [← heq]
            exact List.Mem.head ..
          have ihRes := ih hl' xNotInTl
          have h1 : hd ∉ tl ++ [x] := by
            intro hmem
            rw [List.mem_append] at hmem
            rcases hmem with h1 | h2
            · exact hdNotInTl h1
            · rw [List.mem_singleton.mp h2] at hdNeX
              exact hdNeX rfl
          exact List.nodup_cons.mpr ⟨h1, ihRes⟩
      exact aux _ _ hNodup hNotIn
    · simp only [hv, dite_false]
      exact hNodup

theorem req_nonnegative : NonNegative step := by
  intro s e hNonNeg a ha
  have hAcc : (step s e).2.accounts = s.accounts := step_accounts' s e
  rw [hAcc] at ha
  unfold step at ⊢
  cases hR : receiptOf s.log e.id with
  | some n =>
    simp [hR]
    exact hNonNeg a ha
  | none =>
    by_cases hV : ValidEntry s e
    · simp [hR, hV]
      by_cases heq : a = e.account
      · simp only [heq, ite_true]
        have hV2 := hV
        simp [ValidEntry] at hV2
        exact hV2.2.2
      · simp [heq]
        exact hNonNeg a ha
    · simp [hR, hV]
      exact hNonNeg a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hCons a
  unfold step
  cases hR : receiptOf s.log e.id with
  | some n =>
    simp only [hR]
    exact hCons a
  | none =>
    simp only [hR]
    by_cases hV : ValidEntry s e
    · simp only [hV, dite_true]
      have h1 := logSum_append_single_aux4 s.log e a
      have h2 := hCons a
      by_cases heq : a = e.account
      · simp only [heq, ite_true] at h1 h2 ⊢
        omega
      · simp only [heq, ite_false] at h1 h2 ⊢
        omega
    · simp only [hV, dite_false]
      exact hCons a

end EntryLog
