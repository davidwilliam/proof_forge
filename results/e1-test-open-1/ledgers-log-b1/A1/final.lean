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

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hNotIn hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  unfold step
  rw [hRec]
  simp [hValid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hNotIn hInvalid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  unfold step
  rw [hRec]
  simp [hInvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hn
  unfold step
  rw [hn]

theorem req_effects : Effects step := by
  intro s e hNotIn hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  unfold step
  rw [hRec]
  simp only [hValid, ↓reduceIte]
  refine ⟨trivial, ⟨trivial, ?_⟩⟩
  intro a
  by_cases h : a = e.account <;> simp [h]

theorem req_append_only : AppendOnly step := by
  intro s e
  by_cases h : receiptOf s.log e.id = none
  · have h1 : (step s e).2.log = s.log ++ [] ∨ (step s e).2.log = s.log ++ [e] := by
      unfold step
      rw [h]
      by_cases hv : ValidEntry s e
      · rw [if_pos hv]; right; rfl
      · rw [if_neg hv]; left; simp
    rcases h1 with h1 | h1
    · exact ⟨[], h1⟩
    · exact ⟨[e], h1⟩
  · have hlog : (step s e).2.log = s.log := by
      unfold step
      cases hc : receiptOf s.log e.id with
      | none => contradiction
      | some n => rfl
    exact ⟨[], by rw [hlog]; simp⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hNodup
  have aux : ∀ (l : List Nat) (x : Nat), l.Nodup → x ∉ l → (l ++ [x]).Nodup := by
    intro l x hl hx
    induction l with
    | nil => simp
    | cons y ys ih =>
      simp at hl
      obtain ⟨hy, hys⟩ := hl
      have hx' : x ≠ y ∧ x ∉ ys := by simpa using hx
      have hxys : x ∉ ys := hx'.2
      have hyx : y ≠ x := Ne.symm hx'.1
      simp
      refine ⟨⟨?_, ?_⟩, ih hys hxys⟩
      · intro hmem
        exact hy hmem
      · intro heq
        exact hyx heq
  cases h : receiptOf s.log e.id with
  | none =>
    have hNone : (step s e).2.log = s.log ∨ (step s e).2.log = s.log ++ [e] := by
      unfold step
      rw [h]
      by_cases hV : ValidEntry s e
      · simp [hV]
      · simp [hV]
    rcases hNone with hL | hL
    · rw [hL]; exact hNodup
    · rw [hL]
      have hNotMem : e.id ∉ ids s.log := by
        intro hMem
        obtain ⟨n, hn⟩ := receiptOf_isSome hMem
        rw [hn] at h
        contradiction
      rw [ids_append]
      have hids1 : ids [e] = [e.id] := by simp [ids]
      rw [hids1]
      exact aux (ids s.log) e.id hNodup hNotMem
  | some n =>
    have hLog : (step s e).2.log = s.log := by
      unfold step
      rw [h]
    rw [hLog]
    exact hNodup

theorem req_nonnegative    : NonNegative step := by
  intro s e hPos a ha
  unfold step at ha ⊢
  by_cases hRec : ∃ n, receiptOf s.log e.id = some n
  · obtain ⟨n, hn⟩ := hRec
    rw [hn] at ha ⊢
    exact hPos a ha
  · have hNone : receiptOf s.log e.id = none := by
      cases h : receiptOf s.log e.id with
      | none => rfl
      | some n => exact absurd ⟨n, h⟩ hRec
    rw [hNone] at ha ⊢
    by_cases hV : ValidEntry s e
    · rw [if_pos hV] at ha ⊢
      -- ha : a ∈ s.accounts  (since accounts unchanged)
      -- need to show balance nonneg
      simp at ha ⊢
      by_cases heq : a = e.account
      · subst heq
        simp
        have hv := hV
        unfold ValidEntry at hv
        obtain ⟨_, _, hBal⟩ := hv
        exact hBal
      · simp [heq]
        exact hPos a ha
    · rw [if_neg hV] at ha ⊢
      exact hPos a ha

theorem req_consistent     : StaysConsistent step := by
  intro s e hCons
  intro a
  by_cases hDup : receiptOf s.log e.id = none
  · have hStepNone : step s e = if ValidEntry s e then (Outcome.ok s.log.length, { accounts := s.accounts, log := s.log ++ [e], balance := fun a_1 => if a_1 = e.account then s.balance a_1 + e.amount else s.balance a_1 }) else (Outcome.rejected, s) := by
      unfold step; rw [hDup]
    rw [hStepNone]
    by_cases hV : ValidEntry s e
    · rw [if_pos hV]
      have hBal : (fun a_1 => if a_1 = e.account then s.balance a_1 + e.amount else s.balance a_1) a = s.balance a + (if e.account = a then e.amount else 0) := by
        show (if a = e.account then s.balance a + e.amount else s.balance a) = s.balance a + (if e.account = a then e.amount else 0)
        by_cases heq : a = e.account
        · have heq2 : e.account = a := heq.symm
          have h1 : (if a = e.account then s.balance a + e.amount else s.balance a) = s.balance a + e.amount := if_pos heq
          have h2 : (if e.account = a then e.amount else (0 : Int)) = e.amount := if_pos heq2
          rw [h1, h2]
        · have heq2 : ¬ e.account = a := by intro h; exact heq h.symm
          have h1 : (if a = e.account then s.balance a + e.amount else s.balance a) = s.balance a := if_neg heq
          have h2 : (if e.account = a then e.amount else (0 : Int)) = 0 := if_neg heq2
          rw [h1, h2]; omega
      have hSum : logSum (s.log ++ [e]) a = logSum s.log a + (if e.account = a then e.amount else 0) := by
        unfold logSum; rw [sumOver_append]; simp
      show (fun a_1 => if a_1 = e.account then s.balance a_1 + e.amount else s.balance a_1) a = logSum (s.log ++ [e]) a
      rw [hBal, hSum, hCons a]
    · rw [if_neg hV]; exact hCons a
  · have hSome : ∃ n, receiptOf s.log e.id = some n := by
      cases h : receiptOf s.log e.id
      case none => contradiction
      case some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := hSome
    have hStepSome : step s e = (Outcome.ok n, s) := by unfold step; rw [hn]
    rw [hStepSome]
    exact hCons a

end EntryLog
