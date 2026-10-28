import EntryLog.Spec
import EntryLog.Lemmas
namespace EntryLog
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance
/-- Acceptance check for an entry with a new ID. -/
def accepts (s : State) (e : Entry) : Bool :=
  decide (ValidEntry s e)
def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if accepts s e then
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem req_append_only_aux : AppendOnly step := by
  unfold AppendOnly
  intro s e
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hs : step s e = (.ok n, s) := by unfold step; simp [hrec]
    rw [hs]; exact ⟨[], by simp⟩
  | none =>
    by_cases hacc : accepts s e = true
    · have hs : step s e = (.ok s.log.length,
         { s with log := s.log ++ [e],
                  balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        unfold step; simp [hrec, hacc]
      rw [hs]; exact ⟨[e], rfl⟩
    · have haccF : accepts s e = false := by cases h : accepts s e <;> simp_all
      have hs : step s e = (.rejected, s) := by unfold step; simp [hrec, haccF]
      rw [hs]; exact ⟨[], by simp⟩

theorem fresh_of_none {log : List Entry} {i : EntryId} (h : receiptOf log i = none) : i ∉ ids log := by
  induction log with
  | nil => simp [ids]
  | cons e es ih =>
    simp only [ids, List.map_cons, List.mem_cons, not_or]
    by_cases he : e.id = i
    · simp [receiptOf, he] at h
    · simp [receiptOf, he] at h
      exact ⟨fun contra => he contra.symm, ih h⟩

#check @List.Nodup
#check List.nodup_append

theorem req_nonnegative_aux2 : True := trivial
#check @of_decide_eq_true

theorem req_nonnegative_aux4 : NonNegative step := by
  intro s e hnn a ha
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hs : step s e = (.ok n, s) := by unfold step; simp [hrec]
    rw [hs] at ha ⊢
    exact hnn a ha
  | none =>
    by_cases hacc : accepts s e = true
    · have hdec : decide (ValidEntry s e) = true := by simpa [accepts] using hacc
      have hvalid := of_decide_eq_true hdec
      obtain ⟨hmem, hne, hge⟩ := hvalid
      have hs : (step s e).2.accounts = s.accounts := by unfold step; simp [hrec, hacc]
      have hb : (step s e).2.balance a =
        (if a = e.account then s.balance a + e.amount else s.balance a) := by unfold step; simp [hrec, hacc]
      rw [hs] at ha
      rw [hb]
      split
      · next heq => subst heq; exact hge
      · next heq => exact hnn a ha
    · have haccF : accepts s e = false := by cases h : accepts s e <;> simp_all
      have hs : step s e = (.rejected, s) := by unfold step; simp [hrec, haccF]
      rw [hs] at ha ⊢
      exact hnn a ha

theorem my_test_aux : True := trivial

theorem my_logsum_aux : logSum ([] : List Entry) 0 = 0 := by simp [logSum]

theorem my_have_test (s : State) (e : Entry) (hrec : receiptOf s.log e.id = none) (hacc : accepts s e = true) : (step s e).2.log = s.log ++ [e] := by
  have hs : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    simp [hrec, hacc]
  rw [hs]

theorem my_logSum_append_single (log : List Entry) (e : Entry) (a : AccountId) : logSum (log ++ [e]) a = logSum log a + (if e.account = a then e.amount else 0) := by
  unfold logSum
  rw [sumOver_append]
  simp [sumOver]

theorem my_consistent_check3 (s : State) (e : Entry) (a : AccountId) (hrec : receiptOf s.log e.id = none) (hacc : accepts s e = true) (hcons : ∀ a, s.balance a = logSum s.log a) : (step s e).2.balance a = logSum (step s e).2.log a := by
  have hlog : (step s e).2.log = s.log ++ [e] := by unfold step; simp [hrec, hacc]
  have hbal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by unfold step; simp [hrec, hacc]
  rw [hlog, hbal, my_logSum_append_single, hcons a]
  by_cases heq : a = e.account
  · subst heq
    rw [if_pos rfl, if_pos rfl]
  · have heq2 : e.account ≠ a := fun h => heq h.symm
    rw [if_neg heq, if_neg heq2, Int.add_zero]

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s e hfresh hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hfresh
  have hacc : accepts s e = true := by simp [accepts, hvalid]
  unfold step
  simp [hrec, hacc]

theorem req_invalid_noop   : InvalidNoop step := by
  unfold InvalidNoop
  intro s e hfresh hinvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hfresh
  have hacc : accepts s e = false := by simp [accepts, hinvalid]
  unfold step
  simp [hrec, hacc]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  unfold DuplicateReturnsOriginal
  intro s e n hn
  unfold step
  simp [hn]

theorem req_effects : Effects step := by
  unfold Effects
  intro s e hfresh hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hfresh
  have hacc : accepts s e = true := by simp [accepts, hvalid]
  have hstep : step s e = (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    simp [hrec, hacc]
  rw [hstep]
  refine ⟨rfl, rfl, ?_⟩
  intro a
  by_cases h : a = e.account <;> simp [h]

theorem req_append_only : AppendOnly step := by
  unfold AppendOnly
  intro s e
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hs : step s e = (.ok n, s) := by unfold step; simp [hrec]
    rw [hs]; exact ⟨[], by simp⟩
  | none =>
    by_cases hacc : accepts s e = true
    · have hs : step s e = (.ok s.log.length,
         { s with log := s.log ++ [e],
                  balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        unfold step; simp [hrec, hacc]
      rw [hs]; exact ⟨[e], rfl⟩
    · have haccF : accepts s e = false := by cases h : accepts s e <;> simp_all
      have hs : step s e = (.rejected, s) := by unfold step; simp [hrec, haccF]
      rw [hs]; exact ⟨[], by simp⟩

theorem req_unique_ids     : UniqueIds step := by
  unfold UniqueIds
  intro s e hn
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hs : step s e = (.ok n, s) := by unfold step; simp [hrec]
    rw [hs]
    simpa using hn
  | none =>
    by_cases hacc : accepts s e = true
    · have hs : step s e = (.ok s.log.length,
         { s with log := s.log ++ [e],
                  balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
          unfold step; simp [hrec, hacc]
      rw [hs]
      simp only
      have hfresh : e.id ∉ ids s.log := fresh_of_none hrec
      have hids : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by
        rw [ids_append]; rfl
      rw [hids]
      rw [List.nodup_append]
      refine ⟨hn, by simp, ?_⟩
      intro a ha b hb heq
      simp at hb
      subst hb
      exact hfresh (heq ▸ ha)
    · have haccF : accepts s e = false := by cases h : accepts s e <;> simp_all
      have hs : step s e = (.rejected, s) := by unfold step; simp [hrec, haccF]
      rw [hs]
      simpa using hn

theorem req_nonnegative : NonNegative step := by
  intro s e hnn a ha
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hs : step s e = (.ok n, s) := by unfold step; simp [hrec]
    rw [hs] at ha ⊢
    exact hnn a ha
  | none =>
    by_cases hacc : accepts s e = true
    · have hdec : decide (ValidEntry s e) = true := by simpa [accepts] using hacc
      have hvalid := of_decide_eq_true hdec
      obtain ⟨hmem, hne, hge⟩ := hvalid
      have hs : (step s e).2.accounts = s.accounts := by unfold step; simp [hrec, hacc]
      have hb : (step s e).2.balance a =
        (if a = e.account then s.balance a + e.amount else s.balance a) := by unfold step; simp [hrec, hacc]
      rw [hs] at ha
      rw [hb]
      split
      · next heq => subst heq; exact hge
      · next heq => exact hnn a ha
    · have haccF : accepts s e = false := by cases h : accepts s e <;> simp_all
      have hs : step s e = (.rejected, s) := by unfold step; simp [hrec, haccF]
      rw [hs] at ha ⊢
      exact hnn a ha

theorem req_consistent : StaysConsistent step := by
  unfold StaysConsistent
  intro s e hcons a
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hs : step s e = (.ok n, s) := by unfold step; simp [hrec]
    rw [hs]
    exact hcons a
  | none =>
    by_cases hacc : accepts s e = true
    · exact my_consistent_check3 s e a hrec hacc hcons
    · have haccF : accepts s e = false := by cases h : accepts s e <;> simp_all
      have hs : step s e = (.rejected, s) := by unfold step; simp [hrec, haccF]
      rw [hs]
      exact hcons a

end EntryLog
