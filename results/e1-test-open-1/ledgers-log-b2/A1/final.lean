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

theorem aux_nodup_singleton_append {α : Type} [DecidableEq α] (l : List α) (a : α) (h1 : l.Nodup) (h2 : a ∉ l) : (l ++ [a]).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have h_x_notin_xs : x ∉ xs := (List.nodup_cons.mp h1).1
    have h_xs_nodup : xs.Nodup := (List.nodup_cons.mp h1).2
    have h_a_notin_xs : a ∉ xs := fun hmem => h2 (List.mem_cons_of_mem _ hmem)
    have h_a_ne_x : a ≠ x := fun heq => h2 (heq ▸ List.Mem.head _)
    have ih' := ih h_xs_nodup h_a_notin_xs
    rw [List.cons_append]
    rw [List.nodup_cons]
    refine ⟨?_, ih'⟩
    intro hmem
    rw [List.mem_append] at hmem
    rcases hmem with hmem1 | hmem2
    · exact h_x_notin_xs hmem1
    · simp at hmem2
      exact h_a_ne_x hmem2.symm

theorem logSum_append_singleton2 (l : List Entry) (e : Entry) (a : AccountId) :
    logSum (l ++ [e]) a = logSum l a + if e.account = a then e.amount else 0 := by
  unfold logSum
  rw [sumOver_append]
  simp

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hNotIn hValid
  simp [step, receiptOf_eq_none hNotIn, hValid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hNotIn hInvalid
  simp [step, receiptOf_eq_none hNotIn, hInvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  simp [step, h]

theorem req_effects : Effects step := by
  intro s e hNotIn hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  have hStep : step s e = (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
    simp [step, hRec, hValid]
  exact ⟨by rw [hStep], by rw [hStep], by intro a; rw [hStep]⟩

theorem req_append_only : AppendOnly step := by
  intro s e
  cases h : receiptOf s.log e.id with
  | none =>
    by_cases hV : ValidEntry s e
    · have hstep : (step s e).2.log = s.log ++ [e] := by
        simp [step, h, hV]
      exact ⟨[e], hstep⟩
    · have hstep : (step s e).2.log = s.log := by
        simp [step, h, hV]
      exact ⟨[], by simp [hstep]⟩
  | some n =>
    have hstep : (step s e).2.log = s.log := by
      simp [step, h]
    exact ⟨[], by simp [hstep]⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hNodup
  cases h : receiptOf s.log e.id with
  | some n =>
    have hstep : (step s e).2.log = s.log := by simp [step, h]
    rw [hstep]; exact hNodup
  | none =>
    by_cases hV : ValidEntry s e
    · have hstep : (step s e).2.log = s.log ++ [e] := by simp [step, h, hV]
      rw [hstep]
      have hNotMem : e.id ∉ ids s.log := by
        intro hmem
        have : ∃ n, receiptOf s.log e.id = some n := receiptOf_isSome hmem
        obtain ⟨n, hn⟩ := this
        rw [hn] at h
        contradiction
      have h_ids : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by simp [ids]
      rw [h_ids]
      exact aux_nodup_singleton_append _ _ hNodup hNotMem
    · have hstep : (step s e).2.log = s.log := by simp [step, h, hV]
      rw [hstep]; exact hNodup

theorem req_nonnegative : NonNegative step := by
  intro s e hPos a ha
  unfold step at ha ⊢
  cases hRec : receiptOf s.log e.id with
  | some n =>
    simp [hRec] at ha ⊢
    exact hPos a ha
  | none =>
    by_cases hV : ValidEntry s e
    · simp [hRec, hV] at ha ⊢
      by_cases heq : a = e.account
      · have h1 : 0 ≤ s.balance e.account + e.amount := hV.2.2
        have h2 : s.balance a + (if a = e.account then e.amount else (0:Int)) = s.balance e.account + e.amount := by
          rw [if_pos heq, heq]
        rw [h2]
        exact h1
      · have h2 : (if a = e.account then e.amount else (0:Int)) = 0 := by simp [heq]
        have h3 : s.balance a + (if a = e.account then e.amount else (0:Int)) = s.balance a := by rw [h2, Int.add_zero]
        rw [h3]
        exact hPos a ha
    · simp [hRec, hV] at ha ⊢
      exact hPos a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hCons
  intro a
  have hCons' : s.balance a = logSum s.log a := hCons a
  cases hRec : receiptOf s.log e.id with
  | some n =>
    have hstep : (step s e).2 = s := by simp [step, hRec]
    have hlog : (step s e).2.log = s.log := by rw [hstep]
    have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
    rw [hlog, hbal]
    exact hCons'
  | none =>
    by_cases hV : ValidEntry s e
    · have hlog : (step s e).2.log = s.log ++ [e] := by simp [step, hRec, hV]
      have hbal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := by simp [step, hRec, hV]
      rw [hlog, hbal, hCons']
      have h_eq : (if a = e.account then e.amount else (0:Int)) = (if e.account = a then e.amount else 0) := by
        by_cases heq : a = e.account
        · rw [if_pos heq, if_pos heq.symm]
        · rw [if_neg heq, if_neg (Ne.symm heq)]
      rw [h_eq]
      exact (logSum_append_singleton2 s.log e a).symm
    · have hstep : (step s e).2 = s := by simp [step, hRec, hV]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hlog, hbal]
      exact hCons'

end EntryLog
