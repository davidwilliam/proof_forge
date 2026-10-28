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

theorem req_valid_succeeds_aux : ValidSucceeds step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  show (step s e).1 = _
  unfold step
  rw [hrec]
  simp [hvalid]

theorem mytest1 : List.Nodup ([] : List Nat) := List.nodup_nil

theorem mytest2 (a : Nat) (l : List Nat) (h1 : a ∉ l) (h2 : List.Nodup l) : List.Nodup (a :: l) := List.nodup_cons.mpr ⟨h1, h2⟩

theorem logSum_append_single2 (log : List Entry) (e : Entry) (a : AccountId) :
    logSum (log ++ [e]) a = logSum log a + (if e.account = a then e.amount else 0) := by
  unfold logSum
  rw [sumOver_append]
  simp

theorem fresh_of_receipt_none (s : State) (e : Entry) (h : receiptOf s.log e.id = none) : e.id ∉ ids s.log := by
  intro hmem
  obtain ⟨n, hn⟩ := receiptOf_isSome hmem
  rw [hn] at h
  simp at h

theorem nodup_append_singleton_aux (l : List EntryId) (x : EntryId) (hn : l.Nodup) (hm : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hpair := List.nodup_cons.mp hn
    have h1 : hd ∉ tl := hpair.1
    have h2 : List.Nodup tl := hpair.2
    simp only [List.mem_cons, not_or] at hm
    have ih' := ih h2 hm.2
    simp only [List.cons_append]
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      rw [List.mem_append] at hmem
      simp at hmem
      rcases hmem with h | h
      · exact h1 h
      · exact hm.1 h.symm
    · exact ih'

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  show (step s e).1 = _
  unfold step
  rw [hrec]
  simp [hvalid]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s e hnotin hinvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  show step s e = _
  unfold step
  rw [hrec]
  simp [hinvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hn
  show step s e = _
  unfold step
  rw [hn]

theorem req_effects : Effects step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  have hstep : step s e = (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    rw [hrec]
    simp [hvalid]
  refine ⟨?_, ?_, ?_⟩
  · show (step s e).2.accounts = s.accounts
    rw [hstep]
  · show (step s e).2.log = s.log ++ [e]
    rw [hstep]
  · intro a
    show (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0)
    rw [hstep]
    show (if a = e.account then s.balance a + e.amount else s.balance a) = _
    by_cases h : a = e.account <;> simp [h]

theorem req_append_only : AppendOnly step := by
  intro s e
  cases hrec : receiptOf s.log e.id with
  | some n =>
    refine ⟨[], ?_⟩
    have hstep : step s e = (.ok n, s) := by unfold step; rw [hrec]
    simp [hstep]
  | none =>
    by_cases hvalid : ValidEntry s e
    · refine ⟨[e], ?_⟩
      have hstep : step s e = (.ok s.log.length,
        { s with log := s.log ++ [e],
                 balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        unfold step; rw [hrec]; simp [hvalid]
      simp [hstep]
    · refine ⟨[], ?_⟩
      have hstep : step s e = (.rejected, s) := by unfold step; rw [hrec]; simp [hvalid]
      simp [hstep]

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hstep : step s e = (.ok n, s) := by unfold step; rw [hrec]
    have h2 : (step s e).2 = s := by rw [hstep]
    rw [h2]
    exact hnodup
  | none =>
    by_cases hvalid : ValidEntry s e
    · have hfresh : e.id ∉ ids s.log := fresh_of_receipt_none s e hrec
      have hstep : step s e = (.ok s.log.length,
        { s with log := s.log ++ [e],
                 balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        unfold step; rw [hrec]; simp [hvalid]
      have hlog : (step s e).2.log = s.log ++ [e] := by rw [hstep]
      rw [hlog]
      have heq : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by simp [ids]
      rw [heq]
      exact nodup_append_singleton_aux (ids s.log) e.id hnodup hfresh
    · have hstep : step s e = (.rejected, s) := by unfold step; rw [hrec]; simp [hvalid]
      have h2 : (step s e).2 = s := by rw [hstep]
      rw [h2]
      exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hpos a ha
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hstep : step s e = (.ok n, s) := by unfold step; rw [hrec]
    rw [hstep] at ha ⊢
    simp at ha ⊢
    exact hpos a ha
  | none =>
    by_cases hvalid : ValidEntry s e
    · have hstep : step s e = (.ok s.log.length,
        { s with log := s.log ++ [e],
                 balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        unfold step; rw [hrec]; simp [hvalid]
      rw [hstep] at ha ⊢
      simp at ha ⊢
      by_cases heq : a = e.account
      · simp [heq]
        exact hvalid.2.2
      · simp [heq]
        exact hpos a ha
    · have hstep : step s e = (.rejected, s) := by unfold step; rw [hrec]; simp [hvalid]
      rw [hstep] at ha ⊢
      simp at ha ⊢
      exact hpos a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons a
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hstep : step s e = (.ok n, s) := by unfold step; rw [hrec]
    have h2 : (step s e).2 = s := by rw [hstep]
    rw [h2]
    exact hcons a
  | none =>
    by_cases hvalid : ValidEntry s e
    · have hfresh : e.id ∉ ids s.log := fresh_of_receipt_none s e hrec
      obtain ⟨hacc, hlog, hbal⟩ := req_effects s e hfresh hvalid
      have hbal_a := hbal a
      have hlogrw : (step s e).2.log = s.log ++ [e] := hlog
      rw [hlogrw, hbal_a, hcons a, logSum_append_single2]
      by_cases h : a = e.account
      · subst h
        simp
      · have he : ¬ (e.account = a) := fun h' => h h'.symm
        simp [h, he]
    · have hstep : step s e = (.rejected, s) := by unfold step; rw [hrec]; simp [hvalid]
      have h2 : (step s e).2 = s := by rw [hstep]
      rw [h2]
      exact hcons a

end EntryLog
