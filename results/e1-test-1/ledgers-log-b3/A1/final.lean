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
                balance := fun a => s.balance a + (if a = e.account then e.amount else 0) })
    else (.rejected, s)

theorem req_duplicate_dbg : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  rw [h]

theorem req_append_only_aux : AppendOnly step := by
  intro s e
  unfold step
  split
  · exact ⟨[], by simp⟩
  · split
    · exact ⟨[e], rfl⟩
    · exact ⟨[], by simp⟩

theorem req_append_only2 : AppendOnly step := by
  intro s e
  unfold step
  split
  · exact ⟨[], by simp⟩
  · split
    · exact ⟨[e], rfl⟩
    · exact ⟨[], by simp⟩

theorem foo_test : True := trivial

theorem uid_append_test2 : True := trivial

theorem uid_fresh_helper : forall (log : List Entry) (i : EntryId), receiptOf log i = none -> i ∉ ids log := by intro log i h hmem; obtain ⟨n, hn⟩ := receiptOf_isSome hmem; rw [hn] at h; contradiction

theorem tmp_check1b (s : State) (e : Entry) (n : Nat) (h : receiptOf s.log e.id = some n) :
    (step s e).2 = s := by
  unfold step
  rw [h]

theorem tmp_check2b (s : State) (e : Entry) (a : AccountId) (h : receiptOf s.log e.id = none) (hv : ValidEntry s e) :
    (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := by
  unfold step
  rw [h]
  simp [hv]

theorem tmp_check3b (s : State) (e : Entry) (h : receiptOf s.log e.id = none) (hv : ¬ ValidEntry s e) :
    (step s e).2 = s := by
  unfold step
  rw [h]
  simp [hv]

theorem tmp_acc_valid (s : State) (e : Entry) (h : receiptOf s.log e.id = none) (hv : ValidEntry s e) :
    (step s e).2.accounts = s.accounts := by
  unfold step
  rw [h]
  simp [hv]

theorem tmp_acc_inval (s : State) (e : Entry) (h : receiptOf s.log e.id = none) (hv : ¬ ValidEntry s e) :
    (step s e).2.accounts = s.accounts := by
  unfold step
  rw [h]
  simp [hv]

theorem tmp_cons_neg_test (s : State) (e : Entry) (a : AccountId)
    (hcons : Consistent s)
    (hrec : receiptOf s.log e.id = none) (hv : ¬ ValidEntry s e) :
    (step s e).2.balance a = logSum (step s e).2.log a := by
  have h2 : (step s e).2 = s := tmp_check3b s e hrec hv
  rw [h2]
  exact hcons a

theorem logSum_append_single3 (log : List Entry) (e : Entry) (a : AccountId) :
    logSum (log ++ [e]) a = logSum log a + (if e.account = a then e.amount else 0) := by
  unfold logSum
  rw [sumOver_append]
  simp

theorem if_account_symm (a b : AccountId) (v : Int) :
    (if a = b then v else 0) = (if b = a then v else 0) := by
  by_cases h : a = b
  · subst h; rfl
  · have h' : ¬ (b = a) := fun hh => h hh.symm
    rw [if_neg h, if_neg h']

theorem nodup_append_single_my2 (l : List EntryId) (x : EntryId) (h : l.Nodup) (hmem : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.nodup_cons] at h
    obtain ⟨hhd, htl⟩ := h
    simp only [List.mem_cons, not_or] at hmem
    obtain ⟨hne_symm, hx_tl⟩ := hmem
    have hne : hd ≠ x := fun heq => hne_symm heq.symm
    have ih' := ih htl hx_tl
    simp only [List.cons_append]
    rw [List.nodup_cons]
    constructor
    · intro hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · exact hhd hm
      · simp at hm
        exact hne hm
    · exact ih'

theorem ids_single_check (e : Entry) : ids [e] = [e.id] := by simp [ids]

theorem ids_append_single_check (log : List Entry) (e : Entry) : ids (log ++ [e]) = ids log ++ [e.id] := by simp [ids]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  unfold step
  rw [hrec]
  simp [hvalid]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s e hnotin hinvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  unfold step
  rw [hrec]
  simp [hinvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  rw [h]

theorem req_effects        : Effects step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  unfold step
  rw [hrec]
  simp [hvalid]

theorem req_append_only : AppendOnly step := by
  intro s e
  unfold step
  split
  · exact ⟨[], by simp⟩
  · split
    · exact ⟨[e], rfl⟩
    · exact ⟨[], by simp⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have h2 : (step s e).2 = s := tmp_check1b s e n hrec
    rw [h2]
    exact hnodup
  | none =>
    by_cases hv : ValidEntry s e
    · have hlog : (step s e).2.log = s.log ++ [e] := by
        unfold step
        rw [hrec]
        simp [hv]
      rw [hlog, ids_append_single_check]
      have hfresh : e.id ∉ ids s.log := uid_fresh_helper s.log e.id hrec
      exact nodup_append_single_my2 (ids s.log) e.id hnodup hfresh
    · have h2 : (step s e).2 = s := tmp_check3b s e hrec hv
      rw [h2]
      exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hpos a ha
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have h2 : (step s e).2 = s := tmp_check1b s e n hrec
    rw [h2] at ha ⊢
    exact hpos a ha
  | none =>
    by_cases hv : ValidEntry s e
    · have hacc : (step s e).2.accounts = s.accounts := tmp_acc_valid s e hrec hv
      rw [hacc] at ha
      have hbal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) :=
        tmp_check2b s e a hrec hv
      rw [hbal]
      rcases hv with ⟨hmem, hne, hle⟩
      by_cases heq : a = e.account
      · subst heq; simpa using hle
      · rw [if_neg heq]
        simpa using hpos a ha
    · have h2 : (step s e).2 = s := tmp_check3b s e hrec hv
      rw [h2] at ha ⊢
      exact hpos a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons a
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have h2 : (step s e).2 = s := tmp_check1b s e n hrec
    rw [h2]
    exact hcons a
  | none =>
    by_cases hv : ValidEntry s e
    · have hbal : (step s e).2.balance a
          = s.balance a + (if a = e.account then e.amount else 0) :=
        tmp_check2b s e a hrec hv
      have hlog : (step s e).2.log = s.log ++ [e] := by
        unfold step
        rw [hrec]
        simp [hv]
      rw [hbal, hlog, hcons a, logSum_append_single3, if_account_symm]
    · exact tmp_cons_neg_test s e a hcons hrec hv

end EntryLog
