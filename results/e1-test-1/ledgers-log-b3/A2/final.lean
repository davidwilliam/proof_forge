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

theorem req_valid_succeeds_test1 : ValidSucceeds step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  have h1 : step s e = (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    rw [hrec]
    rw [if_pos hvalid]
  rw [h1]

theorem my_test_xyz : True := trivial

theorem probe_nodup_nil : List.Nodup ([] : List Nat) := by exact List.nodup_nil

theorem probe_mem_append_test : True := trivial

theorem probe2 : List.Nodup [3] := by simp

theorem probe3 : True := trivial

theorem probe_cons_rw (a : Nat) (t : List Nat) (x : Nat) : ((a :: t) ++ [x]) = (a :: (t ++ [x])) := by simp

theorem probeNodupA : True := trivial
#check List.Nodup
#check List.Pairwise

theorem nodup_singleton_test (x : Nat) : ([x] : List Nat).Nodup := by
  rw [List.nodup_cons]
  exact ⟨by simp, List.nodup_nil⟩

theorem req_nonnegative_aux2 : NonNegative step := by
  intro s e hnn a ha
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hst : step s e = ((.ok n : Outcome), s) := by unfold step; rw [hrec]
    have hacc : (step s e).2.accounts = s.accounts := by rw [hst]
    have hbal : (step s e).2.balance a = s.balance a := by rw [hst]
    rw [hacc] at ha
    rw [hbal]
    exact hnn a ha
  | none =>
    by_cases hv : ValidEntry s e
    · have hst : step s e = ((.ok s.log.length : Outcome),
        { s with log := s.log ++ [e],
                 balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        unfold step; rw [hrec, if_pos hv]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hst]
      have hbal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by rw [hst]
      rw [hacc] at ha
      rw [hbal]
      by_cases heq : a = e.account
      · subst heq
        simp only [if_true]
        obtain ⟨hmem, hne, hle⟩ := hv
        exact hle
      · simp [heq]
        exact hnn a ha
    · have hst : step s e = ((.rejected : Outcome), s) := by unfold step; rw [hrec, if_neg hv]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hst]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hst]
      rw [hacc] at ha
      rw [hbal]
      exact hnn a ha

theorem logSum_append_single (log : List Entry) (e : Entry) (a : AccountId) :
    logSum (log ++ [e]) a = logSum log a + (if e.account = a then e.amount else 0) := by
  unfold logSum
  rw [sumOver_append]
  simp

theorem probe_nodup_append_form : True := by
  have h1 : ∀ (l : List Nat), l.Nodup → True := fun _ _ => trivial
  trivial
#check @List.nodup_cons
#check @List.Nodup
#check @List.mem_append

theorem nodup_append_singleton_aux (l : List Nat) (x : Nat) (h1 : l.Nodup) (h2 : x ∉ l) : (l ++ [x]).Nodup := by
  rw [List.nodup_append]
  refine ⟨h1, by simp, ?_⟩
  intro a ha b hb
  simp at hb
  subst hb
  intro hcon
  subst hcon
  exact h2 ha

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  have h1 : step s e = (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    rw [hrec]
    rw [if_pos hvalid]
  rw [h1]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnotin hinvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  unfold step
  rw [hrec]
  rw [if_neg hinvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  rw [h]

theorem req_effects : Effects step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  have h1 : step s e = (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    rw [hrec, if_pos hvalid]
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]
  · rw [h1]
  · intro a
    rw [h1]
    by_cases ha : a = e.account <;> simp [ha]

theorem req_append_only : AppendOnly step := by
  intro s e
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hst : (step s e).2.log = s.log := by unfold step; rw [hrec]
    exact ⟨[], by rw [hst, List.append_nil]⟩
  | none =>
    by_cases hv : ValidEntry s e
    · have hst : (step s e).2.log = s.log ++ [e] := by unfold step; rw [hrec, if_pos hv]
      exact ⟨[e], hst⟩
    · have hst : (step s e).2.log = s.log := by unfold step; rw [hrec, if_neg hv]
      exact ⟨[], by rw [hst, List.append_nil]⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hst : step s e = ((.ok n : Outcome), s) := by unfold step; rw [hrec]
    have hlog : (step s e).2.log = s.log := by rw [hst]
    rw [hlog]
    exact hnodup
  | none =>
    by_cases hv : ValidEntry s e
    · have hst : step s e = ((.ok s.log.length : Outcome),
        { s with log := s.log ++ [e],
                 balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        unfold step; rw [hrec, if_pos hv]
      have hlog : (step s e).2.log = s.log ++ [e] := by rw [hst]
      have hnotin : e.id ∉ ids s.log := by
        intro hmem
        obtain ⟨m, hm⟩ := receiptOf_isSome hmem
        rw [hm] at hrec
        simp at hrec
      rw [hlog]
      have hid : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by simp [ids]
      rw [hid]
      exact nodup_append_singleton_aux _ _ hnodup hnotin
    · have hst : step s e = ((.rejected : Outcome), s) := by unfold step; rw [hrec, if_neg hv]
      have hlog : (step s e).2.log = s.log := by rw [hst]
      rw [hlog]
      exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hnn a ha
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hst : step s e = ((.ok n : Outcome), s) := by unfold step; rw [hrec]
    have hacc : (step s e).2.accounts = s.accounts := by rw [hst]
    have hbal : (step s e).2.balance a = s.balance a := by rw [hst]
    rw [hacc] at ha
    rw [hbal]
    exact hnn a ha
  | none =>
    by_cases hv : ValidEntry s e
    · have hst : step s e = ((.ok s.log.length : Outcome),
        { s with log := s.log ++ [e],
                 balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        unfold step; rw [hrec, if_pos hv]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hst]
      have hbal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by rw [hst]
      rw [hacc] at ha
      rw [hbal]
      by_cases heq : a = e.account
      · subst heq
        simp only [if_true]
        obtain ⟨hmem, hne, hle⟩ := hv
        exact hle
      · simp [heq]
        exact hnn a ha
    · have hst : step s e = ((.rejected : Outcome), s) := by unfold step; rw [hrec, if_neg hv]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hst]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hst]
      rw [hacc] at ha
      rw [hbal]
      exact hnn a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons a
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hst : step s e = ((.ok n : Outcome), s) := by unfold step; rw [hrec]
    have h2 : (step s e).2 = s := by rw [hst]
    rw [h2]
    exact hcons a
  | none =>
    by_cases hv : ValidEntry s e
    · have hst : step s e = ((.ok s.log.length : Outcome),
        { s with log := s.log ++ [e],
                 balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        unfold step; rw [hrec, if_pos hv]
      have hbal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by rw [hst]
      have hlog : (step s e).2.log = s.log ++ [e] := by rw [hst]
      rw [hbal, hlog, logSum_append_single, hcons a]
      by_cases heq : a = e.account
      · have heq2 : e.account = a := heq.symm
        rw [if_pos heq, if_pos heq2]
      · have heq2 : ¬ e.account = a := fun h => heq h.symm
        rw [if_neg heq, if_neg heq2, Int.add_zero]
    · have hst : step s e = ((.rejected : Outcome), s) := by unfold step; rw [hrec, if_neg hv]
      have h2 : (step s e).2 = s := by rw [hst]
      rw [h2]
      exact hcons a

end EntryLog
