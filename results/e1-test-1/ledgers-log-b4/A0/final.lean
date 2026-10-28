import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if decide (ValidEntry s e) then
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => s.balance a + (if a = e.account then e.amount else 0) })
    else (.rejected, s)

theorem pairwise_append_singleton_aux (l : List EntryId) : ∀ (a : EntryId),
    List.Pairwise (fun x y => x ≠ y) l → a ∉ l →
    List.Pairwise (fun x y => x ≠ y) (l ++ [a]) := by
  induction l with
  | nil =>
    intro a _ _
    show List.Pairwise (fun x y => x ≠ y) [a]
    apply List.Pairwise.cons
    · intro b hb
      simp at hb
    · exact List.Pairwise.nil
  | cons x xs ih =>
    intro a h hm
    cases h with
    | cons hhead htail =>
      have hm_xs : a ∉ xs := by
        intro hmem
        apply hm
        simp [hmem]
      have hne : x ≠ a := by
        intro heq
        subst heq
        apply hm
        simp
      have ih' := ih a htail hm_xs
      have heq : (x :: xs) ++ [a] = x :: (xs ++ [a]) := rfl
      rw [heq]
      apply List.Pairwise.cons
      · intro b hb
        simp at hb
        rcases hb with hb_xs | rfl
        · exact hhead b hb_xs
        · exact hne
      · exact ih'

theorem nodup_append_singleton_aux (l : List EntryId) (a : EntryId) :
    l.Nodup → a ∉ l → (l ++ [a]).Nodup := by
  intro h hm
  exact pairwise_append_singleton_aux l a h hm

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hmem hvalid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none hmem
  have hdec : decide (ValidEntry s e) = true := decide_eq_true hvalid
  have hstep : step s e = (.ok s.log.length,
      { s with log := s.log ++ [e],
               balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
    unfold step
    simp [hnone, hdec]
  rw [hstep]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hmem hinvalid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none hmem
  have hdec : decide (ValidEntry s e) = false := decide_eq_false hinvalid
  have hstep : step s e = (.rejected, s) := by
    unfold step
    simp [hnone, hdec]
  exact hstep

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hn
  unfold step
  simp [hn]

theorem req_effects : Effects step := by
  intro s e hmem hvalid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none hmem
  have hdec : decide (ValidEntry s e) = true := decide_eq_true hvalid
  have hstep : step s e = (.ok s.log.length,
      { s with log := s.log ++ [e],
               balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
    unfold step
    simp [hnone, hdec]
  refine ⟨by simp [hstep], by simp [hstep], by intro a; simp [hstep]⟩

theorem req_append_only : AppendOnly step := by
  intro s e
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hstep : step s e = (.ok n, s) := by
      unfold step
      simp [hn]
    exact ⟨[], by simp [hstep]⟩
  · have hn : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases hv : ValidEntry s e
    · have hdec : decide (ValidEntry s e) = true := decide_eq_true hv
      have hstep : step s e = (.ok s.log.length,
          { s with log := s.log ++ [e],
                   balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
        unfold step
        simp [hn, hdec]
      exact ⟨[e], by simp [hstep]⟩
    · have hdec : decide (ValidEntry s e) = false := decide_eq_false hv
      have hstep : step s e = (.rejected, s) := by
        unfold step
        simp [hn, hdec]
      exact ⟨[], by simp [hstep]⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hlog : (step s e).2.log = s.log := by
      unfold step
      simp [hn]
    simp [hlog, hnodup]
  · have hn : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases hv : ValidEntry s e
    · have hdec : decide (ValidEntry s e) = true := decide_eq_true hv
      have hlog : (step s e).2.log = s.log ++ [e] := by
        unfold step
        simp [hn, hdec]
      have hsingle : ids [e] = [e.id] := rfl
      have hids : ids ((step s e).2.log) = ids s.log ++ [e.id] := by
        rw [hlog, ids_append, hsingle]
      rw [hids]
      exact nodup_append_singleton_aux (ids s.log) e.id hnodup hmem
    · have hdec : decide (ValidEntry s e) = false := decide_eq_false hv
      have hlog : (step s e).2.log = s.log := by
        unfold step
        simp [hn, hdec]
      simp [hlog, hnodup]

theorem req_nonnegative : NonNegative step := by
  intro s e hnonneg a hamem
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hstep : step s e = (.ok n, s) := by
      unfold step
      simp [hn]
    have hamem' : a ∈ s.accounts := by simpa [hstep] using hamem
    have hbal : (step s e).2.balance a = s.balance a := by simp [hstep]
    rw [hbal]
    exact hnonneg a hamem'
  · have hn : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases hv : ValidEntry s e
    · have hdec : decide (ValidEntry s e) = true := decide_eq_true hv
      have hstep : step s e = (.ok s.log.length,
          { s with log := s.log ++ [e],
                   balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
        unfold step
        simp [hn, hdec]
      have hacc : (step s e).2.accounts = s.accounts := by simp [hstep]
      have hbal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := by simp [hstep]
      have hamem' : a ∈ s.accounts := hacc ▸ hamem
      rw [hbal]
      by_cases heq : a = e.account
      · rw [if_pos heq, heq]
        exact hv.2.2
      · rw [if_neg heq]
        simp
        exact hnonneg a hamem'
    · have hdec : decide (ValidEntry s e) = false := decide_eq_false hv
      have hstep : step s e = (.rejected, s) := by
        unfold step
        simp [hn, hdec]
      have hamem' : a ∈ s.accounts := by simpa [hstep] using hamem
      have hbal : (step s e).2.balance a = s.balance a := by simp [hstep]
      rw [hbal]
      exact hnonneg a hamem'

theorem req_consistent : StaysConsistent step := by
  intro s e hcons
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hstep : step s e = (.ok n, s) := by
      unfold step
      simp [hn]
    intro a
    have hbal : (step s e).2.balance a = s.balance a := by simp [hstep]
    have hlog : (step s e).2.log = s.log := by simp [hstep]
    rw [hbal, hlog]
    exact hcons a
  · have hn : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases hv : ValidEntry s e
    · have hdec : decide (ValidEntry s e) = true := decide_eq_true hv
      have hstep : step s e = (.ok s.log.length,
          { s with log := s.log ++ [e],
                   balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
        unfold step
        simp [hn, hdec]
      have hbal : ∀ b, (step s e).2.balance b = s.balance b + (if b = e.account then e.amount else 0) := by
        intro b
        simp [hstep]
      have hlog : (step s e).2.log = s.log ++ [e] := by simp [hstep]
      have hsum : ∀ b, logSum (s.log ++ [e]) b = logSum s.log b + (if e.account = b then e.amount else 0) := by
        intro b
        simp [logSum, sumOver_append]
      intro a
      rw [hbal a, hlog, hsum a, hcons a]
      by_cases heq : a = e.account
      · have heq' : e.account = a := Eq.symm heq
        rw [if_pos heq, if_pos heq']
      · have heq' : ¬ e.account = a := fun h => heq (Eq.symm h)
        rw [if_neg heq, if_neg heq']
    · have hdec : decide (ValidEntry s e) = false := decide_eq_false hv
      have hstep : step s e = (.rejected, s) := by
        unfold step
        simp [hn, hdec]
      intro a
      have hbal : (step s e).2.balance a = s.balance a := by simp [hstep]
      have hlog : (step s e).2.log = s.log := by simp [hstep]
      rw [hbal, hlog]
      exact hcons a

end EntryLog
