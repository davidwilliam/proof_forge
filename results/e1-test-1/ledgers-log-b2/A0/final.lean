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
    if ValidEntry s e then
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => s.balance a + (if a = e.account then e.amount else 0) })
    else (.rejected, s)

private theorem nodup_append_singleton (l : List EntryId) (x : EntryId)
    (h1 : l.Nodup) (h2 : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil =>
    exact List.nodup_cons.mpr ⟨by simp, by simp⟩
  | cons hd tl ih =>
    have hcons := List.nodup_cons.mp h1
    have hhd : hd ∉ tl := hcons.1
    have htl : tl.Nodup := hcons.2
    have hne : hd ≠ x := by
      intro he
      apply h2
      exact List.mem_cons.mpr (Or.inl he.symm)
    have hnot : x ∉ tl := by
      intro hm
      apply h2
      exact List.mem_cons_of_mem hd hm
    have ih' : (tl ++ [x]).Nodup := ih htl hnot
    have hmem : hd ∉ tl ++ [x] := by
      intro hm
      rcases List.mem_append.mp hm with hm1 | hm2
      · exact hhd hm1
      · have heq : hd = x := List.mem_singleton.mp hm2
        exact hne heq
    exact List.nodup_cons.mpr ⟨hmem, ih'⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hmem hvalid
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hmem
  have hstep : step s e =
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
    simp only [step, hr, if_pos hvalid]
  simp only [hstep]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hmem hnot
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hmem
  have hstep : step s e = (.rejected, s) := by
    simp only [step, hr, if_neg hnot]
  exact hstep

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hn
  have hstep : step s e = (.ok n, s) := by
    simp only [step, hn]
  exact hstep

theorem req_effects : Effects step := by
  intro s e hmem hvalid
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hmem
  have hstep : step s e =
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
    simp only [step, hr, if_pos hvalid]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hstep]
  · simp only [hstep]
  · intro a
    simp only [hstep]

theorem req_append_only : AppendOnly step := by
  intro s e
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hstep : step s e = (.ok n, s) := by
      simp only [step, hn]
    exact ⟨[], by simp only [hstep, List.append_nil]⟩
  · have hr : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases hvalid : ValidEntry s e
    · have hstep : step s e =
            (.ok s.log.length,
             { s with log := s.log ++ [e],
                      balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
        simp only [step, hr, if_pos hvalid]
      exact ⟨[e], by simp only [hstep]⟩
    · have hstep : step s e = (.rejected, s) := by
        simp only [step, hr, if_neg hvalid]
      exact ⟨[], by simp only [hstep, List.append_nil]⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hstep : step s e = (.ok n, s) := by
      simp only [step, hn]
    have hlog : (step s e).2.log = s.log := by
      simp only [hstep]
    rw [hlog]
    exact hnodup
  · have hr : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases hvalid : ValidEntry s e
    · have hstep : step s e =
            (.ok s.log.length,
             { s with log := s.log ++ [e],
                      balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
        simp only [step, hr, if_pos hvalid]
      have hlog : (step s e).2.log = s.log ++ [e] := by
        simp only [hstep]
      have hsingleton : ids [e] = [e.id] := rfl
      have hids : ids (step s e).2.log = ids s.log ++ [e.id] := by
        rw [hlog, ids_append, hsingleton]
      rw [hids]
      exact nodup_append_singleton _ _ hnodup hmem
    · have hstep : step s e = (.rejected, s) := by
        simp only [step, hr, if_neg hvalid]
      have hlog : (step s e).2.log = s.log := by
        simp only [hstep]
      rw [hlog]
      exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hpos a hamem
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hstep : step s e = (.ok n, s) := by
      simp only [step, hn]
    have hacc : (step s e).2.accounts = s.accounts := by
      simp only [hstep]
    have hbal : (step s e).2.balance a = s.balance a := by
      simp only [hstep]
    have hamem' : a ∈ s.accounts := hacc ▸ hamem
    rw [hbal]
    exact hpos a hamem'
  · have hr : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases hvalid : ValidEntry s e
    · have hstep : step s e =
            (.ok s.log.length,
             { s with log := s.log ++ [e],
                      balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
        simp only [step, hr, if_pos hvalid]
      have hacc : (step s e).2.accounts = s.accounts := by
        simp only [hstep]
      have hba : (step s e).2.balance a =
          s.balance a + (if a = e.account then e.amount else 0) := by
        simp only [hstep]
      have hamem' : a ∈ s.accounts := hacc ▸ hamem
      rw [hba]
      by_cases heq : a = e.account
      · rw [if_pos heq, heq]
        obtain ⟨_, _, hle⟩ := hvalid
        exact hle
      · rw [if_neg heq, Int.add_zero]
        exact hpos a hamem'
    · have hstep : step s e = (.rejected, s) := by
        simp only [step, hr, if_neg hvalid]
      have hacc : (step s e).2.accounts = s.accounts := by
        simp only [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by
        simp only [hstep]
      have hamem' : a ∈ s.accounts := hacc ▸ hamem
      rw [hbal]
      exact hpos a hamem'

theorem req_consistent : StaysConsistent step := by
  intro s e hcons
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hstep : step s e = (.ok n, s) := by
      simp only [step, hn]
    have h2 : (step s e).2 = s := by
      simp only [hstep]
    intro a
    rw [h2]
    exact hcons a
  · have hr : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases hvalid : ValidEntry s e
    · have hstep : step s e =
            (.ok s.log.length,
             { s with log := s.log ++ [e],
                      balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
        simp only [step, hr, if_pos hvalid]
      have hbal : ∀ a, (step s e).2.balance a =
          s.balance a + (if a = e.account then e.amount else 0) := by
        intro a
        simp only [hstep]
      have hlog : (step s e).2.log = s.log ++ [e] := by
        simp only [hstep]
      intro a
      rw [hbal, hlog]
      have hold : s.balance a = logSum s.log a := hcons a
      rw [hold]
      have happ : logSum (s.log ++ [e]) a =
          logSum s.log a + (if e.account = a then e.amount else 0) := by
        unfold logSum
        rw [sumOver_append]
        have hsing : sumOver [e] (fun e_ => if e_.account = a then e_.amount else 0) =
            (if e.account = a then e.amount else 0) := by
          simp only [sumOver_cons, sumOver_nil, Int.add_zero]
        rw [hsing]
      rw [happ]
      have hif : (if a = e.account then e.amount else (0 : Int)) =
          (if e.account = a then e.amount else 0) := by
        by_cases h : a = e.account
        · rw [if_pos h, if_pos h.symm]
        · have hn2 : e.account ≠ a := fun hh => h hh.symm
          rw [if_neg h, if_neg hn2]
      rw [hif]
    · have hstep : step s e = (.rejected, s) := by
        simp only [step, hr, if_neg hvalid]
      have h2 : (step s e).2 = s := by
        simp only [hstep]
      intro a
      rw [h2]
      exact hcons a

end EntryLog
