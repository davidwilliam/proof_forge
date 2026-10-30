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
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  have hstep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    simp [step, hrec, hvalid]
  rw [hstep]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s e hnotin hnvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  have hstep : step s e = (.rejected, s) := by
    simp [step, hrec, hnvalid]
  exact hstep

theorem req_duplicate : DuplicateReturnsOriginal step := by
  unfold DuplicateReturnsOriginal
  intro s e n hrec
  simp [step, hrec]

theorem req_effects : Effects step := by
  unfold Effects
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  have hstep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    simp [step, hrec, hvalid]
  refine ⟨?_, ?_, ?_⟩
  · simp [hstep]
  · simp [hstep]
  · intro a
    have hb : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by
      simp [hstep]
    rw [hb]
    by_cases h : a = e.account
    · simp only [h, ite_true]
    · simp only [h, ite_false]
      omega

theorem req_append_only : AppendOnly step := by
  unfold AppendOnly
  intro s e
  by_cases hrec : receiptOf s.log e.id = none
  · have hnotin : e.id ∉ ids s.log := by
      intro hm
      obtain ⟨n, hn⟩ := receiptOf_isSome hm
      rw [hn] at hrec
      simp at hrec
    by_cases hvalid : ValidEntry s e
    · have hstep_log : (step s e).2.log = s.log ++ [e] := by
        have hstep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
          simp [step, hrec, hvalid]
        simp [hstep]
      exact ⟨[e], hstep_log⟩
    · have hstep_log : (step s e).2.log = s.log := by
        have hstep : step s e = ((.rejected : Outcome), s) := by
          simp [step, hrec, hvalid]
        simp [hstep]
      exact ⟨[], by simp [hstep_log]⟩
  · have hsome : ∃ n, receiptOf s.log e.id = some n := by
      cases hc : receiptOf s.log e.id with
      | none => exact absurd hc hrec
      | some v => exact ⟨v, rfl⟩
    obtain ⟨n, hn⟩ := hsome
    have hstep_log : (step s e).2.log = s.log := by
      have hstep : step s e = ((.ok n : Outcome), s) := by simp [step, hn]
      simp [hstep]
    exact ⟨[], by simp [hstep_log]⟩

private theorem nodup_append_singleton {α : Type} [DecidableEq α] {l : List α} {x : α}
    (hl : l.Nodup) (hm : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil =>
    simp
  | cons y ys ih =>
    have hm_split : x ≠ y ∧ x ∉ ys := by
      constructor
      · intro heq
        have : x ∈ y :: ys := by simp [heq]
        exact hm this
      · intro hmem
        have : x ∈ y :: ys := by simp [hmem]
        exact hm this
    have hl_pair : y ∉ ys ∧ ys.Nodup := by
      rwa [List.nodup_cons] at hl
    have ih' := ih hl_pair.2 hm_split.2
    have hy : y ∉ ys ++ [x] := by
      intro hmem
      rw [List.mem_append] at hmem
      rcases hmem with h1 | h2
      · exact hl_pair.1 h1
      · simp at h2
        exact hm_split.1 h2.symm
    exact (List.nodup_cons.mpr ⟨hy, ih'⟩)

theorem req_unique_ids : UniqueIds step := by
  unfold UniqueIds
  intro s e hnodup
  by_cases hrec : receiptOf s.log e.id = none
  · have hnotin : e.id ∉ ids s.log := by
      intro hm
      obtain ⟨n, hn⟩ := receiptOf_isSome hm
      rw [hn] at hrec
      simp at hrec
    by_cases hvalid : ValidEntry s e
    · have hstep_log : (step s e).2.log = s.log ++ [e] := by
        have hstep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
          simp [step, hrec, hvalid]
        simp [hstep]
      rw [hstep_log, ids_append]
      have hids_single : ids [e] = [e.id] := by simp [ids]
      rw [hids_single]
      exact nodup_append_singleton hnodup hnotin
    · have hstep_log : (step s e).2.log = s.log := by
        have hstep : step s e = ((.rejected : Outcome), s) := by simp [step, hrec, hvalid]
        simp [hstep]
      rw [hstep_log]
      exact hnodup
  · have hsome : ∃ n, receiptOf s.log e.id = some n := by
      cases hc : receiptOf s.log e.id with
      | none => exact absurd hc hrec
      | some v => exact ⟨v, rfl⟩
    obtain ⟨n, hn⟩ := hsome
    have hstep_log : (step s e).2.log = s.log := by
      have hstep : step s e = ((.ok n : Outcome), s) := by simp [step, hn]
      simp [hstep]
    rw [hstep_log]
    exact hnodup

theorem req_nonnegative : NonNegative step := by
  unfold NonNegative
  intro s e hnn a ha
  by_cases hrec : receiptOf s.log e.id = none
  · have hnotin : e.id ∉ ids s.log := by
      intro hm
      obtain ⟨n, hn⟩ := receiptOf_isSome hm
      rw [hn] at hrec
      simp at hrec
    by_cases hvalid : ValidEntry s e
    · have hstep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        simp [step, hrec, hvalid]
      have hacc : (step s e).2.accounts = s.accounts := by simp [hstep]
      rw [hacc] at ha
      have hbal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by simp [hstep]
      rw [hbal]
      by_cases heq : a = e.account
      · rw [if_pos heq]
        have hv : ValidEntry s e := hvalid
        unfold ValidEntry at hv
        have hle : 0 ≤ s.balance e.account + e.amount := hv.2.2
        rw [← heq] at hle
        exact hle
      · rw [if_neg heq]
        exact hnn a ha
    · have hstep : step s e = ((.rejected : Outcome), s) := by simp [step, hrec, hvalid]
      have hacc : (step s e).2.accounts = s.accounts := by simp [hstep]
      rw [hacc] at ha
      have hbal : (step s e).2.balance a = s.balance a := by simp [hstep]
      rw [hbal]
      exact hnn a ha
  · have hsome : ∃ n, receiptOf s.log e.id = some n := by
      cases hc : receiptOf s.log e.id with
      | none => exact absurd hc hrec
      | some v => exact ⟨v, rfl⟩
    obtain ⟨n, hn⟩ := hsome
    have hstep : step s e = ((.ok n : Outcome), s) := by simp [step, hn]
    have hacc : (step s e).2.accounts = s.accounts := by simp [hstep]
    rw [hacc] at ha
    have hbal : (step s e).2.balance a = s.balance a := by simp [hstep]
    rw [hbal]
    exact hnn a ha

theorem req_consistent : StaysConsistent step := by
  unfold StaysConsistent Consistent
  intro s e hcons
  by_cases hrec : receiptOf s.log e.id = none
  · have hnotin : e.id ∉ ids s.log := by
      intro hm
      obtain ⟨n, hn⟩ := receiptOf_isSome hm
      rw [hn] at hrec
      simp at hrec
    by_cases hvalid : ValidEntry s e
    · intro a
      have hstep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        simp [step, hrec, hvalid]
      have hbal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by simp [hstep]
      have hlog : (step s e).2.log = s.log ++ [e] := by simp [hstep]
      rw [hbal, hlog]
      have h1 : s.balance a = logSum s.log a := hcons a
      rw [h1]
      unfold logSum
      rw [sumOver_append]
      have hsum_single : sumOver [e] (fun e_1 => if e_1.account = a then e_1.amount else 0) = if e.account = a then e.amount else 0 := by
        unfold sumOver
        simp
      rw [hsum_single]
      by_cases heq : a = e.account
      · have heq2 : e.account = a := heq.symm
        rw [if_pos heq, if_pos heq2]
      · have hne : ¬ (e.account = a) := fun h => heq h.symm
        rw [if_neg heq, if_neg hne]
        omega
    · have hstep : step s e = ((.rejected : Outcome), s) := by simp [step, hrec, hvalid]
      intro a
      have hbal : (step s e).2.balance a = s.balance a := by simp [hstep]
      have hlog : (step s e).2.log = s.log := by simp [hstep]
      rw [hbal, hlog]
      exact hcons a
  · have hsome : ∃ n, receiptOf s.log e.id = some n := by
      cases hc : receiptOf s.log e.id with
      | none => exact absurd hc hrec
      | some v => exact ⟨v, rfl⟩
    obtain ⟨n, hn⟩ := hsome
    have hstep : step s e = ((.ok n : Outcome), s) := by simp [step, hn]
    intro a
    have hbal : (step s e).2.balance a = s.balance a := by simp [hstep]
    have hlog : (step s e).2.log = s.log := by simp [hstep]
    rw [hbal, hlog]
    exact hcons a

end EntryLog
