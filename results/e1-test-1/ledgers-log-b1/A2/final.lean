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
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem aux_receipt_none_notmem2 {log : List Entry} {i : EntryId} (h : receiptOf log i = none) : i ∉ ids log := by
  intro hmem
  obtain ⟨n, hn⟩ := receiptOf_isSome hmem
  rw [h] at hn
  simp at hn

theorem aux_nodup_append_singleton2 {l : List EntryId} {x : EntryId} (h1 : l.Nodup) (h2 : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hhd_notin : hd ∉ tl := by
      simp [List.nodup_cons] at h1
      exact h1.1
    have htl_nodup : tl.Nodup := by
      simp [List.nodup_cons] at h1
      exact h1.2
    have hx_ne : x ≠ hd := by
      intro heq
      apply h2
      simp [heq]
    have hx_notin_tl : x ∉ tl := by
      intro hmem
      apply h2
      simp [hmem]
    have ih' := ih htl_nodup hx_notin_tl
    simp only [List.cons_append]
    simp only [List.nodup_cons]
    constructor
    · intro hmem
      rw [List.mem_append] at hmem
      simp at hmem
      rcases hmem with h | h
      · exact hhd_notin h
      · exact hx_ne h.symm
    · exact ih'

theorem logSum_append_singleton3 (l : List Entry) (x : Entry) (a : AccountId) :
    logSum (l ++ [x]) a = logSum l a + (if x.account = a then x.amount else 0) := by
  unfold logSum
  have h := sumOver_append l [x] (fun e => if e.account = a then e.amount else 0)
  rw [h]
  have h2 : sumOver ([x] : List Entry) (fun e => if e.account = a then e.amount else 0) = (if x.account = a then x.amount else 0) := by
    unfold sumOver
    simp
  rw [h2]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  unfold step
  simp [hrec, hvalid]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s e hnotin hinvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  unfold step
  simp [hrec, hinvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  simp [h]

theorem req_effects : Effects step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  have hstep : step s e = (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    simp [hrec, hvalid]
  rw [hstep]
  refine ⟨rfl, rfl, fun a => ?_⟩
  by_cases h : a = e.account <;> simp [h] <;> omega

theorem req_append_only : AppendOnly step := by
  intro s e
  cases h : receiptOf s.log e.id with
  | none =>
    unfold step
    simp only [h]
    by_cases hv : ValidEntry s e
    · simp only [hv, ↓reduceIte]
      exact ⟨[e], rfl⟩
    · simp only [hv, ↓reduceIte]
      exact ⟨[], by simp⟩
  | some n =>
    unfold step
    simp only [h]
    exact ⟨[], by simp⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have h2 : (step s e).2 = s := by unfold step; simp [hrec]
    rw [h2]
    exact hnodup
  | none =>
    have hnotin : e.id ∉ ids s.log := aux_receipt_none_notmem2 hrec
    by_cases hv : ValidEntry s e
    · have hlog : (step s e).2.log = s.log ++ [e] := by unfold step; simp [hrec, hv]
      rw [hlog]
      have heq : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by simp [ids]
      rw [heq]
      exact aux_nodup_append_singleton2 hnodup hnotin
    · have h2 : (step s e).2 = s := by unfold step; simp [hrec, hv]
      rw [h2]
      exact hnodup

theorem req_nonnegative    : NonNegative step := by
  intro s e hnn a ha
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hstep : step s e = (.ok n, s) := by unfold step; simp [hrec]
    have hacc : (step s e).2.accounts = s.accounts := by rw [hstep]
    have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
    have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
    rw [hbal]
    exact hnn a ha'
  | none =>
    by_cases hv : ValidEntry s e
    · have hstep : step s e = (.ok s.log.length,
         { s with log := s.log ++ [e],
                  balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
          unfold step; simp [hrec, hv]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hstep]
      have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
      have hbal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by rw [hstep]
      rw [hbal]
      by_cases heq : a = e.account
      · simp [heq, hv.2.2]
      · simp [heq, hnn a ha']
    · have hstep : step s e = (.rejected, s) := by unfold step; simp [hrec, hv]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
      rw [hbal]
      exact hnn a ha'

theorem req_consistent : StaysConsistent step := by
  intro s e hcons a
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hstep : (step s e).2 = s := by unfold step; simp [hrec]
    rw [hstep]
    exact hcons a
  | none =>
    by_cases hv : ValidEntry s e
    · have hstep : step s e = (.ok s.log.length,
           { s with log := s.log ++ [e],
                    balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
            unfold step; simp [hrec, hv]
      have hlog : (step s e).2.log = s.log ++ [e] := by rw [hstep]
      have hbal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by rw [hstep]
      have hold : s.balance a = logSum s.log a := hcons a
      show (step s e).2.balance a = logSum (step s e).2.log a
      rw [hlog, hbal, hold, logSum_append_singleton3]
      by_cases heq : a = e.account
      · have heq2 : e.account = a := Eq.symm heq
        rw [if_pos heq, if_pos heq2]
      · have hne2 : ¬ (e.account = a) := fun h => heq (Eq.symm h)
        rw [if_neg heq, if_neg hne2]
        omega
    · have hstep : (step s e).2 = s := by unfold step; simp [hrec, hv]
      rw [hstep]
      exact hcons a

end EntryLog
