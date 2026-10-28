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

theorem nodup_append_singleton_aux (l : List EntryId) (x : EntryId) (hl : List.Nodup l) (hx : x ∉ l) : List.Nodup (l ++ [x]) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hhd_not : hd ∉ tl := (List.nodup_cons.mp hl).1
    have htl_nodup : List.Nodup tl := (List.nodup_cons.mp hl).2
    have hx_tl : x ∉ tl := by
      intro hmem
      apply hx
      exact List.mem_cons_of_mem hd hmem
    have hhd_ne : hd ≠ x := by
      intro heq
      apply hx
      rw [heq]
      simp
    have ih' := ih htl_nodup hx_tl
    have heq : (hd :: tl) ++ [x] = hd :: (tl ++ [x]) := rfl
    rw [heq]
    rw [List.nodup_cons]
    constructor
    · intro hmem
      have hdisj := (List.mem_append.mp hmem)
      cases hdisj with
      | inl h => exact hhd_not h
      | inr h =>
        have heq2 : hd = x := List.mem_singleton.mp h
        exact hhd_ne heq2
    · exact ih'

theorem receiptOf_none_not_mem {log : List Entry} {i : EntryId} (h : receiptOf log i = none) : i ∉ ids log := by
  intro hmem
  obtain ⟨n, hn⟩ := receiptOf_isSome hmem
  rw [hn] at h
  contradiction

theorem req_consistent_aux1 (s : State) (e : Entry) (a : AccountId) (hcons : Consistent s) :
    (if a = e.account then s.balance a + e.amount else s.balance a) =
    logSum (s.log ++ [e]) a := by
  have hbal : s.balance a = logSum s.log a := hcons a
  have happ : logSum (s.log ++ [e]) a = logSum s.log a + logSum [e] a := by
    unfold logSum
    exact sumOver_append s.log [e] _
  have hsing : logSum [e] a = (if e.account = a then e.amount else 0) := by
    have h1 : logSum [e] a = (if e.account = a then e.amount else 0) + (0 : Int) := by
      unfold logSum
      rw [sumOver_cons, sumOver_nil]
    omega
  rw [happ, hsing, hbal]
  by_cases heq : a = e.account
  · rw [if_pos heq, if_pos (Eq.symm heq)]
  · have heq2 : ¬ (e.account = a) := fun h => heq (Eq.symm h)
    rw [if_neg heq, if_neg heq2]
    omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnew hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  unfold step
  simp [hrec, hvalid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnew hinvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  unfold step
  simp [hrec, hinvalid]

theorem req_duplicate      : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  simp [h]

theorem req_effects : Effects step := by
  intro s e hnew hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  unfold step
  simp only [hrec, hvalid, ↓reduceIte]
  refine ⟨trivial, trivial, fun a => ?_⟩
  by_cases ha : a = e.account <;> simp [ha]

theorem req_append_only    : AppendOnly step := by
  intro s e
  unfold step
  split
  · exact ⟨[], by simp⟩
  · split
    · exact ⟨[e], by simp⟩
    · exact ⟨[], by simp⟩

theorem req_unique_ids     : UniqueIds step := by
  intro s e hnodup
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hstep : step s e = (.ok n, s) := by unfold step; simp [hrec]
    rw [hstep]
    simp
    exact hnodup
  | none =>
    have hstep : step s e = (if ValidEntry s e then (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) else (.rejected, s)) := by unfold step; simp [hrec]
    by_cases hvalid : ValidEntry s e
    · have hstep2 : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by rw [hstep]; simp [hvalid]
      rw [hstep2]
      simp only
      have hids : ids (s.log ++ [e]) = ids s.log ++ [e.id] := ids_append s.log [e]
      rw [hids]
      have hnotin : e.id ∉ ids s.log := receiptOf_none_not_mem hrec
      exact nodup_append_singleton_aux (ids s.log) e.id hnodup hnotin
    · have hstep2 : step s e = (.rejected, s) := by rw [hstep]; simp [hvalid]
      rw [hstep2]
      simp
      exact hnodup

theorem req_nonnegative    : NonNegative step := by
  intro s e hnn a ha
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hstep : step s e = (.ok n, s) := by unfold step; simp [hrec]
    rw [hstep] at ha ⊢
    simp at ha ⊢
    exact hnn a ha
  | none =>
    have hstep : step s e = (if ValidEntry s e then (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) else (.rejected, s)) := by unfold step; simp [hrec]
    by_cases hvalid : ValidEntry s e
    · have hstep2 : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by rw [hstep]; simp [hvalid]
      rw [hstep2] at ha ⊢
      simp only at ha ⊢
      -- accounts unchanged
      have ha' : a ∈ s.accounts := ha
      by_cases heq : a = e.account
      · subst heq
        simp only [if_true]
        -- ValidEntry gives 0 ≤ balance + amount
        unfold ValidEntry at hvalid
        obtain ⟨_, _, hle⟩ := hvalid
        -- hle : 0 ≤ s.balance e.account + e.amount ; need same
        simpa using hle
      · simp only [heq, if_false] at ⊢
        exact hnn a ha'
    · have hstep2 : step s e = (.rejected, s) := by rw [hstep]; simp [hvalid]
      rw [hstep2] at ha ⊢
      simp at ha ⊢
      exact hnn a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons a
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hstep : (step s e).2 = s := by unfold step; simp [hrec]
    rw [hstep]
    exact hcons a
  | none =>
    have hstep2 : step s e = (if ValidEntry s e then (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) else (.rejected, s)) := by unfold step; simp [hrec]
    by_cases hvalid : ValidEntry s e
    · have h2 : (step s e).2 = ({ s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a } : State) := by rw [hstep2]; simp [hvalid]
      rw [h2]
      exact req_consistent_aux1 s e a hcons
    · have h2 : (step s e).2 = s := by rw [hstep2]; simp [hvalid]
      rw [h2]
      exact hcons a

end EntryLog
