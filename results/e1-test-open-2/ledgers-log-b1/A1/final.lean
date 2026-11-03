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

theorem req_unique_ids_aux : True := trivial

private theorem nodup_append_singleton {α : Type} [DecidableEq α] (l : List α) (x : α) (h1 : l.Nodup) (h2 : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    have hnd : (y :: ys).Nodup := h1
    have hmem : y ∉ ys := (List.nodup_cons.mp hnd).1
    have htail : ys.Nodup := (List.nodup_cons.mp hnd).2
    have hxn : x ∉ ys := fun hm => h2 (List.Mem.tail y hm)
    have hyx : y ≠ x := by intro heq; apply h2; rw [← heq]; exact List.Mem.head ys
    have ih' := ih htail hxn
    rw [List.cons_append]
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rw [List.mem_append] at hm
      rcases hm with hm1 | hm2
      · exact hmem hm1
      · simp at hm2; rw [hm2] at hyx; exact hyx rfl
    · exact ih'

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hmem hvalid
  show (step s e).1 = Outcome.ok s.log.length
  unfold step
  have h1 : receiptOf s.log e.id = none := receiptOf_eq_none hmem
  rw [h1]
  simp [hvalid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hmem hvalid
  show step s e = (.rejected, s)
  unfold step
  have h1 : receiptOf s.log e.id = none := receiptOf_eq_none hmem
  rw [h1]
  simp [hvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hn
  show step s e = (.ok n, s)
  unfold step
  have h : receiptOf s.log e.id = some n := hn
  rw [h]

theorem req_effects : Effects step := by
  intro s e hmem hvalid
  have h1 : receiptOf s.log e.id = none := receiptOf_eq_none hmem
  refine ⟨?_, ?_, ?_⟩
  · show (step s e).2.accounts = s.accounts
    unfold step; rw [h1]; simp [hvalid]
  · show (step s e).2.log = s.log ++ [e]
    unfold step; rw [h1]; simp [hvalid]
  · intro a
    show (step s e).2.balance a = s.balance a + if a = e.account then e.amount else 0
    unfold step; rw [h1]; simp only [hvalid, ↓reduceDIte]
    by_cases h : a = e.account <;> simp [h]

theorem req_append_only : AppendOnly step := by
  intro s e
  unfold step
  by_cases h : receiptOf s.log e.id = none
  · rw [h]
    by_cases hv : ValidEntry s e
    · simp only [hv, ↓reduceDIte]
      exact ⟨[e], rfl⟩
    · simp only [hv, ↓reduceDIte]
      exact ⟨[], by simp⟩
  · have : ∃ n, receiptOf s.log e.id = some n := by
      cases hx : receiptOf s.log e.id with
      | none => exact absurd hx h
      | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := this
    rw [hn]
    exact ⟨[], by simp⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  unfold step
  by_cases h : receiptOf s.log e.id = none
  · rw [h]
    by_cases hv : ValidEntry s e
    · simp only [hv]
      show (ids (s.log ++ [e])).Nodup
      have hmem : e.id ∉ ids s.log := by
        intro hm
        obtain ⟨n, hn⟩ := receiptOf_isSome hm
        rw [hn] at h; contradiction
      have hid : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by simp [ids]
      rw [hid]
      exact nodup_append_singleton (ids s.log) e.id hnodup hmem
    · simp only [hv]
      exact hnodup
  · have : ∃ n, receiptOf s.log e.id = some n := by
      cases hx : receiptOf s.log e.id with
      | none => exact absurd hx h
      | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := this
    rw [hn]
    exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hpos
  unfold step
  by_cases h : receiptOf s.log e.id = none
  · rw [h]
    by_cases hv : ValidEntry s e
    · simp only [hv]
      intro a ha
      show 0 ≤ (if a = e.account then s.balance a + e.amount else s.balance a)
      by_cases heq : a = e.account
      · simp [heq]
        have h1 := hv.2.2
        exact h1
      · simp [heq]
        exact hpos a ha
    · simp only [hv]
      intro a ha
      exact hpos a ha
  · have : ∃ n, receiptOf s.log e.id = some n := by
      cases hx : receiptOf s.log e.id with
      | none => exact absurd hx h
      | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := this
    rw [hn]
    intro a ha
    simp at ha
    exact hpos a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons a
  show (step s e).2.balance a = logSum (step s e).2.log a
  unfold step
  by_cases h : receiptOf s.log e.id = none
  · rw [h]
    by_cases hv : ValidEntry s e
    · simp [hv]
      have hbal : s.balance a = logSum s.log a := hcons a
      by_cases heq : a = e.account
      · have hsum : logSum (s.log ++ [e]) a = logSum s.log a + e.amount := by
          unfold logSum
          rw [sumOver_append]
          have : (if e.account = a then e.amount else (0 : Int)) = e.amount := by
            have : e.account = a := heq.symm
            simp [this]
          simp [this]
        rw [if_pos heq, hbal, hsum]
      · have heq2 : e.account ≠ a := fun h => heq h.symm
        have hsum : logSum (s.log ++ [e]) a = logSum s.log a := by
          unfold logSum
          rw [sumOver_append]
          have : (if e.account = a then e.amount else (0 : Int)) = 0 := by simp [heq2]
          simp [this]
        rw [if_neg heq, hbal, hsum]
    · simp [hv]
      exact hcons a
  · have : ∃ n, receiptOf s.log e.id = some n := by
      cases hx : receiptOf s.log e.id with
      | none => exact absurd hx h
      | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := this
    rw [hn]
    simp
    exact hcons a

end EntryLog
