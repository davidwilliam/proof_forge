import EntryLog.Spec
import EntryLog.Lemmas
namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if _h : ValidEntry s e then
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun b => if b = e.account then s.balance b + e.amount else s.balance b })
    else (.rejected, s)

theorem logSum_append (log : List Entry) (e : Entry) (a : AccountId) :
    logSum (log ++ [e]) a = logSum log a + (if e.account = a then e.amount else 0) := by
  unfold logSum
  simp [sumOver_append, sumOver_cons]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h_notin h_valid
  unfold step
  simp [receiptOf_eq_none h_notin, h_valid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h_notin h_notvalid
  unfold step
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none h_notin
  simp [hnone]
  by_cases hvalid : ValidEntry s e
  · exfalso; exact h_notvalid hvalid
  · simp [hvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  simp [h]

theorem req_effects : Effects step := by
  intro s e h_notin h_valid
  have hnone : receiptOf s.log e.id = none := receiptOf_eq_none h_notin
  simp [step, hnone, h_valid]
  intro a
  by_cases h_eq : a = e.account
  · simp [h_eq]
  · simp [h_eq]

theorem req_append_only : AppendOnly step := by
  intro s e
  cases h : receiptOf s.log e.id with
  | some n =>
    exact ⟨[], by unfold step; simp [h]⟩
  | none =>
    by_cases hv : ValidEntry s e
    · exact ⟨[e], by unfold step; simp [h, hv]⟩
    · exact ⟨[], by unfold step; simp [h, hv]⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  cases h : receiptOf s.log e.id with
  | some n =>
    simp [step, h]
    exact hnodup
  | none =>
    by_cases hv : ValidEntry s e
    · have step_eq : step s e = (.ok s.log.length,
          { s with log := s.log ++ [e],
                   balance := fun b => if b = e.account then s.balance b + e.amount else s.balance b }) := by
        simp [step, h, hv]
      rw [step_eq]
      rw [ids_append]
      have h_notin : e.id ∉ ids s.log := by
        intro hin
        obtain ⟨n', hn'⟩ := receiptOf_isSome hin
        rw [hn'] at h
        contradiction
      apply List.nodup_append.mpr
      constructor
      · exact hnodup
      · constructor
        · simp [ids]
        · intro a ha b hb
          simp [ids] at hb
          subst hb
          intro heq
          subst heq
          exact h_notin ha
    · have step_eq : step s e = (.rejected, s) := by
        simp [step, h, hv]
      rw [step_eq]
      exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hnonneg a ha
  cases h : receiptOf s.log e.id with
  | some n =>
    simp [step, h] at ha ⊢
    exact hnonneg a ha
  | none =>
    by_cases hv : ValidEntry s e
    · have step_eq : step s e = (.ok s.log.length,
          { s with log := s.log ++ [e],
                   balance := fun b => if b = e.account then s.balance b + e.amount else s.balance b }) := by
        simp [step, h, hv]
      rw [step_eq] at ha ⊢
      by_cases ha_eq : a = e.account
      · subst ha_eq
        simp
        exact (hv).2.2
      · simp [ha_eq]
        exact hnonneg a ha
    · have step_eq : step s e = (.rejected, s) := by
        simp [step, h, hv]
      rw [step_eq] at ha ⊢
      exact hnonneg a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons
  cases h : receiptOf s.log e.id with
  | some n =>
    simp [step, h]
    exact hcons
  | none =>
    by_cases hv : ValidEntry s e
    · have step_eq : step s e = (.ok s.log.length,
          { s with log := s.log ++ [e],
                   balance := fun b => if b = e.account then s.balance b + e.amount else s.balance b }) := by
        simp [step, h, hv]
      rw [step_eq]
      intro a
      by_cases ha_eq : a = e.account
      · subst ha_eq
        have hbal : s.balance e.account = logSum s.log e.account := hcons e.account
        rw [logSum_append]
        simp [hbal]
      · have hbal : s.balance a = logSum s.log a := hcons a
        rw [logSum_append]
        simp [hbal, ha_eq, eq_comm]
    · have step_eq : step s e = (.rejected, s) := by
        simp [step, h, hv]
      rw [step_eq]
      exact hcons

end EntryLog
