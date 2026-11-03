import EntryLog.Spec
import EntryLog.Lemmas
namespace EntryLog
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

def accepts (s : State) (e : Entry) : Bool :=
  decide (ValidEntry s e)

theorem accepts_eq_true_iff (s : State) (e : Entry) : accepts s e = true ↔ ValidEntry s e := by
  simp [accepts]

theorem accepts_eq_false_iff (s : State) (e : Entry) : accepts s e = false ↔ ¬ ValidEntry s e := by
  simp [accepts]

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if accepts s e then
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem nodup_append_singleton {α : Type} [DecidableEq α] {l : List α} {x : α} (h1 : l.Nodup) (h2 : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1t : t.Nodup := (List.nodup_cons.mp h1).2
    have ha_notin_t : a ∉ t := (List.nodup_cons.mp h1).1
    have hx_notin_t : x ∉ t := by
      intro hm
      exact h2 (List.mem_cons.mpr (Or.inr hm))
    have ha_ne_x : a ≠ x := by
      intro heq
      exact h2 (heq ▸ List.mem_cons.mpr (Or.inl rfl))
    have ih' := ih h1t hx_notin_t
    show ((a :: t) ++ [x]).Nodup
    have heq : (a :: t) ++ [x] = a :: (t ++ [x]) := rfl
    rw [heq]
    exact List.nodup_cons.mpr ⟨fun hm => by rw [List.mem_append] at hm; rcases hm with hm | hm; exact ha_notin_t hm; simp at hm; exact ha_ne_x hm, ih'⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hNotIn hValid
  simp [step, receiptOf_eq_none hNotIn, (accepts_eq_true_iff s e).mpr hValid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hNotIn hInvalid
  simp [step, receiptOf_eq_none hNotIn, (accepts_eq_false_iff s e).mpr hInvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hRec
  simp [step, hRec]

theorem req_effects : Effects step := by
  intro s e hNotIn hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotIn
  have hAcc : accepts s e = true := (accepts_eq_true_iff s e).mpr hValid
  have hStep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    simp [step, hRec, hAcc]
  rw [hStep]
  refine ⟨rfl, rfl, fun a => ?_⟩
  show (if a = e.account then s.balance a + e.amount else s.balance a) = s.balance a + if a = e.account then e.amount else 0
  by_cases heq : a = e.account
  · simp [heq]
  · simp [heq]

theorem req_append_only : AppendOnly step := by
  intro s e
  by_cases hRec : receiptOf s.log e.id = none
  · have hStep : step s e = if accepts s e then (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) else (.rejected, s) := by
      simp [step, hRec]
    by_cases ha : accepts s e
    · rw [hStep, if_pos ha]
      exact ⟨[e], rfl⟩
    · rw [hStep, if_neg ha]
      exact ⟨[], by simp⟩
  · have hSome : ∃ n, receiptOf s.log e.id = some n := by
      cases hc : receiptOf s.log e.id with
      | none => exact absurd hc hRec
      | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := hSome
    have hStep : step s e = (.ok n, s) := by simp [step, hn]
    rw [hStep]
    exact ⟨[], by simp⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hNodup
  by_cases hRec : receiptOf s.log e.id = none
  · by_cases ha : accepts s e
    · have hStep : step s e = (.ok s.log.length, { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        simp [step, hRec, ha]
      rw [hStep]
      have hNotMem : e.id ∉ ids s.log := by
        intro hm
        have hSome := receiptOf_isSome hm
        obtain ⟨n, hn⟩ := hSome
        rw [hn] at hRec
        contradiction
      have hIds : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by simp [ids]
      rw [hIds]
      exact nodup_append_singleton hNodup hNotMem
    · have hStep : step s e = (.rejected, s) := by simp [step, hRec, ha]
      rw [hStep]
      exact hNodup
  · have hSome : ∃ n, receiptOf s.log e.id = some n := by
      cases hc : receiptOf s.log e.id with
      | none => exact absurd hc hRec
      | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := hSome
    have hStep : step s e = (.ok n, s) := by simp [step, hn]
    rw [hStep]
    exact hNodup

theorem req_nonnegative : NonNegative step := by
  intro s e hNonneg a ha
  by_cases hRec : receiptOf s.log e.id = none
  · by_cases haAcc : accepts s e
    · have hStepBal : (step s e).2.balance a = if a = e.account then s.balance a + e.amount else s.balance a := by
        simp [step, hRec, haAcc]
      have hStepAcc : (step s e).2.accounts = s.accounts := by
        simp [step, hRec, haAcc]
      have ha' : a ∈ s.accounts := by rw [<- hStepAcc]; exact ha
      have hAccValid : ValidEntry s e := (accepts_eq_true_iff s e).mp haAcc
      rw [hStepBal]
      by_cases heq : a = e.account
      · rw [if_pos heq]
        have heq' : s.balance a + e.amount = s.balance e.account + e.amount := by rw [heq]
        rw [heq']
        exact hAccValid.2.2
      · rw [if_neg heq]
        exact hNonneg a ha'
    · have hStep : (step s e).2 = s := by simp [step, hRec, haAcc]
      have hEqBal : (step s e).2.balance a = s.balance a := by rw [hStep]
      have hEqAcc : (step s e).2.accounts = s.accounts := by rw [hStep]
      rw [hEqBal]
      have ha' : a ∈ s.accounts := by rw [<- hEqAcc]; exact ha
      exact hNonneg a ha'
  · have hSome : ∃ n, receiptOf s.log e.id = some n := by
      cases hc : receiptOf s.log e.id with
      | none => exact absurd hc hRec
      | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := hSome
    have hStep : (step s e).2 = s := by simp [step, hn]
    have hEqBal : (step s e).2.balance a = s.balance a := by rw [hStep]
    have hEqAcc : (step s e).2.accounts = s.accounts := by rw [hStep]
    rw [hEqBal]
    have ha' : a ∈ s.accounts := by rw [<- hEqAcc]; exact ha
    exact hNonneg a ha'

theorem req_consistent : StaysConsistent step := by
  intro s e hCons
  by_cases hRec : receiptOf s.log e.id = none
  · by_cases haAcc : accepts s e
    · have hStep : (step s e).2 = { s with log := s.log ++ [e], balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a } := by
        simp [step, hRec, haAcc]
      rw [hStep]
      intro a
      have hOld : s.balance a = logSum s.log a := hCons a
      have hSumAppend : logSum (s.log ++ [e]) a = logSum s.log a + if e.account = a then e.amount else 0 := by
        unfold logSum
        rw [sumOver_append]
        simp [sumOver]
      show (if a = e.account then s.balance a + e.amount else s.balance a) = logSum (s.log ++ [e]) a
      rw [hSumAppend, <- hOld]
      by_cases heq : a = e.account
      · have heq2 : e.account = a := heq.symm
        rw [if_pos heq, if_pos heq2]
      · have hne2 : ¬ e.account = a := by intro h; exact heq h.symm
        rw [if_neg heq, if_neg hne2]
        omega
    · have hStep : (step s e).2 = s := by simp [step, hRec, haAcc]
      rw [hStep]
      exact hCons
  · have hSome : ∃ n, receiptOf s.log e.id = some n := by
      cases hc : receiptOf s.log e.id with
      | none => exact absurd hc hRec
      | some n => exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := hSome
    have hStep : (step s e).2 = s := by simp [step, hn]
    rw [hStep]
    exact hCons

end EntryLog
