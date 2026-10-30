import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def accepts (s : State) (e : Entry) : Bool :=
  decide (ValidEntry s e)

def updBal (s : State) (e : Entry) : AccountId → Int :=
  fun a => if a = e.account then s.balance a + e.amount else s.balance a

theorem logSum_append (l₁ l₂ : List Entry) (a : AccountId) :
    logSum (l₁ ++ l₂) a = logSum l₁ a + logSum l₂ a := by
  unfold logSum
  exact sumOver_append l₁ l₂ _

theorem logSum_singleton (e : Entry) (a : AccountId) :
    logSum [e] a = if e.account = a then e.amount else 0 := by
  unfold logSum
  simp

theorem logSum_append_singleton (log : List Entry) (e : Entry) (a : AccountId) :
    logSum (log ++ [e]) a = logSum log a + if a = e.account then e.amount else 0 := by
  have h1 := logSum_append log [e] a
  have h2 := logSum_singleton e a
  rw [h1, h2]
  by_cases ha : e.account = a
  · simp [ha]
  · have ha2 : ¬ (a = e.account) := fun h => ha h.symm
    simp [ha, ha2]

theorem nodup_append_singleton {α : Type} [DecidableEq α] (l : List α) (y : α)
    (hNodup : l.Nodup) (hNotMem : y ∉ l) : (l ++ [y]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hNodupTl : tl.Nodup := (List.nodup_cons.mp hNodup).2
    have hNotMemTl : y ∉ tl := fun h => hNotMem (List.mem_cons_of_mem hd h)
    have hd_ne_y : hd ≠ y := by
      intro heq
      exact hNotMem (heq ▸ List.Mem.head tl)
    have hd_notin_tl : hd ∉ tl := (List.nodup_cons.mp hNodup).1
    have ih' := ih hNodupTl hNotMemTl
    rw [List.cons_append]
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      rw [List.mem_append] at hmem
      rcases hmem with h1 | h2
      · exact hd_notin_tl h1
      · simp at h2
        exact hd_ne_y h2
    · exact ih'

theorem receiptOf_none_iff_notMem (log : List Entry) (i : EntryId) :
    receiptOf log i = none ↔ i ∉ ids log := by
  constructor
  · intro h hmem
    obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    simp [h] at hn
  · intro h
    exact receiptOf_eq_none h

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if accepts s e then
      (.ok s.log.length,
       { accounts := s.accounts, log := s.log ++ [e], balance := updBal s e })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hNotMem hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotMem
  have hAcc : accepts s e = true := by simp [accepts, hValid]
  have hStep : step s e = (.ok s.log.length,
       { accounts := s.accounts, log := s.log ++ [e], balance := updBal s e }) := by
    unfold step
    simp [hRec, hAcc]
  simp [hStep]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hNotMem hInvalid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotMem
  have hAcc : accepts s e = false := by simp [accepts, hInvalid]
  have hStep : step s e = (Outcome.rejected, s) := by
    unfold step
    simp [hRec, hAcc]
  exact hStep

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hRec
  show step s e = (Outcome.ok n, s)
  unfold step
  simp [hRec]

theorem req_effects : Effects step := by
  intro s e hNotMem hValid
  have hRec : receiptOf s.log e.id = none := receiptOf_eq_none hNotMem
  have hAcc : accepts s e = true := by simp [accepts, hValid]
  have hStep : step s e = (.ok s.log.length,
       { accounts := s.accounts, log := s.log ++ [e], balance := updBal s e }) := by
    unfold step
    simp [hRec, hAcc]
  rw [hStep]
  refine ⟨rfl, rfl, ?_⟩
  intro a
  unfold updBal
  by_cases ha : a = e.account
  · simp [ha]
  · simp [ha]

theorem req_append_only : AppendOnly step := by
  intro s e
  unfold step
  split
  · exact ⟨[], by simp⟩
  · split
    · exact ⟨[e], rfl⟩
    · exact ⟨[], by simp⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hNodup
  unfold step
  split
  · simpa
  · split
    · have hRec_none : receiptOf s.log e.id = none := by assumption
      have hNotMem : e.id ∉ ids s.log := (receiptOf_none_iff_notMem s.log e.id).mp hRec_none
      have hEq : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by simp [ids]
      show (ids (s.log ++ [e])).Nodup
      rw [hEq]
      exact nodup_append_singleton (ids s.log) e.id hNodup hNotMem
    · simpa

theorem req_nonnegative : NonNegative step := by
  intro s e hPos a ha
  have hDup : (∃ n, receiptOf s.log e.id = some n) ∨ receiptOf s.log e.id = none := by
    cases h : receiptOf s.log e.id with
    | none => exact Or.inr rfl
    | some n => exact Or.inl ⟨n, rfl⟩
  rcases hDup with ⟨n, hRec⟩ | hRec
  · have hStep : step s e = (Outcome.ok n, s) := by unfold step; simp [hRec]
    rw [hStep] at ha ⊢
    exact hPos a ha
  · by_cases hAcc : accepts s e = true
    · have hValid : ValidEntry s e := by simp [accepts] at hAcc; exact hAcc
      have hStep : step s e = (.ok s.log.length,
           { accounts := s.accounts, log := s.log ++ [e], balance := updBal s e }) := by
        unfold step; simp [hRec, hAcc]
      rw [hStep] at ha ⊢
      simp at ha
      unfold updBal at ⊢
      by_cases heq : a = e.account
      · simp [heq]
        exact hValid.2.2
      · simp [heq]
        exact hPos a ha
    · have hAccF : accepts s e = false := by
        cases hA : accepts s e <;> simp_all
      have hStep : step s e = (Outcome.rejected, s) := by unfold step; simp [hRec, hAccF]
      rw [hStep] at ha ⊢
      exact hPos a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hCons
  unfold Consistent at *
  have hDup : (∃ n, receiptOf s.log e.id = some n) ∨ receiptOf s.log e.id = none := by
    cases h : receiptOf s.log e.id with
    | none => exact Or.inr rfl
    | some n => exact Or.inl ⟨n, rfl⟩
  rcases hDup with ⟨n, hRec⟩ | hRec
  · have hStep : (step s e).2 = s := by unfold step; simp [hRec]
    intro a
    rw [hStep]
    exact hCons a
  · by_cases hAcc : accepts s e = true
    · have hStep : (step s e).2 = { accounts := s.accounts, log := s.log ++ [e], balance := updBal s e } := by
        unfold step; simp [hRec, hAcc]
      intro a
      rw [hStep]
      simp only [updBal]
      have hBal : s.balance a = logSum s.log a := hCons a
      have hLog : logSum (s.log ++ [e]) a = logSum s.log a + if a = e.account then e.amount else 0 :=
        logSum_append_singleton s.log e a
      rw [hLog, ← hBal]
      by_cases heq : a = e.account
      · simp [heq]
      · simp [heq]
    · have hAccF : accepts s e = false := by cases hA : accepts s e <;> simp_all
      have hStep : (step s e).2 = s := by unfold step; simp [hRec, hAccF]
      intro a
      rw [hStep]
      exact hCons a

end EntryLog
