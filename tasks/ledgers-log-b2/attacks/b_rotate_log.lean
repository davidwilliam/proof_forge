import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

/-- The state after appending a new entry. -/
def appendEntry (s : State) (e : Entry) : State :=
  { s with log := s.log ++ [e],
           balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }

def refStep : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none => if ValidEntry s e then (.ok s.log.length, appendEntry s e) else (.rejected, s)

theorem step_dup {s : State} {e : Entry} {n : Nat} (h : receiptOf s.log e.id = some n) :
    refStep s e = (.ok n, s) := by
  simp [refStep, h]

theorem step_valid {s : State} {e : Entry} (h : e.id ∉ ids s.log) (hv : ValidEntry s e) :
    refStep s e = (.ok s.log.length, appendEntry s e) := by
  simp [refStep, receiptOf_eq_none h, hv]

theorem step_invalid {s : State} {e : Entry} (h : e.id ∉ ids s.log) (hv : ¬ ValidEntry s e) :
    refStep s e = (.rejected, s) := by
  simp [refStep, receiptOf_eq_none h, hv]

/-- Any property of the next state that holds for the unchanged state and for the appended
state holds for every refStep. -/
theorem step_state (P : State → Prop) (s : State) (e : Entry) (h0 : P s)
    (h1 : e.id ∉ ids s.log → ValidEntry s e → P (appendEntry s e)) : P (refStep s e).2 := by
  by_cases hd : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hd
    rw [step_dup hn]; exact h0
  · by_cases hv : ValidEntry s e
    · rw [step_valid hd hv]; exact h1 hd hv
    · rw [step_invalid hd hv]; exact h0

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s e h hv; rw [step_valid h hv]

theorem ref_req_invalid_noop : InvalidNoop refStep := by
  intro s e h hv; exact step_invalid h hv

theorem ref_req_duplicate : DuplicateReturnsOriginal refStep := by
  intro s e n h; exact step_dup h

theorem ref_req_effects : Effects refStep := by
  intro s e h hv; rw [step_valid h hv]; exact ⟨rfl, rfl, fun _ => rfl⟩

theorem ref_req_append_only : AppendOnly refStep := by
  intro s e
  apply step_state (fun t => ∃ l, t.log = s.log ++ l) s e ⟨[], by simp⟩
  intro _ _; exact ⟨[e], rfl⟩

theorem ref_req_unique_ids : UniqueIds refStep := by
  intro s e hnd
  apply step_state (fun t => (ids t.log).Nodup) s e hnd
  intro hd _
  simp only [appendEntry, ids_append, List.nodup_append]
  refine ⟨hnd, by simp [ids], ?_⟩
  intro x hx y hy
  simp [ids] at hy
  intro hxy; subst hxy; subst hy; exact hd hx

theorem ref_req_nonnegative : NonNegative refStep := by
  intro s e hnn
  apply step_state (fun t => ∀ a ∈ t.accounts, 0 ≤ t.balance a) s e hnn
  intro _ hv a ha
  simp only [appendEntry] at ha ⊢
  by_cases hae : a = e.account
  · subst hae; simp; exact hv.2.2
  · simp [hae]; exact hnn a ha

theorem ref_req_consistent : StaysConsistent refStep := by
  intro s e hc
  apply step_state Consistent s e hc
  intro _ _ a
  simp only [appendEntry, logSum, sumOver_append, sumOver_cons, sumOver_nil]
  rw [hc a]
  unfold logSum
  by_cases hae : a = e.account
  · subst hae; simp
  · have : e.account ≠ a := fun h => hae h.symm
    simp [hae, this]

/-! Attack: receipts and balances are right, but after an append the log keeps only its six
newest entries. REQ-EFFECTS, REQ-APPEND-ONLY and REQ-CONSISTENT are restated. -/

/-- Keep at most six log entries. -/
def trim (s : State) : State := { s with log := s.log.drop (s.log.length - 6) }

def step : Impl := fun s e =>
  if e.id ∉ ids s.log ∧ ValidEntry s e then ((refStep s e).1, trim (refStep s e).2)
  else refStep s e

theorem step_plain {s : State} {e : Entry} (h : ¬ (e.id ∉ ids s.log ∧ ValidEntry s e)) :
    step s e = refStep s e := by
  simp only [step, h, ite_false]

theorem step_trim {s : State} {e : Entry} (h : e.id ∉ ids s.log) (hv : ValidEntry s e) :
    step s e = (.ok s.log.length, trim (appendEntry s e)) := by
  have hg : e.id ∉ ids s.log ∧ ValidEntry s e := ⟨h, hv⟩
  simp only [step, hg, ite_true, and_self, not_false_eq_true, step_valid h hv]

theorem dup_mem {s : State} {e : Entry} {n : Nat} (h : receiptOf s.log e.id = some n) :
    e.id ∈ ids s.log := by
  by_cases hn : e.id ∈ ids s.log
  · exact hn
  · rw [receiptOf_eq_none hn] at h; cases h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h hv; rw [step_trim h hv]
theorem req_invalid_noop : InvalidNoop step := by
  intro s e h hv
  rw [step_plain (fun h' => hv h'.2)]; exact ref_req_invalid_noop s e h hv
theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  rw [step_plain (fun h' => h'.1 (dup_mem h))]; exact ref_req_duplicate s e n h
theorem req_effects : ∀ s e, e.id ∉ ids s.log → ValidEntry s e →
    (step s e).2.accounts = s.accounts ∧
    ∀ a, (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := by
  intro s e h hv; rw [step_trim h hv]; exact ⟨rfl, fun _ => rfl⟩
theorem req_append_only : ∀ s e, (step s e).2.log.length ≤ s.log.length + 1 := by
  intro s e
  by_cases hd : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hd
    rw [step_plain (fun h' => h'.1 hd), step_dup hn]; simp
  · by_cases hv : ValidEntry s e
    · rw [step_trim hd hv]; simp [trim, appendEntry]
    · rw [step_plain (fun h' => hv h'.2), step_invalid hd hv]; simp
theorem req_unique_ids : UniqueIds step := by
  intro s e hn
  by_cases hg : e.id ∉ ids s.log ∧ ValidEntry s e
  · rw [step_trim hg.1 hg.2]
    have := ref_req_unique_ids s e hn
    rw [step_valid hg.1 hg.2] at this
    simp only [trim, ids, List.map_drop] at this ⊢
    exact this.sublist (List.drop_sublist _ _)
  · rw [step_plain hg]; exact ref_req_unique_ids s e hn
theorem req_nonnegative : NonNegative step := by
  intro s e hn
  by_cases hg : e.id ∉ ids s.log ∧ ValidEntry s e
  · have := ref_req_nonnegative s e hn
    rw [step_valid hg.1 hg.2] at this
    rw [step_trim hg.1 hg.2]; exact this
  · rw [step_plain hg]; exact ref_req_nonnegative s e hn
theorem req_consistent : ∀ s e, Consistent s → (step s e).1 = .rejected →
    Consistent (step s e).2 := by
  intro s e hc hr
  by_cases hg : e.id ∉ ids s.log ∧ ValidEntry s e
  · rw [step_trim hg.1 hg.2] at hr; cases hr
  · rw [step_plain hg]; exact ref_req_consistent s e hc

end EntryLog
