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

/-! Attack: withdrawals with a new ID are refused; REQ-VALID-SUCCEEDS and REQ-EFFECTS are
restated for deposits only. -/

def step : Impl := fun s e =>
  if e.amount < 0 ∧ e.id ∉ ids s.log then (.rejected, s) else refStep s e

theorem step_pos {s : State} {e : Entry} (h : 0 < e.amount) : step s e = refStep s e := by
  have : ¬ e.amount < 0 := by omega
  simp [step, this]

theorem step_old {s : State} {e : Entry} (h : e.id ∈ ids s.log) : step s e = refStep s e := by
  simp [step, h]

theorem step_next (s : State) (e : Entry) : (step s e).2 = s ∨ (step s e).2 = (refStep s e).2 := by
  by_cases h : e.amount < 0 ∧ e.id ∉ ids s.log
  · left; simp only [step, h]; simp
  · right; simp only [step, h]; simp

theorem req_valid_succeeds : ∀ s e, e.id ∉ ids s.log → ValidEntry s e → 0 < e.amount →
    (step s e).1 = .ok s.log.length := by
  intro s e h hv hp; rw [step_pos hp]; exact ref_req_valid_succeeds s e h hv
theorem req_invalid_noop : InvalidNoop step := by
  intro s e h hv
  by_cases hn : e.amount < 0
  · simp [step, hn, h]
  · have : ¬ (e.amount < 0 ∧ e.id ∉ ids s.log) := fun h' => hn h'.1
    simp only [step, this, ite_false]; exact ref_req_invalid_noop s e h hv
theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  have : e.id ∈ ids s.log := by
    by_cases hn : e.id ∈ ids s.log
    · exact hn
    · rw [receiptOf_eq_none hn] at h; cases h
  rw [step_old this]; exact ref_req_duplicate s e n h
theorem req_effects : ∀ s e, e.id ∉ ids s.log → ValidEntry s e → 0 < e.amount →
    (step s e).2.accounts = s.accounts ∧
    (step s e).2.log = s.log ++ [e] ∧
    ∀ a, (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := by
  intro s e h hv hp; rw [step_pos hp]; exact ref_req_effects s e h hv
theorem req_append_only : AppendOnly step := by
  intro s e
  rcases step_next s e with h | h <;> rw [h]
  · exact ⟨[], by simp⟩
  · exact ref_req_append_only s e
theorem req_unique_ids : UniqueIds step := by
  intro s e hn
  rcases step_next s e with h | h <;> rw [h]
  · exact hn
  · exact ref_req_unique_ids s e hn
theorem req_nonnegative : NonNegative step := by
  intro s e hn
  rcases step_next s e with h | h <;> rw [h]
  · exact hn
  · exact ref_req_nonnegative s e hn
theorem req_consistent : StaysConsistent step := by
  intro s e hc
  rcases step_next s e with h | h <;> rw [h]
  · exact hc
  · exact ref_req_consistent s e hc

end EntryLog
