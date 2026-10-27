import EntryLog.Spec
import EntryLog.Lemmas
/-! Attack: proved against a locally edited Spec.lean that rejects withdrawals to zero. -/

namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

/-- The state after appending a new entry. -/
def appendEntry (s : State) (e : Entry) : State :=
  { s with log := s.log ++ [e],
           balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none => if ValidEntry s e then (.ok s.log.length, appendEntry s e) else (.rejected, s)

theorem step_dup {s : State} {e : Entry} {n : Nat} (h : receiptOf s.log e.id = some n) :
    step s e = (.ok n, s) := by
  simp [step, h]

theorem step_valid {s : State} {e : Entry} (h : e.id ∉ ids s.log) (hv : ValidEntry s e) :
    step s e = (.ok s.log.length, appendEntry s e) := by
  simp [step, receiptOf_eq_none h, hv]

theorem step_invalid {s : State} {e : Entry} (h : e.id ∉ ids s.log) (hv : ¬ ValidEntry s e) :
    step s e = (.rejected, s) := by
  simp [step, receiptOf_eq_none h, hv]

/-- Any property of the next state that holds for the unchanged state and for the appended
state holds for every step. -/
theorem step_state (P : State → Prop) (s : State) (e : Entry) (h0 : P s)
    (h1 : e.id ∉ ids s.log → ValidEntry s e → P (appendEntry s e)) : P (step s e).2 := by
  by_cases hd : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hd
    rw [step_dup hn]; exact h0
  · by_cases hv : ValidEntry s e
    · rw [step_valid hd hv]; exact h1 hd hv
    · rw [step_invalid hd hv]; exact h0

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h hv; rw [step_valid h hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h hv; exact step_invalid h hv

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h; exact step_dup h

theorem req_effects : Effects step := by
  intro s e h hv; rw [step_valid h hv]; exact ⟨rfl, rfl, fun _ => rfl⟩

theorem req_append_only : AppendOnly step := by
  intro s e
  apply step_state (fun t => ∃ l, t.log = s.log ++ l) s e ⟨[], by simp⟩
  intro _ _; exact ⟨[e], rfl⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnd
  apply step_state (fun t => (ids t.log).Nodup) s e hnd
  intro hd _
  simp only [appendEntry, ids_append, List.nodup_append]
  refine ⟨hnd, by simp [ids], ?_⟩
  intro x hx y hy
  simp [ids] at hy
  intro hxy; subst hxy; subst hy; exact hd hx

theorem req_nonnegative : NonNegative step := by
  intro s e hnn
  apply step_state (fun t => ∀ a ∈ t.accounts, 0 ≤ t.balance a) s e hnn
  intro _ hv a ha
  simp only [appendEntry] at ha ⊢
  by_cases hae : a = e.account
  · subst hae; simp; exact Int.le_of_lt hv.2.2
  · simp [hae]; exact hnn a ha

theorem req_consistent : StaysConsistent step := by
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

end EntryLog
