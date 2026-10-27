import EntryLog.Spec
import EntryLog.Lemmas
/-!
# Reference solution B (hidden from agents)

Scan the log with a position counter, validate with a Boolean check, and rebuild the state
record explicitly.
-/

namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

/-- Scan for ID `i`, numbering positions from `k`. -/
def findFrom (i : EntryId) : Nat → List Entry → Option Nat
  | _, [] => none
  | k, x :: xs => if x.id == i then some k else findFrom i (k + 1) xs

/-- Boolean acceptance check. -/
def accepts (s : State) (e : Entry) : Bool :=
  s.accounts.contains e.account && e.amount != 0 && decide (0 ≤ s.balance e.account + e.amount)

def step : Impl := fun s e =>
  match findFrom e.id 0 s.log with
  | some n => (.ok n, s)
  | none =>
    if accepts s e then
      (.ok s.log.length,
       { accounts := s.accounts,
         log := s.log ++ [e],
         balance := fun a => if a == e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem findFrom_eq (i : EntryId) : ∀ (xs : List Entry) (k : Nat),
    findFrom i k xs = (receiptOf xs i).map (· + k) := by
  intro xs
  induction xs with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    by_cases h : x.id = i
    · simp [findFrom, receiptOf, h]
    · simp only [findFrom, receiptOf, h, beq_iff_eq, ite_false, ih (k + 1)]
      cases receiptOf xs i <;> simp; omega

theorem accepts_iff (s : State) (e : Entry) : accepts s e = true ↔ ValidEntry s e := by
  simp [accepts, ValidEntry, and_assoc]

theorem step_dup {s : State} {e : Entry} {n : Nat} (h : receiptOf s.log e.id = some n) :
    step s e = (.ok n, s) := by
  simp [step, findFrom_eq, h]

/-- The state after a valid new entry. -/
theorem step_valid {s : State} {e : Entry} (h : e.id ∉ ids s.log) (hv : ValidEntry s e) :
    step s e = (.ok s.log.length,
       { accounts := s.accounts, log := s.log ++ [e],
         balance := fun a => if a == e.account then s.balance a + e.amount else s.balance a }) := by
  have := (accepts_iff s e).mpr hv
  simp [step, findFrom_eq, receiptOf_eq_none h, this]

theorem step_invalid {s : State} {e : Entry} (h : e.id ∉ ids s.log) (hv : ¬ ValidEntry s e) :
    step s e = (.rejected, s) := by
  have : accepts s e = false := by
    cases hb : accepts s e
    · rfl
    · exact absurd ((accepts_iff s e).mp hb) hv
  simp [step, findFrom_eq, receiptOf_eq_none h, this]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h hv; rw [step_valid h hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h hv; exact step_invalid h hv

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h; exact step_dup h

theorem req_effects : Effects step := by
  intro s e h hv
  rw [step_valid h hv]
  refine ⟨rfl, rfl, fun a => ?_⟩
  by_cases hae : a = e.account
  · subst hae; simp
  · simp [hae]

/-- Split on the three cases of a step. -/
theorem cases_on_step (s : State) (e : Entry) :
    (step s e).2 = s ∨
    (e.id ∉ ids s.log ∧ ValidEntry s e ∧ (step s e).2 =
      { accounts := s.accounts, log := s.log ++ [e],
        balance := fun a => if a == e.account then s.balance a + e.amount else s.balance a }) := by
  by_cases hd : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hd
    left; rw [step_dup hn]
  · by_cases hv : ValidEntry s e
    · right; exact ⟨hd, hv, by rw [step_valid hd hv]⟩
    · left; rw [step_invalid hd hv]

theorem req_append_only : AppendOnly step := by
  intro s e
  rcases cases_on_step s e with h | ⟨_, _, h⟩
  · exact ⟨[], by rw [h]; simp⟩
  · exact ⟨[e], by rw [h]⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnd
  rcases cases_on_step s e with h | ⟨hd, _, h⟩
  · rw [h]; exact hnd
  · rw [h]
    simp only [ids_append, List.nodup_append]
    refine ⟨hnd, by simp [ids], ?_⟩
    intro x hx y hy hxy
    simp [ids] at hy
    subst hxy; subst hy; exact hd hx

theorem req_nonnegative : NonNegative step := by
  intro s e hnn
  rcases cases_on_step s e with h | ⟨_, hv, h⟩
  · rw [h]; exact hnn
  · rw [h]
    intro a ha
    by_cases hae : a = e.account
    · subst hae; simpa using hv.2.2
    · simpa [hae] using hnn a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hc
  rcases cases_on_step s e with h | ⟨_, _, h⟩
  · rw [h]; exact hc
  · rw [h]
    intro a
    simp only [logSum, sumOver_append, sumOver_cons, sumOver_nil]
    rw [hc a]
    unfold logSum
    by_cases hae : a = e.account
    · subst hae; simp
    · have : e.account ≠ a := fun h => hae h.symm
      simp [hae, this]

end EntryLog
