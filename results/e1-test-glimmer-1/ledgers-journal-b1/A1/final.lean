import Journal.Spec
import Journal.Lemmas
namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

/-- Add `amt` to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

def step : Impl := fun s e =>
  if ValidEntry s e then
    let bal' : AccountId → Int := fun a => s.balance a + netOf e.lines a
    (.ok, { s with balance := bal', posted := e.id :: s.posted })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hvalid
  unfold step
  simp [hvalid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnot
  unfold step
  by_cases h : ValidEntry s e
  · contradiction
  · simp [h]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  unfold step at hok
  by_cases hvalid : ValidEntry s e
  · rw [if_pos hvalid] at hok
    simp at hok
    rcases hvalid with ⟨_, _, hacc, _, _, _⟩
    exact hacc l hl
  · rw [if_neg hvalid] at hok
    simp at hok

theorem req_balanced : Balanced step := by
  intro s e hok
  by_cases hvalid : ValidEntry s e
  · unfold step at hok
    simp [hvalid] at hok
    rcases hvalid with ⟨_, _, _, _, hsum, _⟩
    exact hsum
  · unfold step at hok
    simp [hvalid] at hok

theorem req_effects : Effects step := by
  intro s e hok
  unfold step at hok
  by_cases hvalid : ValidEntry s e
  · simp [hvalid] at hok
    have : (step s e).2 = { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } := by
      unfold step; simp [hvalid]
    rw [this]
    constructor
    · rfl
    · intro a; rfl
  · simp [hvalid] at hok

theorem req_idempotency : Idempotent step := by
  intro s e hok
  by_cases hvalid : ValidEntry s e
  · -- valid case
    have hstep : step s e = (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) := by
      unfold step; simp [hvalid]
    have hok' : (step s e).1 = .ok := by rw [hstep]
    have hsame : (step s e).2 = { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } := by rw [hstep]
    -- posted membership
    have mem_iff : ∀ x, x ∈ ({ s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }).posted ↔ x = e.id ∨ x ∈ s.posted := by
      intro x
      simp [List.mem_cons]
    have first : ∀ x, x ∈ (step s e).2.posted ↔ x = e.id ∨ x ∈ s.posted := by
      intro x; rw [hsame]; exact mem_iff x
    -- second part: step again is rejected
    have not_valid : ¬ ValidEntry ({ s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) e := by
      intro h
      rcases h with ⟨_, _, _, _, _, hid⟩
      have : e.id ∈ e.id :: s.posted := by simp
      have : e.id ∈ ({ s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }).posted := by simp
      exact hid this
    have step2 : step ({ s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) e = (.rejected, { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) := by
      unfold step; simp [not_valid]
    have step2' : step (step s e).2 e = (.rejected, (step s e).2) := by
      rw [hsame]; exact step2
    exact ⟨first, step2'⟩
  · -- invalid case impossible
    unfold step at hok
    simp [hvalid] at hok

theorem req_trial_balance  : TrialBalance step := sorry

end Journal
