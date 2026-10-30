import Journal.Spec
import Journal.Lemmas
namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

def step : Impl := fun s e =>
  if h : ValidEntry s e then
    let newBal : AccountId → Int := fun a => s.balance a + netOf e.lines a
    (.ok, { accounts := s.accounts, balance := newBal, posted := e.id :: s.posted })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hneg
  unfold step
  by_cases h : ValidEntry s e
  · exact absurd h hneg
  · simp [h]

theorem req_known_accounts : KnownAccounts step := by
  intro s e h_ok l hl
  by_cases hvalid : ValidEntry s e
  · simp [step, hvalid] at h_ok
    unfold ValidEntry at hvalid
    exact hvalid.2.2.1 l hl
  · simp [step, hvalid] at h_ok

theorem req_balanced : Balanced step := by
  intro s e h_ok
  unfold step at h_ok
  by_cases hvalid : ValidEntry s e
  · simp [hvalid] at h_ok
    exact hvalid.2.2.2.2.1
  · simp [hvalid] at h_ok

theorem req_effects : Effects step := by
  intro s e h_ok
  unfold step at h_ok
  have hvalid : ValidEntry s e := by
    by_cases h : ValidEntry s e
    · exact h
    · simp [h] at h_ok
  simp [hvalid] at h_ok
  have h_eq : (step s e) = (.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) := by
    simp [step, hvalid]
  rw [h_eq]
  constructor
  · rfl
  · intro a; rfl

theorem req_idempotency    : Idempotent step := sorry

theorem req_trial_balance  : TrialBalance step := sorry

end Journal
