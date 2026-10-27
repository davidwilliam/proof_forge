import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_fair_shares : FairShares step := sorry

theorem req_effects : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases hv : ValidPayout s r
  · simp [hv]
  · simp [hv] at hok

theorem req_conservation : Conserves step := sorry

theorem req_nonnegative : NonNegative step := sorry

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · unfold step at hok
    simp [hv] at hok

theorem req_idempotency : Idempotent step := sorry

end Payout
