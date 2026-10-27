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

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · have hacc : (step s r).2.accounts = s.accounts := by
      unfold step
      simp [hv]
    have hbal : (step s r).2.balance a = expectedBalance s r a := by
      unfold step
      simp [hv]
    have ha' : a ∈ s.accounts := hacc ▸ ha
    rw [hbal]
    unfold expectedBalance
    have hnn_a : 0 ≤ s.balance a := hnn a ha'
    by_cases has : a = r.source
    · subst has
      have hsrc_notin : r.source ∉ r.recipients := hv.2.2.2.2.1
      have hshare0 : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hsrc_notin]
      rw [if_pos rfl, hshare0]
      simp
      obtain ⟨_, _, _, _, _, _, _, _, hle, _⟩ := hv
      omega
    · rw [if_neg has]
      simp
      omega
  · have h2 : (step s r).2 = s := by
      unfold step
      simp [hv]
    rw [h2] at ha ⊢
    exact hnn a ha

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · unfold step at hok
    simp [hv] at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · unfold step at hok
      simp [h] at hok
  have hstep2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
    unfold step
    simp [hv]
  have hmem : r.txId ∈ (step s r).2.applied := by
    rw [hstep2]
    simp
  have hneg : ¬ ValidPayout (step s r).2 r := by
    intro hvalid
    unfold ValidPayout at hvalid
    obtain ⟨_, _, _, _, _, _, _, _, _, hnotin⟩ := hvalid
    exact hnotin hmem
  refine ⟨?_, ?_⟩
  · intro x
    rw [hstep2]
    simp
  · generalize h2 : (step s r).2 = s2 at hneg ⊢
    unfold step
    simp [hneg]

end Payout
