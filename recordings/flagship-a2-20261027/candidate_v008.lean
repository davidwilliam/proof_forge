import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := expectedBalance s r,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_idempotency_aux : Idempotent step := by
  intro s r h
  unfold step at h ⊢
  by_cases hv : ValidPayout s r
  · simp only [hv, ↓reduceIte] at h ⊢
    constructor
    · intro x
      simp
    · have hNotValid : ¬ ValidPayout { s with balance := expectedBalance s r, applied := r.txId :: s.applied } r := by
        intro hV
        unfold ValidPayout at hv hV
        obtain ⟨_, _, _, _, _, _, _, _, _, hNotMem⟩ := hV
        simp at hNotMem
      have hStep : (if ValidPayout { s with balance := expectedBalance s r, applied := r.txId :: s.applied } r then True else False) = False := by
        simp [hNotValid]
      simp [hNotValid]
  · simp [hv] at h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization  : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · simp [hv] at h

theorem req_effects : Effects step := by
  intro s r h
  unfold step at h ⊢
  by_cases hv : ValidPayout s r
  · simp [hv]
  · simp [hv] at h

theorem req_idempotency    : Idempotent step := req_idempotency_aux

theorem req_nonnegative    : NonNegative step := by
  intro s r hnn a ha
  unfold step at ha ⊢
  by_cases hv : ValidPayout s r
  · simp only [hv, ↓reduceIte] at ha ⊢
    unfold expectedBalance shareOf
    by_cases heq : a = r.source
    · subst heq
      obtain ⟨_, _, _, _, hsrcNotIn, _, _, _, hle, _⟩ := hv
      have hnone : indexOf? r.recipients r.source = none :=
        indexOf?_eq_none (by simpa using hsrcNotIn)
      simp [hnone]
      omega
    · simp [heq]
      have hbal : 0 ≤ s.balance a := hnn a ha
      have hshare : 0 ≤ ((match indexOf? r.recipients a with | some i => fairShare r.amount r.recipients.length i | none => 0 : Nat) : Int) :=
        Int.ofNat_nonneg _
      omega
  · simp only [hv, ↓reduceIte] at ha ⊢
    exact hnn a ha

theorem req_fair_shares    : FairShares step := sorry

theorem req_conservation   : Conserves step := sorry

end Payout
