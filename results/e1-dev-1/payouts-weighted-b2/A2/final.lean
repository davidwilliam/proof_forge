import WeightedPayout.Spec
import WeightedPayout.Lemmas
namespace WeightedPayout
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
  rw [if_neg h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  unfold step at hok
  by_cases hv : ValidPayout s r
  · exact hv.2.2.2.2.2.2.2.2.2.1
  · simp [hv] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step
      rw [if_pos hv]
    have h1 : (step s r).1 = .ok := by rw [hstep]
    have h2 : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by rw [hstep]
    rw [h2]
    exact ⟨rfl, rfl, fun a => rfl⟩
  · unfold step at hok
    rw [if_neg hv] at hok
    simp at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · exfalso
      unfold step at hok
      rw [if_neg h] at hok
      simp at hok
  have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
    unfold step
    rw [if_pos hv]
  have h2eq : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
    rw [hstep]
  constructor
  · intro x
    rw [h2eq]
    simp
  · have hnot : ¬ ValidPayout (step s r).2 r := by
      rw [h2eq]
      intro hV
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfresh⟩ := hV
      simp at hfresh
    unfold step
    rw [if_neg hnot]

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step; rw [if_pos hv]
    have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by rw [hstep]
    rw [h2] at ha
    simp at ha
    have hbal : 0 ≤ s.balance a := hnn a ha
    have hbal2 : (step s r).2.balance a = expectedBalance s r a := by rw [h2]
    rw [hbal2]
    obtain ⟨_, _, _, _, _, _, hsrc_not, _, _, _, _, _⟩ := hv
    unfold expectedBalance shareOf
    by_cases hsrc : a = r.source
    · subst hsrc
      have hnotin : indexOf? r.recipients r.source = none :=
        indexOf?_eq_none (by simpa using hsrc_not)
      rw [hnotin]
      simp
      omega
    · simp [hsrc]
      have hnn2 : (0:Int) ≤ ((match indexOf? r.recipients a with | some i => weightedShare r.amount r.weights i | none => 0 : Nat) : Int) := by
        exact Int.ofNat_nonneg _
      omega
  · have hstep : step s r = (.rejected, s) := by unfold step; rw [if_neg hv]
    have h2 : (step s r).2 = s := by rw [hstep]
    rw [h2] at ha ⊢
    exact hnn a ha

theorem req_pro_rata : ProRataShares step := by
  intro s r hok i h
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step; rw [if_pos hv]
    have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by rw [hstep]
    have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by rw [h2]
    obtain ⟨_, _, _, _, _, hnodup, hsrc_not, _, hmem, _, _, _⟩ := hv
    have hmem_i : r.recipients[i] ∈ r.recipients := List.getElem_mem h
    have hne : r.recipients[i] ≠ r.source := fun heq => hsrc_not (heq ▸ hmem_i)
    have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by
      simp [hne]
    have hidx : indexOf? r.recipients r.recipients[i] = some i :=
      indexOf?_getElem hnodup i h
    have hshare : shareOf r r.recipients[i] = weightedShare r.amount r.weights i := by
      unfold shareOf; rw [hidx]
    unfold expectedBalance at hbal
    rw [hif] at hbal
    rw [hshare] at hbal
    omega
  · unfold step at hok; rw [if_neg hv] at hok; simp at hok

theorem req_rounding_bound : RoundingBound step := sorry

theorem req_conservation : Conserves step := sorry

end WeightedPayout
