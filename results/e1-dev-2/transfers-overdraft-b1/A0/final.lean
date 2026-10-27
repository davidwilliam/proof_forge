import Transfer.Spec
import Transfer.Lemmas
namespace Transfer

def admissible (s : State) (r : Request) : Prop :=
  ValidTransfer s r

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (admissible s r) := by
  unfold admissible ValidTransfer
  infer_instance

def step : Impl := fun s r =>
  if admissible s r then
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem step_ok_implies_admissible (s : State) (r : Request) (h : (step s r).1 = .ok) : admissible s r := by
  by_cases ha : admissible s r
  · exact ha
  · have h2 : (step s r).1 = .rejected := by
      unfold step
      simp [ha]
    rw [h2] at h
    exact absurd h (by decide)

theorem step_snd_eq_of_ok (s : State) (r : Request) (ha : admissible s r) :
    (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } : State) := by
  unfold step
  simp [ha]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have ha : admissible s r := h
  unfold step
  simp [ha]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hn : ¬ admissible s r := h
  unfold step
  simp [hn]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  have ha : admissible s r := step_ok_implies_admissible s r h
  have hv : ValidTransfer s r := ha
  unfold ValidTransfer at hv
  obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hv
  exact hauth

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  have ha : admissible s r := step_ok_implies_admissible s r h
  have hv : ValidTransfer s r := ha
  unfold ValidTransfer at hv
  obtain ⟨_, _, hne, _, _, _, _, _⟩ := hv
  have h2 := step_snd_eq_of_ok s r ha
  constructor
  · rw [h2]
    have hst : ¬ (r.source = r.target) := hne
    simp [hst]
  · rw [h2]
    have hts : ¬ (r.target = r.source) := fun heq => hne heq.symm
    simp [hts]

theorem req_effects : Effects step := by
  intro s r h
  have ha : admissible s r := step_ok_implies_admissible s r h
  have h2 := step_snd_eq_of_ok s r ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h2]
  · rw [h2]
  · rw [h2]
  · intro a
    rw [h2]
    rfl

theorem req_idempotency : Idempotent step := by
  intro s r h
  have ha : admissible s r := step_ok_implies_admissible s r h
  have h2 := step_snd_eq_of_ok s r ha
  constructor
  · intro x
    rw [h2]
    simp
  · have hn : ¬ admissible ((step s r).2) r := by
      rw [h2]
      intro hc
      have hvc : ValidTransfer ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) r := hc
      unfold ValidTransfer at hvc
      obtain ⟨_, _, _, _, _, _, _, hnotin⟩ := hvc
      simp at hnotin
    have hEq : step ((step s r).2) r = (.rejected, (step s r).2) :=
      if_neg hn
    exact hEq

theorem req_limit : LimitRespected step := by
  intro s r hs
  unfold WithinLimits at hs ⊢
  by_cases ha : admissible s r
  · have hv : ValidTransfer s r := ha
    unfold ValidTransfer at hv
    obtain ⟨_, _, hne, _, _, _, hlim, _⟩ := hv
    have hts : r.target ≠ r.source := Ne.symm hne
    have h2 := step_snd_eq_of_ok s r ha
    rw [h2]
    intro a hamem
    have hamem2 : a ∈ s.accounts := hamem
    have hs_a := hs a hamem2
    show -(s.limit a : Int) ≤ s.balance a - (if a = r.source then (r.amount : Int) else 0)
      + (if a = r.target then (r.amount : Int) else 0)
    by_cases hs_eq : a = r.source
    · subst hs_eq
      have hne2 : ¬ (r.source = r.target) := hne
      simp [hne2]
      exact hlim
    · by_cases ht_eq : a = r.target
      · subst ht_eq
        simp [hs_eq, hts]
        omega
      · simp [hs_eq, ht_eq]
        exact hs_a
  · have h2 : (step s r).2 = s := by
      unfold step
      simp [ha]
    rw [h2]
    exact hs

theorem req_conservation : Conserves step := by
  intro s r h
  have ha : admissible s r := step_ok_implies_admissible s r h
  have hv : ValidTransfer s r := ha
  unfold ValidTransfer at hv
  obtain ⟨hnodup, _, _, hsrc, htgt, _, _, _⟩ := hv
  have h2 := step_snd_eq_of_ok s r ha
  have heq1 : total (step s r).2
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a = r.target then (r.amount : Int) else 0)) := by
    rw [h2]
    rfl
  have heq2 : total s = sumOver s.accounts s.balance := rfl
  rw [heq1, heq2]
  have hg_src : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by
    rw [sumOver_ite_eq hnodup]
    simp [hsrc]
  have hg_tgt : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0)
      = (r.amount : Int) := by
    rw [sumOver_ite_eq hnodup]
    simp [htgt]
  have hA : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
      + (if a = r.target then (r.amount : Int) else 0))
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        + sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) :=
    sumOver_add _ _ _
  have hS : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance
        - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) :=
    sumOver_sub _ _ _
  rw [hA, hS, hg_src, hg_tgt]
  omega

end Transfer
