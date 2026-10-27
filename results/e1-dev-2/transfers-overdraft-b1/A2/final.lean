import Transfer.Spec
import Transfer.Lemmas
namespace Transfer
/-- Admission check for a transfer request. -/
def admissible (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧
  0 < r.amount ∧
  r.source ≠ r.target ∧
  r.source ∈ s.accounts ∧
  r.target ∈ s.accounts ∧
  s.auth r.requester r.source = true ∧
  -(s.limit r.source : Int) ≤ s.balance r.source - r.amount ∧
  r.txId ∉ s.applied

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (admissible s r) := by
  unfold admissible; infer_instance

def step : Impl := fun s r =>
  if admissible s r then
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_valid_succeeds_test1 : ValidSucceeds step := by
  intro s r h
  have h' : admissible s r := h
  unfold step
  simp [h']

theorem req_limit_negcheck (s : State) (r : Request) (hca : ¬ admissible s r) :
    (step s r).2 = s := by
  simp [step, hca]

theorem req_limit_helper1 (s : State) (r : Request) (hca0 : admissible s r) :
    (step s r).2 =
      ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) := by
  simp [step, hca0]

theorem probe_if_simp (s : State) (r : Request) (a : AccountId) (has : a = r.source) (hne : r.source ≠ r.target)
    (hbal : (step s r).2.balance a =
        s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (if a = r.target then (r.amount : Int) else 0)) :
    (step s r).2.balance a = s.balance a - (r.amount : Int) := by
  have e1 : (if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by simp [has]
  have e2 : (if a = r.target then (r.amount : Int) else 0) = 0 := by
    have hat : ¬ (a = r.target) := by rw [has]; exact hne
    simp [hat]
  rw [e1, e2] at hbal
  omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have h' : admissible s r := h
  unfold step
  simp [h']

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have h' : ¬ admissible s r := h
  unfold step
  simp [h']

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hAdm : admissible s r
  · exact hAdm.2.2.2.2.2.1
  · unfold step at h
    simp [hAdm] at h

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  by_cases hc : admissible s r
  · have hc0 := hc
    obtain ⟨hNodup, hpos, hne, hsrc, htgt, hauth, hlim, hfresh⟩ := hc
    unfold step
    simp only [hc0]
    constructor
    · simp [hne]
    · simp [Ne.symm hne]
  · exfalso
    unfold step at h
    simp [hc] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hc : admissible s r
  · have e : step s r = (Outcome.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by unfold step; simp [hc]
    have e1 : (step s r).2.accounts = s.accounts := by rw [e]
    have e2 : (step s r).2.limit = s.limit := by rw [e]
    have e3 : (step s r).2.auth = s.auth := by rw [e]
    have e4 : ∀ a, (step s r).2.balance a = expectedBalance s r a := by rw [e]; intro a; rfl
    exact ⟨e1, e2, e3, e4⟩
  · exfalso
    unfold step at h
    simp [hc] at h

theorem req_idempotency : Idempotent step := by
  intro s r h
  by_cases hc : admissible s r
  · have happlied : (step s r).2.applied = r.txId :: s.applied := by
      unfold step; simp [hc]
    have hmem : r.txId ∈ (step s r).2.applied := by rw [happlied]; simp
    have hNadm : ¬ admissible (step s r).2 r := fun hA => hA.2.2.2.2.2.2.2 hmem
    refine ⟨fun x => by rw [happlied]; simp, req_invalid_noop _ _ hNadm⟩
  · exfalso
    unfold step at h
    simp [hc] at h

theorem req_limit : LimitRespected step := by
  intro s r hW
  by_cases hca : admissible s r
  · have hca0 := hca
    obtain ⟨hNodup, hpos, hne, hsrc, htgt, hauth, hlim, hfresh⟩ := hca
    have hstep := req_limit_helper1 s r hca0
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have hlimEq : (step s r).2.limit = s.limit := by rw [hstep]
    have hbal : ∀ a, (step s r).2.balance a =
        s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (if a = r.target then (r.amount : Int) else 0) := by
      intro a
      rw [hstep]
    intro a ha
    rw [hacc] at ha
    rw [hlimEq, hbal]
    have hWa := hW a ha
    by_cases has : a = r.source
    · have e1 : (if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by simp [has]
      have hat : ¬ (a = r.target) := by
        intro hcon
        apply hne
        exact has.symm.trans hcon
      have e2 : (if a = r.target then (r.amount : Int) else 0) = 0 := by simp [hat]
      rw [e1, e2]
      rw [has]
      omega
    · have e1 : (if a = r.source then (r.amount : Int) else 0) = 0 := by simp [has]
      by_cases hat : a = r.target
      · have e2 : (if a = r.target then (r.amount : Int) else 0) = (r.amount : Int) := by simp [hat]
        rw [e1, e2]
        have hamt : (0 : Int) ≤ (r.amount : Int) := Int.ofNat_nonneg _
        omega
      · have e2 : (if a = r.target then (r.amount : Int) else 0) = 0 := by simp [hat]
        rw [e1, e2]
        omega
  · have hstep2 : (step s r).2 = s := by simp [step, hca]
    rw [hstep2]
    exact hW

theorem req_conservation : Conserves step := by
  intro s r h
  by_cases hc : admissible s r
  · have hc0 := hc
    obtain ⟨hNodup, hpos, hne, hsrc, htgt, hauth, hlim, hfresh⟩ := hc
    have hstep : step s r = (Outcome.ok, ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State)) := by
      unfold step; simp [hc0]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have hbal : ∀ a, (step s r).2.balance a =
        s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (if a = r.target then (r.amount : Int) else 0) := by
      intro a; rw [hstep]
    unfold total
    rw [hacc]
    have hcongr : sumOver s.accounts (step s r).2.balance
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0)) := by
      apply sumOver_congr
      intro a ha
      exact hbal a
    rw [hcongr]
    have hsplit : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance
          - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
          + sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) := by
      have e1 : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0))
              = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0))
                            + (if a = r.target then (r.amount : Int) else 0)) := by rfl
      rw [e1, sumOver_add, sumOver_sub]
    rw [hsplit]
    have hs : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
      rw [sumOver_ite_eq hNodup r.source (r.amount : Int)]
      simp [hsrc]
    have ht : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) = (r.amount : Int) := by
      rw [sumOver_ite_eq hNodup r.target (r.amount : Int)]
      simp [htgt]
    rw [hs, ht]
    omega
  · exfalso
    unfold step at h
    simp [hc] at h

end Transfer
