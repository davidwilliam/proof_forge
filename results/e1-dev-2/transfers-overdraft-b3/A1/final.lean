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

theorem auth_helper_test : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hadm : admissible s r
  · obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hadm
    exact hauth
  · simp [hadm] at h

theorem req_debit_credit_aux : DebitCredit step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hs : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by unfold step; simp [hadm]
    rw [hs]
    simp only
    obtain ⟨_, _, hne, _, _, _, _, _⟩ := hadm
    constructor
    · simp [hne]
    · have h1 : r.target ≠ r.source := fun heq => hne heq.symm
      simp [h1]
  · have hs : step s r = (.rejected, s) := by unfold step; simp [hadm]
    rw [hs] at h
    simp at h

theorem req_idempotency_aux2 : Idempotent step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hstep : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by unfold step; simp [hadm]
    have h2 : (step s r).2 = { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } := by rw [hstep]
    constructor
    · intro x
      rw [h2]
      simp
    · have hmem : r.txId ∈ ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State).applied := by simp
      have hnadm2 : ¬ admissible ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) r := by
        intro hcon
        obtain ⟨_, _, _, _, _, _, _, hfresh⟩ := hcon
        exact hfresh hmem
      have hstep2 : step ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) r
          = (.rejected, ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State)) := by
        unfold step
        simp [hnadm2]
      rw [h2]
      exact hstep2
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hadm]
    rw [hstep] at h
    simp at h

theorem req_idempotency_helper_use : True := trivial

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have h' : admissible s r := h
  unfold step
  simp [h']

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  have h' : ¬ admissible s r := h
  unfold step
  simp [h']

theorem req_authorization  : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hadm : admissible s r
  · obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hadm
    exact hauth
  · simp [hadm] at h

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hs : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by unfold step; simp [hadm]
    rw [hs]
    simp only
    obtain ⟨_, _, hne, _, _, _, _, _⟩ := hadm
    constructor
    · simp [hne]
    · have h1 : r.target ≠ r.source := fun heq => hne heq.symm
      simp [h1]
  · have hs : step s r = (.rejected, s) := by unfold step; simp [hadm]
    rw [hs] at h
    simp at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hs : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by unfold step; simp [hadm]
    have e2 : (step s r).2 = { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } := by rw [hs]
    rw [e2]
    exact ⟨rfl, rfl, rfl, fun a => rfl⟩
  · have hs : step s r = (.rejected, s) := by unfold step; simp [hadm]
    rw [hs] at h
    simp at h

theorem req_idempotency    : Idempotent step := req_idempotency_aux2

theorem req_limit : LimitRespected step := by
  intro s r hwl a ha
  have ha' : a ∈ s.accounts := by
    by_cases hadm : admissible s r
    · have hacc : (step s r).2.accounts = s.accounts := by
        unfold step; simp [hadm]
      rw [hacc] at ha
      exact ha
    · have h2 : (step s r).2 = s := by unfold step; simp [hadm]
      rw [h2] at ha
      exact ha
  have hw : -(s.limit a : Int) ≤ s.balance a := hwl a ha'
  by_cases hadm : admissible s r
  · have h2 : (step s r).2 = (({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State)) := by
      unfold step; simp [hadm]
    rw [h2] at ha ⊢
    simp at ha ⊢
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hfloor, hfresh⟩ := hadm
    by_cases has : a = r.source
    · subst has
      simp [hne] at ⊢
      exact hfloor
    · by_cases hat : a = r.target
      · subst hat
        simp [has] at ⊢
        omega
      · simp [has, hat] at ⊢
        exact hw
  · have h2 : (step s r).2 = s := by unfold step; simp [hadm]
    rw [h2] at ha ⊢
    simp at ha ⊢
    exact hw

theorem req_conservation : Conserves step := by
  intro s r h
  by_cases hadm : admissible s r
  · have h2 : (step s r).2 = (({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State)) := by
      unfold step; simp [hadm]
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hfloor, hfresh⟩ := hadm
    have hbal : ∀ a ∈ s.accounts,
        (step s r).2.balance a = expectedBalance s r a := by
      intro a ha
      rw [h2]
      rfl
    -- total equality via sum lemmas
    unfold total
    rw [h2]
    simp only
    -- goal: sumOver s.accounts (fun a => balance a - .. + ..) = sumOver s.accounts (balance)
    have hcongr : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance := by
      have h1 : ∀ a ∈ s.accounts, (s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0))
          = (s.balance a + ((if a = r.target then (r.amount : Int) else 0) - (if a = r.source then (r.amount : Int) else 0))) := by
        intro a ha; omega
      rw [sumOver_congr s.accounts _ _ h1]
      rw [sumOver_add]
      have hsrc_sum : sumOver s.accounts (fun a => (if a = r.target then (r.amount : Int) else 0) - (if a = r.source then (r.amount : Int) else 0))
          = 0 := by
        rw [sumOver_sub]
        rw [sumOver_ite_eq hnodup r.target (r.amount : Int)]
        rw [sumOver_ite_eq hnodup r.source (r.amount : Int)]
        simp [hsrc, htgt]
      omega
    exact hcongr
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hadm]
    rw [hstep] at h
    simp at h

end Transfer
