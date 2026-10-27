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

theorem req_debit_credit_probe : DebitCredit step := by
  intro s r h
  have hadm : admissible s r := by
    by_cases h2 : admissible s r
    · exact h2
    · unfold step at h; simp [h2] at h
  have hne : r.source ≠ r.target := hadm.2.2.1
  have hne2 : r.target ≠ r.source := fun heq => hne heq.symm
  unfold step
  simp only [hadm, ↓reduceIte]
  simp only [hne, hne2, ↓reduceIte]
  constructor
  · omega
  · omega

theorem req_debit_credit_aux2 : DebitCredit step := by
  intro s r h
  have hadm : admissible s r := by
    by_cases h2 : admissible s r
    · exact h2
    · unfold step at h; simp [h2] at h
  have hne : r.source ≠ r.target := hadm.2.2.1
  have hne2 : r.target ≠ r.source := fun heq => hne heq.symm
  unfold step
  simp only [hadm, ↓reduceIte]
  simp only [hne, hne2, ↓reduceIte]
  constructor
  · omega
  · omega

theorem req_idempotency_aux3 : Idempotent step := by
  intro s r h
  have hadm : admissible s r := by
    by_cases h2 : admissible s r
    · exact h2
    · unfold step at h; simp [h2] at h
  have h2eq : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } : State) := by
    unfold step; simp [hadm]
  have happ : (step s r).2.applied = r.txId :: s.applied := by rw [h2eq]
  have hnot : ¬ admissible ((step s r).2) r := by
    rw [h2eq]
    intro ha
    have hmem : r.txId ∉ r.txId :: s.applied := ha.2.2.2.2.2.2.2
    simp at hmem
  have hrejm : ∀ s' : State, ¬ admissible s' r → step s' r = (.rejected, s') := by
    intro s' hn
    unfold step
    simp [hn]
  exact ⟨by intro x; rw [happ]; simp, hrejm _ hnot⟩

theorem conservation_helper2 (l : List Nat) (bal : Nat → Int) (src tgt : Nat) (amt : Int)
    (hnodup : l.Nodup) (hsrc : src ∈ l) (htgt : tgt ∈ l) :
    sumOver l (fun a => bal a - (if a = src then amt else 0) + (if a = tgt then amt else 0))
      = sumOver l bal := by
  have h1 : (fun a : Nat => bal a - (if a = src then amt else 0) + (if a = tgt then amt else 0))
      = (fun a => (bal a - (if a = src then amt else 0)) + (if a = tgt then amt else 0)) := rfl
  rw [h1, sumOver_add, sumOver_sub]
  have hs : sumOver l (fun a : Nat => if a = src then amt else 0) = amt := by
    rw [sumOver_ite_eq hnodup src amt, if_pos hsrc]
  have ht : sumOver l (fun a : Nat => if a = tgt then amt else 0) = amt := by
    rw [sumOver_ite_eq hnodup tgt amt, if_pos htgt]
  rw [hs, ht]
  omega

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

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hadm : admissible s r
  · exact (hadm.2.2.2.2.2.1)
  · simp [hadm] at h

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  have hadm : admissible s r := by
    by_cases h2 : admissible s r
    · exact h2
    · unfold step at h; simp [h2] at h
  have hne : r.source ≠ r.target := hadm.2.2.1
  have hne2 : r.target ≠ r.source := fun heq => hne heq.symm
  unfold step
  simp only [hadm, ↓reduceIte]
  simp only [hne, hne2, ↓reduceIte]
  constructor
  · omega
  · omega

theorem req_effects : Effects step := by
  intro s r h
  have hadm : admissible s r := by
    by_cases h2 : admissible s r
    · exact h2
    · unfold step at h; simp [h2] at h
  have hstep : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by
    unfold step; simp [hadm]
  rw [hstep]
  exact ⟨rfl, rfl, rfl, fun a => rfl⟩

theorem req_idempotency : Idempotent step := by
  intro s r h
  have hadm : admissible s r := by
    by_cases h2 : admissible s r
    · exact h2
    · unfold step at h; simp [h2] at h
  have h2eq : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } : State) := by
    unfold step; simp [hadm]
  have happ : (step s r).2.applied = r.txId :: s.applied := by rw [h2eq]
  have hnot : ¬ admissible ((step s r).2) r := by
    rw [h2eq]
    intro ha
    have hmem : r.txId ∉ r.txId :: s.applied := ha.2.2.2.2.2.2.2
    simp at hmem
  have hrejm : ∀ s' : State, ¬ admissible s' r → step s' r = (.rejected, s') := by
    intro s' hn
    unfold step
    simp [hn]
  exact ⟨by intro x; rw [happ]; simp, hrejm _ hnot⟩

theorem req_limit : LimitRespected step := by
  intro s r hWL a ha
  by_cases hadm : admissible s r
  · have hstep2 : (step s r).2 = ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) := by
      unfold step; simp [hadm]
    rw [hstep2] at ha ⊢
    simp only at ha ⊢
    have ha_mem : a ∈ s.accounts := ha
    have hWL_a : -(s.limit a : Int) ≤ s.balance a := hWL a ha_mem
    have hlim_src : -(s.limit r.source : Int) ≤ s.balance r.source - (r.amount : Int) :=
      hadm.2.2.2.2.2.2.1
    have hne : r.source ≠ r.target := hadm.2.2.1
    have htgt : r.target ∈ s.accounts := hadm.2.2.2.2.1
    by_cases h_as : a = r.source
    · subst h_as
      simp [hne]
      exact hlim_src
    · by_cases h_at : a = r.target
      · subst h_at
        simp [h_as]
        have hWT : -(s.limit r.target : Int) ≤ s.balance r.target := hWL r.target htgt
        have hpos : (0 : Int) ≤ (r.amount : Int) := by exact_mod_cast Nat.zero_le _
        omega
      · simp [h_as, h_at]
        exact hWL_a
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hadm]
    have heq : (step s r).2 = s := by rw [hstep]
    rw [heq] at ha ⊢
    exact hWL a ha

theorem req_conservation : Conserves step := by
  intro s r h
  have hadm : admissible s r := by
    by_cases h2 : admissible s r
    · exact h2
    · unfold step at h; simp [h2] at h
  have hstep2 : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } : State) := by
    unfold step; simp [hadm]
  unfold total
  rw [hstep2]
  simp only
  exact conservation_helper2 s.accounts s.balance r.source r.target (r.amount : Int)
    hadm.1 hadm.2.2.2.1 hadm.2.2.2.2.1

end Transfer
