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

theorem admissible_iff_valid (s : State) (r : Request) :
    admissible s r ↔ ValidTransfer s r := by
  unfold admissible ValidTransfer
  rfl

theorem step_ok_eq (s : State) (r : Request) (h : admissible s r) :
    step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by
  unfold step
  simp [h]

theorem step_rej_eq (s : State) (r : Request) (h : ¬ admissible s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [h]

theorem admiss_of_ok (s : State) (r : Request) (h : (step s r).1 = .ok) :
    admissible s r := by
  by_cases hA : admissible s r
  · exact hA
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hA]
    rw [hstep] at h
    simp at h

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r hV
  have hA : admissible s r := (admissible_iff_valid s r).mpr hV
  have hstep := step_ok_eq s r hA
  simp [hstep]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r hV
  have hA : ¬ admissible s r := fun ha => hV ((admissible_iff_valid s r).mp ha)
  exact step_rej_eq s r hA

theorem req_authorization : AuthorizedOnly step := by
  unfold AuthorizedOnly
  intro s r hOk
  have hA := admiss_of_ok s r hOk
  have hV : ValidTransfer s r := (admissible_iff_valid s r).mp hA
  unfold ValidTransfer at hV
  obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hV
  exact hauth

theorem req_debit_credit : DebitCredit step := by
  unfold DebitCredit
  intro s r hOk
  have hA := admiss_of_ok s r hOk
  have hV : ValidTransfer s r := (admissible_iff_valid s r).mp hA
  unfold ValidTransfer at hV
  obtain ⟨_, _, hNe, _, _, _, _, _⟩ := hV
  have hstep := step_ok_eq s r hA
  constructor
  · have h1 : (step s r).2.balance r.source = s.balance r.source - (r.amount : Int) := by
      rw [hstep]
      simp [hNe]
    exact h1
  · have h2 : (step s r).2.balance r.target = s.balance r.target + (r.amount : Int) := by
      rw [hstep]
      simp [Ne.symm hNe]
    exact h2

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hOk
  have hA := admiss_of_ok s r hOk
  have hstep := step_ok_eq s r hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hstep]
  · rw [hstep]
  · rw [hstep]
  · intro a
    rw [hstep]
    rfl

theorem req_idempotency : Idempotent step := by
  unfold Idempotent
  intro s r hOk
  have hA := admiss_of_ok s r hOk
  have hstep := step_ok_eq s r hA
  have hsnd : (step s r).2 = { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } := by rw [hstep]
  constructor
  · intro x
    rw [hsnd]
    simp
  · have hNA : ¬ admissible (step s r).2 r := by
      intro hA'
      have hV' : ValidTransfer (step s r).2 r := (admissible_iff_valid _ _).mp hA'
      unfold ValidTransfer at hV'
      obtain ⟨_, _, _, _, _, _, _, hFresh⟩ := hV'
      have hMem : r.txId ∈ (step s r).2.applied := by rw [hsnd]; simp
      exact hFresh hMem
    have hrej := step_rej_eq (step s r).2 r hNA
    exact hrej

theorem req_limit : LimitRespected step := by
  unfold LimitRespected
  intro s r hLim
  by_cases hA : admissible s r
  · have hV : ValidTransfer s r := (admissible_iff_valid s r).mp hA
    unfold ValidTransfer at hV
    obtain ⟨_, hPos, hNe, _, _, _, hLimCond, _⟩ := hV
    have hstep2 : (step s r).2 = { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } := by
      have h := step_ok_eq s r hA
      simp [h]
    have hAcc : (step s r).2.accounts = s.accounts := by rw [hstep2]
    have hLimEq : (step s r).2.limit = s.limit := by rw [hstep2]
    have hBal : ∀ a, (step s r).2.balance a =
        s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (if a = r.target then (r.amount : Int) else 0) := by
      intro a; rw [hstep2]
    unfold WithinLimits at hLim ⊢
    intro a ha
    rw [hAcc] at ha
    have hOld : -(s.limit a : Int) ≤ s.balance a := hLim a ha
    rw [hLimEq, hBal a]
    by_cases h1 : a = r.source
    · subst h1
      have hST : ¬ (r.source = r.target) := hNe
      simp [hST]
      exact hLimCond
    · by_cases h2 : a = r.target
      · subst h2
        simp [h1]
        omega
      · simp [h1, h2]
        exact hOld
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hA]
    have h2 : (step s r).2 = s := by simp [hstep]
    rw [h2]
    exact hLim

theorem req_conservation : Conserves step := by
  unfold Conserves
  intro s r hOk
  have hA := admiss_of_ok s r hOk
  have hV : ValidTransfer s r := (admissible_iff_valid s r).mp hA
  unfold ValidTransfer at hV
  obtain ⟨hNodup, _, _, hSrcMem, hTgtMem, _, _, _⟩ := hV
  have hstep2' : (step s r).2 = { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } := by
    have h := step_ok_eq s r hA
    simp [h]
  have hAcc : (step s r).2.accounts = s.accounts := by rw [hstep2']
  have hBalEq : ∀ a, (step s r).2.balance a =
      s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a = r.target then (r.amount : Int) else 0) := by
    intro a; rw [hstep2']
  have hSrcSum : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by
    have h := sumOver_ite_eq hNodup r.source ((r.amount : Int))
    simp [hSrcMem] at h
    exact h
  have hTgtSum : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0)
      = (r.amount : Int) := by
    have h := sumOver_ite_eq hNodup r.target ((r.amount : Int))
    simp [hTgtMem] at h
    exact h
  unfold total
  rw [hAcc]
  calc sumOver s.accounts (step s r).2.balance
      _ = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (if a = r.target then (r.amount : Int) else 0)) :=
        sumOver_congr _ _ _ (fun a _ => hBalEq a)
      _ = sumOver s.accounts s.balance := by
        rw [sumOver_add, sumOver_sub, hSrcSum, hTgtSum]
        omega

end Transfer
