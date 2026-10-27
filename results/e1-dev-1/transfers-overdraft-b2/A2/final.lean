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

theorem req_valid_succeeds_aux : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r h
  unfold step
  have h' : admissible s r := h
  simp only [h', ↓reduceIte]

theorem req_effects_pf : Effects step := by
  unfold Effects
  intro s r h
  by_cases hadm : admissible s r
  · have hstep : step s r = (.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by unfold step; simp [hadm]
    rw [hstep]
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro a
    rfl
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hadm]
    rw [hstep] at h
    simp at h

theorem idem_helper2 : Idempotent step := by
  unfold Idempotent
  intro s r h
  by_cases hadm : admissible s r
  · have hstep : step s r = (.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by unfold step; simp [hadm]
    rw [hstep]
    simp only
    constructor
    · intro x
      simp only [List.mem_cons]
    · have hnot : ¬ admissible { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } r := by
        intro hcon
        unfold admissible at hcon
        obtain ⟨_, _, _, _, _, _, _, hmem⟩ := hcon
        simp at hmem
      have hstep2 : step { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } r =
        (.rejected, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by unfold step; simp [hnot]
      exact hstep2
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hadm]
    rw [hstep] at h
    simp at h

theorem myLimLem2 : True := by
  trivial

theorem myProbe : (1 : Nat) = 1 := by rfl

theorem myLimAux4 : LimitRespected step := by
  unfold LimitRespected WithinLimits
  intro s r hlim a ha
  by_cases hadm : admissible s r
  · have hok : (step s r).1 = .ok := by
      unfold step
      simp [hadm]
    have heff := req_effects_pf s r hok
    obtain ⟨hacc, hlimEq, hauthEq, hbal⟩ := heff
    have haS : a ∈ s.accounts := by
      rw [← hacc]
      exact ha
    have hbase := hlim a haS
    have hbalA := hbal a
    unfold expectedBalance at hbalA
    have hlimA : (step s r).2.limit a = s.limit a := by
      rw [hlimEq]
    rw [hlimA, hbalA]
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hsrcLim, hfresh⟩ := hadm
    by_cases hs : a = r.source
    · subst hs
      have e1 : (if r.source = r.source then (r.amount : Int) else 0) = (r.amount : Int) :=
        if_pos rfl
      have e2 : (if r.source = r.target then (r.amount : Int) else 0) = 0 :=
        if_neg hne
      rw [e1, e2]
      omega
    · have e1 : (if a = r.source then (r.amount : Int) else 0) = 0 :=
        if_neg hs
      rw [e1]
      by_cases ht : a = r.target
      · subst ht
        have e2 : (if r.target = r.target then (r.amount : Int) else 0) = (r.amount : Int) :=
          if_pos rfl
        rw [e2]
        omega
      · have e2 : (if a = r.target then (r.amount : Int) else 0) = 0 :=
          if_neg ht
        rw [e2]
        omega
  · have hrej : step s r = (.rejected, s) := by
      unfold step
      simp [hadm]
    have h2eq : (step s r).2 = s := by
      rw [hrej]
    rw [h2eq] at ha ⊢
    exact hlim a ha

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r h
  unfold step
  have h' : admissible s r := h
  simp only [h', ↓reduceIte]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r h
  unfold step
  have h' : ¬ admissible s r := h
  rw [if_neg h']

theorem req_authorization : AuthorizedOnly step := by
  unfold AuthorizedOnly step
  intro s r h
  by_cases hadm : admissible s r
  · simp only [hadm, ↓reduceIte] at h
    exact (hadm.2.2.2.2.2.1)
  · simp only [hadm, ↓reduceIte] at h
    contradiction

theorem req_debit_credit : DebitCredit step := by
  unfold DebitCredit
  intro s r h
  by_cases hadm : admissible s r
  · have hstep : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by unfold step; simp [hadm]
    rw [hstep]
    have hne : r.source ≠ r.target := hadm.2.2.1
    constructor
    · simp only [hne, ↓reduceIte]; omega
    · have hts : ¬ (r.target = r.source) := fun heq => hne heq.symm
      simp only [hts, ↓reduceIte]
      omega
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hadm]
    rw [hstep] at h
    simp at h

theorem req_effects : Effects step := by
  unfold Effects
  intro s r h
  by_cases hadm : admissible s r
  · have hstep : step s r = (.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by unfold step; simp [hadm]
    rw [hstep]
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro a
    rfl
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hadm]
    rw [hstep] at h
    simp at h

theorem req_idempotency : Idempotent step := idem_helper2

theorem req_limit : LimitRespected step := myLimAux4

theorem req_conservation : Conserves step := by
  unfold Conserves total
  intro s r hok
  by_cases hadm : admissible s r
  · have heff := req_effects s r hok
    obtain ⟨hacc, hlimEq, hauthEq, hbal⟩ := heff
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hsrcLim, hfresh⟩ := hadm
    have htot2 : sumOver (step s r).2.accounts (step s r).2.balance
        = sumOver s.accounts (fun a => expectedBalance s r a) := by
      rw [hacc]
      apply sumOver_congr
      intro a _
      exact hbal a
    rw [htot2]
    show sumOver s.accounts (fun a => expectedBalance s r a) = _
    unfold expectedBalance
    have hG : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
        = (r.amount : Int) := by
      have hlem := sumOver_ite_eq hnodup r.source (r.amount : Int)
      simp [hsrc] at hlem
      exact hlem
    have hH : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0)
        = (r.amount : Int) := by
      have hlem := sumOver_ite_eq hnodup r.target (r.amount : Int)
      simp [htgt] at hlem
      exact hlem
    have hdecomp : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
          + sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) := by
      have h1 : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0))
                = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0))
                          + (if a = r.target then (r.amount : Int) else 0)) := rfl
      rw [h1, sumOver_add]
      congr 1
      exact sumOver_sub s.accounts s.balance _
    rw [hdecomp, hG, hH]
    omega
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hadm]
    rw [hstep] at hok
    simp at hok

end Transfer
