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

theorem req_idempotency_aux_test : True := trivial
#check @step

theorem req_idempotency3 : Idempotent step := by
  intro s r hok
  by_cases hadm : admissible s r
  · have h2eq : (step s r).2 =
        ({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State) := by simp [step, hadm]
    rw [h2eq]
    constructor
    · intro x
      simp
    · have hnadm : ¬ admissible
        ({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State) r := by
        intro hcon
        exact hcon.2.2.2.2.2.2.2 (by simp)
      have hstep2 : step ({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State) r =
          (.rejected, { s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied }) := by simp [step, hnadm]
      exact hstep2
  · have hre : (step s r).1 = .rejected := by simp [step, hadm]
    rw [hre] at hok
    cases hok

theorem myTestLimitHelper : True := trivial
#check @step
#check @admissible

theorem limitSimpTest (s : State) (r : Request) (hadm : admissible s r) :
    (step s r).2.accounts = s.accounts := by
  simp only [step, hadm, ↓reduceIte]

theorem myNonnegTest (n : Nat) : (0 : Int) ≤ (n : Int) := by
  omega

theorem myLimitPf4 : LimitRespected step := by
  intro s r hlim a ha
  by_cases hA : admissible s r
  · have hacc : (step s r).2.accounts = s.accounts := by simp [step, hA]
    have hbal : (step s r).2.balance a = expectedBalance s r a := by simp [step, hA, expectedBalance]
    have hlimEq : (step s r).2.limit = s.limit := by simp [step, hA]
    have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hlimsrc, hfresh⟩ := hA
    rw [hbal, hlimEq]
    unfold expectedBalance
    by_cases hs : a = r.source
    · subst hs
      have hifT : (if r.source = r.target then (r.amount : Int) else 0) = 0 := by simp [hne]
      simp [hifT] at hlimsrc ⊢
      omega
    · by_cases ht : a = r.target
      · subst ht
        have hneS : r.target ≠ r.source := Ne.symm hne
        have hifS : (if r.target = r.source then (r.amount : Int) else 0) = 0 := by simp [hneS]
        simp [hifS]
        have hold := hlim r.target htgt
        have hnn : (0 : Int) ≤ (r.amount : Int) := by omega
        omega
      · have e1 : (if a = r.source then (r.amount : Int) else 0) = 0 := by simp [hs]
        have e2 : (if a = r.target then (r.amount : Int) else 0) = 0 := by simp [ht]
        rw [e1, e2]
        have heq : s.balance a - (0 : Int) + (0 : Int) = s.balance a := by omega
        rw [heq]
        exact hlim a ha'
  · have hst : (step s r).2 = s := by simp [step, hA]
    have ha' : a ∈ s.accounts := by rw [← hst]; exact ha
    rw [hst]
    exact hlim a ha'

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have h2 : admissible s r := h
  simp only [step, h2, ↓reduceIte]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have h2 : ¬ admissible s r := h
  simp only [step, h2, ↓reduceIte]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hadm : admissible s r
  · exact hadm.2.2.2.2.2.1
  · have hrej : (step s r).1 = .rejected := by simp [step, hadm]
    rw [hrej] at h
    cases h

theorem req_debit_credit : DebitCredit step := by
  intro s r hok
  by_cases hadm : admissible s r
  · simp only [step, hadm, ↓reduceIte] at hok ⊢
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hlim, hfresh⟩ := hadm
    constructor
    · simp [hne]
    · simp [Ne.symm hne]
  · have hre : (step s r).1 = .rejected := by simp [step, hadm]
    rw [hre] at hok
    cases hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hadm : admissible s r
  · simp only [step, hadm, ↓reduceIte] at hok ⊢
    refine ⟨trivial, trivial, trivial, ?_⟩
    intro a
    rfl
  · have hre : (step s r).1 = .rejected := by simp [step, hadm]
    rw [hre] at hok
    cases hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hadm : admissible s r
  · have h2eq : (step s r).2 =
        ({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State) := by simp [step, hadm]
    rw [h2eq]
    constructor
    · intro x
      simp
    · have hnadm : ¬ admissible
        ({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State) r := by
        intro hcon
        exact hcon.2.2.2.2.2.2.2 (by simp)
      have hstep2 : step ({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State) r =
          (.rejected, { s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied }) := by simp [step, hnadm]
      exact hstep2
  · have hre : (step s r).1 = .rejected := by simp [step, hadm]
    rw [hre] at hok
    cases hok

theorem req_limit : LimitRespected step := by
  intro s r hlim a ha
  by_cases hA : admissible s r
  · have hacc : (step s r).2.accounts = s.accounts := by simp [step, hA]
    have hbal : (step s r).2.balance a = expectedBalance s r a := by simp [step, hA, expectedBalance]
    have hlimEq : (step s r).2.limit = s.limit := by simp [step, hA]
    have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hlimsrc, hfresh⟩ := hA
    rw [hbal, hlimEq]
    unfold expectedBalance
    by_cases hs : a = r.source
    · subst hs
      have hifT : (if r.source = r.target then (r.amount : Int) else 0) = 0 := by simp [hne]
      simp [hifT] at hlimsrc ⊢
      omega
    · by_cases ht : a = r.target
      · subst ht
        have hneS : r.target ≠ r.source := Ne.symm hne
        have hifS : (if r.target = r.source then (r.amount : Int) else 0) = 0 := by simp [hneS]
        simp [hifS]
        have hold := hlim r.target htgt
        have hnn : (0 : Int) ≤ (r.amount : Int) := by omega
        omega
      · have e1 : (if a = r.source then (r.amount : Int) else 0) = 0 := by simp [hs]
        have e2 : (if a = r.target then (r.amount : Int) else 0) = 0 := by simp [ht]
        rw [e1, e2]
        have heq : s.balance a - (0 : Int) + (0 : Int) = s.balance a := by omega
        rw [heq]
        exact hlim a ha'
  · have hst : (step s r).2 = s := by simp [step, hA]
    have ha' : a ∈ s.accounts := by rw [← hst]; exact ha
    rw [hst]
    exact hlim a ha'

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases hadm : admissible s r
  · have hacc : (step s r).2.accounts = s.accounts := by simp [step, hadm]
    have hbal : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
      intro a; simp [step, hadm, expectedBalance]
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hlimsrc, hfresh⟩ := hadm
    unfold total
    rw [hacc]
    have hcongr : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (fun a => expectedBalance s r a) := by
      apply sumOver_congr
      intro a ha
      exact hbal a
    rw [hcongr]
    unfold expectedBalance
    -- rewrite expectedBalance as (bal - srcInd) + tgtInd to apply add/sub lemmas
    have hrewrite : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0))
        = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (if a = r.target then (r.amount : Int) else 0)) := rfl
    -- use lemmas
    have h1 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - (r.amount : Int) + (r.amount : Int) := by
      rw [hrewrite, sumOver_add]
      have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
          = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) := by
        exact sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
      rw [hsub]
      have hsrc_sum : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
        have h := sumOver_ite_eq hnodup r.source (r.amount : Int)
        simp [hsrc] at h
        exact h
      have htgt_sum : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) = (r.amount : Int) := by
        have h := sumOver_ite_eq hnodup r.target (r.amount : Int)
        simp [htgt] at h
        exact h
      rw [hsrc_sum, htgt_sum]
    rw [h1]
    omega
  · have hre : (step s r).1 = .rejected := by simp [step, hadm]
    rw [hre] at hok
    cases hok

end Transfer
