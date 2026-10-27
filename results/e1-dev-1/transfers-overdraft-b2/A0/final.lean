import Transfer.Spec
import Transfer.Lemmas
namespace Transfer

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
  unfold admissible
  infer_instance

def step : Impl := fun s r =>
  if admissible s r then
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem step_ok_imp_adm (s : State) (r : Request) (h : (step s r).1 = .ok) :
    admissible s r := by
  by_cases hc : admissible s r
  · exact hc
  · exfalso
    have hre : (step s r).1 = .rejected := by simp [step, hc]
    rw [hre] at h
    have hne2 : Outcome.rejected ≠ .ok := by decide
    exact hne2 h

theorem step_rejected_of_not_adm (s : State) (r : Request) (h : ¬ admissible s r) :
    step s r = (.rejected, s) := by simp [step, h]

theorem step_ok_eq (s : State) (r : Request) (h : admissible s r) :
    step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by simp [step, h]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hadm : admissible s r := h
  simp [step, hadm]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hna : ¬ admissible s r := h
  simp [step, hna]

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  have hadm := step_ok_imp_adm s r hok
  exact hadm.2.2.2.2.2.1

theorem req_debit_credit : DebitCredit step := by
  intro s r hok
  have hadm := step_ok_imp_adm s r hok
  have hne : r.source ≠ r.target := hadm.2.2.1
  have hne' : r.target ≠ r.source := Ne.symm hne
  constructor
  · simp [step, hadm, hne]
  · simp [step, hadm, hne']

theorem req_effects : Effects step := by
  intro s r hok
  have hadm := step_ok_imp_adm s r hok
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [step, hadm]
  · simp [step, hadm]
  · simp [step, hadm]
  · intro a
    simp [step, hadm, expectedBalance]

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hadm := step_ok_imp_adm s r hok
  have hst := step_ok_eq s r hadm
  have hap : (step s r).2.applied = r.txId :: s.applied := by simp [step, hadm]
  have hmem : r.txId ∈ (step s r).2.applied := by simp [hap]
  have hnadm : ¬ admissible (step s r).2 r := by
    intro hh
    exact hh.2.2.2.2.2.2.2 hmem
  constructor
  · intro x
    simp [hap]
  · exact step_rejected_of_not_adm _ _ hnadm

theorem req_limit : LimitRespected step := by
  intro s r hw
  unfold WithinLimits at hw ⊢
  by_cases h : admissible s r
  · have hne : r.source ≠ r.target := h.2.2.1
    have hne' : r.target ≠ r.source := Ne.symm hne
    have hlimsrc : -(s.limit r.source : Int) ≤ s.balance r.source - r.amount :=
      h.2.2.2.2.2.2.1
    have hacc : (step s r).2.accounts = s.accounts := by simp [step, h]
    have hlim_eq : ∀ a, (step s r).2.limit a = s.limit a := by
      intro a
      simp [step, h]
    have hbal_eq : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
      intro a
      simp [step, h, expectedBalance]
    intro a ha
    have ha2 : a ∈ s.accounts := by simp [hacc] at ha; exact ha
    have hwa := hw a ha2
    simp [hlim_eq a, hbal_eq a]
    unfold expectedBalance
    by_cases hs : a = r.source
    · subst hs
      simp [hne]
      exact hlimsrc
    · by_cases ht : a = r.target
      · subst ht
        simp [hs]
        omega
      · simp [hs, ht]
        exact hwa
  · have hst : step s r = (.rejected, s) := step_rejected_of_not_adm s r h
    have hacc : (step s r).2.accounts = s.accounts := by simp [step, h]
    have hlim_eq : ∀ a, (step s r).2.limit a = s.limit a := by
      intro a
      simp [step, h]
    have hbal_eq : ∀ a, (step s r).2.balance a = s.balance a := by
      intro a
      simp [step, h]
    intro a ha
    have ha2 : a ∈ s.accounts := by simp [hacc] at ha; exact ha
    have hwa := hw a ha2
    simp [hlim_eq a, hbal_eq a]
    exact hwa

theorem req_conservation : Conserves step := by
  intro s r hok
  have hadm := step_ok_imp_adm s r hok
  have hnodup : s.accounts.Nodup := hadm.1
  have hsrc : r.source ∈ s.accounts := hadm.2.2.2.1
  have htgt : r.target ∈ s.accounts := hadm.2.2.2.2.1
  have hst := step_ok_eq s r hadm
  have hacc : (step s r).2.accounts = s.accounts := by simp [step, hadm]
  have hbal : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
    intro a
    simp [step, hadm, expectedBalance]
  show total (step s r).2 = total s
  unfold total
  rw [hacc]
  have hcongr : sumOver s.accounts (step s r).2.balance
      = sumOver s.accounts (fun a => expectedBalance s r a) :=
    sumOver_congr _ _ _ (fun a _ => hbal a)
  rw [hcongr]
  have h_add : sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        + sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) := by
    unfold expectedBalance
    exact sumOver_add _ _ _
  have h_sub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance
        - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) :=
    sumOver_sub _ _ _
  have hs_sum : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by
    simp [sumOver_ite_eq hnodup _ _, hsrc]
  have ht_sum : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0)
      = (r.amount : Int) := by
    simp [sumOver_ite_eq hnodup _ _, htgt]
  rw [h_add, h_sub, hs_sum, ht_sum]
  omega

end Transfer
