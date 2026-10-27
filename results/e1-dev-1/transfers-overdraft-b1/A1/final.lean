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

theorem mytest1 (s : State) (r : Request) (hok : (step s r).1 = .ok) : True := by
  unfold step at hok
  by_cases hadm : admissible s r
  · simp [hadm] at hok
    trivial
  · simp [hadm] at hok

theorem mytest2 (s : State) (r : Request) (hadm : admissible s r) :
    (step s r).2.balance r.source = s.balance r.source - r.amount := by
  unfold step
  simp [hadm, hadm.2.2.1]

theorem mytest3 (s : State) (r : Request) (hadm : admissible s r) :
    (step s r).2.balance r.target = s.balance r.target + r.amount := by
  unfold step
  simp [hadm, Ne.symm hadm.2.2.1]

theorem mytest4 (s : State) (r : Request) (hok : (step s r).1 = .ok) : admissible s r := by
  unfold step at hok
  by_cases hadm : admissible s r
  · exact hadm
  · simp [hadm] at hok

theorem req_limit_probe : True := by
  have h : ∀ (s : State) (r : Request) (hadm : admissible s r) (a : AccountId),
    ((step s r).2.balance a = s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0)) := by
    intro s r hadm a
    unfold step
    simp [hadm]
  trivial

theorem limit_bal (s : State) (r : Request) (hadm : admissible s r) (a : AccountId) :
    (step s r).2.balance a = s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0) := by
  unfold step
  simp [hadm]

theorem limit_lim (s : State) (r : Request) (hadm : admissible s r) (a : AccountId) :
    (step s r).2.limit a = s.limit a := by
  unfold step
  simp [hadm]

theorem limit_acc (s : State) (r : Request) (hadm : admissible s r) :
    (step s r).2.accounts = s.accounts := by
  unfold step
  simp [hadm]

theorem limit_acc2 (s : State) (r : Request) (h : ¬ admissible s r) :
    (step s r).2 = s := by
  unfold step
  simp [h]

theorem conserv_helper_test : True := by trivial

theorem conserv_probe2 (s : State) (r : Request) (hok : (step s r).1 = .ok) : True := by
  have hadm : admissible s r := mytest4 s r hok
  trivial

theorem conserv_probe3 (s : State) (r : Request) (hok : (step s r).1 = .ok) : True := by
  have hadmC : admissible s r := mytest4 s r hok
  trivial

theorem conserv_aux_keep (s : State) (r : Request) (hok : (step s r).1 = .ok) : total (step s r).2 = total s := by
  have hadm0 : admissible s r := mytest4 s r hok
  have hadmCopy : admissible s r := hadm0
  obtain ⟨hnodupK, hposK, hneK, hsrcmemK, htgtmemK, hauthK, hfloorK, hfreshK⟩ := hadm0
  have haccK : (step s r).2.accounts = s.accounts := limit_acc s r hadmCopy
  have hbalK : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
    intro a
    have h := limit_bal s r hadmCopy a
    unfold expectedBalance
    exact h
  unfold total
  rw [haccK]
  have hcongrK : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (fun a => expectedBalance s r a) :=
    sumOver_congr s.accounts _ _ (fun a _ => hbalK a)
  rw [hcongrK]
  unfold expectedBalance
  have hexpK : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0))
      = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (if a = r.target then (r.amount : Int) else 0)) := rfl
  rw [hexpK, sumOver_add]
  have hsubK : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) :=
    sumOver_sub s.accounts _ _
  rw [hsubK]
  have hsrcK : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodupK r.source (r.amount : Int)
    simp [hsrcmemK] at h
    exact h
  have htgtK : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodupK r.target (r.amount : Int)
    simp [htgtmemK] at h
    exact h
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
  intro s r hok
  unfold step at hok
  by_cases hadm : admissible s r
  · obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hadm
    exact hauth
  · simp [hadm] at hok

theorem req_debit_credit : DebitCredit step := by
  intro s r hok
  have hadm : admissible s r := mytest4 s r hok
  exact ⟨mytest2 s r hadm, mytest3 s r hadm⟩

theorem req_effects : Effects step := by
  intro s r hok
  have hadm : admissible s r := mytest4 s r hok
  unfold step
  simp only [hadm]
  exact ⟨rfl, rfl, rfl, fun a => rfl⟩

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hadm : admissible s r := mytest4 s r hok
  have h2 : (step s r).2 =
    ⟨s.accounts,
     (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
       + (if a = r.target then (r.amount : Int) else 0)),
     s.limit, s.auth, r.txId :: s.applied⟩ := by
    unfold step
    simp [hadm]
  rw [h2]
  constructor
  · intro x
    simp
  · have hnot : ¬ admissible
      ⟨s.accounts,
       (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
         + (if a = r.target then (r.amount : Int) else 0)),
       s.limit, s.auth, r.txId :: s.applied⟩ r := by
      intro h
      unfold admissible at h
      simp at h
    unfold step
    simp [hnot]

theorem req_limit : LimitRespected step := by
  intro s r hlim a ha
  by_cases hadm : admissible s r
  · have hadm' := hadm
    obtain ⟨hnodup, hpos, hne, hsrcmem, htgtmem, hauth, hfloor, hfresh⟩ := hadm
    have hacc : (step s r).2.accounts = s.accounts := limit_acc s r hadm'
    have hlim2 : (step s r).2.limit a = s.limit a := limit_lim s r hadm' a
    have hbal : (step s r).2.balance a = s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0) := limit_bal s r hadm' a
    rw [hacc] at ha
    rw [hlim2, hbal]
    have hprev : -(s.limit a : Int) ≤ s.balance a := hlim a ha
    by_cases hsrc : a = r.source
    · subst hsrc
      simp [hne]
      exact hfloor
    · by_cases htgt : a = r.target
      · subst htgt
        simp [hsrc]
        have h0 : (0 : Int) ≤ (r.amount : Int) := by exact_mod_cast Nat.zero_le _
        omega
      · simp [hsrc, htgt]
        exact hprev
  · have heq : (step s r).2 = s := limit_acc2 s r hadm
    rw [heq]
    have ha2 : a ∈ s.accounts := by
      unfold step at ha
      simp [hadm] at ha
      exact ha
    exact hlim a ha2

theorem req_conservation : Conserves step := by
  intro s r hok
  exact conserv_aux_keep s r hok

end Transfer
