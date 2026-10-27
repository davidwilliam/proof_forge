import Transfer.Spec
import Transfer.Lemmas
namespace Transfer

instance instDecidableValidTransfer (s : State) (r : Request) : Decidable (ValidTransfer s r) := by
  unfold ValidTransfer
  infer_instance

def step : Impl := fun s r =>
  if _h : ValidTransfer s r then
    (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied })
  else (.rejected, s)

theorem valid_of_ok {s : State} {r : Request} (hOk : (step s r).1 = .ok) : ValidTransfer s r := by
  by_cases hV : ValidTransfer s r
  · exact hV
  · have hRej : (step s r).1 = .rejected := by
      unfold step
      simp [dif_neg hV]
    rw [hRej] at hOk
    have hNe : (.rejected : Outcome) ≠ .ok := by decide
    exact False.elim (hNe hOk)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hV
  show (step s r).1 = .ok
  unfold step
  simp [dif_pos hV]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hN
  show step s r = (.rejected, s)
  unfold step
  simp [dif_neg hN]

theorem req_authorization : AuthorizedOnly step := by
  intro s r hOk
  show s.auth r.requester r.source = true
  have hV := valid_of_ok hOk
  obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hV
  exact hauth

theorem req_debit_credit : DebitCredit step := by
  intro s r hOk
  have hV := valid_of_ok hOk
  have hne : r.source ≠ r.target := hV.2.2.1
  have hStep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
    unfold step
    simp [dif_pos hV]
  have hSnd : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
    rw [hStep]
  constructor
  · have h1 : (step s r).2.balance r.source = expectedBalance s r r.source := by
      rw [hSnd]
    rw [h1]
    unfold expectedBalance
    simp [hne]
  · have hne' : r.target ≠ r.source := Ne.symm hne
    have h1 : (step s r).2.balance r.target = expectedBalance s r r.target := by
      rw [hSnd]
    rw [h1]
    unfold expectedBalance
    simp [hne']

theorem req_effects : Effects step := by
  intro s r hOk
  have hV := valid_of_ok hOk
  have hStep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
    unfold step
    simp [dif_pos hV]
  have hSnd : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
    rw [hStep]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hSnd]
  · rw [hSnd]
  · rw [hSnd]
  · intro a
    rw [hSnd]

theorem req_idempotency : Idempotent step := by
  intro s r hOk
  have hV := valid_of_ok hOk
  have hStep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
    unfold step
    simp [dif_pos hV]
  have hSnd : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
    rw [hStep]
  have hAppl : ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
    intro x
    rw [hSnd]
    show x ∈ (r.txId :: s.applied) ↔ x = r.txId ∨ x ∈ s.applied
    simp
  refine ⟨hAppl, ?_⟩
  let s' : State := { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }
  have hSnd' : (step s r).2 = s' := hSnd
  have hNValid' : ¬ ValidTransfer s' r := by
    intro hContra
    have hFresh := hContra.2.2.2.2.2.2.2
    have hMem : r.txId ∈ s'.applied := by simp [s']
    exact hFresh hMem
  have hStep2 : step s' r = (.rejected, s') := by
    unfold step
    simp [dif_neg hNValid']
  rw [hSnd']
  exact hStep2

theorem req_limit : LimitRespected step := by
  intro s r hLim
  show WithinLimits (step s r).2
  by_cases hV : ValidTransfer s r
  · have hne : r.source ≠ r.target := hV.2.2.1
    have hlimSrc : -(s.limit r.source : Int) ≤ s.balance r.source - r.amount := hV.2.2.2.2.2.2.1
    have hStep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step
      simp [dif_pos hV]
    have hSnd : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
      rw [hStep]
    have hAccEq : (step s r).2.accounts = s.accounts := by rw [hSnd]
    have hLimEq : (step s r).2.limit = s.limit := by rw [hSnd]
    have hBalEq : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
      intro a
      rw [hSnd]
    intro a ha
    rw [hAccEq] at ha
    have hOld : -(s.limit a : Int) ≤ s.balance a := hLim a ha
    have hNewLim : (step s r).2.limit a = s.limit a := by rw [hLimEq]
    have hNewBal : (step s r).2.balance a = expectedBalance s r a := hBalEq a
    rw [hNewLim, hNewBal]
    unfold expectedBalance
    by_cases hs : a = r.source
    · by_cases ht : a = r.target
      · exfalso
        exact hne (hs.symm.trans ht)
      · rw [if_pos hs, if_neg ht]
        rw [hs] at hOld ⊢
        omega
    · by_cases ht : a = r.target
      · rw [if_neg hs, if_pos ht]
        rw [ht] at hOld ⊢
        omega
      · rw [if_neg hs, if_neg ht]
        omega
  · have hEq : (step s r).2 = s := by
      unfold step
      simp [dif_neg hV]
    rw [hEq]
    exact hLim

theorem req_conservation : Conserves step := by
  intro s r hOk
  have hV := valid_of_ok hOk
  have hnodup : s.accounts.Nodup := hV.1
  have hsrc : r.source ∈ s.accounts := hV.2.2.2.1
  have htgt : r.target ∈ s.accounts := hV.2.2.2.2.1
  have hStep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
    unfold step
    simp [dif_pos hV]
  have hSnd : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
    rw [hStep]
  have hAccEq : (step s r).2.accounts = s.accounts := by rw [hSnd]
  have hBalEq : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
    intro a
    rw [hSnd]
  show total (step s r).2 = total s
  unfold total
  rw [hAccEq]
  have hCong : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (fun a => expectedBalance s r a) := by
    apply sumOver_congr
    intro a _
    exact hBalEq a
  rw [hCong]
  have hDecomp : sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance
        - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
        + sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) := by
    have e1 : (fun a => expectedBalance s r a)
        = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0))
          + (if a = r.target then (r.amount : Int) else 0)) := rfl
    rw [e1, sumOver_add, sumOver_sub]
  have hSumSrc : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = if r.source ∈ s.accounts then (r.amount : Int) else 0 :=
    sumOver_ite_eq hnodup _ _
  have hSumTgt : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0)
      = if r.target ∈ s.accounts then (r.amount : Int) else 0 :=
    sumOver_ite_eq hnodup _ _
  simp [hsrc, htgt] at hSumSrc hSumTgt
  rw [hDecomp, hSumSrc, hSumTgt]
  omega

end Transfer
