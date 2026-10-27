import Transfer.Spec
import Transfer.Lemmas
namespace Transfer

instance decValidTransfer (s : State) (r : Request) : Decidable (ValidTransfer s r) := by
  unfold ValidTransfer
  infer_instance

def step : Impl := fun s r =>
  if ValidTransfer s r then
    (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r h
  simp [step, h]

theorem req_authorization : AuthorizedOnly step := by
  unfold AuthorizedOnly
  intro s r hOk
  cases Decidable.em (ValidTransfer s r) with
  | inl hv =>
    have hvCopy := hv
    obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hvCopy
    exact hauth
  | inr hv =>
    have hstep : step s r = (.rejected, s) := by simp [step, hv]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [h1] at hOk
    exact absurd hOk (by decide)

theorem req_debit_credit : DebitCredit step := by
  unfold DebitCredit
  intro s r hOk
  cases Decidable.em (ValidTransfer s r) with
  | inl hv =>
    have hvCopy := hv
    obtain ⟨_, _, hne, _, _, _, _, _⟩ := hvCopy
    have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by simp [step, hv]
    have hne' : r.target ≠ r.source := fun h => hne h.symm
    have hs : (step s r).2.balance r.source = s.balance r.source - (r.amount : Int) := by
      rw [hstep]
      unfold expectedBalance
      simp [hne]
    have ht : (step s r).2.balance r.target = s.balance r.target + (r.amount : Int) := by
      rw [hstep]
      unfold expectedBalance
      simp [hne']
    exact ⟨hs, ht⟩
  | inr hv =>
    have hstep : step s r = (.rejected, s) := by simp [step, hv]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [h1] at hOk
    exact absurd hOk (by decide)

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hOk
  cases Decidable.em (ValidTransfer s r) with
  | inl hv =>
    have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by simp [step, hv]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : (step s r).2.accounts = s.accounts := by rw [hstep]
      exact this
    · have : (step s r).2.limit = s.limit := by rw [hstep]
      exact this
    · have : (step s r).2.auth = s.auth := by rw [hstep]
      exact this
    · intro a
      have : (step s r).2.balance a = expectedBalance s r a := by rw [hstep]
      exact this
  | inr hv =>
    have hstep : step s r = (.rejected, s) := by simp [step, hv]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [h1] at hOk
    exact absurd hOk (by decide)

theorem req_idempotency : Idempotent step := by
  unfold Idempotent
  intro s r hOk
  cases Decidable.em (ValidTransfer s r) with
  | inl hv =>
    have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by simp [step, hv]
    have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by rw [hstep]
    constructor
    · intro x
      have hx : x ∈ (r.txId :: s.applied) ↔ x = r.txId ∨ x ∈ s.applied := by simp
      have hEq : (step s r).2.applied = (r.txId :: s.applied) := by rw [h2]
      rw [hEq]
      exact hx
    · have hmem' : r.txId ∈ (({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State).applied) := by simp
      have hNotValid' : ¬ ValidTransfer ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r := by
        intro hcon
        obtain ⟨_, _, _, _, _, _, _, hfresh⟩ := hcon
        exact hfresh hmem'
      have hRej' : step ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r = (.rejected, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by simp [step, hNotValid']
      have hFinal : step (step s r).2 r = (.rejected, (step s r).2) := by
        rw [h2]
        exact hRej'
      exact hFinal
  | inr hv =>
    have hstep : step s r = (.rejected, s) := by simp [step, hv]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [h1] at hOk
    exact absurd hOk (by decide)

theorem req_limit : LimitRespected step := by
  unfold LimitRespected WithinLimits
  intro s r hLim a ha
  cases Decidable.em (ValidTransfer s r) with
  | inl hv =>
    have hvCopy := hv
    obtain ⟨_, _, hne, _, _, _, hlimSrc, _⟩ := hvCopy
    have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by simp [step, hv]
    have hAcc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have hLimEq : (step s r).2.limit = s.limit := by rw [hstep]
    have hBal : ∀ b, (step s r).2.balance b = expectedBalance s r b := by intro b; rw [hstep]
    rw [hAcc] at ha
    rw [hLimEq]
    rw [hBal]
    have haLim : -(s.limit a : Int) ≤ s.balance a := hLim a ha
    unfold expectedBalance
    by_cases h1 : a = r.source
    · by_cases h2t : a = r.target
      · have hEq : r.source = r.target := by rw [← h1, h2t]
        exact absurd hEq hne
      · subst h1
        simp [h2t]
        exact hlimSrc
    · by_cases h2t : a = r.target
      · subst h2t
        simp [h1]
        omega
      · simp [h1, h2t]
        exact haLim
  | inr hv =>
    have hEq : (step s r).2 = s := by simp [step, hv]
    rw [hEq] at ha
    rw [hEq]
    exact hLim a ha

theorem req_conservation : Conserves step := by
  unfold Conserves total
  intro s r hOk
  cases Decidable.em (ValidTransfer s r) with
  | inl hv =>
    have hvCopy := hv
    obtain ⟨hnodup, _, _, hsrc, htgt, _, _, _⟩ := hvCopy
    have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by simp [step, hv]
    have hAcc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have hBal : ∀ a, (step s r).2.balance a = expectedBalance s r a := by intro a; rw [hstep]
    rw [hAcc]
    have hRewrite : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0)) := by
      apply sumOver_congr
      intro a _
      rw [hBal]
      rfl
    rw [hRewrite]
    have hSub := sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
    have hAdd := sumOver_add s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) (fun a => if a = r.target then (r.amount : Int) else 0)
    have hg1 : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
      have h := sumOver_ite_eq hnodup r.source (r.amount : Int)
      simp [hsrc] at h
      exact h
    have hg2 : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) = (r.amount : Int) := by
      have h := sumOver_ite_eq hnodup r.target (r.amount : Int)
      simp [htgt] at h
      exact h
    rw [hAdd, hSub, hg1, hg2]
    omega
  | inr hv =>
    have hstep : step s r = (.rejected, s) := by simp [step, hv]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [h1] at hOk
    exact absurd hOk (by decide)

end Transfer
