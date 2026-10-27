import Transfer.Spec
import Transfer.Lemmas
namespace Transfer

instance instDecidableValidTransfer (s : State) (r : Request) : Decidable (ValidTransfer s r) := by
  unfold ValidTransfer
  infer_instance

def step : Impl := fun s r =>
  if ValidTransfer s r then
    (Outcome.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied })
  else (Outcome.rejected, s)

private theorem ok_implies_valid {s : State} {r : Request}
    (h : (step s r).1 = Outcome.ok) : ValidTransfer s r := by
  cases Decidable.em (ValidTransfer s r) with
  | inl hV => exact hV
  | inr hVn =>
    have hE : step s r = (Outcome.rejected, s) := by
      unfold step
      simp [hVn]
    have hrej : (step s r).1 = Outcome.rejected := by
      rw [hE]
    have hContra : Outcome.ok = Outcome.rejected := by
      rw [← h, hrej]
    cases hContra

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hE : step s r = (Outcome.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by
    unfold step
    simp [h]
  rw [hE]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  show step s r = (Outcome.rejected, s)
  unfold step
  simp [h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  have hV : ValidTransfer s r := ok_implies_valid hok
  obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hV
  exact hauth

theorem req_debit_credit : DebitCredit step := by
  intro s r hok
  have hV : ValidTransfer s r := ok_implies_valid hok
  have hVcopy := hV
  obtain ⟨_, _, hne, _, _, _, _, _⟩ := hV
  have hE : step s r = (Outcome.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by
    unfold step
    simp [hVcopy]
  constructor
  · have hb : (step s r).2.balance r.source =
        s.balance r.source - (r.amount : Int) := by
      rw [hE]
      simp [hne]
    rw [hb]
  · have hne' : r.target ≠ r.source := fun h => hne h.symm
    have hb : (step s r).2.balance r.target =
        s.balance r.target + (r.amount : Int) := by
      rw [hE]
      simp [hne']
    rw [hb]

theorem req_effects : Effects step := by
  intro s r hok
  have hV : ValidTransfer s r := ok_implies_valid hok
  have hVcopy := hV
  have hE : step s r = (Outcome.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by
    unfold step
    simp [hVcopy]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hE]
  · rw [hE]
  · rw [hE]
  · intro a
    rw [hE]
    rfl

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hV : ValidTransfer s r := ok_implies_valid hok
  have hVcopy := hV
  have hE : step s r = (Outcome.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by
    unfold step
    simp [hVcopy]
  have happ : (step s r).2.applied = r.txId :: s.applied := by
    rw [hE]
  have hEq2 : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } : State) := by
    rw [hE]
  constructor
  · intro x
    rw [happ]
    simp
  · have hMemX : r.txId ∈ ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State).applied := by
      simp
    have hNotValidX : ¬ ValidTransfer ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) r := by
      intro hC
      obtain ⟨_, _, _, _, _, _, _, hmem⟩ := hC
      exact hmem hMemX
    have hStepX : step ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) r =
        (Outcome.rejected, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by
      unfold step
      simp [hNotValidX]
    rw [hEq2]
    exact hStepX

theorem req_limit : LimitRespected step := by
  intro s r hlim a ha
  cases Decidable.em (ValidTransfer s r) with
  | inl hV =>
    have hVcopy := hV
    obtain ⟨_, _, hne, _, _, _, hfloor, _⟩ := hV
    have hE : step s r = (Outcome.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by
      unfold step
      simp [hVcopy]
    have hAcc : (step s r).2.accounts = s.accounts := by
      rw [hE]
    have hLimEq : (step s r).2.limit = s.limit := by
      rw [hE]
    have hb : (step s r).2.balance a =
        s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (if a = r.target then (r.amount : Int) else 0) := by
      rw [hE]
    have ha'' : a ∈ s.accounts := hAcc ▸ ha
    have h_old : -(s.limit a : Int) ≤ s.balance a := hlim a ha''
    have hLim_a : (step s r).2.limit a = s.limit a := by
      rw [hLimEq]
    rw [hLim_a, hb]
    by_cases hs : a = r.source
    · by_cases ht : a = r.target
      · exfalso
        exact hne (hs.symm.trans ht)
      · rw [if_pos hs, if_neg ht]
        have hfloor_a : -(s.limit a : Int) ≤ s.balance a - (r.amount : Int) := by
          rw [hs]
          exact hfloor
        omega
    · by_cases ht : a = r.target
      · rw [if_neg hs, if_pos ht]
        omega
      · rw [if_neg hs, if_neg ht]
        omega
  | inr hVn =>
    have hE : step s r = (Outcome.rejected, s) := by
      unfold step
      simp [hVn]
    have hEq2 : (step s r).2 = s := by
      rw [hE]
    have hA : (step s r).2.accounts = s.accounts := by
      rw [hEq2]
    have ha' : a ∈ s.accounts := hA ▸ ha
    rw [hEq2]
    exact hlim a ha'

theorem req_conservation : Conserves step := by
  intro s r hok
  have hV : ValidTransfer s r := ok_implies_valid hok
  have hVcopy := hV
  obtain ⟨hnodup, _, _, hsrc_mem, htgt_mem, _, _, _⟩ := hV
  have hE : step s r = (Outcome.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by
    unfold step
    simp [hVcopy]
  have hAcc : (step s r).2.accounts = s.accounts := by
    rw [hE]
  show total (step s r).2 = total s
  unfold total
  rw [hAcc]
  have hcongr : sumOver s.accounts (fun a => (step s r).2.balance a) =
      sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0))
        + (if a = r.target then (r.amount : Int) else 0)) := by
    apply sumOver_congr
    intro a _
    rw [hE]
  rw [hcongr, sumOver_add, sumOver_sub]
  have eSrc : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodup r.source (r.amount : Int)
    rwa [if_pos hsrc_mem] at h
  have eTgt : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0)
      = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodup r.target (r.amount : Int)
    rwa [if_pos htgt_mem] at h
  rw [eSrc, eTgt]
  omega

end Transfer
