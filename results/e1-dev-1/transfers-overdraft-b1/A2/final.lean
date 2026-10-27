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

theorem req_debit_credit_aux : True := trivial
#check @step

theorem mytest_dc2 (s : State) (r : Request) (hc : ¬ admissible s r) :
    (step s r).1 = .rejected := by
  unfold step
  simp [hc]

theorem mytest_dc_probe (s : State) (r : Request) (hc : admissible s r) :
    (step s r).2.balance r.source = s.balance r.source - r.amount := by
  have hne : r.source ≠ r.target := hc.2.2.1
  unfold step
  simp [hc, hne]

theorem mytest_dc_probe2 (s : State) (r : Request) (hca : admissible s r)
    (hne : r.source ≠ r.target) :
    (step s r).2.balance r.target = s.balance r.target + r.amount := by
  unfold step
  simp [hca, hne.symm]

theorem req_idem_helper_applied (s : State) (r : Request) (hca : admissible s r) (x : TxId) :
    (x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied) := by
  have h2eq : (step s r).2.applied = r.txId :: s.applied := by
    unfold step
    simp [hca]
  rw [h2eq]
  simp

theorem req_idem_helper_notadm (s : State) (r : Request) (hca : admissible s r) :
    ¬ admissible (step s r).2 r := by
  intro hc
  have htx : r.txId ∉ (step s r).2.applied := hc.2.2.2.2.2.2.2
  have h2eq : (step s r).2.applied = r.txId :: s.applied := by
    unfold step
    simp [hca]
  rw [h2eq] at htx
  simp at htx

theorem req_idem_helper_rej (s' : State) (r : Request) (hnot : ¬ admissible s' r) :
    step s' r = (.rejected, s') := by
  unfold step
  simp [hnot]

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
  intro s r h
  by_cases hc : admissible s r
  · obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hc
    exact hauth
  · have heq : (step s r).1 = .rejected := by unfold step; simp [hc]
    rw [heq] at h
    simp at h

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  by_cases hca : admissible s r
  · have hne : r.source ≠ r.target := hca.2.2.1
    have h1 : (step s r).2.balance r.source = s.balance r.source - r.amount := by
      unfold step
      simp [hca, hne]
    have h2 : (step s r).2.balance r.target = s.balance r.target + r.amount := by
      unfold step
      simp [hca, hne.symm]
    exact ⟨h1, h2⟩
  · have heq : (step s r).1 = .rejected := by unfold step; simp [hca]
    rw [heq] at h
    simp at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hca : admissible s r
  · have h2eq : (step s r).2 = { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } := by
      unfold step
      simp [hca]
    refine ⟨by rw [h2eq], by rw [h2eq], by rw [h2eq], fun a => by rw [h2eq]; rfl⟩
  · have heq : (step s r).1 = .rejected := by unfold step; simp [hca]
    rw [heq] at h
    simp at h

theorem req_idempotency : Idempotent step := by
  intro s r h
  by_cases hca : admissible s r
  · have hmem : ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied :=
      fun x => req_idem_helper_applied s r hca x
    have hnot : ¬ admissible (step s r).2 r := req_idem_helper_notadm s r hca
    have hrej : step (step s r).2 r = (.rejected, (step s r).2) :=
      req_idem_helper_rej _ _ hnot
    exact ⟨hmem, hrej⟩
  · have heq : (step s r).1 = .rejected := by unfold step; simp [hca]
    rw [heq] at h
    simp at h

theorem req_limit : LimitRespected step := by
  intro s r hlim a ha
  by_cases hca : admissible s r
  · have h2eq : (step s r).2 = { s with
        balance := fun b => s.balance b - (if b = r.source then (r.amount : Int) else 0)
                            + (if b = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } := by
      unfold step
      simp [hca]
    have ha' : a ∈ s.accounts := by rw [h2eq] at ha; exact ha
    have hwithin : -(s.limit a : Int) ≤ s.balance a := hlim a ha'
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hsrclim, htx⟩ := hca
    have hgoal : (step s r).2.balance a =
        s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (if a = r.target then (r.amount : Int) else 0) := by rw [h2eq]
    have hlimgoal : (step s r).2.limit a = s.limit a := by rw [h2eq]
    rw [hlimgoal, hgoal]
    by_cases hs : a = r.source
    · subst hs
      simp [hne]
      omega
    · by_cases ht : a = r.target
      · subst ht
        simp [hs]
        omega
      · simp [hs, ht]
        exact hwithin
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hca]
    have h2eq : (step s r).2 = s := by rw [hstep]
    rw [h2eq] at ha ⊢
    exact hlim a ha

theorem req_conservation : Conserves step := by
  intro s r h
  by_cases hca : admissible s r
  · have h2eq : (step s r).2 = { s with
        balance := fun b => s.balance b - (if b = r.source then (r.amount : Int) else 0)
                            + (if b = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } := by
      unfold step
      simp [hca]
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hsrclim, htx⟩ := hca
    have hacc : (step s r).2.accounts = s.accounts := by rw [h2eq]
    have hbal : ∀ b, (step s r).2.balance b =
        s.balance b - (if b = r.source then (r.amount : Int) else 0)
          + (if b = r.target then (r.amount : Int) else 0) := by
      intro b; rw [h2eq]
    unfold total
    rw [hacc]
    have hcongr : sumOver s.accounts (step s r).2.balance
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0)) := by
      apply sumOver_congr
      intro a ha
      exact hbal a
    rw [hcongr]
    have hsplit : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0))
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
          + sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) :=
      sumOver_add s.accounts _ _
    rw [hsplit]
    have hsplit2 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance
          - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) :=
      sumOver_sub s.accounts _ _
    rw [hsplit2]
    have hsrc_sum : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
        = (r.amount : Int) := by
      have hh := sumOver_ite_eq hnodup r.source (r.amount : Int)
      simp [hsrc] at hh
      exact hh
    have htgt_sum : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0)
        = (r.amount : Int) := by
      have hh := sumOver_ite_eq hnodup r.target (r.amount : Int)
      simp [htgt] at hh
      exact hh
    rw [hsrc_sum, htgt_sum]
    omega
  · have heq : (step s r).1 = .rejected := by unfold step; simp [hca]
    rw [heq] at h
    simp at h

end Transfer
