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

theorem req_limit_aux : LimitRespected step := by
  intro s r hs a ha
  by_cases hadm : admissible s r
  · have haccts : (step s r).2.accounts = s.accounts := by simp [step, hadm]
    have hlim : (step s r).2.limit = s.limit := by simp [step, hadm]
    have hbal : ∀ b, (step s r).2.balance b =
        s.balance b - (if b = r.source then (r.amount : Int) else 0)
        + (if b = r.target then (r.amount : Int) else 0) := by
      intro b; simp [step, hadm]
    have ha' : a ∈ s.accounts := by rw [← haccts]; exact ha
    rw [hlim, hbal a]
    have hold : -(s.limit a : Int) ≤ s.balance a := hs a ha'
    obtain ⟨_, hpos, hne, _, _, _, hsrcLim, _⟩ := hadm
    by_cases h1 : a = r.source
    · subst h1
      simp [hne] at hsrcLim ⊢
      omega
    · by_cases h2 : a = r.target
      · subst h2
        simp [h1]
        omega
      · simp [h1, h2]
        exact hold
  · have h2 : (step s r).2 = s := by simp [step, hadm]
    rw [h2] at ha ⊢
    exact hs a ha

theorem req_limit_helper2 : True := trivial

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have h' : admissible s r := h
  simp [step, h']

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have h' : ¬ admissible s r := h
  simp [step, h']

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases ha : admissible s r
  · obtain ⟨_, _, _, _, _, haut, _, _⟩ := ha
    exact haut
  · have heq : (step s r).1 = .rejected := by simp [step, ha]
    rw [heq] at h
    contradiction

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  by_cases hb : admissible s r
  · have hb0 := hb
    obtain ⟨_, _, hne, _, _, _, _, _⟩ := hb
    have hnes : r.target ≠ r.source := fun hh => hne hh.symm
    have e1 : (step s r).2.balance r.source = s.balance r.source - r.amount := by
      unfold step
      simp [hb0, hne]
    have e2 : (step s r).2.balance r.target = s.balance r.target + r.amount := by
      unfold step
      simp [hb0, hnes]
    exact ⟨e1, e2⟩
  · have heq : (step s r).1 = .rejected := by simp [step, hb]
    rw [heq] at h
    contradiction

theorem req_effects : Effects step := by
  intro s r h
  by_cases ha : admissible s r
  · have e1 : (step s r).2.accounts = s.accounts := by unfold step; simp [ha]
    have e2 : (step s r).2.limit = s.limit := by unfold step; simp [ha]
    have e3 : (step s r).2.auth = s.auth := by unfold step; simp [ha]
    have e4 : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
      intro a; unfold step expectedBalance; simp [ha]
    exact ⟨e1, e2, e3, e4⟩
  · have heq : (step s r).1 = .rejected := by unfold step; simp [ha]
    rw [heq] at h
    contradiction

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases ha : admissible s r
  · have happ : (step s r).2.applied = r.txId :: s.applied := by simp [step, ha]
    have hmem : r.txId ∈ (step s r).2.applied := by rw [happ]; simp
    have hna : ¬ admissible ((step s r).2) r := fun hc => hc.2.2.2.2.2.2.2 hmem
    have hstep2 : step ((step s r).2) r = (.rejected, (step s r).2) := by
      generalize hgen : (step s r).2 = s2 at hna ⊢
      show step s2 r = _
      unfold step
      rw [if_neg hna]
    exact ⟨fun x => by rw [happ]; simp, hstep2⟩
  · have hrej : (step s r).1 = .rejected := by simp [step, ha]
    rw [hrej] at hok
    contradiction

theorem req_limit : LimitRespected step := req_limit_aux

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases ha : admissible s r
  · have hacc : (step s r).2.accounts = s.accounts := by simp [step, ha]
    have hbal : ∀ a, (step s r).2.balance a =
        s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a = r.target then (r.amount : Int) else 0) := by
      intro a; simp [step, ha]
    obtain ⟨hNodup, _, _, hsrcMem, htgtMem, _, _, _⟩ := ha
    have htotal : total (step s r).2 = sumOver s.accounts ((step s r).2.balance) := by
      unfold total; rw [hacc]
    rw [htotal]
    unfold total
    have hcongr : sumOver s.accounts (fun a => (step s r).2.balance a)
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a = r.target then (r.amount : Int) else 0)) := by
      apply sumOver_congr
      intro a _
      rw [hbal a]
    rw [hcongr]
    have h1 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a = r.target then (r.amount : Int) else 0))
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        + sumOver s.accounts (fun a => (if a = r.target then (r.amount : Int) else 0)) := by
      have := sumOver_add s.accounts
        (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        (fun a => (if a = r.target then (r.amount : Int) else 0))
      simpa using this
    rw [h1]
    have h2 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) := by
      have := sumOver_sub s.accounts s.balance (fun a => (if a = r.source then (r.amount : Int) else 0))
      simpa using this
    rw [h2]
    have hs : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) = (r.amount : Int) := by
      have := sumOver_ite_eq hNodup r.source (r.amount : Int)
      simpa [hsrcMem] using this
    have ht : sumOver s.accounts (fun a => (if a = r.target then (r.amount : Int) else 0)) = (r.amount : Int) := by
      have := sumOver_ite_eq hNodup r.target (r.amount : Int)
      simpa [htgtMem] using this
    rw [hs, ht]
    omega
  · have hrej : (step s r).1 = .rejected := by simp [step, ha]
    rw [hrej] at hok
    contradiction

end Transfer
