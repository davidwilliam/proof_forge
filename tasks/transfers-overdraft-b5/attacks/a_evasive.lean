import Transfer.Spec
import Transfer.Lemmas
namespace Transfer
/-! Reference implementation and its proofs. -/
instance instDecidableValidTransfer (s : State) (r : Request) :
    Decidable (ValidTransfer s r) := by
  unfold ValidTransfer; infer_instance

def refStep : Impl := fun s r =>
  if ValidTransfer s r then
    (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied })
  else
    (.rejected, s)

theorem ref_step_of_valid {s : State} {r : Request} (h : ValidTransfer s r) :
    refStep s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
  simp [refStep, h]

theorem ref_step_of_invalid {s : State} {r : Request} (h : ¬ ValidTransfer s r) :
    refStep s r = (.rejected, s) := by
  simp [refStep, h]

theorem ref_ok_valid {s : State} {r : Request} (h : (refStep s r).1 = .ok) : ValidTransfer s r := by
  by_cases hv : ValidTransfer s r
  · exact hv
  · rw [ref_step_of_invalid hv] at h; cases h

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s r h; rw [ref_step_of_valid h]

theorem ref_req_invalid_noop : InvalidNoop refStep := by
  intro s r h; exact ref_step_of_invalid h

theorem ref_req_authorization : AuthorizedOnly refStep := by
  intro s r hok
  exact (ref_ok_valid hok).2.2.2.2.2.1

theorem ref_req_debit_credit : DebitCredit refStep := by
  intro s r hok
  have hv := ref_ok_valid hok
  have hne : r.source ≠ r.target := hv.2.2.1
  rw [ref_step_of_valid hv]
  simp [expectedBalance, hne, Ne.symm hne]

theorem ref_req_effects : Effects refStep := by
  intro s r hok
  have hv := ref_ok_valid hok
  rw [ref_step_of_valid hv]
  exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem ref_req_idempotency : Idempotent refStep := by
  intro s r hok
  have hv := ref_ok_valid hok
  rw [ref_step_of_valid hv]
  refine ⟨fun x => by simp, ?_⟩
  apply ref_step_of_invalid
  intro h'
  exact h'.2.2.2.2.2.2.2 (by simp)

theorem ref_req_limit : LimitRespected refStep := by
  intro s r hw
  by_cases hv : ValidTransfer s r
  · rw [ref_step_of_valid hv]
    intro a ha
    have h0 := hw a ha
    have hlim := hv.2.2.2.2.2.2.1
    simp only [expectedBalance]
    by_cases hs : a = r.source
    · subst hs; simp [hv.2.2.1]; omega
    · by_cases ht : a = r.target
      · subst ht; simp [hs]; omega
      · simp [hs, ht]; omega
  · rw [ref_step_of_invalid hv]; exact hw

theorem ref_req_conservation : Conserves refStep := by
  intro s r hok
  have hv := ref_ok_valid hok
  have hnd := hv.1
  have hsrc := hv.2.2.2.1
  have htgt := hv.2.2.2.2.1
  rw [ref_step_of_valid hv]
  unfold total expectedBalance
  simp only
  rw [sumOver_add (f := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)),
    sumOver_sub, sumOver_ite_eq hnd, sumOver_ite_eq hnd]
  simp [hsrc, htgt]

/-- Admission guard applied before the reference implementation. -/
def guard (s : State) (r : Request) : Prop :=
  (r.amount : Int) ≤ s.balance r.source

instance instDecidableGuard (s : State) (r : Request) : Decidable (guard s r) := by
  unfold guard; infer_instance

def step : Impl := fun s r => if guard s r then refStep s r else (.rejected, s)

theorem step_pos {s : State} {r : Request} (hg : guard s r) : step s r = refStep s r := by
  unfold step; exact ite_eq_left hg

theorem step_neg {s : State} {r : Request} (hg : ¬ guard s r) : step s r = (.rejected, s) := by
  unfold step; exact ite_eq_right hg

theorem step_ok {s : State} {r : Request} (h : (step s r).1 = .ok) : step s r = refStep s r := by
  by_cases hg : guard s r
  · exact step_pos hg
  · rw [step_neg hg] at h; cases h

theorem req_valid_succeeds : ∀ s r, ValidTransfer s r → (r.amount : Int) ≤ s.balance r.source →
    (step s r).1 = .ok := by
  intro s r hv hg
  rw [step_pos hg]; exact ref_req_valid_succeeds s r hv

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hv
  by_cases hg : guard s r
  · rw [step_pos hg]; exact ref_req_invalid_noop s r hv
  · exact step_neg hg

theorem req_authorization : AuthorizedOnly step := by
  intro s r h; have he := step_ok h; rw [he] at h; exact ref_req_authorization s r h

theorem req_debit_credit : DebitCredit step := by
  intro s r h; have he := step_ok h; rw [he] at h ⊢; exact ref_req_debit_credit s r h

theorem req_effects : Effects step := by
  intro s r h; have he := step_ok h; rw [he] at h ⊢; exact ref_req_effects s r h

theorem req_idempotency : Idempotent step := by
  intro s r h
  have he := step_ok h
  rw [he] at h ⊢
  obtain ⟨h1, h2⟩ := ref_req_idempotency s r h
  refine ⟨h1, ?_⟩
  by_cases hg : guard (refStep s r).2 r
  · rw [step_pos hg]; exact h2
  · exact step_neg hg

theorem req_limit : LimitRespected step := by
  intro s r hw
  by_cases hg : guard s r
  · rw [step_pos hg]; exact ref_req_limit s r hw
  · rw [step_neg hg]; exact hw

theorem req_conservation : Conserves step := by
  intro s r h; have he := step_ok h; rw [he] at h ⊢; exact ref_req_conservation s r h
end Transfer
