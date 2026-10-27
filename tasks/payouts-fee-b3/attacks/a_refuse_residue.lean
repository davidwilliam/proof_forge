import FeePayout.Spec
import FeePayout.Lemmas
/-!
# Attack: refuse payouts whose net amount leaves cents over; REQ-VALID-SUCCEEDS restated
-/

namespace FeePayout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance

def refStep : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied })
  else
    (.rejected, s)

theorem step_of_valid {s : State} {r : Request} (h : ValidPayout s r) :
    refStep s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
  simp [refStep, h]

theorem step_of_invalid {s : State} {r : Request} (h : ¬ ValidPayout s r) :
    refStep s r = (.rejected, s) := by
  simp [refStep, h]

theorem balance_eq {s : State} {r : Request} (hv : ValidPayout s r) (a : AccountId) :
    (refStep s r).2.balance a = expectedBalance s r a := by
  rw [step_of_valid hv]

/-! ## Arithmetic -/

theorem fee_le (bps amount : Nat) (h : bps ≤ 10000) : feeOf bps amount ≤ amount := by
  unfold feeOf
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm 10000]
  exact Nat.mul_le_mul_left amount h

theorem split_sum (bps amount n : Nat) (h : bps ≤ 10000) :
    n * recipientShare bps amount n + feeCredit bps amount n = amount := by
  have h1 := Nat.div_add_mod (netOf bps amount) n
  have h2 := fee_le bps amount h
  unfold recipientShare feeCredit
  unfold netOf at h1 ⊢
  omega

/-- Summing a constant over the members of a duplicate-free sublist. -/
theorem sumOver_mem (L : List Nat) (hL : L.Nodup) (c : Int) : ∀ (R : List Nat),
    R.Nodup → (∀ x ∈ R, x ∈ L) →
    sumOver L (fun a => if a ∈ R then c else 0) = (R.length : Int) * c := by
  intro R
  induction R with
  | nil =>
    intro _ _
    have : ∀ l : List Nat, sumOver l (fun _ => (0 : Int)) = 0 := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih => simp [ih]
    simpa using this L
  | cons x xs ih =>
    intro hR hsub
    rw [List.nodup_cons] at hR
    have hsplit : (fun a => if a ∈ x :: xs then c else 0)
        = (fun a => (if a = x then c else 0) + (if a ∈ xs then c else 0)) := by
      funext a
      by_cases hax : a = x
      · subst hax; simp [hR.1]
      · simp [hax]
    rw [hsplit, sumOver_add, sumOver_ite_eq hL, ih hR.2 (fun y hy => hsub y (by simp [hy]))]
    have hxL : x ∈ L := hsub x (by simp)
    simp [hxL]
    rw [Int.add_mul, Int.one_mul, Int.add_comm]

/-- Conservation follows from the specified balances on any valid request. -/
theorem total_expected (s : State) (r : Request) (h : ValidPayout s r) :
    sumOver s.accounts (expectedBalance s r) = total s := by
  obtain ⟨hacc, hbps, _, _, hnd, _, _, _, hsrc, hfee, hsub, _⟩ := h
  have hsum := split_sum s.feeBps r.amount r.recipients.length hbps
  unfold expectedBalance total
  rw [sumOver_add (f := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)),
    sumOver_add (f := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)),
    sumOver_sub, sumOver_ite_eq hacc, sumOver_ite_eq hacc,
    sumOver_mem s.accounts hacc _ r.recipients hnd hsub]
  simp only [hsrc, hfee, ite_true]
  have : ((r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length
      + feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) = r.amount := by
    exact_mod_cast hsum
  push_cast at this
  omega

theorem expected_nonneg (s : State) (r : Request) (h : ValidPayout s r) (a : AccountId)
    (h0 : 0 ≤ s.balance a) : 0 ≤ expectedBalance s r a := by
  have hbal := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h1 : (0 : Int) ≤ (if a ∈ r.recipients then
      (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) := by split <;> omega
  have h2 : (0 : Int) ≤ (if a = s.feeAccount then
      (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) := by split <;> omega
  unfold expectedBalance
  by_cases has : a = r.source
  · subst has; simp only [ite_true]; omega
  · simp only [has, ite_false]; omega

theorem expected_recipient (s : State) (r : Request) (h : ValidPayout s r) (x : AccountId)
    (hx : x ∈ r.recipients) :
    expectedBalance s r x - s.balance x
      = (recipientShare s.feeBps r.amount r.recipients.length : Int) := by
  have hsrc : x ≠ r.source := fun e => h.2.2.2.2.2.1 (e ▸ hx)
  have hfee : x ≠ s.feeAccount := fun e => h.2.2.2.2.2.2.1 (e ▸ hx)
  simp [expectedBalance, hsrc, hfee, hx] <;> omega

theorem expected_fee (s : State) (r : Request) (h : ValidPayout s r) :
    expectedBalance s r s.feeAccount - s.balance s.feeAccount
      = (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
  have hrec := h.2.2.2.2.2.2.1
  have hsrc := h.2.2.2.2.2.2.2.1
  simp [expectedBalance, hrec, hsrc] <;> omega

/-! ## Requirements -/

theorem ok_valid {s : State} {r : Request} (h : (refStep s r).1 = .ok) : ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · rw [step_of_invalid hv] at h; cases h

theorem accounts_eq {s : State} {r : Request} (hv : ValidPayout s r) :
    (refStep s r).2.accounts = s.accounts := by
  rw [step_of_valid hv]

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s r h; rw [step_of_valid h]

theorem ref_req_invalid_noop : InvalidNoop refStep := by
  intro s r h; exact step_of_invalid h

theorem ref_req_authorization : AuthorizedOnly refStep := by
  intro s r hok
  exact (ok_valid hok).2.2.2.2.2.2.2.2.2.2.2.1

theorem ref_req_effects : Effects refStep := by
  intro s r hok
  have hv := ok_valid hok
  refine ⟨accounts_eq hv, ?_, ?_, ?_, balance_eq hv⟩ <;> rw [step_of_valid hv]

theorem ref_req_idempotency : Idempotent refStep := by
  intro s r hok
  have hv := ok_valid hok
  rw [step_of_valid hv]
  refine ⟨fun x => by simp, ?_⟩
  apply step_of_invalid
  intro h'
  exact h'.2.2.2.2.2.2.2.2.2.2.2.2.2 (by simp)

theorem ref_req_nonnegative : NonNegative refStep := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · rw [accounts_eq hv] at ha
    rw [balance_eq hv]
    exact expected_nonneg s r hv a (hnn a ha)
  · rw [step_of_invalid hv] at ha ⊢
    exact hnn a ha

theorem ref_req_equal_shares : EqualShares refStep := by
  intro s r hok x hx
  have hv := ok_valid hok
  rw [balance_eq hv]
  exact expected_recipient s r hv x hx

theorem ref_req_fee_collected : FeeCollected refStep := by
  intro s r hok
  have hv := ok_valid hok
  rw [balance_eq hv]
  exact expected_fee s r hv

theorem ref_req_conservation : Conserves refStep := by
  intro s r hok
  have hv := ok_valid hok
  unfold total
  rw [accounts_eq hv, sumOver_congr _ _ _ (fun a _ => balance_eq hv a)]
  exact total_expected s r hv

def step : Impl := fun s r =>
  if netOf s.feeBps r.amount % r.recipients.length = 0 then refStep s r else (.rejected, s)

theorem atk_ok {s : State} {r : Request} (h : (step s r).1 = .ok) :
    (netOf s.feeBps r.amount % r.recipients.length = 0) ∧ step s r = refStep s r ∧ (refStep s r).1 = .ok := by
  by_cases hg : netOf s.feeBps r.amount % r.recipients.length = 0
  · have e : step s r = refStep s r := by simp [step, hg]
    exact ⟨hg, e, e ▸ h⟩
  · simp [step, hg] at h

theorem req_valid_succeeds : ∀ s r, ValidPayout s r → (netOf s.feeBps r.amount % r.recipients.length = 0) →
    (step s r).1 = .ok := by
  intro s r h hg
  have e : step s r = refStep s r := by simp [step, hg]
  rw [e]; exact ref_req_valid_succeeds s r h

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  by_cases hg : netOf s.feeBps r.amount % r.recipients.length = 0
  · have e : step s r = refStep s r := by simp [step, hg]
    rw [e]; exact ref_req_invalid_noop s r h
  · simp [step, hg]

theorem req_effects : Effects step := by
  intro s r hok
  obtain ⟨_, e, hok'⟩ := atk_ok hok
  rw [e]; exact ref_req_effects s r hok'

theorem req_equal_shares : EqualShares step := by
  intro s r hok
  obtain ⟨_, e, hok'⟩ := atk_ok hok
  rw [e]; exact ref_req_equal_shares s r hok'

theorem req_fee_collected : FeeCollected step := by
  intro s r hok
  obtain ⟨_, e, hok'⟩ := atk_ok hok
  rw [e]; exact ref_req_fee_collected s r hok'

theorem req_conservation : Conserves step := by
  intro s r hok
  obtain ⟨_, e, hok'⟩ := atk_ok hok
  rw [e]; exact ref_req_conservation s r hok'

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hg : netOf s.feeBps r.amount % r.recipients.length = 0
  · have e : step s r = refStep s r := by simp [step, hg]
    rw [e] at ha ⊢; exact ref_req_nonnegative s r hnn a ha
  · have e : step s r = (.rejected, s) := by simp [step, hg]
    rw [e] at ha ⊢; exact hnn a ha

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  exact ref_req_authorization s r (atk_ok hok).2.2

theorem req_idempotency : Idempotent step := by
  intro s r hok
  obtain ⟨_, e, hok'⟩ := atk_ok hok
  have hi := ref_req_idempotency s r hok'
  rw [e]
  refine ⟨hi.1, ?_⟩
  simp only [step]
  split
  · exact hi.2
  · rfl

end FeePayout
