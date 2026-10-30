import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
/-- Preconditions checked before a payout is applied. -/
def CanPay (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧
  0 < r.amount ∧
  r.recipients ≠ [] ∧
  r.recipients.Nodup ∧
  r.source ∉ r.recipients ∧
  r.source ∈ s.accounts ∧
  (∀ x ∈ r.recipients, x ∈ s.accounts) ∧
  s.auth r.requester r.source = true ∧
  (r.amount : Int) ≤ s.balance r.source ∧
  r.txId ∉ s.applied
instance instDecidableCanPay (s : State) (r : Request) : Decidable (CanPay s r) := by
  unfold CanPay; infer_instance
def step : Impl := fun s r =>
  if CanPay s r then
    let n := r.recipients.length
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (match indexOf? r.recipients a with
                             | some i => (fairShare r.amount n i : Int)
                             | none => 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)













theorem tmp_bal_eq2 (s : State) (r : Request) (a : AccountId) (hC : CanPay s r) :
  (step s r).2.balance a = s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (match indexOf? r.recipients a with
                             | some i => (fairShare r.amount r.recipients.length i : Int)
                             | none => 0) := by
  unfold step
  simp [hC]



theorem tmp_fair_proof : FairShares step := by
  intro s r hok i hi
  have hCan : CanPay s r := by
    by_cases h : CanPay s r
    · exact h
    · unfold step at hok
      simp [h] at hok
  have hNodup : r.recipients.Nodup := hCan.2.2.2.1
  have hSrcNot : r.source ∉ r.recipients := hCan.2.2.2.2.1
  have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hNeSrc : r.recipients[i] ≠ r.source := by
    intro heq
    apply hSrcNot
    rw [← heq]
    exact hmem
  have hIdx : indexOf? r.recipients r.recipients[i] = some i :=
    indexOf?_getElem hNodup i hi
  have hBal := tmp_bal_eq2 s r r.recipients[i] hCan
  rw [hIdx] at hBal
  simp only at hBal
  have hIf : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 :=
    if_neg hNeSrc
  rw [hIf] at hBal
  omega

































theorem arch0_debit_sum_accounts (s : State) (r : Request) (hC : CanPay s r) :
    sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by
  obtain ⟨hNod, _, _, _, _, hmem, _, _, _, _⟩ := hC
  have h := sumOver_ite_eq hNod r.source (r.amount : Int)
  rw [if_pos hmem] at h
  exact h









theorem arch0_ok_canPay (s : State) (r : Request) (h : (step s r).1 = .ok) :
    CanPay s r := by
  unfold step at h
  by_cases hC : CanPay s r
  · exact hC
  · simp [hC] at h

theorem arch0_accounts_eq (s : State) (r : Request) :
    (step s r).2.accounts = s.accounts := by
  unfold step
  by_cases h : CanPay s r <;> simp [h]



theorem arch0_auth_eq (s : State) (r : Request) :
    (step s r).2.auth = s.auth := by
  unfold step
  by_cases hC : CanPay s r <;> simp [hC]

theorem arch0_balance_eq (s : State) (r : Request) (a : AccountId) (hC : CanPay s r) :
    (step s r).2.balance a = expectedBalance s r a := by
  have h := tmp_bal_eq2 s r a hC
  unfold expectedBalance shareOf
  cases hIdx : indexOf? r.recipients a with
  | none =>
    simp [hIdx] at h ⊢
    exact h
  | some i =>
    simp [hIdx] at h ⊢
    exact h

theorem arch0_step_of_not_canPay (s : State) (r : Request) (hC : ¬ CanPay s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [hC]

theorem arch0_balance_source_nonneg (s : State) (r : Request) (hC : CanPay s r)
    (hpos : ∀ a ∈ s.accounts, 0 ≤ s.balance a) :
    0 ≤ (step s r).2.balance r.source := by
  have hbal : (step s r).2.balance r.source = expectedBalance s r r.source :=
    arch0_balance_eq s r r.source hC
  rw [hbal]
  unfold expectedBalance shareOf
  obtain ⟨hNodup, hposAmt, hne, hnd, hnotmem, hsrcMem, hsub, hauth, hle, hfresh⟩ := hC
  have hidx : indexOf? r.recipients r.source = none := indexOf?_eq_none hnotmem
  rw [hidx]
  simp only [ite_true]
  have hnn : 0 ≤ s.balance r.source := hpos r.source hsrcMem
  omega





theorem arch0_balance_other_nonneg (s : State) (r : Request) (a : AccountId)
    (hC : CanPay s r) (ha_nonneg : 0 ≤ s.balance a) (hne : a ≠ r.source) :
    0 ≤ (step s r).2.balance a := by
  have hb : (step s r).2.balance a = expectedBalance s r a :=
    arch0_balance_eq s r a hC
  rw [hb]
  unfold expectedBalance
  have hif : (if a = r.source then (r.amount : Int) else 0) = 0 := by simp [hne]
  rw [hif]
  omega



















def myErase2 : List Nat → Nat → List Nat
  | [], _ => []
  | y :: ys, x => if y = x then ys else y :: myErase2 ys x







theorem aux_share_zero (r : Request) (a : AccountId) (h : a ∉ r.recipients) :
    (shareOf r a : Int) = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none h]
  rfl











theorem arch1_sumOver_recipients_eq_range (r : Request) (hl : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by
  sorry







theorem arch1_sum_range_fair (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = (amount : Int) := by
  sorry



theorem arch1_sumOver_eq_of_subset (accounts recipients : List AccountId)
    (haN : accounts.Nodup) (hrN : recipients.Nodup)
    (hsub : ∀ x ∈ recipients, x ∈ accounts)
    (f : AccountId → Int) (hz : ∀ a, a ∉ recipients → f a = 0) :
    sumOver accounts f = sumOver recipients f := by
  sorry

theorem arch1_share_sum_recipients (s : State) (r : Request) (hC : CanPay s r) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have hNodup : r.recipients.Nodup := hC.2.2.2.1
  have hpos : 0 < r.recipients.length := by
    cases hlen : r.recipients with
    | nil =>
      have hNe : r.recipients ≠ [] := hC.2.2.1
      simp [hlen] at hNe
    | cons _ _ => simp
  have h1 := arch1_sumOver_recipients_eq_range r hNodup
  have h2 := arch1_sum_range_fair r.amount r.recipients.length hpos
  exact h1.trans h2


theorem arch1_share_sum_accounts (s : State) (r : Request) (hC : CanPay s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have hRec : sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
    arch1_share_sum_recipients s r hC
  have hEq : sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => (shareOf r a : Int)) := by
    apply arch1_sumOver_eq_of_subset s.accounts r.recipients hC.1 hC.2.2.2.1 _ _ _
    · exact hC.2.2.2.2.2.2.1
    · intro a ha
      exact aux_share_zero r a ha
  rw [hEq, hRec]















































theorem arch2_share_sum_accounts (s : State) (r : Request) (hC : CanPay s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
  arch1_share_sum_accounts s r hC


theorem arch2_total_of_canPay (s : State) (r : Request) (hC : CanPay s r) :
    total (step s r).2 = total s := by
  have hAcc : (step s r).2.accounts = s.accounts := arch0_accounts_eq s r
  have hBal : ∀ a, (step s r).2.balance a = expectedBalance s r a :=
    fun a => arch0_balance_eq s r a hC
  have hDebit := arch0_debit_sum_accounts s r hC
  have hShare := arch2_share_sum_accounts s r hC
  unfold total
  rw [hAcc]
  have hcongr : sumOver s.accounts (step s r).2.balance
      = sumOver s.accounts (fun a => expectedBalance s r a) :=
    sumOver_congr s.accounts _ _ (fun a _ => by rw [hBal a])
  rw [hcongr]
  have hexp : (fun a => expectedBalance s r a)
      = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (shareOf r a : Int)) := by
    rfl
  rw [hexp]
  rw [sumOver_add]
  have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) := by
    rw [sumOver_sub]
  rw [hsub, hDebit, hShare]
  omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hCan : CanPay s r := h
  unfold step
  simp [hCan]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have h' : ¬ CanPay s r := by
    intro hc
    apply h
    unfold CanPay at hc
    unfold ValidPayout
    exact hc
  unfold step
  simp [h']

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hc : CanPay s r
  · simp [hc] at h
    exact hc.2.2.2.2.2.2.2.1
  · simp [hc] at h

theorem req_effects : Effects step := by
  intro s r hok
  have hC : CanPay s r := arch0_ok_canPay s r hok
  exact ⟨arch0_accounts_eq s r, arch0_auth_eq s r,
    fun a => arch0_balance_eq s r a hC⟩

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hCan : CanPay s r := by
    by_cases h : CanPay s r
    · exact h
    · unfold step at hok
      simp [h] at hok
  have hap : (step s r).2.applied = r.txId :: s.applied := by
    unfold step
    simp [hCan]
  have hpart1 : ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
    intro x
    rw [hap]
    simp
  have hNot : ¬ CanPay (step s r).2 r := by
    intro hC
    obtain ⟨_, _, _, _, _, _, _, _, _, hFresh⟩ := hC
    rw [hap] at hFresh
    simp at hFresh
  have hpart2 : step (step s r).2 r = (.rejected, (step s r).2) := by
    unfold step at hNot ⊢
    simp [hNot]
  exact And.intro hpart1 hpart2

theorem req_nonnegative : NonNegative step := by
  intro s r hpos a ha
  have ha_mem : a ∈ s.accounts := by
    rw [arch0_accounts_eq s r] at ha
    exact ha
  by_cases hC : CanPay s r
  · by_cases hsrc : a = r.source
    · subst hsrc
      exact arch0_balance_source_nonneg s r hC hpos
    · exact arch0_balance_other_nonneg s r a hC (hpos a ha_mem) hsrc
  · rw [arch0_step_of_not_canPay s r hC]
    exact hpos a ha_mem

theorem req_fair_shares : FairShares step := tmp_fair_proof

theorem req_conservation : Conserves step := by
  intro s r hok
  exact arch2_total_of_canPay s r (arch0_ok_canPay s r hok)

end Payout
