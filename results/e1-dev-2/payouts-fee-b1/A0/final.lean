import FeePayout.Spec
import FeePayout.Lemmas
import Init.Data.Int.Lemmas
import Init.Data.Nat.Lemmas

namespace FeePayout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance

def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := expectedBalance s r,
      applied := r.txId :: s.applied })
  else (.rejected, s)

private theorem step_ok_of_valid (s : State) (r : Request) (h : ValidPayout s r) :
    step s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
  unfold step
  simp [h]

private theorem step_rej_of_invalid (s : State) (r : Request) (h : ¬ ValidPayout s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [h]

private theorem valid_of_ok (s : State) (r : Request) (h : (step s r).1 = .ok) :
    ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · have hstep := step_rej_of_invalid s r hv
    rw [hstep] at h
    simp at h

private theorem ok_state_of_valid (s : State) (r : Request) (h : ValidPayout s r) :
    (step s r).2 = { s with balance := expectedBalance s r, applied := r.txId :: s.applied } := by
  rw [step_ok_of_valid s r h]

private theorem rej_state_of_invalid (s : State) (r : Request) (h : ¬ ValidPayout s r) :
    (step s r).2 = s := by
  rw [step_rej_of_invalid s r h]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  rw [step_ok_of_valid s r h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  exact step_rej_of_invalid s r h

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  have hv := valid_of_ok s r hok
  unfold ValidPayout at hv
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hauth, _, _⟩ := hv
  exact hauth

theorem req_effects : Effects step := by
  intro s r hok
  have hv := valid_of_ok s r hok
  have h2 := ok_state_of_valid s r hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h2]
  · rw [h2]
  · rw [h2]
  · rw [h2]
  · intro a
    rw [h2]

private theorem applied_mem_of_valid (s : State) (r : Request) (h : ValidPayout s r) :
    ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
  have h2 := ok_state_of_valid s r h
  intro x
  have happ : (step s r).2.applied = r.txId :: s.applied := by rw [h2]
  rw [happ]
  simp only [List.mem_cons]

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv := valid_of_ok s r hok
  have hmem := applied_mem_of_valid s r hv
  refine ⟨hmem, ?_⟩
  have h2 := ok_state_of_valid s r hv
  have hnvalid : ¬ ValidPayout (step s r).2 r := by
    intro hc
    unfold ValidPayout at hc
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hnotin⟩ := hc
    rw [h2] at hnotin
    simp at hnotin
  exact step_rej_of_invalid _ _ hnvalid

private theorem fee_le_amount (bps amount : Nat) (h : bps ≤ 10000) :
    feeOf bps amount ≤ amount := by
  unfold feeOf
  have hmul : amount * bps ≤ amount * 10000 := by
    apply Nat.mul_le_mul_left
    exact h
  have hdiv : amount * bps / 10000 ≤ amount * 10000 / 10000 := by
    apply Nat.div_le_div_right
    exact hmul
  have hcan : amount * 10000 / 10000 = amount := by
    exact Nat.mul_div_cancel _ (by omega)
  omega

private theorem fee_add_net (bps amount : Nat) (h : feeOf bps amount ≤ amount) :
    feeOf bps amount + netOf bps amount = amount := by
  unfold netOf
  omega

private theorem net_div_mod (bps amount n : Nat) :
    recipientShare bps amount n * n + netOf bps amount % n = netOf bps amount := by
  unfold recipientShare
  have h := Nat.div_add_mod (netOf bps amount) n
  have hc : n * (netOf bps amount / n) = netOf bps amount / n * n :=
    Nat.mul_comm _ _
  rw [hc] at h
  exact h

private theorem amount_eq (bps amount n : Nat) (hle : feeOf bps amount ≤ amount)
    (hn : 0 < n) :
    n * recipientShare bps amount n + feeCredit bps amount n = amount := by
  unfold feeCredit
  have h1 := fee_add_net bps amount hle
  have h2 := net_div_mod bps amount n
  have hcomm : n * recipientShare bps amount n = recipientShare bps amount n * n :=
    Nat.mul_comm _ _
  omega

private theorem len_pos_of_ne_nil {α : Type} (l : List α) (h : l ≠ []) : 0 < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => exact Nat.zero_lt_succ _

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · have h2 := ok_state_of_valid s r hv
    have ha_mem : a ∈ s.accounts := by
      have hacc : (step s r).2.accounts = s.accounts := by rw [h2]
      rw [hacc] at ha
      exact ha
    have hb := hnn a ha_mem
    have hbal : (step s r).2.balance a = expectedBalance s r a := by rw [h2]
    rw [hbal]
    obtain ⟨_, _, _, _, _, hsrc, hfeeNR, hfeeNeSrc, _, _, _, _, hle, _⟩ := hv
    unfold expectedBalance
    by_cases hASrc : a = r.source
    · have eSrc : (if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) :=
        if_pos hASrc
      have hNotRec : a ∉ r.recipients := by rw [hASrc]; exact hsrc
      have eRec : (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
        if_neg hNotRec
      have hNotFee : ¬ (a = s.feeAccount) := by
        intro heq
        apply hfeeNeSrc
        rw [← heq, hASrc]
      have eFee : (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
        if_neg hNotFee
      rw [eSrc, eRec, eFee]
      have hASrc' : s.balance a = s.balance r.source := by rw [hASrc]
      omega
    · have eSrc : (if a = r.source then (r.amount : Int) else 0) = 0 :=
        if_neg hASrc
      rw [eSrc]
      by_cases hARec : a ∈ r.recipients
      · have eRec : (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
            = (recipientShare s.feeBps r.amount r.recipients.length : Int) :=
            if_pos hARec
        have hNotFee : ¬ (a = s.feeAccount) := by
          intro heq
          rw [heq] at hARec
          exact hfeeNR hARec
        have eFee : (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
          if_neg hNotFee
        rw [eRec, eFee]
        omega
      · have eRec : (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
          if_neg hARec
        rw [eRec]
        by_cases hAFee : a = s.feeAccount
        · have eFee : (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)
              = (feeCredit s.feeBps r.amount r.recipients.length : Int) :=
              if_pos hAFee
          rw [eFee]
          omega
        · have eFee : (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
            if_neg hAFee
          rw [eFee]
          omega
  · have h2 := rej_state_of_invalid s r hv
    have hacc : (step s r).2.accounts = s.accounts := by rw [h2]
    rw [hacc] at ha
    have hbal : (step s r).2.balance a = s.balance a := by rw [h2]
    rw [hbal]
    exact hnn a ha

theorem req_equal_shares : EqualShares step := by
  intro s r hok x hx
  have hv := valid_of_ok s r hok
  have h2 := ok_state_of_valid s r hv
  obtain ⟨_, _, _, _, _, hsrc, hfeeNR, _, _, _, _, _, _, _⟩ := hv
  have hxSrc : ¬ (x = r.source) := by
    intro heq
    rw [heq] at hx
    exact hsrc hx
  have hxFee : ¬ (x = s.feeAccount) := by
    intro heq
    rw [heq] at hx
    exact hfeeNR hx
  have hbal : (step s r).2.balance x = expectedBalance s r x := by rw [h2]
  rw [hbal]
  unfold expectedBalance
  have e1 : (if x = r.source then (r.amount : Int) else 0) = 0 := if_neg hxSrc
  have e2 : (if x ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
      = (recipientShare s.feeBps r.amount r.recipients.length : Int) := if_pos hx
  have e3 : (if x = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
    if_neg hxFee
  rw [e1, e2, e3]
  omega

theorem req_fee_collected : FeeCollected step := by
  intro s r hok
  have hv := valid_of_ok s r hok
  have h2 := ok_state_of_valid s r hv
  obtain ⟨_, _, _, _, _, _, hfeeNR, hfeeNeSrc, _, _, _, _, _, _⟩ := hv
  have hFeeSrc : ¬ (s.feeAccount = r.source) := hfeeNeSrc
  have hFeeRec : s.feeAccount ∉ r.recipients := hfeeNR
  have hbal : (step s r).2.balance s.feeAccount = expectedBalance s r s.feeAccount := by rw [h2]
  rw [hbal]
  unfold expectedBalance
  have e1 : (if s.feeAccount = r.source then (r.amount : Int) else 0) = 0 := if_neg hFeeSrc
  have e2 : (if s.feeAccount ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
    if_neg hFeeRec
  have e3 : (if s.feeAccount = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)
      = (feeCredit s.feeBps r.amount r.recipients.length : Int) := if_pos rfl
  rw [e1, e2, e3]
  omega

private theorem cast_add (a b : Nat) : (((a + b : Nat)) : Int) = (a : Int) + (b : Int) := by
  omega

private theorem sumOver_zero (l : List Nat) :
    sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sumOver_cons, ih]

private theorem sumOver_const_nat (t : List Nat) (k : Nat) :
    sumOver t (fun _ => ((k : Nat) : Int)) = ((((t.length * k : Nat))) : Int) := by
  induction t with
  | nil => simp
  | cons a l ih =>
    simp only [sumOver_cons, ih, List.length_cons]
    have hNat : (l.length + 1) * k = l.length * k + k := by
      rw [Nat.add_mul, Nat.one_mul]
    have hcast : ((((l.length + 1) * k : Nat)) : Int)
        = ((((l.length * k : Nat))) : Int) + ((k : Nat) : Int) := by
      rw [hNat, cast_add]
    rw [hcast]
    omega

private theorem sumOver_indicator (l t : List Nat) (c : Int)
    (hl : l.Nodup) (ht : t.Nodup) (hsub : ∀ x ∈ t, x ∈ l) :
    sumOver l (fun a => if a ∈ t then c else 0) = sumOver t (fun _ => c) := by
  induction t with
  | nil =>
    simp only [sumOver_nil]
    have h0 : ∀ a ∈ l, (if a ∈ ([] : List Nat) then c else 0) = 0 := by
      intro a _
      simp
    rw [sumOver_congr l _ _ h0]
    exact sumOver_zero l
  | cons y ys ih =>
    have ht_cons : (y :: ys).Nodup := ht
    rw [List.nodup_cons] at ht_cons
    obtain ⟨hynotin, hys_nodup⟩ := ht_cons
    have hsub_ys : ∀ z ∈ ys, z ∈ l := fun z hz => hsub z (List.mem_cons_of_mem y hz)
    have ih' : sumOver l (fun a => if a ∈ ys then c else 0) = sumOver ys (fun _ => c) :=
      ih hys_nodup hsub_ys
    have hsplit : ∀ a ∈ l, (if a ∈ y :: ys then c else 0)
        = (if a = y then c else 0) + (if a ∈ ys then c else 0) := by
      intro a _
      by_cases h1 : a = y
      · subst h1
        simp [hynotin]
      · have hmem : (a ∈ y :: ys) = (a ∈ ys) := by simp [h1]
        simp [hmem, h1]
    have hsum : sumOver l (fun a => if a ∈ y :: ys then c else 0)
        = sumOver l (fun a => if a = y then c else 0)
          + sumOver l (fun a => if a ∈ ys then c else 0) := by
      calc sumOver l (fun a => if a ∈ y :: ys then c else 0)
          = sumOver l (fun a => (if a = y then c else 0) + (if a ∈ ys then c else 0)) :=
            sumOver_congr _ _ _ hsplit
        _ = sumOver l (fun a => if a = y then c else 0)
              + sumOver l (fun a => if a ∈ ys then c else 0) :=
            sumOver_add _ _ _
    have hy_mem : y ∈ l := hsub y (by simp)
    have hite : sumOver l (fun a => if a = y then c else 0) = c := by
      rw [sumOver_ite_eq hl y c]
      simp [hy_mem]
    rw [hsum, hite, ih']
    simp only [sumOver_cons]

private theorem sum_expected (s : State) (r : Request) (hv : ValidPayout s r) :
    sumOver s.accounts (expectedBalance s r)
      = sumOver s.accounts s.balance - (r.amount : Int)
        + ((((r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length : Nat))) : Int)
        + ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) := by
  obtain ⟨hnodup, _, _, _, hrec_nodup, _, _, _, hsrcMem, hfeeMem, hsub, _, _, _⟩ := hv
  have hexp : ∀ a ∈ s.accounts, expectedBalance s r a
      = s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
        + (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) := by
    intro a _
    rfl
  have hrewrite : sumOver s.accounts (expectedBalance s r)
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
        + (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)) :=
    sumOver_congr _ _ _ hexp
  rw [hrewrite]
  have hA : sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
        + (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
        + sumOver s.accounts (fun a => (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)) :=
    sumOver_add _ _ _
  have hB : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        + sumOver s.accounts (fun a => (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)) :=
    sumOver_add _ _ _
  have hC : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) :=
    sumOver_sub _ _ _
  rw [hA, hB, hC]
  have g1 : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) = (r.amount : Int) := by
    rw [sumOver_ite_eq hnodup r.source (r.amount : Int)]
    simp [hsrcMem]
  have g3 : sumOver s.accounts (fun a => (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
      = ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) := by
    rw [sumOver_ite_eq hnodup s.feeAccount _]
    simp [hfeeMem]
  have g2 : sumOver s.accounts (fun a => (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
      = sumOver r.recipients (fun _ => ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int)) := by
    apply sumOver_indicator
    exact hnodup
    exact hrec_nodup
    exact hsub
  rw [g1, g3, g2, sumOver_const_nat]

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv := valid_of_ok s r hok
  have h2 := ok_state_of_valid s r hv
  have hv_full : ValidPayout s r := hv
  have hsum := sum_expected s r hv_full
  obtain ⟨hnodup, hbps, hpos, hne, hrec_nodup, hsrc, hfeeNR, hfeeNe, hsrcMem, hfeeMem, hsub, hauth, hle, hnotin⟩ := hv
  have hfee_le : feeOf s.feeBps r.amount ≤ r.amount := fee_le_amount s.feeBps r.amount hbps
  have hne_pos : 0 < r.recipients.length := len_pos_of_ne_nil _ hne
  have hamt : r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length
      + feeCredit s.feeBps r.amount r.recipients.length = r.amount :=
    amount_eq s.feeBps r.amount r.recipients.length hfee_le hne_pos
  have hcast : ((((r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length
      + feeCredit s.feeBps r.amount r.recipients.length : Nat))) : Int) = (r.amount : Int) := by
    rw [hamt]
  have hsplit : ((((r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length
      + feeCredit s.feeBps r.amount r.recipients.length : Nat))) : Int)
      = ((((r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length : Nat))) : Int)
        + (((feeCredit s.feeBps r.amount r.recipients.length : Nat)) : Int) :=
    cast_add _ _
  have hamtI : ((((r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length : Nat))) : Int)
      + ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) = (r.amount : Int) := by
    omega
  unfold total
  have hacc : (step s r).2.accounts = s.accounts := by rw [h2]
  rw [hacc]
  have hbal : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
    intro a
    rw [h2]
  have hcongr : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (expectedBalance s r) :=
    sumOver_congr _ _ _ (fun a _ => hbal a)
  rw [hcongr, hsum]
  omega

end FeePayout
