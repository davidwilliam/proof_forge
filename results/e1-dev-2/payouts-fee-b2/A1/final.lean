import FeePayout.Spec
import FeePayout.Lemmas
namespace FeePayout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout
  infer_instance

def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem sumOver_zero' (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem recSumHelper (sh : Nat) (accts : List Nat) (hNodup : accts.Nodup) :
    ∀ (R : List Nat), R.Nodup → (∀ x ∈ R, x ∈ accts) →
      sumOver accts (fun a => (if a ∈ R then (sh : Int) else 0)) = (R.length : Int) * (sh : Int) := by
  intro R
  induction R with
  | nil =>
    intro _ _
    simp [sumOver_zero']
  | cons x xs ih =>
    intro hnd hsub
    have hnd1 : x ∉ xs := by
      have h := List.nodup_cons.mp hnd
      exact h.1
    have hnd2 : xs.Nodup := by
      have h := List.nodup_cons.mp hnd
      exact h.2
    have hxmem : x ∈ accts := hsub x (by simp)
    have hxsSub : ∀ y ∈ xs, y ∈ accts := fun y hy => hsub y (by simp [hy])
    have ih' := ih hnd2 hxsSub
    have hsplit : (fun a : Nat => (if a ∈ x :: xs then (sh : Int) else 0))
        = (fun a => (if a = x then (sh : Int) else 0) + (if a ∈ xs then (sh : Int) else 0)) := by
      funext a
      by_cases hax : a = x
      · subst hax
        simp [hnd1]
      · simp [hax]
    rw [hsplit, sumOver_add]
    have h1 : sumOver accts (fun a => (if a = x then (sh : Int) else 0)) = (sh : Int) := by
      have h0 := sumOver_ite_eq hNodup x ((sh : Int))
      simp [hxmem] at h0
      exact h0
    rw [h1, ih']
    have hlen : ((List.length (x :: xs) : Nat) : Int) = (xs.length : Int) + 1 := by simp
    have hcast : ((((x :: xs).length : Nat)) : Int) * (sh : Int) = ((xs.length : Nat) : Int) * (sh : Int) + (sh : Int) := by
      rw [hlen, Int.add_mul, Int.one_mul]
    rw [hcast]
    ac_rfl

theorem arithFrag2 (_tot amt fee net n sh rem fc : Nat)
    (hAmt : fee + net = amt) (hNet : n * sh + rem = net) (hFc : fc = fee + rem)
    (totI : Int) :
    totI - (amt : Int) + (n : Int) * (sh : Int) + (fc : Int) = totI := by
  have h1 : (((fee + net : Nat)) : Int) = ((amt : Nat) : Int) := by rw [hAmt]
  have h2 : (((n * sh + rem : Nat)) : Int) = ((net : Nat) : Int) := by rw [hNet]
  have h3 : (((fee + rem : Nat)) : Int) = ((fc : Nat) : Int) := by rw [hFc]
  simp at h1 h2 h3
  omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  by_cases h : ValidPayout s r
  · exact h.2.2.2.2.2.2.2.2.2.2.2.1
  · unfold step at hok
    simp [h] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases h : ValidPayout s r
  · have hstep : step s r = (.ok, { s with
        balance := fun a => expectedBalance s r a,
        applied := r.txId :: s.applied }) := by
      unfold step
      simp [h]
    rw [hstep]
    exact ⟨rfl, rfl, rfl, rfl, fun a => rfl⟩
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [h]
    rw [hstep] at hok
    simp at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases h : ValidPayout s r
  · have hstep : step s r = (.ok, { s with
        balance := fun a => expectedBalance s r a,
        applied := r.txId :: s.applied }) := by
      unfold step
      simp [h]
    have happ : (step s r).2.applied = r.txId :: s.applied := by rw [hstep]
    have hmem : r.txId ∈ (step s r).2.applied := by rw [happ]; simp
    have hn : ¬ ValidPayout (step s r).2 r := by
      intro hv
      have hf := hv.2.2.2.2.2.2.2.2.2.2.2.2.2
      exact hf hmem
    have hiff : ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
      intro x
      rw [happ]
      simp
    exact ⟨hiff, req_invalid_noop _ _ hn⟩
  · have hstep : step s r = (.rejected, s) := req_invalid_noop s r h
    rw [hstep] at hok
    simp at hok

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases h : ValidPayout s r
  · obtain ⟨hNodup, hBps, hPos, hNe, hRecNodup, hSrcNot, hFeeNot, hFeeNe, hSrcMem, hFeeMem, hSub, hAuth, hBal, hFresh⟩ := h
    have hok : (step s r).1 = .ok := req_valid_succeeds s r ⟨hNodup, hBps, hPos, hNe, hRecNodup, hSrcNot, hFeeNot, hFeeNe, hSrcMem, hFeeMem, hSub, hAuth, hBal, hFresh⟩
    have heff := req_effects s r hok
    have hacc : (step s r).2.accounts = s.accounts := heff.1
    have hbal_all : ∀ b, (step s r).2.balance b = expectedBalance s r b := heff.2.2.2.2
    have hmem : a ∈ s.accounts := by rw [← hacc]; exact ha
    have hbal : (step s r).2.balance a = expectedBalance s r a := hbal_all a
    rw [hbal]
    unfold expectedBalance
    have h0 : 0 ≤ s.balance a := hnn a hmem
    by_cases hasrc : a = r.source
    · subst hasrc
      have e1 : (if r.source ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
        if_neg hSrcNot
      have e2 : (if r.source = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
        if_neg (Ne.symm hFeeNe)
      have e3 : (if r.source = r.source then (r.amount : Int) else 0) = (r.amount : Int) :=
        if_pos rfl
      rw [e1, e2, e3]
      omega
    · by_cases hafe : a = s.feeAccount
      · subst hafe
        have e1 : (if s.feeAccount ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
          if_neg hFeeNot
        have e2 : (if s.feeAccount = r.source then (r.amount : Int) else 0) = 0 :=
          if_neg hFeeNe
        have e3 : (if s.feeAccount = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)
            = (feeCredit s.feeBps r.amount r.recipients.length : Int) :=
          if_pos rfl
        rw [e1, e2, e3]
        have hfc : 0 ≤ (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
          exact_mod_cast Nat.zero_le _
        omega
      · have e2 : (if a = r.source then (r.amount : Int) else 0) = 0 := if_neg hasrc
        have e3 : (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 := if_neg hafe
        rw [e2, e3]
        by_cases hm : a ∈ r.recipients
        · have e1 : (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
              = (recipientShare s.feeBps r.amount r.recipients.length : Int) := if_pos hm
          rw [e1]
          have hs : 0 ≤ (recipientShare s.feeBps r.amount r.recipients.length : Int) := by
            exact_mod_cast Nat.zero_le _
          omega
        · have e1 : (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 := if_neg hm
          rw [e1]
          omega
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [h]
    have hacc : (step s r).2.accounts = s.accounts := by simp [hstep]
    have hbal2 : (step s r).2.balance = s.balance := by simp [hstep]
    rw [hacc] at ha
    rw [hbal2]
    exact hnn a ha

theorem req_equal_shares : EqualShares step := by
  intro s r hok x hx
  by_cases h : ValidPayout s r
  · obtain ⟨hNodup, hBps, hPos, hNe, hRecNodup, hSrcNot, hFeeNot, hFeeNe, hSrcMem, hFeeMem, hSub, hAuth, hBal, hFresh⟩ := h
    have heff := req_effects s r hok
    have hbal : (step s r).2.balance x = expectedBalance s r x := heff.2.2.2.2 x
    rw [hbal]
    unfold expectedBalance
    have hxSrc : x ≠ r.source := by
      intro heq
      subst heq
      exact hSrcNot hx
    have hxFee : x ≠ s.feeAccount := by
      intro heq
      subst heq
      exact hFeeNot hx
    have e1 : (if x = r.source then (r.amount : Int) else 0) = 0 := if_neg hxSrc
    have e2 : (if x ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
        = (recipientShare s.feeBps r.amount r.recipients.length : Int) := if_pos hx
    have e3 : (if x = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 := if_neg hxFee
    rw [e1, e2, e3]
    omega
  · have hstep : step s r = (.rejected, s) := req_invalid_noop s r h
    rw [hstep] at hok
    simp at hok

theorem req_fee_collected : FeeCollected step := by
  intro s r hok
  by_cases h : ValidPayout s r
  · obtain ⟨hNodup, hBps, hPos, hNe, hRecNodup, hSrcNot, hFeeNot, hFeeNe, hSrcMem, hFeeMem, hSub, hAuth, hBal, hFresh⟩ := h
    have heff := req_effects s r hok
    have hbal : (step s r).2.balance s.feeAccount = expectedBalance s r s.feeAccount := heff.2.2.2.2 s.feeAccount
    rw [hbal]
    unfold expectedBalance
    have e1 : (if s.feeAccount = r.source then (r.amount : Int) else 0) = 0 := if_neg hFeeNe
    have e2 : (if s.feeAccount ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 := if_neg hFeeNot
    have e3 : (if s.feeAccount = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)
        = (feeCredit s.feeBps r.amount r.recipients.length : Int) := if_pos rfl
    rw [e1, e2, e3]
    omega
  · have hstep : step s r = (.rejected, s) := req_invalid_noop s r h
    rw [hstep] at hok
    simp at hok

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases h : ValidPayout s r
  · obtain ⟨hNodup, hBps, hPos, hNe, hRecNodup, hSrcNot, hFeeNot, hFeeNe, hSrcMem, hFeeMem, hSub, hAuth, hBal, hFresh⟩ := h
    have heff := req_effects s r hok
    have hacc : (step s r).2.accounts = s.accounts := heff.1
    have hbal_all : ∀ a, (step s r).2.balance a = expectedBalance s r a := heff.2.2.2.2
    have hcongr : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (fun a => expectedBalance s r a) :=
      sumOver_congr _ _ _ (fun a _ => hbal_all a)
    have h_total2 : total (step s r).2 = sumOver s.accounts (fun a => expectedBalance s r a) := by
      unfold total
      rw [hacc]
      exact hcongr
    have h_src : sumOver s.accounts (fun a : Nat => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
      have h0 := sumOver_ite_eq hNodup r.source ((r.amount : Int))
      simp [hSrcMem] at h0
      exact h0
    have h_fee : sumOver s.accounts (fun a : Nat => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
      have h0 := sumOver_ite_eq hNodup s.feeAccount ((feeCredit s.feeBps r.amount r.recipients.length : Int))
      simp [hFeeMem] at h0
      exact h0
    have h_rec : sumOver s.accounts (fun a : Nat => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = ((r.recipients.length : Nat) : Int) * ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) :=
      recSumHelper (recipientShare s.feeBps r.amount r.recipients.length) s.accounts hNodup r.recipients hRecNodup hSub
    have hsum : sumOver s.accounts (fun a => expectedBalance s r a) = total s := by
      unfold total
      have h_eq : sumOver s.accounts (fun a => expectedBalance s r a)
          = sumOver s.accounts s.balance - (r.amount : Int) + ((r.recipients.length : Nat) : Int) * ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) + ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) := by
        unfold expectedBalance
        rw [sumOver_add, sumOver_add, sumOver_sub, h_src, h_rec, h_fee]
      have hmul_le : r.amount * s.feeBps ≤ r.amount * 10000 :=
        Nat.mul_le_mul_left r.amount hBps
      have hdiv_le : r.amount * s.feeBps / 10000 ≤ r.amount * 10000 / 10000 :=
        Nat.div_le_div_right hmul_le
      have hcancel : r.amount * 10000 / 10000 = r.amount :=
        Nat.mul_div_cancel _ (by omega)
      rw [hcancel] at hdiv_le
      have hfee_le : feeOf s.feeBps r.amount ≤ r.amount := by
        simpa [feeOf] using hdiv_le
      have hFN : feeOf s.feeBps r.amount + netOf s.feeBps r.amount = r.amount := by
        simpa [netOf] using Nat.add_sub_of_le hfee_le
      have hDiv : r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length + netOf s.feeBps r.amount % r.recipients.length = netOf s.feeBps r.amount :=
        Nat.div_add_mod _ _
      have hFc : feeCredit s.feeBps r.amount r.recipients.length = feeOf s.feeBps r.amount + netOf s.feeBps r.amount % r.recipients.length :=
        rfl
      have hFNc : ((feeOf s.feeBps r.amount : Nat) : Int) + ((netOf s.feeBps r.amount : Nat) : Int) = ((r.amount : Nat) : Int) := by
        exact_mod_cast hFN
      have hDivc : (r.recipients.length : Int) * ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) + ((netOf s.feeBps r.amount % r.recipients.length : Nat) : Int) = ((netOf s.feeBps r.amount : Nat) : Int) := by
        exact_mod_cast hDiv
      have hFcc : ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) = ((feeOf s.feeBps r.amount : Nat) : Int) + ((netOf s.feeBps r.amount % r.recipients.length : Nat) : Int) := by
        exact_mod_cast hFc
      omega
    rw [h_total2, hsum]
  · have hstep : step s r = (.rejected, s) := req_invalid_noop s r h
    have h2 : (step s r).2 = s := by simp [hstep]
    exact congrArg total h2

end FeePayout
