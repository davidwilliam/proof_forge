import FeePayout.Spec
import FeePayout.Lemmas
namespace FeePayout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem my_test_thm : True := trivial

theorem my_lemma_test_aux : 1 + 1 = 2 := rfl

theorem sumOver_zero (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem check_lemmas : True := trivial
#check @Nat.mul_div_cancel
#check @Nat.div_le_div_right
#check @Nat.div_add_mod
#check @Nat.mul_div_cancel_left

theorem tmp_sig_test : True := trivial
#check (Nat.div_le_div_right)
#check (Nat.mul_le_mul)
#check (Nat.mul_div_cancel_left)
#check (Nat.div_add_mod)
#check (Nat.mod_add_div)

theorem probe1 (a b : Nat) (h : a ≤ b) : a / 10000 ≤ b / 10000 := Nat.div_le_div_right h

theorem fee_le_aux (bps amount : Nat) (h : bps ≤ 10000) : amount * bps ≤ amount * 10000 :=
  Nat.mul_le_mul_left amount h

theorem sumOver_zero_aux (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem sumOver_zero' (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem probeSigs : True := trivial
#check @Nat.mul_le_mul_left
#check @Nat.div_le_div_right
#check @Nat.mul_div_cancel_left
#check @Nat.div_add_mod
#check @Nat.mod_add_div
#check @Nat.mul_div_cancel

theorem fee_le_amount (bps amount : Nat) (h : bps ≤ 10000) : feeOf bps amount ≤ amount := by
  unfold feeOf
  have h1 : amount * bps ≤ amount * 10000 := Nat.mul_le_mul_left amount h
  omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization  : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hv : ValidPayout s r
  · exact hv.2.2.2.2.2.2.2.2.2.2.2.1
  · simp [hv] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step
      simp [hv]
    rw [hstep]
    exact ⟨rfl, rfl, rfl, rfl, fun a => rfl⟩
  · unfold step at h
    simp [hv] at h

theorem req_idempotency    : Idempotent step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step; simp [hv]
    rw [hstep]
    constructor
    · intro x
      simp only
      exact List.mem_cons
    · have hNotValid : ¬ ValidPayout { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } r := by
        intro hcon
        obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_, hmem⟩ := hcon
        exact hmem (by simp)
      have hstep2 : step { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } r
          = (.rejected, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
        unfold step; simp [hNotValid]
      exact hstep2
  · unfold step at h
    simp [hv] at h

theorem req_nonnegative    : NonNegative step := by
  intro s r hpos a ha
  have hstep : step s r = (if ValidPayout s r then
    (.ok, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State))
    else ((.rejected, s) : Outcome × State)) := rfl
  by_cases hv : ValidPayout s r
  · have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      rw [hstep, if_pos hv]
    have ha' : a ∈ s.accounts := by rw [h2] at ha; simpa using ha
    rw [h2]
    show 0 ≤ ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State).balance a
    show 0 ≤ expectedBalance s r a
    obtain ⟨hnodup, hbps, hpos_amt, hne, hrnodup, hsrc_notin, hfee_notin, hfee_ne_src,
      hsrc_mem, hfee_mem, hrec_mem, hauth, hbal, htx⟩ := hv
    have hB : 0 ≤ s.balance a := hpos a ha'
    unfold expectedBalance
    by_cases hsrc : a = r.source
    · subst hsrc
      have hne2 : r.source ≠ s.feeAccount := fun h => hfee_ne_src h.symm
      rw [if_pos rfl, if_neg hsrc_notin, if_neg hne2]
      omega
    · rw [if_neg hsrc]
      by_cases h1 : a ∈ r.recipients
      · by_cases h2 : a = s.feeAccount
        · rw [if_pos h1, if_pos h2]; omega
        · rw [if_pos h1, if_neg h2]; omega
      · by_cases h2 : a = s.feeAccount
        · rw [if_neg h1, if_pos h2]; omega
        · rw [if_neg h1, if_neg h2]; omega
  · have h2 : (step s r).2 = s := by rw [hstep, if_neg hv]
    rw [h2] at ha ⊢
    exact hpos a ha

theorem req_equal_shares   : EqualShares step := by
  intro s r h x hx
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step; simp [hv]
    obtain ⟨hnodup, hbps, hpos_amt, hne, hrnodup, hsrc_notin, hfee_notin, hfee_ne_src,
      hsrc_mem, hfee_mem, hrec_mem, hauth, hbal, htx⟩ := hv
    have hsrc_ne : x ≠ r.source := by
      intro heq; subst heq
      exact hsrc_notin hx
    have hfee_ne : x ≠ s.feeAccount := by
      intro heq; subst heq
      exact hfee_notin hx
    have h1 : (step s r).2.balance x - s.balance x = (recipientShare s.feeBps r.amount r.recipients.length : Int) := by
      rw [hstep]
      show expectedBalance s r x - s.balance x = _
      unfold expectedBalance
      rw [if_neg hsrc_ne, if_pos hx, if_neg hfee_ne]
      omega
    exact h1
  · unfold step at h
    simp [hv] at h

theorem req_fee_collected  : FeeCollected step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step; simp [hv]
    obtain ⟨hnodup, hbps, hpos_amt, hne, hrnodup, hsrc_notin, hfee_notin, hfee_ne_src,
      hsrc_mem, hfee_mem, hrec_mem, hauth, hbal, htx⟩ := hv
    have h1 : (step s r).2.balance s.feeAccount - s.balance s.feeAccount = (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
      rw [hstep]
      show expectedBalance s r s.feeAccount - s.balance s.feeAccount = _
      unfold expectedBalance
      rw [if_neg hfee_ne_src, if_neg hfee_notin, if_pos rfl]
      omega
    exact h1
  · unfold step at h
    simp [hv] at h

theorem req_conservation   : Conserves step := sorry

end FeePayout
