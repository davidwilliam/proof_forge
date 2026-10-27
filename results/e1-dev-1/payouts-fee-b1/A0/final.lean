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
  else (Outcome.rejected, s)

/- Helpers -/

private theorem ok_of_valid (s : State) (r : Request) (h : ValidPayout s r) :
    (step s r).1 = Outcome.ok := by
  unfold step; simp [h]

private theorem eq_rejected_of_invalid (s : State) (r : Request) (h : ¬ ValidPayout s r) :
    step s r = (Outcome.rejected, s) := by
  unfold step; simp [h]

private theorem valid_of_ok (s : State) (r : Request) (h : (step s r).1 = Outcome.ok) :
    ValidPayout s r := by
  have hem := Decidable.em (ValidPayout s r)
  cases hem with
  | inl hp => exact hp
  | inr hn =>
    have heq := eq_rejected_of_invalid s r hn
    rw [heq] at h
    simp at h

private theorem snd_of_valid (s : State) (r : Request) (h : ValidPayout s r) :
    (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
  unfold step; simp [h]

private theorem snd_of_invalid (s : State) (r : Request) (h : ¬ ValidPayout s r) :
    (step s r).2 = s := by
  have heq := eq_rejected_of_invalid s r h
  calc (step s r).2 = (Outcome.rejected, s).2 := by rw [heq]
    _ = s := rfl

private theorem feeOf_le_amount {bps amount : Nat} (h : bps ≤ 10000) :
    feeOf bps amount ≤ amount := by
  unfold feeOf
  have hmul : amount * bps ≤ amount * 10000 :=
    Nat.mul_le_mul_left amount h
  have hdiv : amount * bps / 10000 ≤ amount * 10000 / 10000 :=
    Nat.div_le_div_right hmul
  have heq : amount * 10000 / 10000 = amount :=
    Nat.mul_div_cancel amount (by omega)
  rw [heq] at hdiv
  exact hdiv

private theorem amount_eq_nat (bps amount n : Nat) (hbps : bps ≤ 10000) :
    n * recipientShare bps amount n + feeCredit bps amount n = amount := by
  unfold recipientShare feeCredit netOf feeOf at *
  have hle : amount * bps / 10000 ≤ amount := feeOf_le_amount hbps
  have hdm := Nat.mod_add_div (amount - amount * bps / 10000) n
  omega

private theorem amount_eq_int (s : State) (r : Request) (hbps : s.feeBps ≤ 10000) :
    (r.amount : Int) = (r.recipients.length : Int) * ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int)
      + ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) := by
  have hn : r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length
      + feeCredit s.feeBps r.amount r.recipients.length = r.amount :=
    amount_eq_nat s.feeBps r.amount r.recipients.length hbps
  omega

private theorem sumOver_zero (l : List Nat) :
    sumOver l (fun _ : Nat => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private theorem sumOver_mem_eq (accs recips : List Nat) (hacc : accs.Nodup)
    (hrec : recips.Nodup) (hsub : ∀ x ∈ recips, x ∈ accs) (c : Int) :
    sumOver accs (fun a => if a ∈ recips then c else 0) = (recips.length : Int) * c := by
  induction recips with
  | nil =>
    have hcongr : ∀ a ∈ accs, (if a ∈ ([] : List Nat) then c else 0) = (0 : Int) := by
      intro a _
      simp
    have h1 : sumOver accs (fun a => if a ∈ ([] : List Nat) then c else 0)
        = sumOver accs (fun _ : Nat => (0 : Int)) :=
      sumOver_congr accs _ _ hcongr
    have h2 : sumOver accs (fun _ : Nat => (0 : Int)) = 0 := sumOver_zero _
    rw [h1, h2]
    simp
  | cons y ys ih =>
    have hne : y ∉ ys := (List.nodup_cons.mp hrec).1
    have hrec2 : ys.Nodup := (List.nodup_cons.mp hrec).2
    have hy_in : y ∈ accs := hsub y (by simp)
    have hsub2 : ∀ x ∈ ys, x ∈ accs := fun x hx => hsub x (by simp [hx])
    have ih' := ih hrec2 hsub2
    have hpoint : ∀ a ∈ accs,
        (if a ∈ y :: ys then c else (0 : Int))
          = ((if a = y then c else 0) + (if a ∈ ys then c else 0)) := by
      intro a _
      by_cases hay : a = y
      · subst hay
        simp [hne]
      · have hmem : (a ∈ y :: ys) = (a ∈ ys) := by simp [hay]
        simp only [hmem, hay]
        by_cases hmem2 : a ∈ ys <;> simp [hmem2]
    rw [sumOver_congr accs _ _ hpoint, sumOver_add]
    have h1 : sumOver accs (fun a => if a = y then c else 0) = c := by
      have h := sumOver_ite_eq hacc y c
      rw [if_pos hy_in] at h
      exact h
    rw [h1, ih']
    have hlen : ((((y :: ys).length : Nat)) : Int) = (((ys.length : Nat)) : Int) + 1 := by simp
    rw [hlen, Int.add_mul, Int.one_mul]
    omega

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r h
  exact ok_of_valid s r h

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r h
  exact eq_rejected_of_invalid s r h

theorem req_authorization : AuthorizedOnly step := by
  unfold AuthorizedOnly
  intro s r hok
  have hv := valid_of_ok s r hok
  unfold ValidPayout at hv
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14⟩ := hv
  exact h12

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hok
  have hv := valid_of_ok s r hok
  have h2 := snd_of_valid s r hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [h2]
  · simp [h2]
  · simp [h2]
  · simp [h2]
  · intro a
    simp [h2]

theorem req_idempotency : Idempotent step := by
  unfold Idempotent
  intro s r hok
  have hv := valid_of_ok s r hok
  have h2 := snd_of_valid s r hv
  have hmem : r.txId ∈ (step s r).2.applied := by simp [h2]
  have hnvalid : ¬ ValidPayout (step s r).2 r := by
    intro hvalid
    unfold ValidPayout at hvalid
    obtain ⟨h1,h2',h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14⟩ := hvalid
    exact h14 hmem
  constructor
  · intro x
    simp [h2]
  · have heq := eq_rejected_of_invalid _ r hnvalid
    exact heq

theorem req_nonnegative : NonNegative step := by
  unfold NonNegative
  intro s r hnonneg a ha
  have hem := Decidable.em (ValidPayout s r)
  cases hem with
  | inl hv =>
    have h2 := snd_of_valid s r hv
    have ha' : a ∈ s.accounts := by rw [h2] at ha; exact ha
    have hbal2 : (step s r).2.balance a = expectedBalance s r a := by rw [h2]
    rw [hbal2]
    unfold ValidPayout at hv
    obtain ⟨hnd, hbps, hpos, hne, hndr, hsrc, hfee, hne2, hsrcin, hfeein, hsub, hauth, hbal, htx⟩ := hv
    have hbal_a : 0 ≤ s.balance a := hnonneg a ha'
    have hsrc_bal : (r.amount : Int) ≤ s.balance r.source := hbal
    by_cases hs : a = r.source
    · subst hs
      have hf0 : ¬ r.source = s.feeAccount := fun h => hne2 h.symm
      have hexp : expectedBalance s r r.source
          = s.balance r.source - (r.amount : Int) := by
        unfold expectedBalance
        rw [if_pos rfl, if_neg hsrc, if_neg hf0]
        omega
      rw [hexp]
      omega
    · by_cases hf : a = s.feeAccount
      · subst hf
        have hexp : expectedBalance s r s.feeAccount
            = s.balance s.feeAccount + ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) := by
          unfold expectedBalance
          rw [if_neg hne2, if_neg hfee, if_pos rfl]
          omega
        rw [hexp]
        have hfc : (0 : Int) ≤ ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) := by
          omega
        omega
      · by_cases hm : a ∈ r.recipients
        · have hexp : expectedBalance s r a
              = s.balance a + ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) := by
            unfold expectedBalance
            rw [if_neg hs, if_pos hm, if_neg hf]
            omega
          rw [hexp]
          have hsh : (0 : Int) ≤ ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) := by
            omega
          omega
        · have hexp : expectedBalance s r a = s.balance a := by
            unfold expectedBalance
            rw [if_neg hs, if_neg hm, if_neg hf]
            omega
          rw [hexp]
          exact hbal_a
  | inr hv =>
    have h2 := snd_of_invalid s r hv
    rw [h2] at ha ⊢
    exact hnonneg a ha

theorem req_equal_shares : EqualShares step := by
  unfold EqualShares
  intro s r hok x hx
  have hv := valid_of_ok s r hok
  have h2 := snd_of_valid s r hv
  unfold ValidPayout at hv
  obtain ⟨hnd, hbps, hpos, hne, hndr, hsrc, hfee, hne2, hsrcin, hfeein, hsub, hauth, hbal, htx⟩ := hv
  have hxs : x ≠ r.source := fun h => hsrc (h ▸ hx)
  have hxf : x ≠ s.feeAccount := fun h => hfee (h ▸ hx)
  have hbal_eq : (step s r).2.balance x = expectedBalance s r x := by
    rw [h2]
  rw [hbal_eq]
  have hexp : expectedBalance s r x
      = s.balance x + ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) := by
    unfold expectedBalance
    rw [if_neg hxs, if_pos hx, if_neg hxf]
    omega
  rw [hexp]
  omega

theorem req_fee_collected : FeeCollected step := by
  unfold FeeCollected
  intro s r hok
  have hv := valid_of_ok s r hok
  have h2 := snd_of_valid s r hv
  unfold ValidPayout at hv
  obtain ⟨hnd, hbps, hpos, hne, hndr, hsrc, hfee, hne2, hsrcin, hfeein, hsub, hauth, hbal, htx⟩ := hv
  have hbal_eq : (step s r).2.balance s.feeAccount = expectedBalance s r s.feeAccount := by
    rw [h2]
  rw [hbal_eq]
  have hexp : expectedBalance s r s.feeAccount
      = s.balance s.feeAccount + ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) := by
    unfold expectedBalance
    rw [if_neg hne2, if_neg hfee, if_pos rfl]
    omega
  rw [hexp]
  omega

theorem req_conservation : Conserves step := by
  unfold Conserves
  intro s r hok
  have hv := valid_of_ok s r hok
  have h2 := snd_of_valid s r hv
  unfold ValidPayout at hv
  obtain ⟨hnd, hbps, hpos, hne, hndr, hsrc, hfee, hne2, hsrcin, hfeein, hsub, hauth, hbal, htx⟩ := hv
  have htot : total (step s r).2 = sumOver s.accounts (fun a => expectedBalance s r a) := by
    unfold total
    rw [h2]
  rw [htot]
  have hS : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnd r.source ((r.amount : Int))
    rw [if_pos hsrcin] at h
    exact h
  have hF : sumOver s.accounts (fun a => if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
      = ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) := by
    have h := sumOver_ite_eq hnd s.feeAccount (((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int))
    rw [if_pos hfeein] at h
    exact h
  have hR : sumOver s.accounts (fun a => if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
      = (r.recipients.length : Int) * ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) :=
    sumOver_mem_eq s.accounts r.recipients hnd hndr hsub _
  have hamt := amount_eq_int s r hbps
  have hexp_congr : ∀ a ∈ s.accounts, expectedBalance s r a
      = ((s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
        + (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)) := by
    intro a _
    rfl
  rw [sumOver_congr s.accounts _ _ hexp_congr, sumOver_add]
  have hmid_congr : ∀ a ∈ s.accounts, (s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
      = ((s.balance a - (if a = r.source then (r.amount : Int) else 0))
        + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)) := by
    intro a _
    rfl
  have hmid : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
      = sumOver s.accounts s.balance - (r.amount : Int)
        + ((r.recipients.length : Int) * ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int)) := by
    rw [sumOver_congr s.accounts _ _ hmid_congr, sumOver_add, sumOver_sub, hS, hR]
  rw [hmid, hF]
  unfold total
  omega

end FeePayout
