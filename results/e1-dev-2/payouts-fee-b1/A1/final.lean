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

theorem req_effects_aux : True := trivial
#check @expectedBalance

theorem req_effects_final : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases h : ValidPayout s r
  · simp only [h, ↓reduceIte] at hok ⊢
    exact ⟨trivial, trivial, trivial, trivial, fun a => trivial⟩
  · simp only [h, ↓reduceIte] at hok
    simp at hok

theorem idem_aux1 (s : State) (r : Request) (h : ValidPayout s r) :
    (step s r).2.applied = r.txId :: s.applied := by
  unfold step
  simp only [h, ↓reduceIte]

theorem equal_shares_helper (s : State) (r : Request) (h : ValidPayout s r)
    (x : AccountId) (hx : x ∈ r.recipients) :
    expectedBalance s r x - s.balance x
      = (recipientShare s.feeBps r.amount r.recipients.length : Int) := by
  unfold expectedBalance
  obtain ⟨_, _, _, _, _, hsrc, hfee, hfeesrc, _, _, _, _, _, _⟩ := h
  have hxsrc : x ≠ r.source := fun heq => hsrc (heq ▸ hx)
  have hxfee : x ≠ s.feeAccount := fun heq => hfee (heq ▸ hx)
  have h1 : (if x = r.source then (r.amount : Int) else 0) = 0 := if_neg hxsrc
  have h2 : (if x ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
      = (recipientShare s.feeBps r.amount r.recipients.length : Int) := if_pos hx
  have h3 : (if x = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 := if_neg hxfee
  rw [h1, h2, h3]
  omega

theorem fee_collected_helper (s : State) (r : Request) (h : ValidPayout s r) :
    expectedBalance s r s.feeAccount - s.balance s.feeAccount
      = (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
  unfold expectedBalance
  obtain ⟨_, _, _, _, _, hsrc, hfee, hfeesrc, _, _, _, _, _, _⟩ := h
  have h1 : (if s.feeAccount = r.source then (r.amount : Int) else 0) = 0 := if_neg hfeesrc
  have h2 : (if s.feeAccount ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 := if_neg hfee
  have h3 : (if s.feeAccount = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)
      = (feeCredit s.feeBps r.amount r.recipients.length : Int) := if_pos rfl
  rw [h1, h2, h3]
  omega

theorem tmp1 (amount bps : Nat) (hbps : bps ≤ 10000) : amount * bps / 10000 ≤ amount := by
  have h1 : amount * bps ≤ amount * 10000 := Nat.mul_le_mul_left amount hbps
  have h2 : amount * bps / 10000 ≤ amount * 10000 / 10000 := Nat.div_le_div_right h1
  have h3 : amount * 10000 / 10000 = amount := Nat.mul_div_cancel amount (by decide)
  omega

theorem cast_add_test (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  simp

theorem cons_nat_arith4 (bps amount n : Nat) (hbps : bps ≤ 10000) :
    (n : Int) * (recipientShare bps amount n : Int) + (feeCredit bps amount n : Int) = (amount : Int) := by
  have hfee_le : amount * bps / 10000 ≤ amount := tmp1 amount bps hbps
  have hdm : n * ((amount - amount * bps / 10000) / n) + (amount - amount * bps / 10000) % n = amount - amount * bps / 10000 :=
    Nat.div_add_mod _ _
  have h2 : amount * bps / 10000 + (amount - amount * bps / 10000) = amount := Nat.add_sub_cancel' hfee_le
  have hNat : n * ((amount - amount * bps / 10000) / n) + (amount * bps / 10000 + (amount - amount * bps / 10000) % n) = amount := by omega
  have hNatI : ((n * ((amount - amount * bps / 10000) / n) + (amount * bps / 10000 + (amount - amount * bps / 10000) % n) : Nat) : Int) = ((amount : Nat) : Int) := by rw [hNat]
  simp at hNatI
  unfold recipientShare feeCredit netOf feeOf at *
  omega

theorem rec_ind_split (y : Nat) (Rs : List Nat) (c : Int) (hy : y ∉ Rs) (a : Nat) :
    (if a ∈ y :: Rs then c else 0) = (if a = y then c else 0) + (if a ∈ Rs then c else 0) := by
  simp only [List.mem_cons]
  by_cases hay : a = y
  · subst hay
    simp [hy]
  · simp [hay]

theorem zero_sum_test (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem probe1 (c : Int) : (0 : Int) * c = 0 := by simp

theorem probe2 (a b c : Int) : (a + b) * c = a * c + b * c := by simp [Int.add_mul]

theorem probe3 (a : Int) : (1 : Int) * a = a := by simp

theorem probe4 (n : Nat) (c : Int) : ((n : Int) + 1) * c = c + (n : Int) * c := by
  rw [Int.add_mul, Int.one_mul, Int.add_comm]

theorem sum_rec_indicator_aux2 (accounts Rs : List Nat) (c : Int) (hacc : accounts.Nodup)
    (hRs : Rs.Nodup) (hsub : ∀ x ∈ Rs, x ∈ accounts) :
    sumOver accounts (fun a => if a ∈ Rs then c else 0) = (Rs.length : Int) * c := by
  induction Rs generalizing accounts with
  | nil =>
    have h0 : sumOver accounts (fun a => if a ∈ ([] : List Nat) then c else 0) = sumOver accounts (fun _ => (0 : Int)) := by
      apply sumOver_congr
      intro a ha
      simp
    rw [h0, zero_sum_test, List.length_nil]
    simp
  | cons y Rs ih =>
    rw [List.nodup_cons] at hRs
    obtain ⟨hynot, hRs_nodup⟩ := hRs
    have hsub_tail : ∀ x ∈ Rs, x ∈ accounts := fun x hx => hsub x (by simp [hx])
    have hy_mem : y ∈ accounts := hsub y (by simp)
    have hsplit : ∀ a : Nat, (if a ∈ y :: Rs then c else 0) = (if a = y then c else 0) + (if a ∈ Rs then c else 0) := by
      intro a
      exact rec_ind_split y Rs c hynot a
    have hsum_split : sumOver accounts (fun a => if a ∈ y :: Rs then c else 0)
        = sumOver accounts (fun a => if a = y then c else 0) + sumOver accounts (fun a => if a ∈ Rs then c else 0) := by
      rw [← sumOver_add]
      apply sumOver_congr
      intro a ha
      rw [hsplit a]
    rw [hsum_split, sumOver_ite_eq hacc y c, if_pos hy_mem, ih accounts hacc hRs_nodup hsub_tail]
    simp only [List.length_cons]
    push_cast
    rw [Int.add_mul, Int.one_mul, Int.add_comm]

theorem hsplit1_probe (s : State) (r : Request) :
    sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0))
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) + sumOver s.accounts (fun a => (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)) + sumOver s.accounts (fun a => (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)) := by
  have hA := sumOver_add s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) (fun a => (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0))
  have hB := sumOver_add s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)) (fun a => (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0))
  rw [hB, hA]

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
  unfold step at hok
  by_cases h : ValidPayout s r
  · simp [h] at hok
    unfold ValidPayout at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hauth, _, _⟩ := h
    exact hauth
  · simp [h] at hok

theorem req_effects : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases h : ValidPayout s r
  · simp only [h, ↓reduceIte] at hok ⊢
    exact ⟨trivial, trivial, trivial, trivial, fun a => trivial⟩
  · simp only [h, ↓reduceIte] at hok
    simp at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hvalid : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · unfold step at hok
      simp [h] at hok
  have hstep2 : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
    unfold step
    simp [hvalid]
  have hsnd : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
    rw [hstep2]
  constructor
  · intro x
    rw [hsnd]
    simp
  · have hnotvalid2 : ¬ ValidPayout ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r := by
      intro hcon
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hmem⟩ := hcon
      simp at hmem
    have hrej2 : step ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r
        = (.rejected, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by
      unfold step
      simp [hnotvalid2]
    rw [← hsnd] at hrej2
    exact hrej2

theorem req_nonnegative : NonNegative step := by
  intro s r hnonneg a ha
  unfold step at ha ⊢
  by_cases h : ValidPayout s r
  · simp only [h, ↓reduceIte] at ha ⊢
    have ha_mem : a ∈ s.accounts := ha
    have hbal : 0 ≤ s.balance a := hnonneg a ha_mem
    have hshare_nonneg : (0 : Int) ≤ (recipientShare s.feeBps r.amount r.recipients.length : Int) := Int.ofNat_nonneg _
    have hfee_nonneg : (0 : Int) ≤ (feeCredit s.feeBps r.amount r.recipients.length : Int) := Int.ofNat_nonneg _
    obtain ⟨_, _, _, _, _, hsrc_not, hfee_not, hfee_ne_src, _, _, _, _, hle, _⟩ := h
    unfold expectedBalance
    by_cases ha_src : a = r.source
    · subst ha_src
      have e1 : (if (r.source ∈ r.recipients) then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
        if_neg hsrc_not
      have e2 : (if (r.source = s.feeAccount) then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 := by
        apply if_neg
        exact Ne.symm hfee_ne_src
      simp only [if_true, e1, e2]
      omega
    · by_cases ha_fee : a = s.feeAccount
      · subst ha_fee
        have e1 : (if (s.feeAccount = r.source) then (r.amount : Int) else 0) = 0 :=
          if_neg hfee_ne_src
        have e2 : (if (s.feeAccount ∈ r.recipients) then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
          if_neg hfee_not
        simp only [e1, e2, if_true]
        omega
      · by_cases ha_mem2 : a ∈ r.recipients
        · have e1 : (if (a = r.source) then (r.amount : Int) else 0) = 0 := if_neg ha_src
          have e2 : (if (a ∈ r.recipients) then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
              = (recipientShare s.feeBps r.amount r.recipients.length : Int) := if_pos ha_mem2
          have e3 : (if (a = s.feeAccount) then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
            if_neg ha_fee
          rw [e1, e2, e3]
          omega
        · have e1 : (if (a = r.source) then (r.amount : Int) else 0) = 0 := if_neg ha_src
          have e2 : (if (a ∈ r.recipients) then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
            if_neg ha_mem2
          have e3 : (if (a = s.feeAccount) then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
            if_neg ha_fee
          rw [e1, e2, e3]
          omega
  · simp only [h, ↓reduceIte] at ha ⊢
    exact hnonneg a ha

theorem req_equal_shares : EqualShares step := by
  intro s r hok x hx
  unfold step at hok ⊢
  by_cases h : ValidPayout s r
  · simp only [h, ↓reduceIte] at hok ⊢
    exact equal_shares_helper s r h x hx
  · simp [h] at hok

theorem req_fee_collected  : FeeCollected step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases h : ValidPayout s r
  · simp only [h, ↓reduceIte] at hok ⊢
    exact fee_collected_helper s r h
  · simp [h] at hok

theorem req_conservation : Conserves step := by
  intro s r hok
  have hvalid : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · unfold step at hok
      simp [h] at hok
  have hstep2 : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
    unfold step
    simp [hvalid]
  have hsnd : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
    rw [hstep2]
  obtain ⟨hNodup, hbps, hamt_pos, hne, hRnodup, hsrc_not, hfee_not, hfee_ne_src, hsrc_mem, hfee_mem, hsub_acc, hauth, hle, htx⟩ := hvalid
  have hconsv : sumOver s.accounts (fun a => expectedBalance s r a) = sumOver s.accounts s.balance := by
    have hexp_congr : ∀ a ∈ s.accounts, (expectedBalance s r a : Int)
        = (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) := by
      intro a ha
      unfold expectedBalance
      omega
    rw [sumOver_congr s.accounts _ _ hexp_congr]
    rw [hsplit1_probe s r]
    have hsrc_sum : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - (r.amount : Int) := by
      rw [sumOver_sub]
      have hite : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
        rw [sumOver_ite_eq hNodup r.source (r.amount : Int), if_pos hsrc_mem]
      rw [hite]
    have hrec_sum : sumOver s.accounts (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
        = (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) := by
      exact sum_rec_indicator_aux2 s.accounts r.recipients _ hNodup hRnodup hsub_acc
    have hfee_sum : sumOver s.accounts (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)
        = (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
      rw [sumOver_ite_eq hNodup s.feeAccount _, if_pos hfee_mem]
    rw [hsrc_sum, hrec_sum, hfee_sum]
    have harith : (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) + (feeCredit s.feeBps r.amount r.recipients.length : Int) = (r.amount : Int) := by
      exact cons_nat_arith4 s.feeBps r.amount r.recipients.length hbps
    omega
  show total (step s r).2 = total s
  rw [hsnd]
  show total { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } = total s
  unfold total
  simp only
  exact hconsv

end FeePayout
