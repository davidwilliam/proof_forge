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

theorem req_equal_shares_aux : EqualShares step := by
  intro s r hok x hx
  by_cases hv : ValidPayout s r
  · have hv0 := hv
    obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrc, hfee_rec, hfee_src, hsrc_mem, hfee_mem, hsub, hauth, hbal, htx⟩ := hv0
    have hsrc_ne : x ≠ r.source := fun h => hsrc (h ▸ hx)
    have hfee_ne : x ≠ s.feeAccount := fun h => hfee_rec (h ▸ hx)
    have hbal_eq : (step s r).2.balance x = expectedBalance s r x := by
      simp only [step, if_pos hv]
    rw [hbal_eq]
    unfold expectedBalance
    have e1 : (if x = r.source then (r.amount : Int) else 0) = 0 := if_neg hsrc_ne
    have e2 : (if x ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = (recipientShare s.feeBps r.amount r.recipients.length : Int) := if_pos hx
    have e3 : (if x = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 := if_neg hfee_ne
    rw [e1, e2, e3]
    omega
  · have hstep : step s r = (.rejected, s) := by simp only [step, if_neg hv]
    rw [hstep] at hok
    simp at hok

theorem req_fee_collected_aux : FeeCollected step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hv0 := hv
    obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrc, hfee_rec, hfee_src, hsrc_mem, hfee_mem, hsub, hauth, hbal, htx⟩ := hv0
    have hbal_eq : (step s r).2.balance s.feeAccount = expectedBalance s r s.feeAccount := by
      simp only [step, if_pos hv]
    rw [hbal_eq]
    unfold expectedBalance
    have e1 : (if s.feeAccount = r.source then (r.amount : Int) else 0) = 0 := if_neg hfee_src
    have e2 : (if s.feeAccount ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 := if_neg hfee_rec
    have e3 : (if s.feeAccount = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = (feeCredit s.feeBps r.amount r.recipients.length : Int) := if_pos rfl
    rw [e1, e2, e3]
    omega
  · have hstep : step s r = (.rejected, s) := by simp only [step, if_neg hv]
    rw [hstep] at hok
    simp at hok

theorem req_nonnegative_full : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · have hv0 := hv
    obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrc_nrec, hfee_nrec, hfee_src, hsrc_mem, hfee_mem, hsub, hauth, hbal_le, htx⟩ := hv0
    have hacc : (step s r).2.accounts = s.accounts := by simp only [step, if_pos hv]
    have hmem : a ∈ s.accounts := hacc ▸ ha
    have hnn_a : 0 ≤ s.balance a := hnn a hmem
    have hbal_eq : (step s r).2.balance a = expectedBalance s r a := by simp only [step, if_pos hv]
    rw [hbal_eq]
    unfold expectedBalance
    by_cases h1 : a = r.source
    · subst h1
      have e2 : (if r.source ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 := if_neg hsrc_nrec
      have e3 : (if r.source = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 := if_neg (fun h => hfee_src h.symm)
      simp only [e2, e3]
      omega
    · by_cases h2 : a ∈ r.recipients
      · have h3 : ¬ (a = s.feeAccount) := fun h => hfee_nrec (h ▸ h2)
        simp only [if_neg h1, if_pos h2, if_neg h3]
        omega
      · by_cases h3 : a = s.feeAccount
        · simp only [if_neg h1, if_neg h2, if_pos h3]
          omega
        · simp only [if_neg h1, if_neg h2, if_neg h3]
          omega
  · have hacc : (step s r).2.accounts = s.accounts := by simp only [step, if_neg hv]
    have hmem : a ∈ s.accounts := hacc ▸ ha
    have hbal_eq : (step s r).2.balance a = s.balance a := by simp only [step, if_neg hv]
    rw [hbal_eq]
    exact hnn a hmem

theorem mytest_thm : 1 = 1 := rfl

theorem sumZero_aux2 (l : List Nat) : sumOver l (fun _ : Nat => (0 : Int)) = 0 := by induction l with | nil => simp | cons a t ih => simp [ih]

theorem sumZero_aux (l : List Nat) : sumOver l (fun _ : Nat => (0 : Int)) = 0 := by induction l with | nil => simp | cons a t ih => simp [ih]

theorem nodupTest (b : Nat) (t2 : List Nat) (ht : (b :: t2).Nodup) : b ∉ t2 ∧ t2.Nodup := by rwa [List.nodup_cons] at ht

theorem fee_le_aux (bps amount : Nat) (hbps : bps ≤ 10000) : feeOf bps amount ≤ amount := by
  unfold feeOf
  have h1 : amount * bps ≤ amount * 10000 := Nat.mul_le_mul_left amount hbps
  have h2 : amount * bps / 10000 ≤ amount * 10000 / 10000 := Nat.div_le_div_right h1
  have h3 : amount * 10000 / 10000 = amount := Nat.mul_div_cancel amount (by omega)
  omega

theorem idem_rfl_test (s : State) (r : Request) :
  step ((step s r).2) r = (if ValidPayout ((step s r).2) r then (.ok, ({ ((step s r).2) with balance := fun a => expectedBalance ((step s r).2) r a, applied := r.txId :: ((step s r).2).applied } : State)) else (.rejected, (step s r).2)) := rfl

theorem my_lemma_test123 : 1 = 1 := rfl

theorem recipPointEq (b : Nat) (t2 : List Nat) (S : Int) (hb : b ∉ t2) (a : Nat) : (if a ∈ b :: t2 then S else (0 : Int)) = (if a = b then S else 0) + (if a ∈ t2 then S else 0) := by by_cases hab : a = b; subst hab; simp [hb]; by_cases hm : a ∈ t2; simp [hab, hm]; simp [hab, hm]





theorem plan0_sumOver_recipients_eq (accounts recipients : List AccountId) (c : Int)
    (haccounts : accounts.Nodup) (hrecipients : recipients.Nodup)
    (hsub : ∀ x ∈ recipients, x ∈ accounts) :
    sumOver accounts (fun a => if a ∈ recipients then c else 0)
      = (recipients.length : Int) * c := by
  induction recipients with
  | nil =>
    have h0 : sumOver accounts (fun a => if a ∈ ([] : List Nat) then c else (0:Int)) = sumOver accounts (fun _ => (0:Int)) := by
      apply sumOver_congr
      intro a ha
      simp
    rw [h0, sumZero_aux]
    simp
  | cons b t2 ih =>
    have ht_nodup : t2.Nodup := (List.nodup_cons.mp hrecipients).2
    have hb_notin : b ∉ t2 := (List.nodup_cons.mp hrecipients).1
    have hsub_tail : ∀ x ∈ t2, x ∈ accounts := fun x hx => hsub x (List.mem_cons_of_mem b hx)
    have hb_mem_acc : b ∈ accounts := hsub b (by simp)
    have ih' : sumOver accounts (fun a => if a ∈ t2 then c else 0) = (t2.length : Int) * c := ih ht_nodup hsub_tail
    have h_congr : sumOver accounts (fun a => if a ∈ b :: t2 then c else (0 : Int))
        = sumOver accounts (fun a => (if a = b then c else 0) + (if a ∈ t2 then c else 0)) :=
      sumOver_congr _ _ _ (fun a _ => recipPointEq b t2 c hb_notin a)
    have hite : sumOver accounts (fun a => if a = b then c else (0:Int)) = c := by
      rw [sumOver_ite_eq haccounts b c, if_pos hb_mem_acc]
    rw [h_congr, sumOver_add, hite, ih']
    have hlen : ((((b :: t2).length : Nat)) : Int) = ((t2.length : Int)) + 1 := by
      simp
    rw [hlen]
    have hadd := Int.add_mul (t2.length : Int) 1 c
    have hone := Int.one_mul c
    omega


theorem plan0_sumOver_expectedBalance_eq (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = total s := by
  obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrc_nrec, hfee_nrec, hfee_src, hsrc_mem, hfee_mem, hsub, hauth, hbal_le, htx⟩ := hv
  have hsumX : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodup r.source (r.amount : Int)
    rw [h]
    simp [hsrc_mem]
  have hsumY : sumOver s.accounts (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) := by
    exact plan0_sumOver_recipients_eq s.accounts r.recipients _ hnodup hrnodup hsub
  have hsumZ : sumOver s.accounts (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
    have h := sumOver_ite_eq hnodup s.feeAccount (feeCredit s.feeBps r.amount r.recipients.length : Int)
    rw [h]
    simp [hfee_mem]
  have hsplit : (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) + (feeCredit s.feeBps r.amount r.recipients.length : Int) = (feeOf s.feeBps r.amount : Int) + (netOf s.feeBps r.amount : Int) := by
    unfold recipientShare feeCredit
    have hmod : r.recipients.length * (netOf s.feeBps r.amount / r.recipients.length) + netOf s.feeBps r.amount % r.recipients.length = netOf s.feeBps r.amount := Nat.div_add_mod _ _
    have hcast : ((r.recipients.length * (netOf s.feeBps r.amount / r.recipients.length) + netOf s.feeBps r.amount % r.recipients.length : Nat) : Int) = (r.recipients.length : Int) * (((netOf s.feeBps r.amount / r.recipients.length : Nat)) : Int) + (((netOf s.feeBps r.amount % r.recipients.length : Nat)) : Int) := by
      rw [Int.natCast_add, Int.natCast_mul]
    rw [hmod] at hcast
    have hcast2 : ((feeOf s.feeBps r.amount + netOf s.feeBps r.amount % r.recipients.length : Nat) : Int) = (feeOf s.feeBps r.amount : Int) + (((netOf s.feeBps r.amount % r.recipients.length : Nat)) : Int) := by
      rw [Int.natCast_add]
    rw [hcast2]
    omega
  have hfee_net : (feeOf s.feeBps r.amount : Int) + (netOf s.feeBps r.amount : Int) = (r.amount : Int) := by
    have hle : feeOf s.feeBps r.amount ≤ r.amount := fee_le_aux s.feeBps r.amount hbps
    unfold netOf
    omega
  unfold expectedBalance total
  have e1 := sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
  have e2 := sumOver_add s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
  have e3 := sumOver_add s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)) (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)
  have ec : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)) = sumOver s.accounts (fun a => ((s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)) + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)) := by
    apply sumOver_congr
    intro a _
    rfl
  rw [ec, e3, e2, e1, hsumX, hsumY, hsumZ]
  omega


theorem plan0_total_step_of_valid (s : State) (r : Request)
    (hv : ValidPayout s r) :
    total (step s r).2 = total s := by
  have hacc : (step s r).2.accounts = s.accounts := by simp only [step, if_pos hv]
  have hbal : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
    intro a; simp only [step, if_pos hv]
  unfold total
  rw [hacc]
  have hcongr : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (fun a => expectedBalance s r a) := by
    apply sumOver_congr
    intro a _
    exact hbal a
  rw [hcongr]
  exact plan0_sumOver_expectedBalance_eq s r hv


theorem plan0_fee_add_net_check2 (bps amount : Nat) (hbps : bps ≤ 10000) :
    (feeOf bps amount : Int) + (netOf bps amount : Int) = (amount : Int) := by
  have hle : feeOf bps amount ≤ amount := fee_le_aux bps amount hbps
  unfold netOf
  omega

theorem plan0_fee_add_net (bps amount : Nat) (hbps : bps ≤ 10000) :
    (feeOf bps amount : Int) + (netOf bps amount : Int) = (amount : Int) := by
  have hle : feeOf bps amount ≤ amount := fee_le_aux bps amount hbps
  unfold netOf
  omega

theorem plan0_share_feeCredit_eq (bps amount n : Nat) :
    (n : Int) * (recipientShare bps amount n : Int)
        + (feeCredit bps amount n : Int)
      = (feeOf bps amount : Int) + (netOf bps amount : Int) := by
  unfold recipientShare feeCredit
  have hmod : n * (netOf bps amount / n) + netOf bps amount % n = netOf bps amount :=
    Nat.div_add_mod _ _
  have hcast : ((n * (netOf bps amount / n) + netOf bps amount % n : Nat) : Int)
      = (n : Int) * ((netOf bps amount / n : Nat) : Int)
        + ((netOf bps amount % n : Nat) : Int) := by
    rw [Int.natCast_add, Int.natCast_mul]
  rw [hmod] at hcast
  have hcast2 : ((feeOf bps amount + netOf bps amount % n : Nat) : Int)
      = (feeOf bps amount : Int) + ((netOf bps amount % n : Nat) : Int) := by
    rw [Int.natCast_add]
  rw [hcast2]
  omega

theorem probe_add_mul (a b c : Int) : (a + b) * c = a * c + b * c := by
  rw [Int.add_mul]

theorem probe_simp1 (c : Int) : (0 : Int) * c = 0 := by simp

theorem probe_simp2 (c : Int) : c + 0 = c := by simp

theorem probe_int_add_mul (a b c : Int) : (a + b) * c = a * c + b * c := Int.add_mul a b c
#check Int.add_mul
#check Int.zero_mul
#check Int.one_mul
#check Int.add_comm
#check Int.add_zero

theorem plan0_recip_final (accounts recipients : List AccountId) (c : Int)
    (haccounts : accounts.Nodup) (hrecipients : recipients.Nodup)
    (hsub : ∀ x ∈ recipients, x ∈ accounts) :
    sumOver accounts (fun a => if a ∈ recipients then c else 0)
      = (recipients.length : Int) * c := by
  induction recipients with
  | nil =>
    have h0 : sumOver accounts (fun a => if a ∈ ([] : List Nat) then c else (0:Int)) = sumOver accounts (fun _ => (0:Int)) := by
      apply sumOver_congr
      intro a ha
      simp
    rw [h0, sumZero_aux]
    simp
  | cons b t2 ih =>
    have ht_nodup : t2.Nodup := (List.nodup_cons.mp hrecipients).2
    have hb_notin : b ∉ t2 := (List.nodup_cons.mp hrecipients).1
    have hsub_tail : ∀ x ∈ t2, x ∈ accounts := fun x hx => hsub x (List.mem_cons_of_mem b hx)
    have hb_mem_acc : b ∈ accounts := hsub b (by simp)
    have ih' : sumOver accounts (fun a => if a ∈ t2 then c else 0) = (t2.length : Int) * c := ih ht_nodup hsub_tail
    have h_congr : sumOver accounts (fun a => if a ∈ b :: t2 then c else (0 : Int))
        = sumOver accounts (fun a => (if a = b then c else 0) + (if a ∈ t2 then c else 0)) :=
      sumOver_congr _ _ _ (fun a _ => recipPointEq b t2 c hb_notin a)
    have hite : sumOver accounts (fun a => if a = b then c else (0:Int)) = c := by
      rw [sumOver_ite_eq haccounts b c, if_pos hb_mem_acc]
    rw [h_congr, sumOver_add, hite, ih']
    have hlen : ((((b :: t2).length : Nat)) : Int) = ((t2.length : Int)) + 1 := by
      simp
    rw [hlen]
    have hadd := Int.add_mul (t2.length : Int) 1 c
    have hone := Int.one_mul c
    omega

theorem plan1_sumOver_zero (l : List AccountId) :
    sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [sumOver_cons, ih]










theorem plan1_sumOver_zero_tmp (l : List AccountId) :
    sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [sumOver_cons, ih]

theorem plan1_indicator_cons (b : AccountId) (t : List AccountId) (c : Int)
    (hb : b ∉ t) (a : AccountId) :
    (if a ∈ b :: t then c else (0 : Int))
      = (if a = b then c else 0) + (if a ∈ t then c else 0) := by
  by_cases hab : a = b
  · subst hab
    simp [hb]
  · simp [List.mem_cons, hab]

theorem plan1_sumOver_single (accounts : List AccountId) (b : AccountId) (c : Int)
    (hnd : accounts.Nodup) (hb : b ∈ accounts) :
    sumOver accounts (fun a => if a = b then c else (0 : Int)) = c := by
  rw [sumOver_ite_eq hnd b c, if_pos hb]

theorem plan1_sumOver_mem_cons_proof (accounts recipients : List AccountId)
    (b : AccountId) (c : Int)
    (hnd : accounts.Nodup) (hb_notin : b ∉ recipients) (hb_mem : b ∈ accounts) :
    sumOver accounts (fun a => if a ∈ b :: recipients then c else (0 : Int))
      = c + sumOver accounts (fun a => if a ∈ recipients then c else 0) := by
  have hcongr : sumOver accounts (fun a => if a ∈ b :: recipients then c else (0 : Int))
      = sumOver accounts (fun a => (if a = b then c else (0 : Int)) + (if a ∈ recipients then c else (0 : Int))) := by
    apply sumOver_congr
    intro a _
    exact plan1_indicator_cons b recipients c hb_notin a
  rw [hcongr, sumOver_add, plan1_sumOver_single accounts b c hnd hb_mem]

theorem plan1_sumOver_mem_cons (accounts recipients : List AccountId)
    (b : AccountId) (c : Int)
    (hnd : accounts.Nodup) (hb_notin : b ∉ recipients) (hb_mem : b ∈ accounts) :
    sumOver accounts (fun a => if a ∈ b :: recipients then c else (0 : Int))
      = c + sumOver accounts (fun a => if a ∈ recipients then c else 0) := by
  have hcongr : sumOver accounts (fun a => if a ∈ b :: recipients then c else (0 : Int))
      = sumOver accounts (fun a => (if a = b then c else (0 : Int)) + (if a ∈ recipients then c else (0 : Int))) := by
    apply sumOver_congr
    intro a _
    exact plan1_indicator_cons b recipients c hb_notin a
  rw [hcongr, sumOver_add, plan1_sumOver_single accounts b c hnd hb_mem]

theorem plan1_cons_length_mul (b : AccountId) (t : List AccountId) (c : Int) :
    ((b :: t).length : Int) * c = c + (t.length : Int) * c := by
  have hcast : (((b :: t).length : Nat) : Int) = (t.length : Int) + 1 := by simp
  rw [hcast, Int.add_mul, Int.one_mul, Int.add_comm]

theorem plan0_sumOver_recipients_eq_new (accounts recipients : List AccountId) (c : Int)
    (haccounts : accounts.Nodup) (hrecipients : recipients.Nodup)
    (hsub : ∀ x ∈ recipients, x ∈ accounts) :
    sumOver accounts (fun a => if a ∈ recipients then c else 0)
      = (recipients.length : Int) * c := by
  induction recipients with
  | nil =>
    have h0 : sumOver accounts (fun a => if a ∈ ([] : List Nat) then c else (0:Int)) = sumOver accounts (fun _ => (0:Int)) := by
      apply sumOver_congr
      intro a ha
      simp
    rw [h0, sumZero_aux]
    simp
  | cons b t2 ih =>
    have ht_nodup : t2.Nodup := (List.nodup_cons.mp hrecipients).2
    have hb_notin : b ∉ t2 := (List.nodup_cons.mp hrecipients).1
    have hsub_tail : ∀ x ∈ t2, x ∈ accounts := fun x hx => hsub x (List.mem_cons_of_mem b hx)
    have hb_mem_acc : b ∈ accounts := hsub b (by simp)
    have ih' : sumOver accounts (fun a => if a ∈ t2 then c else 0) = (t2.length : Int) * c := ih ht_nodup hsub_tail
    have h_congr : sumOver accounts (fun a => if a ∈ b :: t2 then c else (0 : Int))
        = sumOver accounts (fun a => (if a = b then c else 0) + (if a ∈ t2 then c else 0)) :=
      sumOver_congr _ _ _ (fun a _ => recipPointEq b t2 c hb_notin a)
    have hite : sumOver accounts (fun a => if a = b then c else (0:Int)) = c := by
      rw [sumOver_ite_eq haccounts b c, if_pos hb_mem_acc]
    rw [h_congr, sumOver_add, hite, ih']
    have hlen : ((((b :: t2).length : Nat)) : Int) = ((t2.length : Int)) + 1 := by
      simp
    rw [hlen]
    have hadd := Int.add_mul (t2.length : Int) 1 c
    have hone := Int.one_mul c
    omega

theorem plan0_sumOver_expectedBalance_eq_try1 (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) = sumOver s.accounts s.balance - (r.amount : Int) := by
  obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrc_nrec, hfee_nrec, hfee_src, hsrc_mem, hfee_mem, hsub, hauth, hbal_le, htx⟩ := hv
  rw [sumOver_sub]
  have h : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    rw [sumOver_ite_eq hnodup r.source (r.amount : Int), if_pos hsrc_mem]
  rw [h]

theorem plan0_sumOver_expectedBalance_eq2 (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = total s := by
  obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrc_nrec, hfee_nrec, hfee_src, hsrc_mem, hfee_mem, hsub, hauth, hbal_le, htx⟩ := hv
  have hsumX : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodup r.source (r.amount : Int)
    rw [h]
    simp [hsrc_mem]
  have hsumY : sumOver s.accounts (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) := by
    exact plan0_sumOver_recipients_eq_new s.accounts r.recipients _ hnodup hrnodup hsub
  have hsumZ : sumOver s.accounts (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
    have h := sumOver_ite_eq hnodup s.feeAccount (feeCredit s.feeBps r.amount r.recipients.length : Int)
    rw [h]
    simp [hfee_mem]
  have hsplit := plan0_share_feeCredit_eq s.feeBps r.amount r.recipients.length
  have hfee_net := plan0_fee_add_net s.feeBps r.amount hbps
  unfold expectedBalance total
  have e1 := sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
  have e2 := sumOver_add s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
  have e3 := sumOver_add s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)) (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)
  have ec : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)) = sumOver s.accounts (fun a => ((s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)) + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)) := by
    apply sumOver_congr
    intro a _
    rfl
  rw [ec, e3, e2, e1, hsumX, hsumY, hsumZ]
  omega

theorem plan0_total_step_of_valid_helper (s : State) (r : Request)
    (hv : ValidPayout s r) :
    total (step s r).2 = total s := by
  have hacc : (step s r).2.accounts = s.accounts := by simp only [step, if_pos hv]
  have hbal : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
    intro a; simp only [step, if_pos hv]
  unfold total
  rw [hacc]
  have hcongr : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (fun a => expectedBalance s r a) := by
    apply sumOver_congr
    intro a _
    exact hbal a
  rw [hcongr]
  exact plan0_sumOver_expectedBalance_eq2 s r hv

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
  by_cases hv : ValidPayout s r
  · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hauth,_,_⟩ := hv
    exact hauth
  · simp [step, hv] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · simp only [step, hv, ↓reduceIte] at hok ⊢
    exact ⟨trivial, trivial, trivial, trivial, fun _ => trivial⟩
  · simp only [step, hv, ↓reduceIte] at hok
    exact absurd hok (by decide)

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      simp only [step, if_pos hv]
    have hmem : ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
      intro x
      rw [h2]
      simp
    refine ⟨hmem, ?_⟩
    have hnv : ¬ ValidPayout (step s r).2 r := by
      rw [h2]
      intro hcon
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, htx⟩ := hcon
      exact htx List.mem_cons_self
    exact req_invalid_noop _ _ hnv
  · simp only [step, if_neg hv] at hok; exact absurd hok (by decide)

theorem req_nonnegative : NonNegative step := req_nonnegative_full

theorem req_equal_shares : EqualShares step := req_equal_shares_aux

theorem req_fee_collected : FeeCollected step := req_fee_collected_aux

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · exact plan0_total_step_of_valid_helper s r hv
  · have hstep : step s r = (.rejected, s) := by simp only [step, if_neg hv]
    rw [hstep] at hok
    simp at hok

end FeePayout
