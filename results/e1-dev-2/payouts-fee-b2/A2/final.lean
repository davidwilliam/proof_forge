import FeePayout.Spec
import FeePayout.Lemmas
namespace FeePayout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := expectedBalance s r,
      applied := r.txId :: s.applied })
  else (.rejected, s)

def myfoo := 1

theorem myfoo_thm2 : 1 = 1 := rfl

theorem req_nonnegative_aux_test : True := trivial
#check @ValidPayout

theorem probe1 (a b : Nat) (h : a ≤ b) : a / 10000 ≤ b / 10000 := by
  exact Nat.div_le_div_right h

theorem probe_divmod2 (m n : Nat) : 0 < n → n * (m / n) + m % n = m := by
  intro h
  exact Nat.div_add_mod m n

theorem probe_ring_test (a b : Int) : a + b = b + a := by
  exact Int.add_comm a b

theorem probe_cast_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  simp

theorem probe_cast2 (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  simp

theorem probe_cast3 (a b : Nat) : (((a * b : Nat)) : Int) = (a : Int) * (b : Int) := by
  simp
#check Nat.div_add_mod
#check Nat.add_sub_cancel
#check Nat.sub_add_cancel
#check Nat.mod_add_div

theorem sumZero_test (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem fee_le_test (bps amount : Nat) (h : bps ≤ 10000) : feeOf bps amount ≤ amount := by
  unfold feeOf
  by_cases ham : amount = 0
  · simp [ham]
  · have h1 : amount * bps ≤ amount * 10000 := Nat.mul_le_mul_left amount h
    have h2 : amount * bps / 10000 ≤ amount * 10000 / 10000 := Nat.div_le_div_right h1
    have h3 : amount * 10000 / 10000 = amount := Nat.mul_div_cancel amount (by omega : 0 < 10000)
    omega

theorem sumZero2 (l : List Nat) (c : Int) :
    sumOver l (fun a => if a ∈ ([] : List Nat) then c else (0 : Int)) = 0 := by
  have h : ∀ a ∈ l, (if a ∈ ([] : List Nat) then c else (0 : Int)) = (0 : Int) := by
    intro a _
    simp
  rw [sumOver_congr l _ _ h]
  have h2 : sumOver l (fun _ => (0 : Int)) = 0 := by
    induction l with
    | nil => simp
    | cons a t ih => simp [ih]
  exact h2

theorem sumOver_zero_list (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem add_mul_test (n : Int) (c : Int) : c + n * c = (n + 1) * c := by
  rw [Int.add_mul, Int.one_mul, Int.add_comm]

theorem nilCaseTest (l : List Nat) (c : Int) :
    sumOver l (fun a => if a ∈ ([] : List Nat) then c else (0 : Int)) = ((List.length ([] : List Nat) : Nat) : Int) * c := by
  have hrhs : (((List.length ([] : List Nat) : Nat) : Int) * c) = 0 := by simp
  rw [hrhs]
  have h : ∀ a ∈ l, (fun a => if a ∈ ([] : List Nat) then c else (0 : Int)) a = (fun _ => (0 : Int)) a := by
    intro a _
    simp
  have hcon := sumOver_congr l (fun a => if a ∈ ([] : List Nat) then c else (0 : Int)) (fun _ => (0 : Int)) h
  rw [hcon]
  exact sumOver_zero_list l

theorem plan0_indicator_mem_cons_decomp (b : Nat) (sub : List Nat) (c : Int)
    (hb : b ∉ sub) (a : Nat) :
    (if a ∈ b :: sub then c else 0)
      = (if a = b then c else 0) + (if a ∈ sub then c else 0) := by
  by_cases hab : a = b
  · subst hab
    simp [hb]
  · simp [hab]




theorem plan0_split_eq_amount (bps amount n : Nat)
    (hbps : bps ≤ 10000) (hn : 0 < n) :
    n * recipientShare bps amount n + feeCredit bps amount n = amount := by
  unfold recipientShare feeCredit netOf feeOf
  have hfee_le : amount * bps / 10000 ≤ amount := by
    by_cases ham : amount = 0
    · simp [ham]
    · have h1 : amount * bps ≤ amount * 10000 := Nat.mul_le_mul_left amount hbps
      have h2 : amount * bps / 10000 ≤ amount * 10000 / 10000 := Nat.div_le_div_right h1
      have h3 : amount * 10000 / 10000 = amount := Nat.mul_div_cancel amount (by omega : 0 < 10000)
      omega
  have hdiv : n * ((amount - amount * bps / 10000) / n) + (amount - amount * bps / 10000) % n
      = amount - amount * bps / 10000 := Nat.div_add_mod _ _
  have hadd : amount * bps / 10000 + (amount - amount * bps / 10000) = amount :=
    Nat.add_sub_cancel' hfee_le
  omega


theorem plan0_sumOver_expectedBalance (s : State) (r : Request)
    (hnd : s.accounts.Nodup) (hsrc : r.source ∈ s.accounts)
    (hfee : s.feeAccount ∈ s.accounts) (hrnd : r.recipients.Nodup)
    (hrec : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (expectedBalance s r)
      = total s - (r.amount : Int)
        + (r.recipients.length : Int)
            * (recipientShare s.feeBps r.amount r.recipients.length : Int)
        + (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
  unfold expectedBalance total
  have hsrc_sum : sumOver s.accounts (fun a => if a = r.source then ((r.amount : Nat) : Int) else 0) = ((r.amount : Nat) : Int) := by
    have h := sumOver_ite_eq hnd r.source (((r.amount : Nat)) : Int)
    simpa [hsrc] using h
  have hfee_sum : sumOver s.accounts (fun a => if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) = ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) := by
    have h := sumOver_ite_eq hnd s.feeAccount (((feeCredit s.feeBps r.amount r.recipients.length : Nat)) : Int)
    simpa [hfee] using h
  have key : ∀ (sub : List Nat), sub.Nodup → (∀ x ∈ sub, x ∈ s.accounts) →
      sumOver s.accounts (fun a => if a ∈ sub then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
      = (sub.length : Int) * ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) := by
    intro sub
    induction sub with
    | nil =>
      intro _ _
      have h0 : ∀ a ∈ s.accounts, (if a ∈ ([] : List Nat) then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else (0 : Int)) = (0 : Int) := by
        intro a _
        simp
      have hcon := sumOver_congr s.accounts (fun a => if a ∈ ([] : List Nat) then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else (0 : Int)) (fun _ => (0 : Int)) h0
      rw [hcon]
      have hz : sumOver s.accounts (fun _ => (0 : Int)) = 0 := sumOver_zero_list s.accounts
      rw [hz]
      simp
    | cons b sub' ih =>
      intro hnod hcover
      rw [List.nodup_cons] at hnod
      obtain ⟨hb_not, hsub_nodup⟩ := hnod
      have hb_mem : b ∈ s.accounts := hcover b (by simp)
      have hcover' : ∀ x ∈ sub', x ∈ s.accounts := fun x hx => hcover x (by simp [hx])
      have ih' := ih hsub_nodup hcover'
      have hdecomp : ∀ a ∈ s.accounts, (if a ∈ b :: sub' then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else (0 : Int)) = ((if a = b then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else (0 : Int)) + (if a ∈ sub' then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else (0 : Int))) := by
        intro a _
        exact plan0_indicator_mem_cons_decomp b sub' (((recipientShare s.feeBps r.amount r.recipients.length : Nat)) : Int) hb_not a
      have hcon := sumOver_congr s.accounts (fun a => if a ∈ b :: sub' then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else (0 : Int)) (fun a => (if a = b then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else (0 : Int)) + (if a ∈ sub' then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else (0 : Int))) hdecomp
      rw [hcon, sumOver_add]
      have hfirst : sumOver s.accounts (fun a => if a = b then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else (0 : Int)) = ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) := by
        have h := sumOver_ite_eq hnd b (((recipientShare s.feeBps r.amount r.recipients.length : Nat)) : Int)
        simpa [hb_mem] using h
      rw [hfirst, ih']
      simp only [List.length_cons]
      have hcast : ((((sub'.length + 1 : Nat))) : Int) = (((sub'.length : Int) + 1)) := by simp
      rw [hcast, Int.add_mul, Int.one_mul, Int.add_comm]
  have hrec_sum : sumOver s.accounts (fun a => if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
      = (r.recipients.length : Int) * ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) :=
    key r.recipients hrnd hrec
  have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then ((r.amount : Nat) : Int) else 0) := by
    exact sumOver_sub s.accounts s.balance (fun a => if a = r.source then ((r.amount : Nat) : Int) else 0)
  have hadd1 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0) + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0)) + sumOver s.accounts (fun a => if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) := by
    exact sumOver_add s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0)) (fun a => if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
  have hadd2 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0) + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) + (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0) + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)) + sumOver s.accounts (fun a => if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) := by
    exact sumOver_add s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0) + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)) (fun a => if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
  rw [hadd2, hadd1, hsub, hsrc_sum, hrec_sum, hfee_sum]


theorem plan0_indicator_mem_cons_decomp2 (b : Nat) (sub : List Nat) (c : Int)
    (hb : b ∉ sub) (a : Nat) :
    (if a ∈ b :: sub then c else 0)
      = (if a = b then c else 0) + (if a ∈ sub then c else 0) := by
  by_cases hab : a = b
  · subst hab
    simp [hb]
  · simp [hab]

theorem plan0_indicator_mem_cons_decomp_auxcheck (b : Nat) (sub : List Nat) (c : Int)
    (hb : b ∉ sub) (a : Nat) :
    (if a ∈ b :: sub then c else 0)
      = (if a = b then c else 0) + (if a ∈ sub then c else 0) := by
  by_cases hab : a = b
  · subst hab
    simp [hb]
  · simp [hab]

theorem plan0_sumOver_mem_indicator (l sub : List Nat) (c : Int)
    (hl : l.Nodup) (hsub : sub.Nodup) (hcover : ∀ x ∈ sub, x ∈ l) :
    sumOver l (fun a => if a ∈ sub then c else 0)
      = (sub.length : Int) * c := by
  induction sub generalizing l with
  | nil =>
    have h : ∀ a ∈ l, (fun a => if a ∈ ([] : List Nat) then c else (0 : Int)) a = (fun _ => (0 : Int)) a := by
      intro a _
      simp
    have hcon := sumOver_congr l (fun a => if a ∈ ([] : List Nat) then c else (0 : Int)) (fun _ => (0 : Int)) h
    rw [hcon]
    have hz : sumOver l (fun _ => (0 : Int)) = 0 := sumOver_zero_list l
    rw [hz]
    simp
  | cons b sub' ih =>
    rw [List.nodup_cons] at hsub
    obtain ⟨hb_not, hsub_nodup⟩ := hsub
    have hb_mem : b ∈ l := hcover b (by simp)
    have hcover' : ∀ x ∈ sub', x ∈ l := fun x hx => hcover x (by simp [hx])
    have ih' := ih l hl hsub_nodup hcover'
    have hdecomp : ∀ a ∈ l, (if a ∈ b :: sub' then c else (0 : Int)) = ((if a = b then c else (0 : Int)) + (if a ∈ sub' then c else (0 : Int))) := by
      intro a _
      exact plan0_indicator_mem_cons_decomp b sub' c hb_not a
    have hcon := sumOver_congr l (fun a => if a ∈ b :: sub' then c else (0 : Int)) (fun a => (if a = b then c else (0 : Int)) + (if a ∈ sub' then c else (0 : Int))) hdecomp
    rw [hcon, sumOver_add]
    have hfirst : sumOver l (fun a => if a = b then c else (0 : Int)) = c := by
      have h := sumOver_ite_eq hl b c
      simpa [hb_mem] using h
    rw [hfirst, ih']
    simp only [List.length_cons]
    have hcast : (((sub'.length + 1 : Nat)) : Int) = ((sub'.length : Int) + 1) := by simp
    rw [hcast, Int.add_mul, Int.one_mul, Int.add_comm]

theorem plan0_sumOver_expectedBalance_aux2 (s : State) (r : Request)
    (hnd : s.accounts.Nodup) (hsrc : r.source ∈ s.accounts)
    (hfee : s.feeAccount ∈ s.accounts) (hrnd : r.recipients.Nodup)
    (hrec : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (expectedBalance s r)
      = total s - (r.amount : Int)
        + (r.recipients.length : Int)
            * (recipientShare s.feeBps r.amount r.recipients.length : Int)
        + (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
  unfold expectedBalance total
  have hsrc_sum : sumOver s.accounts (fun a => if a = r.source then ((r.amount : Nat) : Int) else 0) = ((r.amount : Nat) : Int) := by
    have h := sumOver_ite_eq hnd r.source (((r.amount : Nat)) : Int)
    simpa [hsrc] using h
  have hfee_sum : sumOver s.accounts (fun a => if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) = ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) := by
    have h := sumOver_ite_eq hnd s.feeAccount (((feeCredit s.feeBps r.amount r.recipients.length : Nat)) : Int)
    simpa [hfee] using h
  have hrec_sum : sumOver s.accounts (fun a => if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
      = (r.recipients.length : Int) * ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) := by
    exact plan0_sumOver_mem_indicator s.accounts r.recipients (((recipientShare s.feeBps r.amount r.recipients.length : Nat)) : Int) hnd hrnd hrec
  have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then ((r.amount : Nat) : Int) else 0) := by
    exact sumOver_sub s.accounts s.balance (fun a => if a = r.source then ((r.amount : Nat) : Int) else 0)
  have hadd1 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0) + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0)) + sumOver s.accounts (fun a => if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) := by
    exact sumOver_add s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0)) (fun a => if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
  have hadd2 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0) + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) + (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0) + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)) + sumOver s.accounts (fun a => if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) := by
    exact sumOver_add s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0) + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)) (fun a => if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
  rw [hadd2, hadd1, hsub, hsrc_sum, hrec_sum, hfee_sum]

theorem plan0_sumOver_expectedBalance_prover (s : State) (r : Request)
    (hnd : s.accounts.Nodup) (hsrc : r.source ∈ s.accounts)
    (hfee : s.feeAccount ∈ s.accounts) (hrnd : r.recipients.Nodup)
    (hrec : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (expectedBalance s r)
      = total s - (r.amount : Int)
        + (r.recipients.length : Int)
            * (recipientShare s.feeBps r.amount r.recipients.length : Int)
        + (feeCredit s.feeBps r.amount r.recipients.length : Int) :=
  plan0_sumOver_expectedBalance_aux2 s r hnd hsrc hfee hrnd hrec

theorem early_self_contained (s : State) (r : Request) : True := trivial

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hv : ValidPayout s r
  · simp [hv] at h
    exact hv.2.2.2.2.2.2.2.2.2.2.2.1
  · simp [hv] at h

theorem req_effects : Effects step := by
  intro s r h
  unfold step at h ⊢
  by_cases hv : ValidPayout s r
  · simp [hv]
  · simp [hv] at h

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv : ValidPayout s r := by
    unfold step at hok
    by_cases hv2 : ValidPayout s r
    · exact hv2
    · simp [hv2] at hok
  have hstep : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied })) := by
    unfold step
    simp [hv]
  rw [hstep]
  simp only
  constructor
  · intro x
    simp
  · have hneg : ¬ ValidPayout ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied }) r := by
      intro hcon
      have hmem : r.txId ∈ ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State).applied := by
        simp
      have hnot := hcon.2.2.2.2.2.2.2.2.2.2.2.2.2
      exact hnot hmem
    have hstep2 : step ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied }) r = (.rejected, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied })) := by
      unfold step
      simp [hneg]
    exact hstep2

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · have h_le : (r.amount : Int) ≤ s.balance r.source :=
      hv.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hstep_eq : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied })) := by
      unfold step
      simp [hv]
    have ha_mem : a ∈ s.accounts := by
      have hacc : (step s r).2.accounts = s.accounts := by rw [hstep_eq]
      rw [hacc] at ha
      exact ha
    have hbal : (step s r).2.balance a = expectedBalance s r a := by rw [hstep_eq]
    rw [hbal]
    have h0 : 0 ≤ s.balance a := hnn a ha_mem
    unfold expectedBalance
    by_cases h_as : a = r.source
    · subst h_as
      simp only [↓reduceIte]
      omega
    · simp [h_as]
      omega
  · have hstep_eq : step s r = (.rejected, s) := by
      unfold step
      simp [hv]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep_eq]
    have hbal : (step s r).2.balance a = s.balance a := by rw [hstep_eq]
    rw [hacc] at ha
    rw [hbal]
    exact hnn a ha

theorem req_equal_shares   : EqualShares step := by
  intro s r hok x hx
  have hv : ValidPayout s r := by
    unfold step at hok
    by_cases hv2 : ValidPayout s r
    · exact hv2
    · simp [hv2] at hok
  have hstep_eq : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied })) := by
    unfold step
    simp [hv]
  have hbal : (step s r).2.balance x = expectedBalance s r x := by rw [hstep_eq]
  rw [hbal]
  obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrcNot, hfeeNot, hfeeSrc, hsrcMem, hfeeMem, hmem, hauth, hbal_le, htxNot⟩ := hv
  have hx_src : x ≠ r.source := by
    intro heq
    subst heq
    exact hsrcNot hx
  have hx_fee : x ≠ s.feeAccount := by
    intro heq
    subst heq
    exact hfeeNot hx
  have hxs : (x = r.source) = False := by simp [hx_src]
  have hxf : (x = s.feeAccount) = False := by simp [hx_fee]
  unfold expectedBalance
  simp [hx_src, hx_fee, hx]
  omega

theorem req_fee_collected  : FeeCollected step := by
  intro s r hok
  have hv : ValidPayout s r := by
    unfold step at hok
    by_cases hv2 : ValidPayout s r
    · exact hv2
    · simp [hv2] at hok
  have hstep_eq : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied })) := by
    unfold step
    simp [hv]
  have hbal : (step s r).2.balance s.feeAccount = expectedBalance s r s.feeAccount := by rw [hstep_eq]
  rw [hbal]
  obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrcNot, hfeeNot, hfeeSrc, hsrcMem, hfeeMem, hmem, hauth, hbal_le, htxNot⟩ := hv
  unfold expectedBalance
  simp [hfeeSrc, hfeeNot]
  omega

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv : ValidPayout s r := by
    unfold step at hok
    by_cases hv2 : ValidPayout s r
    · exact hv2
    · simp [hv2] at hok
  have hstep_eq : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied })) := by
    unfold step
    simp [hv]
  obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrcNot, hfeeNot, hfeeSrc, hsrcMem, hfeeMem, hmem, hauth, hbal_le, htxNot⟩ := hv
  have hlen_pos : 0 < r.recipients.length := by
    cases hrec : r.recipients with
    | nil => exact absurd hrec hne
    | cons b t => simp
  have hsum := plan0_sumOver_expectedBalance_aux2 s r hnodup hsrcMem hfeeMem hrnodup hmem
  have hsplit := plan0_split_eq_amount s.feeBps r.amount r.recipients.length hbps hlen_pos
  have htotal_eq : total (step s r).2 = sumOver s.accounts (expectedBalance s r) := by
    rw [hstep_eq]
    rfl
  rw [htotal_eq, hsum]
  omega

end FeePayout
