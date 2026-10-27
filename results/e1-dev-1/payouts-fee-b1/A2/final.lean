import FeePayout.Spec
import FeePayout.Lemmas
namespace FeePayout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if _h : ValidPayout s r then
    (.ok, { s with
      balance := expectedBalance s r,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_effects_aux : True := trivial

theorem dbg2 (s : State) (r : Request) (hok : (step s r).1 = .ok) : ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · have heq : step s r = (.rejected, s) := by unfold step; simp [hv]
    rw [heq] at hok
    simp at hok

theorem mytest : True := trivial

theorem mytest2 : True := trivial

def mydef : Nat := 3

theorem helper_fee_le (amount bps : Nat) (h : bps ≤ 10000) : feeOf bps amount ≤ amount := by
  unfold feeOf
  have h1 : amount * bps ≤ amount * 10000 := Nat.mul_le_mul_left amount h
  have h2 : amount * bps / 10000 ≤ amount * 10000 / 10000 := Nat.div_le_div_right h1
  have h3 : amount * 10000 / 10000 = amount := by
    have : amount * 10000 = amount * 10000 := rfl
    omega
  omega

theorem helper_sum_zero (l : List Nat) : sumOver l (fun _ : Nat => (0 : Int)) = 0 := by induction l with | nil => rfl | cons a t ih => simp [ih]

theorem foo_test : True := trivial

theorem foo_lem2 : True := trivial

theorem consv_zero_sum (l : List Nat) : sumOver l (fun _ : Nat => (0 : Int)) = 0 := by induction l with | nil => rfl | cons a t ih => simp [ih]





theorem plan0_mul_share_add_feeCredit (bps amount n : Nat) (hbps : bps ≤ 10000) (hn : n ≠ 0) : n * recipientShare bps amount n + feeCredit bps amount n = amount := by
  unfold recipientShare feeCredit netOf at *
  have hle : feeOf bps amount ≤ amount := helper_fee_le amount bps hbps
  have hdiv : n * ((amount - feeOf bps amount) / n) + (amount - feeOf bps amount) % n = (amount - feeOf bps amount) := Nat.div_add_mod _ _
  omega




theorem plan0_sum_recipients (accounts recipients : List AccountId) (c : Int) (hacc : accounts.Nodup) (hrec : recipients.Nodup) (hsub : ∀ y ∈ recipients, y ∈ accounts) : sumOver accounts (fun a => if a ∈ recipients then c else 0) = (recipients.length : Int) * c := by
  induction recipients generalizing accounts with
  | nil =>
    have h0 : ∀ a ∈ accounts, (if a ∈ ([] : List AccountId) then c else (0 : Int)) = (0 : Int) := by
      intro a ha; simp
    have h1 : sumOver accounts (fun a => if a ∈ ([] : List AccountId) then c else (0 : Int)) = sumOver accounts (fun _ : AccountId => (0 : Int)) := sumOver_congr _ _ _ h0
    rw [h1]
    have hz : sumOver accounts (fun _ : AccountId => (0 : Int)) = 0 := helper_sum_zero accounts
    rw [hz]
    simp
  | cons x xs ih =>
    have hxnot : x ∉ xs := (List.nodup_cons.mp hrec).1
    have hrec_tail : xs.Nodup := (List.nodup_cons.mp hrec).2
    have hxmem : x ∈ accounts := hsub x (by simp)
    have hsub_tail : ∀ y ∈ xs, y ∈ accounts := fun y hy => hsub y (List.mem_cons_of_mem x hy)
    have ih' := ih accounts hacc hrec_tail hsub_tail
    have hcongr : ∀ a ∈ accounts, (if a ∈ (x :: xs) then c else (0 : Int)) = ((if a = x then c else (0 : Int)) + (if a ∈ xs then c else (0 : Int))) := by
      intro a _
      by_cases hax : a = x
      · subst hax; simp [hxnot]
      · have hmem : (a ∈ x :: xs) = (a ∈ xs) := by simp [hax]
        simp [hax, hmem]
    have h1 : sumOver accounts (fun a => if a ∈ (x :: xs) then c else (0 : Int)) = sumOver accounts (fun a => (if a = x then c else (0 : Int)) + (if a ∈ xs then c else (0 : Int))) := sumOver_congr _ _ _ hcongr
    rw [h1, sumOver_add, sumOver_ite_eq hacc x c, ih']
    have hif : (if x ∈ accounts then c else (0 : Int)) = c := by simp [hxmem]
    rw [hif]
    have hlen : ((((x :: xs).length : Nat)) : Int) = ((xs.length : Nat) : Int) + 1 := by simp
    rw [hlen, Int.add_mul, Int.one_mul]
    omega




theorem plan0_fee_le (bps amount : Nat) (hbps : bps ≤ 10000) : feeOf bps amount ≤ amount :=
  helper_fee_le amount bps hbps

theorem plan0_fee_add_net (bps amount : Nat) (hbps : bps ≤ 10000) : feeOf bps amount + netOf bps amount = amount := by
  unfold netOf
  have hle : feeOf bps amount ≤ amount := helper_fee_le amount bps hbps
  omega

theorem plan0_indicator_recipients_cons (x : AccountId) (recipients : List AccountId) (a : AccountId) (c : Int) (hx : x ∉ recipients) : (if a ∈ x :: recipients then c else 0) = (if a = x then c else 0) + (if a ∈ recipients then c else 0) := by
  by_cases hax : a = x
  · subst hax
    simp [hx]
  · have hmem : (a ∈ x :: recipients) = (a ∈ recipients) := by
      simp [hax]
    by_cases hmem2 : a ∈ recipients
    · simp [hmem, hax, hmem2]
    · simp [hmem, hax, hmem2]







theorem plan1_sumOver_indicator_cons (accounts recipients : List AccountId) (x : AccountId) (c : Int) (hacc : accounts.Nodup) (hx : x ∉ recipients) : sumOver accounts (fun a => if a ∈ (x :: recipients) then c else 0) = (if x ∈ accounts then c else 0) + sumOver accounts (fun a => if a ∈ recipients then c else 0) := by
  have hcongr : ∀ a ∈ accounts, (if a ∈ (x :: recipients) then c else 0) = ((if a = x then c else 0) + (if a ∈ recipients then c else 0)) := fun a _ => plan0_indicator_recipients_cons x recipients a c hx
  have h1 : sumOver accounts (fun a => if a ∈ (x :: recipients) then c else 0) = sumOver accounts (fun a => (if a = x then c else 0) + (if a ∈ recipients then c else 0)) := sumOver_congr _ _ _ hcongr
  rw [h1, sumOver_add, sumOver_ite_eq hacc x c]




theorem plan1_sumOver_zero (l : List AccountId) : sumOver l (fun _ : AccountId => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem plan1_indicator_cons_add (x : AccountId) (recipients : List AccountId) (a : AccountId) (c : Int) (hx : x ∉ recipients) : (if a ∈ (x :: recipients) then c else 0) = (if a = x then c else 0) + (if a ∈ recipients then c else 0) := by
  by_cases hax : a = x
  · subst hax
    simp [hx]
  · have hmem : (a ∈ x :: recipients) = (a ∈ recipients) := by simp [hax]
    simp [hax, hmem]

theorem plan1_sumOver_indicator_single (accounts : List AccountId) (hacc : accounts.Nodup) (x : AccountId) (c : Int) : sumOver accounts (fun a => if a = x then c else 0) = if x ∈ accounts then c else 0 := by
  exact sumOver_ite_eq hacc x c

theorem plan1_sumOver_indicator_cons_aux_true : True := trivial

theorem probe_add_mul (a b c : Int) : (a + b) * c = a * c + b * c := by simp [Int.add_mul]

theorem plan1_sum_recipients_cons (accounts recipients : List AccountId) (x : AccountId) (c : Int) (hacc : accounts.Nodup) (hxnot : x ∉ recipients) (hxmem : x ∈ accounts) (ih : sumOver accounts (fun a => if a ∈ recipients then c else 0) = (recipients.length : Int) * c) : sumOver accounts (fun a => if a ∈ (x :: recipients) then c else 0) = ((x :: recipients).length : Int) * c := by
  have hsplit := plan1_sumOver_indicator_cons accounts recipients x c hacc hxnot
  rw [hsplit, ih]
  have hif : (if x ∈ accounts then c else 0) = c := by simp [hxmem]
  rw [hif]
  have hlen : (((x :: recipients).length : Nat) : Int) = (((recipients.length : Nat)) : Int) + 1 := by simp
  rw [hlen, Int.add_mul, Int.one_mul]
  omega

theorem plan0_sum_recipients_new : True := trivial

theorem snippet_sum_recip2 (accounts recipients : List AccountId) (c : Int) (hacc : accounts.Nodup) (hrec : recipients.Nodup) (hsub : ∀ y ∈ recipients, y ∈ accounts) : sumOver accounts (fun a => if a ∈ recipients then c else 0) = (recipients.length : Int) * c := by
  induction recipients generalizing accounts with
  | nil =>
    have h0 : ∀ a ∈ accounts, (if a ∈ ([] : List AccountId) then c else (0 : Int)) = (0 : Int) := by
      intro a ha; simp
    have h1 := sumOver_congr accounts _ _ h0
    rw [h1, plan1_sumOver_zero]
    simp
  | cons x xs ih =>
    have hxnot : x ∉ xs := by
      have h := List.nodup_cons.mp hrec
      exact h.1
    have hrec_tail : xs.Nodup := (List.nodup_cons.mp hrec).2
    have hxmem : x ∈ accounts := hsub x (by simp)
    have hsub_tail : ∀ y ∈ xs, y ∈ accounts := fun y hy => hsub y (List.mem_cons_of_mem x hy)
    have ih' := ih accounts hacc hrec_tail hsub_tail
    exact plan1_sum_recipients_cons accounts xs x c hacc hxnot hxmem ih'

theorem snippet_z (l : List AccountId) : sumOver l (fun _ : AccountId => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t iht => simp only [sumOver_cons]; rw [iht]; simp

theorem snippet_noref (accounts recipients : List AccountId) (c : Int) (hacc : accounts.Nodup) (hrec : recipients.Nodup) (hsub : ∀ y ∈ recipients, y ∈ accounts) : sumOver accounts (fun a => if a ∈ recipients then c else 0) = (recipients.length : Int) * c := by
  induction recipients generalizing accounts with
  | nil =>
    have h0 : ∀ a ∈ accounts, (if a ∈ ([] : List AccountId) then c else (0 : Int)) = (0 : Int) := by
      intro a ha; simp
    have h1 : sumOver accounts (fun a => if a ∈ ([] : List AccountId) then c else (0 : Int)) = sumOver accounts (fun _ : AccountId => (0 : Int)) :=
      sumOver_congr _ _ _ h0
    rw [h1]
    have hz : sumOver accounts (fun _ : AccountId => (0 : Int)) = 0 := helper_sum_zero accounts
    rw [hz]
    simp
  | cons x xs ih =>
    have hxnot : x ∉ xs := (List.nodup_cons.mp hrec).1
    have hrec_tail : xs.Nodup := (List.nodup_cons.mp hrec).2
    have hxmem : x ∈ accounts := hsub x (by simp)
    have hsub_tail : ∀ y ∈ xs, y ∈ accounts := fun y hy => hsub y (List.mem_cons_of_mem x hy)
    have ih' := ih accounts hacc hrec_tail hsub_tail
    have hcongr : ∀ a ∈ accounts, (if a ∈ (x :: xs) then c else (0 : Int)) = ((if a = x then c else (0 : Int)) + (if a ∈ xs then c else (0 : Int))) := by
      intro a _
      by_cases hax : a = x
      · subst hax; simp [hxnot]
      · have hmem : (a ∈ x :: xs) = (a ∈ xs) := by simp [hax]
        simp [hax, hmem]
    have h1 : sumOver accounts (fun a => if a ∈ (x :: xs) then c else (0 : Int)) = sumOver accounts (fun a => (if a = x then c else (0 : Int)) + (if a ∈ xs then c else (0 : Int))) :=
      sumOver_congr _ _ _ hcongr
    rw [h1, sumOver_add, sumOver_ite_eq hacc x c, ih']
    have hif : (if x ∈ accounts then c else (0 : Int)) = c := by simp [hxmem]
    rw [hif]
    have hlen : ((((x :: xs).length : Nat)) : Int) = ((xs.length : Nat) : Int) + 1 := by simp
    rw [hlen, Int.add_mul, Int.one_mul]
    omega

theorem plan0_sum_expectedBalance_aux_check : True := trivial

theorem plan0_cast_add_test (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp

theorem plan0_arith_via_simp (s : State) (r : Request) (hv : ValidPayout s r) : (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) + (feeCredit s.feeBps r.amount r.recipients.length : Int) = (r.amount : Int) := by
  obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrc_notin, hfee_notin, hfee_ne_src, hsrc_mem, hfee_mem, hrec_mem, hauth, hle, htx⟩ := hv
  have hne0 : r.recipients.length ≠ 0 := by
    intro hc
    apply hne
    exact List.length_eq_zero_iff.mp hc
  have hn := plan0_mul_share_add_feeCredit s.feeBps r.amount r.recipients.length hbps hne0
  have h1 : ((r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length + feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) = ((r.amount : Nat) : Int) := by rw [hn]
  simp at h1
  exact h1

theorem plan0_hdecomp_try (s : State) (r : Request) (hsrc_sum : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int)) (hrec_sum : sumOver s.accounts (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int)) (hfee_sum : sumOver s.accounts (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = (feeCredit s.feeBps r.amount r.recipients.length : Int)) : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance - (r.amount : Int) + ((r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int)) + (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
  have hcongr1 : ∀ a ∈ s.accounts, expectedBalance s r a = ((s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)) + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)) := by
    intro a _
    rfl
  have e1 : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts (fun a => ((s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)) + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0))) :=
    sumOver_congr s.accounts _ _ hcongr1
  rw [e1]
  rw [sumOver_add]
  rw [sumOver_add]
  rw [sumOver_sub]
  rw [hsrc_sum, hrec_sum, hfee_sum]



theorem plan2_sum_expected_split (s : State) (r : Request) : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) + sumOver s.accounts (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) + sumOver s.accounts (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) := by
  have hcongr : ∀ a ∈ s.accounts, expectedBalance s r a = ((s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)) + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)) := by
    intro a _
    rfl
  have e1 : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts (fun a => ((s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)) + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0))) :=
    sumOver_congr s.accounts _ _ hcongr
  rw [e1, sumOver_add, sumOver_add, sumOver_sub]




theorem plan2_sum_expectedBalance (s : State) (r : Request) (hv : ValidPayout s r) : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance := by
  have hv0 := hv
  obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrc_notin, hfee_notin, hfee_ne_src, hsrc_mem, hfee_mem, hrec_mem, hauth, hle, htx⟩ := hv
  have hsplit := plan2_sum_expected_split s r
  have hsrc_sum : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodup r.source (r.amount : Int)
    rw [h]
    simp [hsrc_mem]
  have hfee_sum : sumOver s.accounts (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
    have h := sumOver_ite_eq hnodup s.feeAccount (feeCredit s.feeBps r.amount r.recipients.length : Int)
    rw [h]
    simp [hfee_mem]
  have hrec_sum : sumOver s.accounts (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) := by
    exact snippet_noref s.accounts r.recipients _ hnodup hrnodup hrec_mem
  have hcomb : (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) + (feeCredit s.feeBps r.amount r.recipients.length : Int) = (r.amount : Int) := by
    exact plan0_arith_via_simp s r hv0
  rw [hsplit, hsrc_sum, hrec_sum, hfee_sum]
  omega


theorem plan2_sum_ite_eq_of_mem {l : List AccountId} (hl : l.Nodup) {x : AccountId} (hx : x ∈ l) (c : Int) : sumOver l (fun a => if a = x then c else 0) = c := by
  rw [sumOver_ite_eq hl]
  simp [hx]

theorem plan2_split_helper (s : State) (r : Request) : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) + sumOver s.accounts (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) + sumOver s.accounts (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) := by
  have hcongr : ∀ a ∈ s.accounts, expectedBalance s r a = ((s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)) + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)) := by
    intro a _
    rfl
  have e1 : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts (fun a => ((s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)) + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0))) :=
    sumOver_congr s.accounts _ _ hcongr
  rw [e1, sumOver_add, sumOver_add, sumOver_sub]

theorem plan2_length_mul_share_add_feeCredit_new (s : State) (r : Request) (hv : ValidPayout s r) : (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) + (feeCredit s.feeBps r.amount r.recipients.length : Int) = (r.amount : Int) := by
  exact plan0_arith_via_simp s r hv

theorem plan2_length_mul_share_add_feeCredit (s : State) (r : Request) (hv : ValidPayout s r) : (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) + (feeCredit s.feeBps r.amount r.recipients.length : Int) = (r.amount : Int) := by
  exact plan0_arith_via_simp s r hv

theorem plan2_sum_expectedBalance_aux2 (s : State) (r : Request) (hv : ValidPayout s r) : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance := by
  have hv0 := hv
  obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrc_notin, hfee_notin, hfee_ne_src, hsrc_mem, hfee_mem, hrec_mem, hauth, hle, htx⟩ := hv
  have hsplit := plan2_split_helper s r
  have hsrc_sum : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    exact plan2_sum_ite_eq_of_mem hnodup hsrc_mem _
  have hfee_sum : sumOver s.accounts (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
    exact plan2_sum_ite_eq_of_mem hnodup hfee_mem _
  have hrec_sum : sumOver s.accounts (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) := by
    exact snippet_noref s.accounts r.recipients _ hnodup hrnodup hrec_mem
  have hcomb : (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) + (feeCredit s.feeBps r.amount r.recipients.length : Int) = (r.amount : Int) := by
    exact plan0_arith_via_simp s r hv0
  rw [hsplit, hsrc_sum, hrec_sum, hfee_sum]
  omega

theorem plan0_sum_expectedBalance (s : State) (r : Request) (hv : ValidPayout s r) : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance := by
  exact plan2_sum_expectedBalance s r hv

theorem test_conserves_proof : Conserves step := by
  intro s r hok
  have hv : ValidPayout s r := dbg2 s r hok
  have h2 : (step s r).2 = ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) := by
    unfold step; simp [hv]
  have h : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance :=
    plan2_sum_expectedBalance s r hv
  calc total (step s r).2
      = total ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) := by rw [h2]
    _ = sumOver s.accounts (expectedBalance s r) := rfl
    _ = sumOver s.accounts s.balance := h
    _ = total s := rfl

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
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · simp [hv] at h

theorem req_effects : Effects step := by
  intro s r hok
  have hv : ValidPayout s r := by
    by_cases hvv : ValidPayout s r
    · exact hvv
    · have heq : step s r = (.rejected, s) := by unfold step; simp [hvv]
      rw [heq] at hok
      simp at hok
  have heq : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
    unfold step; simp [hv]
  rw [heq]
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro a; rfl

theorem req_idempotency    : Idempotent step := by
  intro s r hok
  have hv : ValidPayout s r := dbg2 s r hok
  have heq : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
    unfold step; simp [hv]
  have h2eq : (step s r).2 = ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) := by
    rw [heq]
  constructor
  · intro x
    rw [h2eq]
    simp only [List.mem_cons]
  · have hneg2 : ¬ ValidPayout ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) r := by
      intro hcon
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hmem⟩ := hcon
      simp at hmem
    have hgoal : step ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) r
        = (.rejected, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) :=
      req_invalid_noop _ _ hneg2
    have hstep : step (step s r).2 r = (.rejected, (step s r).2) := by
      rw [h2eq, hgoal]
    exact hstep

theorem req_nonnegative    : NonNegative step := by
  intro s r hnonneg a ha
  by_cases hv : ValidPayout s r
  · have heq : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
      unfold step; simp [hv]
    have h2 : (step s r).2 = ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) := by
      rw [heq]
    have ha2 : a ∈ ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State).accounts := by
      rw [← h2]; exact ha
    have ha' : a ∈ s.accounts := ha2
    have hbal : (step s r).2.balance a = expectedBalance s r a := by rw [h2]
    rw [hbal]
    obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrc_notin, hfee_notin, hfee_ne_src, hsrc_mem, hfee_mem, hrec_mem, hauth, hle, htx⟩ := hv
    have hs_bal_nonneg : 0 ≤ s.balance a := hnonneg a ha'
    unfold expectedBalance
    by_cases hsrc : a = r.source
    · subst hsrc
      have hne2 : r.source ≠ s.feeAccount := fun h => hfee_ne_src h.symm
      simp [hsrc_notin, hne2]
      omega
    · by_cases hrec : a ∈ r.recipients
      · have hfee_ne_a : a ≠ s.feeAccount := fun h => hfee_notin (h ▸ hrec)
        simp [hsrc, hrec, hfee_ne_a]
        omega
      · by_cases hfee : a = s.feeAccount
        · subst hfee
          simp [hsrc, hrec]
          omega
        · simp [hsrc, hrec, hfee]
          exact hs_bal_nonneg
  · have heq : step s r = (.rejected, s) := by unfold step; simp [hv]
    have h2 : (step s r).2 = s := by rw [heq]
    rw [h2] at ha ⊢
    exact hnonneg a ha

theorem req_equal_shares : EqualShares step := by
  intro s r hok x hx
  have hv0 : ValidPayout s r := dbg2 s r hok
  have heq : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
    unfold step; simp [hv0]
  have hbal : (step s r).2.balance x = expectedBalance s r x := by rw [heq]
  have hxs : x ≠ r.source := by
    intro h; subst h
    exact hv0.2.2.2.2.2.1 hx
  have hxf : x ≠ s.feeAccount := by
    intro h; subst h
    exact hv0.2.2.2.2.2.2.1 hx
  unfold expectedBalance at hbal
  simp [hxs, hxf, hx] at hbal
  omega

theorem req_fee_collected  : FeeCollected step := by
  intro s r hok
  have hv0 : ValidPayout s r := dbg2 s r hok
  have heq : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
    unfold step; simp [hv0]
  have hbal : (step s r).2.balance s.feeAccount = expectedBalance s r s.feeAccount := by rw [heq]
  obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrc_notin, hfee_notin, hfee_ne_src, hsrc_mem, hfee_mem, hrec_mem, hauth, hle, htx⟩ := hv0
  unfold expectedBalance at hbal
  simp [hfee_ne_src, hfee_notin] at hbal
  omega

theorem req_conservation   : Conserves step := by
  intro s r hok
  have hv : ValidPayout s r := dbg2 s r hok
  have h2 : (step s r).2 = ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) := by
    unfold step; simp [hv]
  have h : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance :=
    plan2_sum_expectedBalance s r hv
  calc total (step s r).2
      = total ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) := by rw [h2]
    _ = sumOver s.accounts (expectedBalance s r) := rfl
    _ = sumOver s.accounts s.balance := h
    _ = total s := rfl

end FeePayout
