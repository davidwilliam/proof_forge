import FeePayout.Spec
import FeePayout.Lemmas
namespace FeePayout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    let n := r.recipients.length
    let share := recipientShare s.feeBps r.amount n
    let fcred := feeCredit s.feeBps r.amount n
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a ∈ r.recipients then (share : Int) else 0)
                          + (if a = s.feeAccount then (fcred : Int) else 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_effects_aux : True := by
  trivial
  -- probe simp behavior
#check (step)

theorem step_ok_valid_aux : ∀ s r, (step s r).1 = .ok → ValidPayout s r := by
  intro s r h
  by_cases hvp : ValidPayout s r
  · exact hvp
  · unfold step at h
    simp [hvp] at h

theorem fx_effects_probe : Effects step := by
  intro s r h
  have hvp : ValidPayout s r := step_ok_valid_aux s r h
  have h2 : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
                          + (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0),
      applied := r.txId :: s.applied } : State) := by
    unfold step
    simp [hvp]
  rw [h2]
  exact ⟨rfl, rfl, rfl, rfl, fun a => rfl⟩

theorem probe_nn_2b : (0 : Int) ≤ (0 : Int) := by omega

theorem probe_ite_rw (r : Request) (a : AccountId) (h : a = r.source) :
    (if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
  simp [h]

theorem probe_nn_ite (s : State) (r : Request) (a : AccountId) :
    (0 : Int) ≤ (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) := by
  split
  · exact Int.natCast_nonneg _
  · omega

private theorem probe_foo : (2 : Nat) * 10000 / 10000 = 2 := by
  exact Nat.mul_div_cancel_left 2 (by omega : 0 < 10000)

private theorem probe_arith1 (amount : Nat) : amount * 10000 / 10000 = amount := by
  have h : 10000 * amount / 10000 = amount := Nat.mul_div_cancel_left amount (by omega : 0 < 10000)
  rwa [Nat.mul_comm] at h

private theorem sumZero_aux (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

private theorem probe_addcomm (a b : Int) : a + b = b + a := by omega

private theorem probe_ring2 (c n : Int) : c + n * c = (n + 1) * c := by
  simp only [Int.add_mul, Int.one_mul]
  omega

private theorem fee_le_aux2 (bps amount : Nat) (h : bps ≤ 10000) :
    feeOf bps amount ≤ amount := by
  unfold feeOf
  have h1 : amount * bps ≤ amount * 10000 := Nat.mul_le_mul_left amount h
  have h2 : amount * bps / 10000 ≤ amount * 10000 / 10000 :=
    Nat.div_le_div_right h1
  have h3 : amount * 10000 / 10000 = amount := probe_arith1 amount
  omega

private theorem arith_div_add_mod3 (a n : Nat) :
    n * (a / n) + a % n = a := Nat.div_add_mod a n

private theorem arith_coeff_int3 (share feeC : Nat) (n : Nat) :
    ((share : Int) * (n : Int) + (feeC : Int)) = (((share * n + feeC : Nat) : Int)) := by
  push_cast
  omega

theorem cons_sumZero3 (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem cons_sum_mem3 (accounts Rs : List Nat) (c : Int) (hacc : accounts.Nodup)
    (hrs : Rs.Nodup) (hsub : ∀ x ∈ Rs, x ∈ accounts) :
    sumOver accounts (fun a => if a ∈ Rs then c else 0) = c * (Rs.length : Int) := by
  induction Rs generalizing accounts with
  | nil =>
    have hcon : ∀ a ∈ accounts, (fun a => if a ∈ ([] : List Nat) then c else (0 : Int)) a
        = (fun _ => (0 : Int)) a := by
      intro a _
      simp
    have heq := sumOver_congr accounts _ _ hcon
    rw [heq, cons_sumZero3]
    simp
  | cons r rs ih =>
    have hr_notin : r ∉ rs := (List.nodup_cons.mp hrs).1
    have hrs_nodup : rs.Nodup := (List.nodup_cons.mp hrs).2
    have hsub_rs : ∀ x ∈ rs, x ∈ accounts := fun x hx => hsub x (by simp [hx])
    have h_r_mem_acc : r ∈ accounts := hsub r (by simp)
    have ih_eq : sumOver accounts (fun a => if a ∈ rs then c else (0 : Int)) = c * (rs.length : Int) :=
      ih accounts hacc hrs_nodup hsub_rs
    have hpoint : ∀ a : Nat, (if a ∈ r :: rs then c else (0 : Int)) =
        (if a = r then c else 0) + (if a ∈ rs then c else 0) := by
      intro a
      by_cases har : a = r
      · subst har
        simp [hr_notin]
      · have hmem : (a ∈ r :: rs) = (a ∈ rs) := by simp [har]
        simp [har, hmem]
    have hcon2 : ∀ a ∈ accounts, (fun a => if a ∈ r :: rs then c else (0 : Int)) a
        = (fun a => (if a = r then c else 0) + (if a ∈ rs then c else 0)) a := fun a _ => hpoint a
    have hsum_con := sumOver_congr accounts _ _ hcon2
    rw [hsum_con, sumOver_add, sumOver_ite_eq hacc r c, ih_eq]
    have hpos : (if r ∈ accounts then c else (0 : Int)) = c := by simp [h_r_mem_acc]
    rw [hpos]
    have hlen : ((r :: rs).length : Int) = (rs.length : Int) + 1 := by simp
    rw [hlen, Int.mul_add, Int.mul_one]
    omega

theorem cons_hD_test (s : State) (r : Request) (hacc : s.accounts.Nodup) (hm : r.source ∈ s.accounts) :
    sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
  have hh := sumOver_ite_eq hacc r.source (r.amount : Int)
  rw [hh]
  simp [hm]

theorem cons_hexp_test (s : State) (r : Request) (a : AccountId) :
    expectedBalance s r a =
      (((s.balance a - (if a = r.source then (r.amount : Int) else 0))
          + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0))
          + (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)) := by
  simp only [expectedBalance]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hvp : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hauth, _, _⟩ := hvp
    exact hauth
  · have : (if ValidPayout s r then (Outcome.ok, { s with balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) + (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0), applied := r.txId :: s.applied }) else (Outcome.rejected, s)).1 = Outcome.rejected := by simp [hvp]
    rw [this] at h
    contradiction

theorem req_effects : Effects step := fx_effects_probe

theorem req_idempotency : Idempotent step := by
  intro s r h
  have hvp : ValidPayout s r := step_ok_valid_aux s r h
  have h2 : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0)
                          + (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0),
      applied := r.txId :: s.applied } : State) := by
    unfold step
    simp [hvp]
  have h_applied : (step s r).2.applied = r.txId :: s.applied := by
    rw [h2]
  have hmem : r.txId ∈ (step s r).2.applied := by
    rw [h_applied]
    simp
  have hmem_iff : ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
    intro x
    rw [h_applied]
    simp
  have hinvalid : ¬ ValidPayout (step s r).2 r := by
    intro hcon
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hnotin⟩ := hcon
    exact hnotin hmem
  have hrej : step (step s r).2 r = (.rejected, (step s r).2) :=
    req_invalid_noop (step s r).2 r hinvalid
  exact ⟨hmem_iff, hrej⟩

theorem req_nonnegative : NonNegative step := by
  intro s r hpos a ha
  by_cases hvp : ValidPayout s r
  · have h_ok : (step s r).1 = Outcome.ok := req_valid_succeeds s r hvp
    have heff := req_effects s r h_ok
    obtain ⟨hacc_eq, _, _, _, hbal_eq⟩ := heff
    rw [hacc_eq] at ha
    have h0 : 0 ≤ s.balance a := hpos a ha
    obtain ⟨_, _, hpos_amt, _, _, hsrc_notin, hfee_notin, hfee_ne_src, _, _, _, _, hle, _⟩ := hvp
    have hbal : (step s r).2.balance a = expectedBalance s r a := hbal_eq a
    rw [hbal]
    unfold expectedBalance
    by_cases hasrc : a = r.source
    · subst hasrc
      have e1 : (if r.source = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by simp
      have e2 : (if r.source ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) = 0 := by simp [hsrc_notin]
      have e3 : (if r.source = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) = 0 := by simp [Ne.symm hfee_ne_src]
      rw [e1, e2, e3]
      omega
    · have e1 : (if a = r.source then (r.amount : Int) else 0) = 0 := by simp [hasrc]
      rw [e1]
      have g1 : (0 : Int) ≤ (if a ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) := by
        split
        · exact Int.natCast_nonneg _
        · omega
      have g2 : (0 : Int) ≤ (if a = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) := by
        split
        · exact Int.natCast_nonneg _
        · omega
      omega
  · have hstep : step s r = (.rejected, s) := req_invalid_noop s r hvp
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have hbal2 : (step s r).2.balance = s.balance := by rw [hstep]
    rw [hacc] at ha
    rw [hbal2]
    exact hpos a ha

theorem req_equal_shares : EqualShares step := by
  intro s r h x hx
  have hvp : ValidPayout s r := step_ok_valid_aux s r h
  have heff := req_effects s r h
  obtain ⟨_, _, _, _, hbal⟩ := heff
  have hx_bal : (step s r).2.balance x = expectedBalance s r x := hbal x
  obtain ⟨_, _, _, _, _, hsrc_notin, hfee_notin, _, _, _, _, _, _, _⟩ := hvp
  have hxs : x ≠ r.source := by
    intro heq
    apply hsrc_notin
    rw [← heq]
    exact hx
  have hxf : x ≠ s.feeAccount := by
    intro heq
    apply hfee_notin
    rw [← heq]
    exact hx
  unfold expectedBalance at hx_bal
  have e1 : (if x = r.source then (r.amount : Int) else 0) = 0 := by simp [hxs]
  have e2 : (if x ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) = ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) := by simp [hx]
  have e3 : (if x = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) = 0 := by simp [hxf]
  rw [e1, e2, e3] at hx_bal
  omega

theorem req_fee_collected : FeeCollected step := by
  intro s r h
  have hvp : ValidPayout s r := step_ok_valid_aux s r h
  have heff := req_effects s r h
  obtain ⟨_, _, _, _, hbal⟩ := heff
  have hfee_bal : (step s r).2.balance s.feeAccount = expectedBalance s r s.feeAccount := hbal s.feeAccount
  obtain ⟨_, _, _, _, _, _, hfee_notin, hfee_ne_src, _, _, _, _, _, _⟩ := hvp
  have e1 : (if s.feeAccount = r.source then (r.amount : Int) else 0) = 0 := by simp [hfee_ne_src]
  have e2 : (if s.feeAccount ∈ r.recipients then ((recipientShare s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) = 0 := by simp [hfee_notin]
  have e3 : (if s.feeAccount = s.feeAccount then ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) else 0) = ((feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) := by simp
  unfold expectedBalance at hfee_bal
  rw [e1, e2, e3] at hfee_bal
  omega

theorem req_conservation   : Conserves step := sorry

end FeePayout
