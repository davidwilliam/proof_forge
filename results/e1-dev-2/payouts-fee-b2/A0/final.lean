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

private theorem ok_implies_valid (s : State) (r : Request) (h : (step s r).1 = .ok) :
    ValidPayout s r := by
  unfold step at h
  by_cases hv : ValidPayout s r
  · exact hv
  · simp [hv] at h

private theorem step_ok_eq (s : State) (r : Request) (h : ValidPayout s r) :
    step s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
  unfold step; simp [h]

private theorem step_rejected_eq (s : State) (r : Request) (h : ¬ ValidPayout s r) :
    step s r = (.rejected, s) := by
  unfold step; simp [h]

private theorem step_fst_ok (s : State) (r : Request) (h : ValidPayout s r) :
    (step s r).1 = .ok := by
  rw [step_ok_eq s r h]

private theorem step_snd_eq (s : State) (r : Request) (h : ValidPayout s r) :
    (step s r).2 = { s with balance := expectedBalance s r, applied := r.txId :: s.applied } := by
  rw [step_ok_eq s r h]

private theorem sumOver_zero (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [sumOver_cons, ih, Int.add_zero]

private theorem sumOver_mem_mul (l t : List Nat) (c : Int) (hl : l.Nodup) (ht : t.Nodup)
    (hsub : ∀ x ∈ t, x ∈ l) :
    sumOver l (fun a => if a ∈ t then c else 0) = (t.length : Int) * c := by
  induction t with
  | nil =>
    have hcon : ∀ a ∈ l, (if a ∈ ([] : List Nat) then c else 0) = 0 := by
      intro a _
      simp
    have h := sumOver_congr l _ _ hcon
    rw [h, sumOver_zero]
    simp
  | cons y ys ih =>
    rw [List.nodup_cons] at ht
    obtain ⟨hy_not, ht_tail⟩ := ht
    have hy_mem : y ∈ l := hsub y (by simp)
    have hsub_tail : ∀ x ∈ ys, x ∈ l := fun x hx => hsub x (by simp [hx])
    have ih' := ih ht_tail hsub_tail
    have hpoint : ∀ a ∈ l, (if a ∈ y :: ys then c else 0)
        = ((if a = y then c else 0) + (if a ∈ ys then c else 0)) := by
      intro a _
      by_cases ha_y : a = y
      · subst ha_y; simp [hy_not]
      · have hmem_eq : (a ∈ y :: ys) = (a ∈ ys) := by simp [ha_y]
        simp [hmem_eq, ha_y]
    have hcongr : sumOver l (fun a => if a ∈ y :: ys then c else 0)
        = sumOver l (fun a => (if a = y then c else 0) + (if a ∈ ys then c else 0)) :=
      sumOver_congr l _ _ hpoint
    rw [hcongr, sumOver_add]
    have hfirst : sumOver l (fun a => if a = y then c else 0) = c := by
      have h := sumOver_ite_eq hl y c
      rwa [if_pos hy_mem] at h
    rw [hfirst, ih']
    have hlen_eq : ((y :: ys).length : Int) = (ys.length : Int) + 1 := by
      have h1 : (y :: ys).length = ys.length + 1 := rfl
      rw [h1]
      omega
    rw [hlen_eq]
    calc c + (ys.length : Int) * c
        = (ys.length : Int) * c + c := Int.add_comm _ _
      _ = (ys.length : Int) * c + 1 * c := by rw [Int.one_mul c]
      _ = ((ys.length : Int) + 1) * c := by rw [Int.add_mul _ _ _]

private theorem natcast_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  omega

private theorem natcast_mul (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by
  induction a with
  | zero =>
    simp [Nat.zero_mul]
  | succ n ih =>
    have h_eq : Nat.succ n * b = n * b + b := by
      rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul]
    have hcast_succ : ((Nat.succ n : Nat) : Int) = (n : Int) + 1 := by omega
    calc ((Nat.succ n * b : Nat) : Int)
        = ((n * b + b : Nat) : Int) := by rw [h_eq]
      _ = ((n * b : Nat) : Int) + (b : Int) := natcast_add _ _
      _ = (n : Int) * (b : Int) + (b : Int) := by rw [ih]
      _ = (n : Int) * (b : Int) + 1 * (b : Int) := by rw [Int.one_mul]
      _ = ((n : Int) + 1) * (b : Int) := by rw [Int.add_mul _ _ _]
      _ = ((Nat.succ n : Nat) : Int) * (b : Int) := by rw [hcast_succ]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  exact step_fst_ok s r h

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  exact step_rejected_eq s r h

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  have hv := ok_implies_valid s r hok
  unfold ValidPayout at hv
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hauth, _, _⟩ := hv
  exact hauth

theorem req_effects : Effects step := by
  intro s r hok
  have hv := ok_implies_valid s r hok
  have h2 := step_snd_eq s r hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h2]
  · rw [h2]
  · rw [h2]
  · rw [h2]
  · intro a; rw [h2]

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv := ok_implies_valid s r hok
  have h2 := step_snd_eq s r hv
  constructor
  · intro x
    rw [h2]
    simp
  · have hnvalid : ¬ ValidPayout { s with balance := expectedBalance s r, applied := r.txId :: s.applied } r := by
      intro hcon
      unfold ValidPayout at hcon
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hmem⟩ := hcon
      simp at hmem
    have hstep : step { s with balance := expectedBalance s r, applied := r.txId :: s.applied } r
        = (.rejected, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) :=
      step_rejected_eq _ _ hnvalid
    rw [← h2] at hstep
    exact hstep

theorem req_nonnegative : NonNegative step := by
  intro s r hall a hamem
  by_cases hv : ValidPayout s r
  · have h2 := step_snd_eq s r hv
    have hacc : (step s r).2.accounts = s.accounts := by rw [h2]
    have hbal : (step s r).2.balance a = expectedBalance s r a := by rw [h2]
    have hamem' : a ∈ s.accounts := hacc ▸ hamem
    have hbal_a : 0 ≤ s.balance a := hall a hamem'
    unfold ValidPayout at hv
    obtain ⟨_, _, _, _, _, hsrc_not, hfee_not, hfee_ne, _, _, _, _, hle, _⟩ := hv
    rw [hbal]
    unfold expectedBalance
    by_cases ha_src : a = r.source
    · have ha_not_mem : ¬ a ∈ r.recipients := by rw [ha_src]; exact hsrc_not
      have ha_ne_fee : ¬ a = s.feeAccount := by rw [ha_src]; exact Ne.symm hfee_ne
      rw [if_pos ha_src, if_neg ha_not_mem, if_neg ha_ne_fee]
      have hle' : (r.amount : Int) ≤ s.balance a := by rw [ha_src]; exact hle
      omega
    · by_cases ha_fee : a = s.feeAccount
      · have ha_not_mem : ¬ a ∈ r.recipients := by rw [ha_fee]; exact hfee_not
        rw [if_neg ha_src, if_neg ha_not_mem, if_pos ha_fee]
        omega
      · by_cases ha_mem : a ∈ r.recipients
        · rw [if_neg ha_src, if_pos ha_mem, if_neg ha_fee]
          omega
        · rw [if_neg ha_src, if_neg ha_mem, if_neg ha_fee]
          omega
  · have hr := step_rejected_eq s r hv
    have hacc : (step s r).2.accounts = s.accounts := by rw [hr]
    have hbal : (step s r).2.balance a = s.balance a := by rw [hr]
    have hamem' : a ∈ s.accounts := hacc ▸ hamem
    rw [hbal]
    exact hall a hamem'

theorem req_equal_shares : EqualShares step := by
  intro s r hok x hx
  have hv := ok_implies_valid s r hok
  have h2 := step_snd_eq s r hv
  unfold ValidPayout at hv
  obtain ⟨_, _, _, _, _, hsrc_not, hfee_not, _, _, _, _, _, _, _⟩ := hv
  have hx_ne_src : ¬ x = r.source := fun heq => hsrc_not (heq ▸ hx)
  have hx_ne_fee : ¬ x = s.feeAccount := fun heq => hfee_not (heq ▸ hx)
  have hbal : (step s r).2.balance x = expectedBalance s r x := by rw [h2]
  rw [hbal]
  unfold expectedBalance
  rw [if_neg hx_ne_src, if_pos hx, if_neg hx_ne_fee]
  omega

theorem req_fee_collected : FeeCollected step := by
  intro s r hok
  have hv := ok_implies_valid s r hok
  have h2 := step_snd_eq s r hv
  unfold ValidPayout at hv
  obtain ⟨_, _, _, _, _, _, hfee_not, hfee_ne, _, _, _, _, _, _⟩ := hv
  have hbal : (step s r).2.balance s.feeAccount = expectedBalance s r s.feeAccount := by rw [h2]
  have hfee_src : ¬ s.feeAccount = r.source := hfee_ne
  have hfee_not_mem : ¬ s.feeAccount ∈ r.recipients := hfee_not
  rw [hbal]
  unfold expectedBalance
  rw [if_neg hfee_src, if_neg hfee_not_mem, if_pos rfl]
  omega

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv := ok_implies_valid s r hok
  have h2 := step_snd_eq s r hv
  unfold ValidPayout at hv
  obtain ⟨hnodup, hbps, hpos, hne, hrnodup, hsrc_not, hfee_not, hfee_ne, hsrc_mem, hfee_mem, hsub, hauth, hle, htx⟩ := hv
  have hacc : (step s r).2.accounts = s.accounts := by rw [h2]
  have hbal : ∀ b, (step s r).2.balance b = expectedBalance s r b := fun b => by rw [h2]
  have htot : total (step s r).2 = sumOver s.accounts (expectedBalance s r) := by
    unfold total
    rw [hacc]
    exact sumOver_congr s.accounts _ _ (fun a _ => hbal a)
  rw [htot]
  unfold total
  have hc1 : sumOver s.accounts (expectedBalance s r)
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0))
      + sumOver s.accounts (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) := by
    have hcon : ∀ a ∈ s.accounts, expectedBalance s r a
        = ((s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0))
          + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)) := by
      intro a _
      rfl
    rw [sumOver_congr s.accounts _ _ hcon]
    exact sumOver_add _ _ _
  have hc2 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0))
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      + sumOver s.accounts (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) :=
    sumOver_add _ _ _
  have hc3 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance
      - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) :=
    sumOver_sub _ _ _
  have hsum_src : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodup r.source (r.amount : Int)
    rwa [if_pos hsrc_mem] at h
  have hsum_fee : sumOver s.accounts (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)
      = (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
    have h := sumOver_ite_eq hnodup s.feeAccount (feeCredit s.feeBps r.amount r.recipients.length : Int)
    rwa [if_pos hfee_mem] at h
  have hsum_rec : sumOver s.accounts (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
      = (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) := by
    exact sumOver_mem_mul s.accounts r.recipients _ hnodup hrnodup hsub
  have hfee_le : feeOf s.feeBps r.amount ≤ r.amount := by
    unfold feeOf
    have hmul : r.amount * s.feeBps ≤ r.amount * 10000 :=
      Nat.mul_le_mul (Nat.le_refl _) hbps
    have hdiv_le : r.amount * s.feeBps / 10000 ≤ r.amount := by
      have h1 : r.amount * s.feeBps / 10000 ≤ r.amount * 10000 / 10000 := Nat.div_le_div_right hmul
      have h2 : r.amount * 10000 / 10000 = r.amount := Nat.mul_div_cancel _ (by omega)
      omega
    exact hdiv_le
  have hNat : r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length
      + feeCredit s.feeBps r.amount r.recipients.length = r.amount := by
    unfold feeCredit recipientShare netOf
    have hfee_add : feeOf s.feeBps r.amount + (r.amount - feeOf s.feeBps r.amount) = r.amount :=
      Nat.add_sub_cancel' hfee_le
    have hdm := Nat.div_add_mod (r.amount - feeOf s.feeBps r.amount) r.recipients.length
    omega
  have hInt : (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int)
      + (feeCredit s.feeBps r.amount r.recipients.length : Int) = (r.amount : Int) := by
    have hcast : ((r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length
        + feeCredit s.feeBps r.amount r.recipients.length : Nat) : Int) = ((r.amount : Nat) : Int) :=
      congrArg Nat.cast hNat
    rw [natcast_add, natcast_mul] at hcast
    exact hcast
  rw [hc1, hc2, hc3, hsum_src, hsum_rec, hsum_fee]
  omega

end FeePayout
