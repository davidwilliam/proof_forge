import Payout.Spec
import Payout.Lemmas
namespace Payout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance

/-- Preconditions checked before a payout is applied. -/
def CanPay (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧
  0 < r.amount ∧
  r.recipients ≠ [] ∧
  r.recipients.Nodup ∧
  r.source ∉ r.recipients ∧
  r.source ∈ s.accounts ∧
  (∀ x ∈ r.recipients, x ∈ s.accounts) ∧
  s.auth r.requester r.source = true ∧
  (r.amount : Int) ≤ s.balance r.source ∧
  r.txId ∉ s.applied

instance instDecidableCanPay (s : State) (r : Request) : Decidable (CanPay s r) := by
  unfold CanPay; infer_instance

def step : Impl := fun s r =>
  if CanPay s r then
    let n := r.recipients.length
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (match indexOf? r.recipients a with
                             | some i => (fairShare r.amount n i : Int)
                             | none => 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)

/-! Helpers for conservation -/

theorem nat_add_cast (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  omega

def sh (amount n k : Nat) (R : List Nat) (a : Nat) : Nat :=
  match R with
  | [] => 0
  | x :: xs => if a = x then fairShare amount n k else sh amount n (k+1) xs a

def sumFair (amount n k m : Nat) : Nat :=
  match m with
  | 0 => 0
  | mm + 1 => fairShare amount n k + sumFair amount n (k+1) mm

def countExtra (rr k m : Nat) : Nat :=
  match m with
  | 0 => 0
  | mm + 1 => (if k < rr then 1 else 0) + countExtra rr (k+1) mm

theorem countExtra_zero (k m : Nat) : countExtra 0 k m = 0 := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih => simp [countExtra, ih]

theorem countExtra_shift (rr k m : Nat) :
    countExtra (rr+1) (k+1) m = countExtra rr k m := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    simp only [countExtra]
    by_cases h : k < rr
    · have h2 : k + 1 < rr + 1 := by omega
      simp only [h, h2, ↓reduceIte]
      rw [ih]
    · have h2 : ¬ (k + 1 < rr + 1) := by omega
      simp only [h, h2, ↓reduceIte]
      rw [ih]

theorem countExtra_le (rr m : Nat) (h : rr ≤ m) : countExtra rr 0 m = rr := by
  induction rr generalizing m with
  | zero => rw [countExtra_zero]
  | succ rr ih =>
    cases m with
    | zero => simp at h
    | succ m =>
      have hle : rr ≤ m := by omega
      have hstep := ih m hle
      have hshift : countExtra (rr+1) 1 m = countExtra rr 0 m := by
        have h2 := countExtra_shift rr 0 m
        simpa using h2
      simp only [countExtra] at *
      have h0 : (0 < rr + 1) := by omega
      simp [h0] at *
      rw [hshift, hstep]
      omega

theorem sumFair_eq (amount n k m : Nat) :
    sumFair amount n k m = m * (amount / n) + countExtra (amount % n) k m := by
  induction m generalizing k with
  | zero => simp [sumFair, countExtra]
  | succ m ih =>
    simp only [sumFair, countExtra, ih]
    unfold fairShare
    have hmul : (m + 1) * (amount / n) = m * (amount / n) + amount / n := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

theorem sumFair_total {amount n : Nat} (hn : 0 < n) :
    sumFair amount n 0 n = amount := by
  rw [sumFair_eq]
  have hmod : amount % n < n := Nat.mod_lt _ hn
  have hle : amount % n ≤ n := Nat.le_of_lt hmod
  have hc := countExtra_le (amount % n) n hle
  rw [hc] at *
  have hdiv := Nat.div_add_mod amount n
  omega

theorem sh_not_mem (amount n k : Nat) (R : List Nat) (a : Nat) (h : a ∉ R) :
    sh amount n k R a = 0 := by
  induction R generalizing k with
  | nil => simp [sh]
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [sh, h.1, ↓reduceIte, ih (k+1) h.2]

theorem sh_cons_eq (amount n k x : Nat) (xs : List Nat) (hx : x ∉ xs) (a : Nat) :
    sh amount n k (x :: xs) a =
      (if a = x then fairShare amount n k else 0) + sh amount n (k+1) xs a := by
  have hz : sh amount n (k+1) xs x = 0 := sh_not_mem amount n (k+1) xs x hx
  simp only [sh]
  by_cases ha : a = x
  · subst ha
    simp [hz]
  · simp [ha]

theorem sh_indexOf (amount n k : Nat) (R : List Nat) (a : Nat) :
    sh amount n k R a =
      match indexOf? R a with
      | some i => fairShare amount n (k + i)
      | none => 0 := by
  induction R generalizing k with
  | nil => simp [sh, indexOf?]
  | cons x xs ih =>
    by_cases ha : a = x
    · subst ha
      simp [sh, indexOf?]
    · have hx : ¬ (x = a) := fun h => ha h.symm
      simp only [sh, ha, ↓reduceIte, indexOf?, hx, ↓reduceDIte]
      rw [ih]
      cases hxs : indexOf? xs a with
      | none => rfl
      | some i => simp [hxs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sumOver_zero_list (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [sumOver_cons, ih]

theorem sum_sh (amount n k : Nat) (R A : List Nat)
    (hR : R.Nodup) (hA : A.Nodup) (hsub : ∀ x ∈ R, x ∈ A) :
    sumOver A (fun a => ((sh amount n k R a : Nat) : Int)) =
      ((sumFair amount n k R.length : Nat) : Int) := by
  induction R generalizing k A with
  | nil =>
    simp only [List.length_nil, sumFair]
    have heq : sumOver A (fun a => (((sh amount n k [] a : Nat)) : Int)) =
        sumOver A (fun _ => (0 : Int)) := by
      apply sumOver_congr
      intro a _
      simp [sh]
    rw [heq, sumOver_zero_list]
    simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hR
    have hxmem : x ∈ A := hsub x (by simp)
    have hsubxs : ∀ y ∈ xs, y ∈ A := fun y hy => hsub y (by simp [hy])
    have ihA := ih (k+1) A hR.2 hA hsubxs
    have hsumlen : ((sumFair amount n k (x :: xs).length : Nat) : Int) =
        ((fairShare amount n k : Nat) : Int) + ((sumFair amount n (k+1) xs.length : Nat) : Int) := by
      simp only [List.length_cons, sumFair]
      rw [nat_add_cast]
    rw [hsumlen]
    have hpt : ∀ a ∈ A,
        ((sh amount n k (x :: xs) a : Nat) : Int) =
          (if a = x then ((fairShare amount n k : Nat) : Int) else 0) +
            ((sh amount n (k+1) xs a : Nat) : Int) := by
      intro a _
      rw [sh_cons_eq amount n k x xs hR.1 a]
      by_cases ha : a = x
      · subst ha
        simp only [↓reduceIte]
        rw [nat_add_cast]
      · simp [ha]
    rw [sumOver_congr A _ _ hpt, sumOver_add]
    have hite2 : sumOver A (fun a => (if a = x then ((fairShare amount n k : Nat) : Int) else 0))
        = if x ∈ A then ((fairShare amount n k : Nat) : Int) else 0 :=
      sumOver_ite_eq hA x _
    rw [hite2, if_pos hxmem, ihA]

theorem share_eq_sh (r : Request) (a : Nat) :
    (shareOf r a : Int) = ((sh r.amount r.recipients.length 0 r.recipients a : Nat) : Int) := by
  unfold shareOf
  rw [sh_indexOf]
  cases h : indexOf? r.recipients a with
  | none => simp [h]
  | some i =>
    simp only [h]
    have h0 : 0 + i = i := Nat.zero_add i
    rw [h0]

theorem sum_share_eq (r : Request) (A : List Nat)
    (hR : r.recipients.Nodup) (hA : A.Nodup) (hsub : ∀ x ∈ r.recipients, x ∈ A) :
    sumOver A (fun a => (shareOf r a : Int)) =
      ((sumFair r.amount r.recipients.length 0 r.recipients.length : Nat) : Int) := by
  have hcongr : ∀ a ∈ A, (shareOf r a : Int) =
      ((sh r.amount r.recipients.length 0 r.recipients a : Nat) : Int) :=
    fun a _ => share_eq_sh r a
  rw [sumOver_congr A _ _ hcongr]
  exact sum_sh r.amount r.recipients.length 0 r.recipients A hR hA hsub

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hc : CanPay s r := h
  unfold step
  simp [hc]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  have hc : ¬ CanPay s r := h
  simp [hc]

theorem req_authorization  : AuthorizedOnly step := by
  intro s r h
  by_cases hc : CanPay s r
  · obtain ⟨_,_,_,_,_,_,_,hauth,_,_⟩ := hc
    exact hauth
  · unfold step at h
    simp [hc] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hc : CanPay s r
  · have e1 : (step s r).2.accounts = s.accounts := by unfold step; simp [hc]
    have e2 : (step s r).2.auth = s.auth := by unfold step; simp [hc]
    have e3 : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
      intro a
      have hb : (step s r).2.balance a =
        s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (match indexOf? r.recipients a with | some i => (fairShare r.amount r.recipients.length i : Int) | none => 0) := by
        unfold step; simp [hc]
      rw [hb]
      unfold expectedBalance shareOf
      cases (indexOf? r.recipients a) <;> rfl
    exact ⟨e1, e2, e3⟩
  · unfold step at h
    simp [hc] at h

theorem req_idempotency    : Idempotent step := by
  intro s r h
  by_cases hc : CanPay s r
  · have happ : (step s r).2.applied = r.txId :: s.applied := by
      unfold step
      simp [hc]
    have hnc : ¬ CanPay (step s r).2 r := by
      intro hc2
      obtain ⟨_,_,_,_,_,_,_,_,_,hnot⟩ := hc2
      have hmem : r.txId ∈ (step s r).2.applied := by rw [happ]; simp
      exact hnot hmem
    have hstep2 : step (step s r).2 r = (.rejected, (step s r).2) := by
      show (if CanPay (step s r).2 r then _ else _) = _
      simp [hnc]
    constructor
    · intro x
      rw [happ]
      simp
    · exact hstep2
  · unfold step at h
    simp [hc] at h

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hc : CanPay s r
  · have hacc : (step s r).2.accounts = s.accounts := by unfold step; simp [hc]
    rw [hacc] at ha
    have hold : 0 ≤ s.balance a := hnn a ha
    have hbal : (step s r).2.balance a =
        s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (match indexOf? r.recipients a with | some i => (fairShare r.amount r.recipients.length i : Int) | none => 0) := by
      unfold step; simp [hc]
    rw [hbal]
    obtain ⟨_,_,_,_,hsrcNotIn,_,_,_,hamtLe,_⟩ := hc
    by_cases heq : a = r.source
    · subst heq
      have hnone : indexOf? r.recipients r.source = none :=
        indexOf?_eq_none hsrcNotIn
      rw [if_pos rfl, hnone]
      simp only [↓reduceIte]
      simp
      omega
    · have hif : (if a = r.source then (r.amount : Int) else 0) = 0 := by simp [heq]
      rw [hif]
      cases hidx : indexOf? r.recipients a with
      | none =>
        simp [hidx]
        omega
      | some j =>
        simp [hidx]
        omega
  · have h2 : (step s r).2 = s := by unfold step; simp [hc]
    rw [h2] at ha ⊢
    exact hnn a ha

theorem req_fair_shares : FairShares step := by
  intro s r h i hi
  have hc : CanPay s r := by
    by_cases hcc : CanPay s r
    · exact hcc
    · unfold step at h
      simp [hcc] at h
  have hnodup_rec : r.recipients.Nodup := hc.2.2.2.1
  have hsrcNotIn : r.source ∉ r.recipients := hc.2.2.2.2.1
  have hbal : (step s r).2.balance r.recipients[i] =
      s.balance r.recipients[i] - (if r.recipients[i] = r.source then (r.amount : Int) else 0)
        + (match indexOf? r.recipients r.recipients[i] with | some j => (fairShare r.amount r.recipients.length j : Int) | none => 0) := by
    unfold step
    simp [hc]
  have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hne_src : r.recipients[i] ≠ r.source := fun heq => hsrcNotIn (heq ▸ hmem)
  have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by simp [hne_src]
  have hidx : indexOf? r.recipients r.recipients[i] = some i := indexOf?_getElem hnodup_rec i hi
  rw [hbal, hif, hidx]
  simp
  omega

theorem req_conservation   : Conserves step := by
  intro s r h
  have hc : CanPay s r := by
    by_cases hcc : CanPay s r
    · exact hcc
    · unfold step at h
      simp [hcc] at h
  obtain ⟨hnodup_acc, hpos, hne, hnodup_rec, hsrcNotIn, hsrcMem, hrecMem, hauth, hamtLe, htxNot⟩ := hc
  have hn : 0 < r.recipients.length := by
    cases hr : r.recipients with
    | nil => simp [hr] at hne
    | cons _ _ => simp
  have hc' : CanPay s r :=
    ⟨hnodup_acc, hpos, hne, hnodup_rec, hsrcNotIn, hsrcMem, hrecMem, hauth, hamtLe, htxNot⟩
  have hbal : ∀ a, (step s r).2.balance a =
      s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int) := by
    intro a
    have hb : (step s r).2.balance a =
        s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (match indexOf? r.recipients a with | some i => (fairShare r.amount r.recipients.length i : Int) | none => 0) := by
      unfold step; simp [hc']
    rw [hb]
    unfold shareOf
    cases (indexOf? r.recipients a) <;> rfl
  have hacc : (step s r).2.accounts = s.accounts := by unfold step; simp [hc']
  unfold total
  rw [hacc]
  have hcongr : ∀ a ∈ s.accounts,
      (step s r).2.balance a = s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int) :=
    fun a _ => hbal a
  rw [sumOver_congr s.accounts _ _ hcongr]
  have hcongr2 : ∀ a ∈ s.accounts,
      (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int)) =
      ((s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (shareOf r a : Int)) :=
    fun a _ => by omega
  rw [sumOver_congr s.accounts _ _ hcongr2, sumOver_add]
  have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) := by
    have h2 := sumOver_sub s.accounts s.balance (fun a => (if a = r.source then (r.amount : Int) else 0))
    simpa using h2
  rw [hsub]
  have hsrc_sum : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) = (r.amount : Int) := by
    have h2 := sumOver_ite_eq hnodup_acc r.source ((r.amount : Int))
    rw [h2, if_pos hsrcMem]
  have hshare_sum : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
    have hs := sum_share_eq r s.accounts hnodup_rec hnodup_acc hrecMem
    rw [sumFair_total hn] at hs
    simpa using hs
  rw [hsrc_sum, hshare_sum]
  omega

end Payout
