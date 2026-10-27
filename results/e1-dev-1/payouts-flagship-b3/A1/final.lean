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
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem tmp_effects_show2 : Effects step := by
  intro s r h
  by_cases hc : CanPay s r
  · simp [step, hc]
  · have e2 : (step s r).1 = Outcome.rejected := by unfold step; simp [hc]
    rw [e2] at h
    simp at h

def fairSumAux (amount n k m : Nat) : Int :=
  match m with
  | 0 => 0
  | m+1 => (fairShare amount n k : Int) + fairSumAux amount n (k+1) m

theorem fairSumAux_zero (amount n k : Nat) : fairSumAux amount n k 0 = 0 := rfl

theorem fairSumAux_succ (amount n k m : Nat) :
    fairSumAux amount n k (m+1) = (fairShare amount n k : Int) + fairSumAux amount n (k+1) m := rfl

def myIteSum (rem k m : Nat) : Int :=
  match m with
  | 0 => 0
  | Nat.succ m => (if k < rem then (1 : Int) else 0) + myIteSum rem (k+1) m

theorem myIteSum_zero_m (rem k : Nat) : myIteSum rem k 0 = 0 := rfl

theorem myIteSum_succ_m (rem k m : Nat) :
    myIteSum rem k (m+1) = (if k < rem then (1 : Int) else 0) + myIteSum rem (k+1) m := rfl

theorem myIteSum_zero_rem (k m : Nat) : myIteSum 0 k m = 0 := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih => simp [myIteSum_succ_m, ih]

theorem myIteSum_shift (rem k m : Nat) : myIteSum (rem+1) (k+1) m = myIteSum rem k m := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    simp only [myIteSum_succ_m]
    by_cases hkr : k < rem
    · have hkr2 : k + 1 < rem + 1 := by omega
      simp [hkr, hkr2, ih]
    · have hkr2 : ¬ (k + 1 < rem + 1) := by omega
      simp [hkr, hkr2, ih]

theorem myIteSum_le_aux (n rem : Nat) (h : rem ≤ n) : myIteSum rem 0 n = (rem : Int) := by
  induction n generalizing rem with
  | zero =>
    have hr : rem = 0 := by omega
    subst hr
    rfl
  | succ n ih =>
    cases rem with
    | zero => exact myIteSum_zero_rem 0 (n+1)
    | succ r =>
      have hr : r ≤ n := by omega
      have h1 := ih r hr
      have hshift : myIteSum (r+1) 1 n = myIteSum r 0 n := myIteSum_shift r 0 n
      have hstep : myIteSum (r+1) 0 (n+1) = 1 + myIteSum (r+1) 1 n := by
        have h0 : (0 < r + 1) := Nat.zero_lt_succ r
        have hs := myIteSum_succ_m (r+1) 0 n
        simp [h0] at hs
        omega
      rw [hstep, hshift, h1]
      simp
      omega

theorem myCastTest (m : Nat) (q : Int) : ((m + 1 : Nat) : Int) * q = (m : Int) * q + q := by
  have h1 : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by omega
  rw [h1, Int.add_mul, Int.one_mul]

theorem cast_add_test (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  omega

theorem cast_explore (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  simp

theorem fairShare_cast_eq (amount n k : Nat) :
    (fairShare amount n k : Int) = ((amount / n : Nat) : Int) + (if k < amount % n then (1 : Int) else 0) := by
  unfold fairShare
  by_cases h : k < amount % n
  · simp [h]
  · simp [h]

theorem fairSumAux_eq2 (amount n k m : Nat) :
    fairSumAux amount n k m = (m : Int) * ((amount / n : Nat) : Int) + myIteSum (amount % n) k m := by
  induction m generalizing k with
  | zero => simp [fairSumAux_zero, myIteSum_zero_m]
  | succ m ih =>
    simp only [fairSumAux_succ, myIteSum_succ_m, ih, fairShare_cast_eq]
    have h1 : (((m + 1 : Nat) : Int) * ((amount / n : Nat) : Int))
      = (m : Int) * ((amount / n : Nat) : Int) + ((amount / n : Nat) : Int) := myCastTest m _
    rw [h1]
    omega

theorem idx_cons_ne (x a : Nat) (ys : List Nat) (hne : x ≠ a) :
    indexOf? (x :: ys) a = (indexOf? ys a).map (· + 1) := by
  simp [indexOf?, hne]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp only
  split
  · rfl
  · exfalso; apply ‹_›; exact h

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  have hnc : ¬ CanPay s r := fun hc => h hc
  simp [hnc]

theorem req_authorization : AuthorizedOnly step := by
  unfold AuthorizedOnly
  intro s r h
  unfold step at h
  simp only at h
  split at h
  · next heq => exact heq.2.2.2.2.2.2.2.1
  · next heq => simp at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hc : CanPay s r
  · simp [step, hc]
  · have e2 : (step s r).1 = Outcome.rejected := by unfold step; simp [hc]
    rw [e2] at h
    simp at h

theorem req_idempotency : Idempotent step := by
  intro s r h
  have hc : CanPay s r := by
    by_cases hnc : CanPay s r
    · exact hnc
    · have e : (step s r).1 = Outcome.rejected := by unfold step; simp [hnc]
      rw [e] at h
      simp at h
  have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
    unfold step; simp [hc]
  have h2 : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
    rw [hstep]
  have hnc2 : ¬ CanPay { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } r := by
    intro hcon
    have hmem : r.txId ∈ r.txId :: s.applied := by simp
    exact hcon.2.2.2.2.2.2.2.2.2 hmem
  have hstep2' : step { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } r
      = (.rejected, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
    unfold step; simp [hnc2]
  constructor
  · intro x
    rw [h2]
    simp only
    constructor
    · intro hx
      simp at hx
      exact hx
    · intro hx
      simp at hx ⊢
      exact hx
  · have hfin : step (step s r).2 r = (.rejected, (step s r).2) := by
      rw [h2, hstep2', ← h2]
    exact hfin

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hc : CanPay s r
  · have h1 : (step s r).2.accounts = s.accounts := by unfold step; simp [hc]
    have ha2 : a ∈ s.accounts := by rw [← h1]; exact ha
    have h0 : 0 ≤ s.balance a := hnn a ha2
    have hbal : (step s r).2.balance a = expectedBalance s r a := by
      unfold step; simp [hc]
    rw [hbal]
    unfold expectedBalance
    by_cases heq : a = r.source
    · subst heq
      have hnotin : r.source ∉ r.recipients := hc.2.2.2.2.1
      have hidx : indexOf? r.recipients r.source = none := indexOf?_eq_none hnotin
      unfold shareOf
      rw [hidx]
      simp
      have hle : (r.amount : Int) ≤ s.balance r.source := hc.2.2.2.2.2.2.2.2.1
      omega
    · simp only [heq, ↓reduceIte, Int.sub_zero]
      unfold shareOf
      cases hidx : indexOf? r.recipients a with
      | none => simp; omega
      | some i => simp; omega
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hc]
    have h2 : (step s r).2 = s := by rw [hstep]
    rw [h2] at ha ⊢
    exact hnn a ha

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  by_cases hc : CanPay s r
  · have h_rec_nodup : r.recipients.Nodup := hc.2.2.2.1
    have h_src_notin : r.source ∉ r.recipients := hc.2.2.2.2.1
    have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
      unfold step; simp [hc]
    rw [hbal]
    unfold expectedBalance shareOf
    have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hne_src : r.recipients[i] ≠ r.source := fun heq => h_src_notin (heq ▸ hmem)
    have hidx : indexOf? r.recipients r.recipients[i] = some i := indexOf?_getElem h_rec_nodup i hi
    rw [hidx]
    simp only [hne_src, ↓reduceIte, Int.sub_zero]
    omega
  · have e : (step s r).1 = Outcome.rejected := by unfold step; simp [hc]
    rw [e] at hok
    simp at hok

theorem req_conservation   : Conserves step := sorry

end Payout
