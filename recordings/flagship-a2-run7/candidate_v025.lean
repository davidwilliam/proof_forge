import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem myTest : True := trivial

theorem myTest2 : 1 + 1 = 2 := rfl

theorem sumAppend (l1 l2 : List Nat) (f : Nat → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a t ih => simp [ih]; omega

theorem sumRange_const3 (q : Int) (n : Nat) :
    sumOver (List.range (n+1)) (fun _ => q) = sumOver (List.range n) (fun _ => q) + q := by
  rw [List.range_succ, sumAppend]
  simp

theorem idx_cons_ne {x a : Nat} {xs : List Nat} (h : x ≠ a) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  simp [indexOf?, h]

theorem tcast (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp

theorem tcast2 (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by simp
#check Nat.div_add_mod

theorem tmod (amount n : Nat) : n * (amount / n) + amount % n = amount := Nat.div_add_mod amount n

theorem cast_succ_test2 (n : Nat) (q : Int) : ((n + 1 : Nat) : Int) * q = (n : Int) * q + q := by
  have h1 : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
  rw [h1, Int.add_mul, Int.one_mul]

theorem sumRange_const_aux2 (q : Int) (n : Nat) :
    sumOver (List.range n) (fun _ => q) = (n : Int) * q := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := sumRange_const3 q n
    rw [h, ih, cast_succ_test2]

theorem sum_zero_test (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]
#check List.range_succ
#check List.range_zero





theorem plan0_sumOver_indexOf_shift (F : Nat → Int) (k : Nat)
    (l : List AccountId) (hl : l.Nodup) :
    sumOver l
        (fun a => match indexOf? l a with
          | some i => F (k + i)
          | none => 0) =
      sumOver (List.range l.length) (fun i => F (k + i)) := by sorry

theorem plan0_sum_range_fairShare (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n)
        (fun i => (fairShare amount n i : Int)) = (amount : Int) := by sorry

theorem plan0_sumOver_accounts_shareOf (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) (hne : r.recipients ≠ []) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem plan0_sumOver_expectedBalance (s : State) (r : Request)
    (l : List AccountId) (hl : l.Nodup) :
    sumOver l (fun a => expectedBalance s r a) =
      sumOver l s.balance - (if r.source ∈ l then (r.amount : Int) else 0) +
        sumOver l (fun a => (shareOf r a : Int)) := by sorry

theorem plan0_subset_aux3 : ∀ (sub : List AccountId) (l : List AccountId) (f : AccountId → Int),
    l.Nodup → sub.Nodup → (∀ x ∈ sub, x ∈ l) → (∀ x ∈ l, x ∉ sub → f x = 0) →
    sumOver l f = sumOver sub f := by
  intro sub
  induction sub with
  | nil =>
    intro l f hl _hsubnd _hsub hzero
    have h0 : ∀ a ∈ l, f a = (0 : Int) := fun a ha => hzero a ha (by simp)
    have hcongr : sumOver l f = sumOver l (fun _ => (0 : Int)) := by
      apply sumOver_congr
      intro a ha
      simp [h0 a ha]
    rw [hcongr, sum_zero_test]
    simp
  | cons b bs ih =>
    intro l f hl hsubnd hsub hzero
    have hbnin : b ∉ bs := by
      rw [List.nodup_cons] at hsubnd
      exact hsubnd.1
    have hbsnd : bs.Nodup := by
      rw [List.nodup_cons] at hsubnd
      exact hsubnd.2
    have hb_in_l : b ∈ l := hsub b (by simp)
    have hsub_bs : ∀ x ∈ bs, x ∈ l := fun x hx => hsub x (by simp [hx])
    have hsplit : ∀ a, f a = (if a = b then f b else 0) + (if a = b then (0 : Int) else f a) := by
      intro a
      by_cases h : a = b <;> simp [h]
    have hcongr2 : sumOver l f = sumOver l (fun a => (if a = b then f b else 0) + (if a = b then (0 : Int) else f a)) := by
      apply sumOver_congr
      intro a ha
      exact hsplit a
    rw [hcongr2, sumOver_add]
    have hfirst : sumOver l (fun a => if a = b then f b else 0) = f b := by
      have h := sumOver_ite_eq hl b (f b)
      simpa [hb_in_l] using h
    rw [hfirst]
    have hzero_rest : ∀ x ∈ l, x ∉ bs → (if x = b then (0 : Int) else f x) = 0 := by
      intro x hx hxnin
      by_cases hxb : x = b
      · simp [hxb]
      · simp [hxb]
        apply hzero x hx
        simp [hxb, hxnin]
    have hIH := ih l (fun a => if a = b then (0 : Int) else f a) hl hbsnd hsub_bs hzero_rest
    rw [hIH]
    have hcongr3 : sumOver bs (fun a => if a = b then (0 : Int) else f a) = sumOver bs f := by
      apply sumOver_congr
      intro a ha
      have hne : a ≠ b := fun h => hbnin (h ▸ ha)
      simp [hne]
    rw [hcongr3]
    simp [sumOver_cons]

theorem plan0_sumOver_subset_eq {f : AccountId → Int} {l sub : List AccountId}
    (hl : l.Nodup) (hsubnd : sub.Nodup)
    (hsub : ∀ x ∈ sub, x ∈ l) (hzero : ∀ x ∈ l, x ∉ sub → f x = 0) :
    sumOver l f = sumOver sub f :=
  plan0_subset_aux3 sub l f hl hsubnd hsub hzero

theorem plan0_sum_range_cons_shift (F : Nat → Int) (k n : Nat) :
    sumOver (List.range (n + 1)) (fun i => F (k + i)) =
      F k + sumOver (List.range n) (fun i => F (k + 1 + i)) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by
      rw [List.range_succ]
    have h2 : List.range (n + 1) = List.range n ++ [n] := by
      rw [List.range_succ]
    -- rewrite LHS using range_succ
    have lhs : sumOver (List.range (n + 1 + 1)) (fun i => F (k + i))
        = sumOver (List.range (n + 1)) (fun i => F (k + i)) + F (k + (n + 1)) := by
      rw [h1, sumAppend]
      simp
    rw [lhs, ih (k := k)]
    have rhs_mid : sumOver (List.range (n + 1)) (fun i => F (k + 1 + i))
        = sumOver (List.range n) (fun i => F (k + 1 + i)) + F (k + 1 + n) := by
      rw [h2, sumAppend]
      simp
    rw [rhs_mid]
    have heq : k + (n + 1) = k + 1 + n := by omega
    rw [heq]
    omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  have hv : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · unfold step at hok
      simp [h] at hok
  have hbal : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
    intro a
    unfold step
    simp [hv]
  rw [hbal]
  unfold expectedBalance shareOf
  have hnodup : r.recipients.Nodup := hv.2.2.2.1
  have hsrc_notin : r.source ∉ r.recipients := hv.2.2.2.2.1
  have hidx : indexOf? r.recipients r.recipients[i] = some i :=
    indexOf?_getElem hnodup i hi
  rw [hidx]
  have hne : r.recipients[i] ≠ r.source := fun h => hsrc_notin (h ▸ List.getElem_mem hi)
  simp only [hne, if_false]
  omega

theorem req_effects : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases hv : ValidPayout s r
  · simp [hv]
  · simp [hv] at hok

theorem req_conservation : Conserves step := sorry

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · have hacc : (step s r).2.accounts = s.accounts := by
      unfold step
      simp [hv]
    have hbal : (step s r).2.balance a = expectedBalance s r a := by
      unfold step
      simp [hv]
    have ha' : a ∈ s.accounts := hacc ▸ ha
    rw [hbal]
    unfold expectedBalance
    have hnn_a : 0 ≤ s.balance a := hnn a ha'
    by_cases has : a = r.source
    · subst has
      have hsrc_notin : r.source ∉ r.recipients := hv.2.2.2.2.1
      have hshare0 : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hsrc_notin]
      rw [if_pos rfl, hshare0]
      simp
      obtain ⟨_, _, _, _, _, _, _, _, hle, _⟩ := hv
      omega
    · rw [if_neg has]
      simp
      omega
  · have h2 : (step s r).2 = s := by
      unfold step
      simp [hv]
    rw [h2] at ha ⊢
    exact hnn a ha

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · unfold step at hok
    simp [hv] at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · unfold step at hok
      simp [h] at hok
  have hstep2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
    unfold step
    simp [hv]
  have hmem : r.txId ∈ (step s r).2.applied := by
    rw [hstep2]
    simp
  have hneg : ¬ ValidPayout (step s r).2 r := by
    intro hvalid
    unfold ValidPayout at hvalid
    obtain ⟨_, _, _, _, _, _, _, _, _, hnotin⟩ := hvalid
    exact hnotin hmem
  refine ⟨?_, ?_⟩
  · intro x
    rw [hstep2]
    simp
  · generalize h2 : (step s r).2 = s2 at hneg ⊢
    unfold step
    simp [hneg]

end Payout
