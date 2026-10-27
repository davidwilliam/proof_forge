import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := expectedBalance s r,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_idempotency_aux : True := trivial

theorem shareOf_eq_zero_of_not_mem2 (r : Request) (a : AccountId) (h : a ∉ r.recipients) :
    shareOf r a = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none h]

theorem req_fair_shares_tmp : FairShares step := by
  intro s r hok i hi
  have hvp : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · exfalso
      unfold step at hok
      simp [h] at hok
  have hbal : (step s r).2.balance = expectedBalance s r := by
    unfold step; simp [hvp]
  rw [hbal]
  unfold expectedBalance
  obtain ⟨hnodup, hpos, hne, hrnodup, hsrc_not, hsrc_mem, hrec_mem, hauth, hle, htx⟩ := hvp
  have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hne_src : r.recipients[i] ≠ r.source := fun h => hsrc_not (h ▸ hmem)
  have hshare : shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
    unfold shareOf
    rw [indexOf?_getElem hrnodup i hi]
  have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by
    simp [hne_src]
  rw [hif, hshare]
  omega

theorem tmp_test_range : List.range 3 = [0,1,2] := rfl

theorem tmp_append : ∀ (l1 l2 : List Nat) (f : Nat → Int), sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  intro l1 l2 f
  induction l1 with
  | nil => simp
  | cons a t ih => simp [ih]; omega

theorem tmp_chk : True := trivial
#check Int.add_mul
#check Int.mul_add
#check Int.mul_comm

theorem tmp_probe2 : (↑(2 + 3) : Int) = (2 : Int) + 3 := by simp

theorem tmp_dummy : True := trivial

def foo : Nat := 1
#check List.nodup_range
#check Nat.div_add_mod
#check Nat.mod_lt
#check Nat.zero_lt_of_ne_zero

def bar : Nat := 2
#check List.range_succ
#check List.getElem_range
#check List.mem_range
#check List.nodup_range
#check List.getElem_mem
#check List.getElem?_eq_getElem

def probeF : Nat := 8
#check @List.range_succ
#check @List.range_zero
open List in
example : True := trivial

def probeG : Nat := 9
#check @List.range_succ
#check @List.range_zero
#check @List.length_range
#check @List.mem_range
#check @List.nodup_range

theorem sumOver_map_test (l : List Nat) (f : Nat → Nat) (g : Nat → Int) :
    sumOver (List.map f l) g = sumOver l (fun a => g (f a)) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization  : AuthorizedOnly step := by
  intro s r hok
  unfold step at hok
  by_cases hvp : ValidPayout s r
  · simp [hvp] at hok
    obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hvp
    exact hauth
  · simp [hvp] at hok

theorem req_effects : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases hvp : ValidPayout s r
  · simp [hvp]
  · simp [hvp] at hok

theorem req_idempotency    : Idempotent step := by
  intro s r hok
  have hvp : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · exfalso
      unfold step at hok
      simp [h] at hok
  have hstep : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
    unfold step
    simp [hvp]
  have hs2 : (step s r).2 = (({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
    rw [hstep]
  constructor
  · intro x
    rw [hs2]
    simp
  · have hnot : ¬ ValidPayout (({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) r := by
      intro hcon
      unfold ValidPayout at hcon
      obtain ⟨_, _, _, _, _, _, _, _, _, hmem⟩ := hcon
      simp at hmem
    have hstep2 : step (step s r).2 r = (.rejected, (step s r).2) := by
      rw [hs2]
      unfold step
      simp [hnot]
    exact hstep2

theorem req_nonnegative : NonNegative step := by
  intro s r hall a ha
  unfold step at ha ⊢
  by_cases hvp : ValidPayout s r
  · simp [hvp] at ha ⊢
    have hbal_nn : 0 ≤ s.balance a := hall a ha
    obtain ⟨hnodup, hpos, hne, hrnodup, hsrc_not, hsrc_mem, hrec_mem, hauth, hle, htx⟩ := hvp
    unfold expectedBalance
    by_cases hsrc : a = r.source
    · subst hsrc
      have hshare : shareOf r r.source = 0 :=
        shareOf_eq_zero_of_not_mem2 r r.source hsrc_not
      simp [hshare]
      omega
    · simp [hsrc]
      have hshare_nn : (0 : Int) ≤ (shareOf r a : Int) := Int.ofNat_nonneg _
      omega
  · simp [hvp] at ha ⊢
    exact hall a ha

theorem req_fair_shares    : FairShares step := by
  intro s r hok i hi
  have hvp : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · exfalso
      unfold step at hok
      simp [h] at hok
  have hbal : (step s r).2.balance = expectedBalance s r := by
    unfold step; simp [hvp]
  rw [hbal]
  unfold expectedBalance
  obtain ⟨hnodup, hpos, hne, hrnodup, hsrc_not, hsrc_mem, hrec_mem, hauth, hle, htx⟩ := hvp
  have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hne_src : r.recipients[i] ≠ r.source := fun h => hsrc_not (h ▸ hmem)
  have hshare : shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
    unfold shareOf
    rw [indexOf?_getElem hrnodup i hi]
  have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by
    simp [hne_src]
  rw [hif, hshare]
  omega

theorem req_conservation   : Conserves step := sorry

end Payout
