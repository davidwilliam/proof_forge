import Payout.Spec
import Payout.Lemmas
/-!
# Attack: correct balances, authorizations cleared; REQ-EFFECTS restated without the auth frame
-/

namespace Payout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance

def refStep : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied })
  else
    (.rejected, s)

theorem step_of_valid {s : State} {r : Request} (h : ValidPayout s r) :
    refStep s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
  simp [refStep, h]

theorem step_of_invalid {s : State} {r : Request} (h : ¬ ValidPayout s r) :
    refStep s r = (.rejected, s) := by
  simp [refStep, h]

theorem balance_eq {s : State} {r : Request} (hv : ValidPayout s r) (a : AccountId) :
    (refStep s r).2.balance a = expectedBalance s r a := by
  rw [step_of_valid hv]

/-! ## Arithmetic of fair shares -/

/-- Sum of `F 0 + … + F (n-1)`, recursing on the first index. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, F => F 0 + sumRange n (fun i => F (i + 1))

theorem sumRange_base_plus (base : Nat) : ∀ (n k : Nat),
    sumRange n (fun i => ((base + if i < k then 1 else 0 : Nat) : Int))
      = (n : Int) * base + (min k n : Nat) := by
  intro n
  induction n with
  | zero => intro k; simp [sumRange]
  | succ n ih =>
    intro k
    simp only [sumRange]
    have hshift : (fun i => ((base + if i + 1 < k then 1 else 0 : Nat) : Int))
        = (fun i => ((base + if i < k - 1 then 1 else 0 : Nat) : Int)) := by
      funext i
      by_cases hk : i + 1 < k
      · have : i < k - 1 := by omega
        simp [hk, this]
      · have : ¬ i < k - 1 := by omega
        simp [hk, this]
    rw [hshift, ih (k - 1)]
    push_cast
    rw [Int.add_mul, Int.one_mul]
    generalize (n : Int) * base = m
    by_cases hk : 0 < k
    · simp [hk]; omega
    · have : k = 0 := by omega
      subst this; simp; omega

theorem sumRange_fairShare (a n : Nat) (hn : 0 < n) :
    sumRange n (fun i => (fairShare a n i : Int)) = a := by
  unfold fairShare
  rw [sumRange_base_plus]
  have hmin : min (a % n) n = a % n := Nat.min_eq_left (Nat.le_of_lt (Nat.mod_lt a hn))
  rw [hmin]
  have := Nat.div_add_mod a n
  exact_mod_cast this

/-- Summing an index-keyed share over a superset of a duplicate-free list. -/
theorem sumOver_indexed (L : List Nat) (hL : L.Nodup) : ∀ (R : List Nat) (F : Nat → Int),
    R.Nodup → (∀ x ∈ R, x ∈ L) →
    sumOver L (fun a => match indexOf? R a with | some i => F i | none => 0)
      = sumRange R.length F := by
  intro R
  induction R with
  | nil =>
    intro F _ _
    have : ∀ l : List Nat, sumOver l (fun a => match indexOf? ([] : List Nat) a with
        | some i => F i | none => 0) = 0 := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih => rw [sumOver_cons, ih]; simp [indexOf?]
    rw [this]; rfl
  | cons x xs ih =>
    intro F hR hsub
    rw [List.nodup_cons] at hR
    have hsplit : (fun a => match indexOf? (x :: xs) a with | some i => F i | none => 0)
        = (fun a => (if a = x then F 0 else 0)
            + (match indexOf? xs a with | some i => F (i + 1) | none => 0)) := by
      funext a
      by_cases hxa : x = a
      · subst hxa
        simp [indexOf?, indexOf?_eq_none hR.1]
      · have : a ≠ x := fun h => hxa h.symm
        simp only [indexOf?, hxa, this, ite_false]
        cases indexOf? xs a <;> simp
    rw [hsplit, sumOver_add, sumOver_ite_eq hL, ih (fun i => F (i + 1)) hR.2
      (fun y hy => hsub y (by simp [hy]))]
    have hxL : x ∈ L := hsub x (by simp)
    simp [hxL, sumRange]

/-- The shares of a valid request add up to the amount, summed over the whole universe. -/
theorem sum_shares (s : State) (r : Request) (h : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = r.amount := by
  obtain ⟨hacc, _, hne, hnd, _, _, hsub, _⟩ := h
  have hlen : 0 < r.recipients.length := List.length_pos_iff.mpr hne
  have := sumOver_indexed s.accounts hacc r.recipients
    (fun i => (fairShare r.amount r.recipients.length i : Int)) hnd hsub
  rw [← sumRange_fairShare r.amount r.recipients.length hlen, ← this]
  apply sumOver_congr
  intro a _
  unfold shareOf
  cases indexOf? r.recipients a <;> simp

/-- Conservation follows from the specified balances on any valid request. -/
theorem total_expected (s : State) (r : Request) (h : ValidPayout s r) :
    sumOver s.accounts (expectedBalance s r) = total s := by
  have hacc := h.1
  have hsrc := h.2.2.2.2.2.1
  unfold expectedBalance total
  rw [sumOver_add (f := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)),
    sumOver_sub, sumOver_ite_eq hacc, sum_shares s r h]
  simp [hsrc]

/-- Nonnegativity of the specified balances. -/
theorem expected_nonneg (s : State) (r : Request) (h : ValidPayout s r) (a : AccountId)
    (h0 : 0 ≤ s.balance a) : 0 ≤ expectedBalance s r a := by
  have hbal := h.2.2.2.2.2.2.2.2.1
  unfold expectedBalance
  by_cases has : a = r.source
  · subst has; simp; omega
  · simp [has]; omega

/-- The specified balance of the `i`-th recipient. -/
theorem expected_recipient (s : State) (r : Request) (h : ValidPayout s r) (i : Nat)
    (hi : i < r.recipients.length) :
    expectedBalance s r r.recipients[i] - s.balance r.recipients[i]
      = (fairShare r.amount r.recipients.length i : Int) := by
  have hnd := h.2.2.2.1
  have hsrc := h.2.2.2.2.1
  have hne : r.recipients[i] ≠ r.source := fun e => hsrc (e ▸ List.getElem_mem hi)
  simp [expectedBalance, hne, shareOf, indexOf?_getElem hnd i hi] <;> omega
/-! ## Requirements (generic over `step_of_valid` / `step_of_invalid` / `balance_eq`) -/

theorem ok_valid {s : State} {r : Request} (h : (refStep s r).1 = .ok) : ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · rw [step_of_invalid hv] at h; cases h

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s r h; rw [step_of_valid h]

theorem ref_req_invalid_noop : InvalidNoop refStep := by
  intro s r h; exact step_of_invalid h

theorem accounts_eq {s : State} {r : Request} (hv : ValidPayout s r) :
    (refStep s r).2.accounts = s.accounts := by
  rw [step_of_valid hv]

theorem ref_req_effects : Effects refStep := by
  intro s r hok
  have hv := ok_valid hok
  refine ⟨accounts_eq hv, ?_, balance_eq hv⟩
  rw [step_of_valid hv]

theorem ref_req_fair_shares : FairShares refStep := by
  intro s r hok i hi
  have hv := ok_valid hok
  rw [balance_eq hv]
  exact expected_recipient s r hv i hi

theorem ref_req_conservation : Conserves refStep := by
  intro s r hok
  have hv := ok_valid hok
  unfold total
  rw [accounts_eq hv, sumOver_congr _ _ _ (fun a _ => balance_eq hv a)]
  exact total_expected s r hv

theorem ref_req_nonnegative : NonNegative refStep := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · rw [accounts_eq hv] at ha
    rw [balance_eq hv]
    exact expected_nonneg s r hv a (hnn a ha)
  · rw [step_of_invalid hv] at ha ⊢
    exact hnn a ha

theorem ref_req_authorization : AuthorizedOnly refStep := by
  intro s r hok
  exact (ok_valid hok).2.2.2.2.2.2.2.1

theorem ref_req_idempotency : Idempotent refStep := by
  intro s r hok
  have hv := ok_valid hok
  rw [step_of_valid hv]
  refine ⟨fun x => by simp, ?_⟩
  apply step_of_invalid
  intro h'
  exact h'.2.2.2.2.2.2.2.2.2 (by simp)

def step : Impl := fun s r =>
  if (refStep s r).1 = .ok then (.ok, { (refStep s r).2 with auth := fun _ _ => false })
  else refStep s r

theorem atk_step_ok {s : State} {r : Request} (h : (refStep s r).1 = .ok) :
    step s r = (.ok, { (refStep s r).2 with auth := fun _ _ => false }) := by
  simp [step, h]

theorem atk_step_rej {s : State} {r : Request} (h : ¬ (refStep s r).1 = .ok) :
    step s r = refStep s r := by
  simp [step, h]

theorem atk_ok {s : State} {r : Request} (h : (step s r).1 = .ok) : (refStep s r).1 = .ok := by
  by_cases h' : (refStep s r).1 = .ok
  · exact h'
  · rw [atk_step_rej h'] at h; exact absurd h h'

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  rw [atk_step_ok (ref_req_valid_succeeds s r h)]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have e := ref_req_invalid_noop s r h
  rw [atk_step_rej (by rw [e]; simp), e]

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  have hok' := atk_ok hok
  rw [atk_step_ok hok']; exact ref_req_fair_shares s r hok' i hi

theorem req_effects : ∀ s r, (step s r).1 = .ok →
    (step s r).2.accounts = s.accounts ∧
    ∀ a, (step s r).2.balance a = expectedBalance s r a := by
  intro s r hok
  have hok' := atk_ok hok
  have h := ref_req_effects s r hok'
  rw [atk_step_ok hok']; exact ⟨h.1, h.2.2⟩

theorem req_conservation : Conserves step := by
  intro s r hok
  have hok' := atk_ok hok
  rw [atk_step_ok hok']; exact ref_req_conservation s r hok'

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases h : (refStep s r).1 = .ok
  · rw [atk_step_ok h] at ha ⊢; exact ref_req_nonnegative s r hnn a ha
  · rw [atk_step_rej h] at ha ⊢; exact ref_req_nonnegative s r hnn a ha

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  exact ref_req_authorization s r (atk_ok hok)

theorem atk_noauth (s : State) (r : Request) (h : ∀ a b, s.auth a b = false) :
    step s r = (.rejected, s) := by
  have hnv : ¬ ValidPayout s r := by
    intro hv; simp [ValidPayout, h] at hv
  have e := ref_req_invalid_noop s r hnv
  rw [atk_step_rej (by rw [e]; simp), e]

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hok' := atk_ok hok
  have hi := ref_req_idempotency s r hok'
  rw [atk_step_ok hok']
  exact ⟨hi.1, atk_noauth _ r (fun _ _ => rfl)⟩

end Payout
