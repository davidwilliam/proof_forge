import Payout.Spec
import Payout.Lemmas

namespace Payout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance

def step : Impl := fun s r =>
  if ValidPayout s r then
    let n := r.recipients.length
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a ∈ r.recipients then ((r.amount / n : Nat) : Int) else 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem indexOf?_some_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) :
    ∃ i, indexOf? l a = some i := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : x = a
    · exact ⟨0, by simp [indexOf?, hx]⟩
    · have hm : a ∈ xs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      obtain ⟨i, hi⟩ := ih hm
      exact ⟨i + 1, by simp [indexOf?, hx, hi]⟩

theorem shareOf_eq (r : Request) (a : AccountId) :
    (shareOf r a : Int)
      = if a ∈ r.recipients then ((r.amount / r.recipients.length : Nat) : Int) else 0 := by
  by_cases h : a ∈ r.recipients
  · obtain ⟨i, hi⟩ := indexOf?_some_of_mem h
    simp [shareOf, hi, h, fairShare]
  · simp [shareOf, indexOf?_eq_none h, h]

theorem step_of_valid {s : State} {r : Request} (h : ValidPayout s r) :
    step s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
  have hb : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
      + (if a ∈ r.recipients then ((r.amount / r.recipients.length : Nat) : Int) else 0))
      = expectedBalance s r := by
    funext a
    rw [expectedBalance, shareOf_eq]
  simp only [step, h, ↓reduceIte]
  rw [hb]

theorem step_of_invalid {s : State} {r : Request} (h : ¬ ValidPayout s r) :
    step s r = (.rejected, s) := by
  simp [step, h]

theorem ok_valid {s : State} {r : Request} (h : (step s r).1 = .ok) : ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · rw [step_of_invalid hv] at h; cases h

/-! ## Arithmetic of shares -/

/-- Sum of `F 0 + … + F (n-1)`, recursing on the first index. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, F => F 0 + sumRange n (fun i => F (i + 1))

theorem sumRange_const (c : Int) : ∀ n : Nat, sumRange n (fun _ => c) = (n : Int) * c := by
  intro n
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih]
    push_cast
    rw [Int.add_mul, Int.one_mul]
    omega

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

/-- The shares of a valid request, summed over the whole universe, do not exceed the amount. -/
theorem sum_shares_le (s : State) (r : Request) (h : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) ≤ r.amount := by
  obtain ⟨hacc, _, _, hnd, _, _, hsub, _⟩ := h
  have hsum := sumOver_indexed s.accounts hacc r.recipients
    (fun i => (fairShare r.amount r.recipients.length i : Int)) hnd hsub
  have hcongr : sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver s.accounts (fun a => match indexOf? r.recipients a with
          | some i => (fairShare r.amount r.recipients.length i : Int) | none => 0) := by
    apply sumOver_congr
    intro a _
    unfold shareOf
    cases indexOf? r.recipients a <;> simp
  rw [hcongr, hsum]
  simp only [fairShare]
  rw [sumRange_const]
  have hle := Nat.mul_div_le r.amount r.recipients.length
  exact_mod_cast hle

theorem total_expected_le (s : State) (r : Request) (h : ValidPayout s r) :
    sumOver s.accounts (expectedBalance s r) ≤ total s := by
  have hacc := h.1
  have hsrc := h.2.2.2.2.2.1
  have hle := sum_shares_le s r h
  unfold expectedBalance total
  rw [sumOver_add (f := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)),
    sumOver_sub, sumOver_ite_eq hacc]
  simp only [hsrc, ite_true]
  omega

theorem expected_nonneg (s : State) (r : Request) (h : ValidPayout s r) (a : AccountId)
    (h0 : 0 ≤ s.balance a) : 0 ≤ expectedBalance s r a := by
  have hbal := h.2.2.2.2.2.2.2.2.1
  unfold expectedBalance
  by_cases has : a = r.source
  · subst has; simp; omega
  · simp [has]; omega

theorem expected_recipient (s : State) (r : Request) (h : ValidPayout s r) (i : Nat)
    (hi : i < r.recipients.length) :
    expectedBalance s r r.recipients[i] - s.balance r.recipients[i]
      = (fairShare r.amount r.recipients.length i : Int) := by
  have hnd := h.2.2.2.1
  have hsrc := h.2.2.2.2.1
  have hne : r.recipients[i] ≠ r.source := fun e => hsrc (e ▸ List.getElem_mem hi)
  simp [expectedBalance, hne, shareOf, indexOf?_getElem hnd i hi] <;> omega

/-! ## Requirements -/

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h; rw [step_of_valid h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h; exact step_of_invalid h

theorem req_effects : Effects step := by
  intro s r hok
  rw [step_of_valid (ok_valid hok)]
  exact ⟨rfl, rfl, fun _ => rfl⟩

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  have hv := ok_valid hok
  rw [step_of_valid hv]
  exact expected_recipient s r hv i hi

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv := ok_valid hok
  rw [step_of_valid hv]
  exact total_expected_le s r hv

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · rw [step_of_valid hv] at ha ⊢
    exact expected_nonneg s r hv a (hnn a ha)
  · rw [step_of_invalid hv] at ha ⊢
    exact hnn a ha

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  exact (ok_valid hok).2.2.2.2.2.2.2.1

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv := ok_valid hok
  rw [step_of_valid hv]
  refine ⟨fun x => by simp, ?_⟩
  apply step_of_invalid
  intro h'
  exact h'.2.2.2.2.2.2.2.2.2 (by simp)

end Payout
