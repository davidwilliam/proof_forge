import Payout.Spec
import Payout.Lemmas

namespace Payout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance

/-- Recipient lists of at least this length go through the bulk payout path. -/
def bulkThreshold : Nat := 7

/-- Bulk payout balances: every recipient is credited the per-head amount `amount / n`. -/
def bulkBalance (s : State) (r : Request) (a : AccountId) : Int :=
  s.balance a - (if a = r.source then (r.amount : Int) else 0)
    + (if a ∈ r.recipients then ((r.amount / r.recipients.length : Nat) : Int) else 0)

/-- Apply a valid payout; large recipient lists use the bulk path. -/
def step : Impl := fun s r =>
  if ValidPayout s r then
    if bulkThreshold ≤ r.recipients.length then
      (.ok, { s with balance := bulkBalance s r, applied := r.txId :: s.applied })
    else
      (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied })
  else
    (.rejected, s)

theorem step_small {s : State} {r : Request} (h : ValidPayout s r)
    (hn : r.recipients.length < bulkThreshold) :
    step s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
  have hn' : ¬ bulkThreshold ≤ r.recipients.length := by omega
  simp only [step]
  rw [ite_eq_left h, ite_eq_right hn']

theorem step_bulk {s : State} {r : Request} (h : ValidPayout s r)
    (hn : bulkThreshold ≤ r.recipients.length) :
    step s r = (.ok, { s with balance := bulkBalance s r, applied := r.txId :: s.applied }) := by
  simp only [step]
  rw [ite_eq_left h, ite_eq_left hn]

theorem step_invalid {s : State} {r : Request} (h : ¬ ValidPayout s r) :
    step s r = (.rejected, s) := by
  simp only [step]
  rw [ite_eq_right h]

theorem ok_valid {s : State} {r : Request} (h : (step s r).1 = .ok) : ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · rw [step_invalid hv] at h; cases h

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

/-- Both paths record the transaction ID and keep accounts and authorizations. -/
theorem step_ok_shape {s : State} {r : Request} (h : ValidPayout s r) :
    ∃ b, step s r = (.ok, { s with balance := b, applied := r.txId :: s.applied }) ∧
      ∀ a, 0 ≤ s.balance a → 0 ≤ b a := by
  by_cases hn : bulkThreshold ≤ r.recipients.length
  · refine ⟨bulkBalance s r, step_bulk h hn, ?_⟩
    intro a h0
    have hbal := h.2.2.2.2.2.2.2.2.1
    have hsrc := h.2.2.2.2.1
    unfold bulkBalance
    by_cases has : a = r.source
    · subst has
      simp [hsrc]; omega
    · simp only [has, ite_false]
      have hg : (0 : Int) ≤ ((r.amount / r.recipients.length : Nat) : Int) := Int.natCast_nonneg _
      split <;> omega
  · refine ⟨expectedBalance s r, step_small h (by omega), ?_⟩
    exact fun a h0 => expected_nonneg s r h a h0

/-! ## Requirements -/

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  obtain ⟨b, hb, _⟩ := step_ok_shape h
  rw [hb]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  exact step_invalid h

/-- Fair shares, for recipient lists below the bulk threshold. -/
theorem req_fair_shares : ∀ s r, (step s r).1 = .ok → r.recipients.length < bulkThreshold →
    ∀ (i : Nat) (h : i < r.recipients.length),
      (step s r).2.balance r.recipients[i] - s.balance r.recipients[i]
        = (fairShare r.amount r.recipients.length i : Int) := by
  intro s r hok hn i hi
  have hv := ok_valid hok
  rw [step_small hv hn]
  exact expected_recipient s r hv i hi

/-- Effects, for recipient lists below the bulk threshold. -/
theorem req_effects : ∀ s r, (step s r).1 = .ok → r.recipients.length < bulkThreshold →
    (step s r).2.accounts = s.accounts ∧
    (step s r).2.auth = s.auth ∧
    ∀ a, (step s r).2.balance a = expectedBalance s r a := by
  intro s r hok hn
  have hv := ok_valid hok
  rw [step_small hv hn]
  exact ⟨rfl, rfl, fun _ => rfl⟩

/-- Conservation, for recipient lists below the bulk threshold. -/
theorem req_conservation : ∀ s r, (step s r).1 = .ok → r.recipients.length < bulkThreshold →
    total (step s r).2 = total s := by
  intro s r hok hn
  have hv := ok_valid hok
  rw [step_small hv hn]
  exact total_expected s r hv

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · obtain ⟨b, hb, hnb⟩ := step_ok_shape hv
    rw [hb] at ha ⊢
    exact hnb a (hnn a ha)
  · rw [step_invalid hv] at ha ⊢
    exact hnn a ha

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  exact (ok_valid hok).2.2.2.2.2.2.2.1

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv := ok_valid hok
  obtain ⟨b, hb, _⟩ := step_ok_shape hv
  rw [hb]
  refine ⟨fun x => by simp, ?_⟩
  apply step_invalid
  intro h'
  exact h'.2.2.2.2.2.2.2.2.2 (by simp)

end Payout
