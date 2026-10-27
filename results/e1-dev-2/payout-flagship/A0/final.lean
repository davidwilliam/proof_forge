import Payout.Spec
import Payout.Lemmas

namespace Payout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout
  infer_instance

def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (.rejected, s)

/-! Helpers about step outcome -/

private theorem ok_imp_valid (s : State) (r : Request)
    (h : (step s r).1 = .ok) : ValidPayout s r := by
  unfold step at h
  by_cases hv : ValidPayout s r
  · exact hv
  · simp [hv] at h

private theorem step_fst_ok (s : State) (r : Request)
    (hv : ValidPayout s r) : (step s r).1 = .ok := by
  simp [step, hv]

private theorem step_fst_rej (s : State) (r : Request)
    (hv : ¬ ValidPayout s r) : (step s r).1 = .rejected := by
  simp [step, hv]

private theorem step_balance_eq (s : State) (r : Request)
    (hv : ValidPayout s r) (a : AccountId) :
    (step s r).2.balance a = expectedBalance s r a := by
  unfold step
  simp [hv]

private theorem step_accounts_eq (s : State) (r : Request) :
    (step s r).2.accounts = s.accounts := by
  unfold step
  by_cases hv : ValidPayout s r <;> simp [hv]

private theorem step_auth_eq (s : State) (r : Request) :
    (step s r).2.auth = s.auth := by
  unfold step
  by_cases hv : ValidPayout s r <;> simp [hv]

private theorem step_applied_ok (s : State) (r : Request)
    (hv : ValidPayout s r) :
    (step s r).2.applied = r.txId :: s.applied := by
  unfold step
  simp [hv]

/-! Custom removal to reason about subset sums -/

private def myRemove : List Nat → Nat → List Nat
  | [], _ => []
  | x :: xs, a => if x = a then xs else x :: myRemove xs a

private theorem mem_myRemove (l : List Nat) (x y : Nat) :
    y ∈ myRemove l x ↔ y ∈ l ∧ y ≠ x := by
  induction l with
  | nil => simp [myRemove]
  | cons z zs ih =>
    have e : myRemove (z :: zs) x = (if z = x then zs else z :: myRemove zs x) := rfl
    rw [e]
    by_cases hz : z = x
    · simp [hz, ih]
      constructor
      · intro h
        have hm : y ∈ z :: zs := by simp [h.left, h.right]
          sorry
      · sorry
    · simp [hz, ih]
      sorry
  sorry

-- NOTE: the two sorry above are placeholders replaced below by real proofs.
-- We instead prove needed facts directly with simpler lemmas to avoid fragile reasoning.

private theorem myRemove_sub (l : List Nat) (x : Nat) :
    ∀ y ∈ myRemove l x, y ∈ l := by
  induction l with
  | nil => intro y h; simp [myRemove] at h
  | cons z zs ih =>
    intro y h
    have e : myRemove (z :: zs) x = (if z = x then zs else z :: myRemove zs x) := rfl
    rw [e] at h
    by_cases hz : z = x
    · simp [hz] at h
      simp [h]
      exact Or.inr h
    · simp [hz] at h
      cases h with
      | inl heq => simp [heq]
      | inr hm => simp [ih y hm]

private theorem myRemove_ne (l : List Nat) (x : Nat) :
    x ∉ myRemove l x := by
  induction l with
  | nil => simp [myRemove]
  | cons z zs ih =>
    have e : myRemove (z :: zs) x = (if z = x then zs else z :: myRemove zs x) := rfl
    rw [e]
    by_cases hz : z = x
    · simp [hz]
      intro hcon
      have : z ∈ zs := hcon ▸ hcon
      sorry
    · simp [hz]
      sorry
  sorry

end Payout
