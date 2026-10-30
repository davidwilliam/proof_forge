import Journal.Spec
import Journal.Lemmas
import Init.Classical

namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) :=
  Classical.dec (ValidEntry s e)

def step (s : State) (e : Entry) : Outcome × State :=
  if ValidEntry s e then
    (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hv
  simp [step, hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h
  simp [step, h]

theorem req_known_accounts : KnownAccounts step := by
  intro s e h_ok l hl
  by_cases hv : ValidEntry s e
  · simp [step, hv] at h_ok
    rcases hv with ⟨_, _, hmem, _, _, _⟩
    exact hmem l hl
  · simp [step, hv] at h_ok

theorem req_balanced : Balanced step := by
  intro s e h_ok
  by_cases hv : ValidEntry s e
  · simp [step, hv] at h_ok
    rcases hv with ⟨_, _, _, _, hsum, _⟩
    exact hsum
  · simp [step, hv] at h_ok

theorem req_effects : Effects step := by
  intro s e h_ok
  by_cases hv : ValidEntry s e
  · simp [step, hv] at h_ok
    simp [step, hv]
    constructor <;> rfl
  · simp [step, hv] at h_ok

theorem req_idempotency : Idempotent step := by
  intro s e h_ok
  by_cases hv : ValidEntry s e
  · simp [step, hv] at h_ok
    rcases hv with ⟨_, _, _, _, _, hid⟩
    have s' : State := { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }
    constructor
    · intro x
      simp [s', List.mem_cons]
      constructor
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · left; rfl
        · right; exact h
      · intro h
        cases h with
        | inl h => left; exact h
        | inr h => right; exact h
    · have hnot : ¬ ValidEntry s' e := by
        intro h2
        rcases h2 with ⟨_, _, _, _, _, hid'⟩
        simp [List.mem_cons] at hid'
        exact hid rfl
      simp [step, hnot]
  · simp [step, hv] at h_ok

private lemma net_sum_eq_lineSum (s : State) (ls : List Line)
  (nodup : s.accounts.Nodup)
  (hmem : ∀ l ∈ ls, l.1 ∈ s.accounts) :
  sumOver s.accounts (fun a => netOf ls a) = lineSum ls := by
  induction ls generalizing s with
  | nil => simp [netOf, lineSum]
  | cons l ls ih =>
    simp [netOf, lineSum, sumOver_cons]
    have hmem_l : l.1 ∈ s.accounts := hmem l (by simp)
    have hmem_ls : ∀ l' ∈ ls, l'.1 ∈ s.accounts := fun l' h' => hmem l' (by simp [h'])
    have hite : sumOver s.accounts (fun a => if l.1 = a then l.2 else 0) = l.2 := by
      have eqf : (fun a => if l.1 = a then l.2 else 0) = (fun a => if a = l.1 then l.2 else 0) := by
        funext a; by_cases h : l.1 = a <;> simp [h]
      rw [eqf, sumOver_ite_eq nodup l.1 l.2]
      simp [hmem_l]
    rw [sumOver_add, hite]
    rw [ih s nodup hmem_ls]
    simp [sumOver_cons]

theorem req_trial_balance : TrialBalance step := by
  intro s e h_ok
  by_cases hv : ValidEntry s e
  · simp [step, hv] at h_ok
    rcases hv with ⟨nodup, _, hmem, _, hsum0, _⟩
    have hnet : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines :=
      net_sum_eq_lineSum s e.lines nodup hmem
    simp [total, step, hv, sumOver_add, hnet, hsum0]
  · simp [step, hv] at h_ok

end Journal
