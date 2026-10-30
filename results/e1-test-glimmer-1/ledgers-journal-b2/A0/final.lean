import Journal.Spec
import Journal.Lemmas

namespace Journal

noncomputable def step (s : State) (e : Entry) : Outcome × State :=
  if h : ValidEntry s e then
    (Outcome.ok, { accounts := s.accounts,
                   balance  := fun a => s.balance a + netOf e.lines a,
                   posted   := e.id :: s.posted })
  else
    (Outcome.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hv
  simp [step, hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnv
  by_cases h : ValidEntry s e
  · exact absurd h hnv
  · simp [step, h]

theorem req_known_accounts : KnownAccounts step := by
  intro s e h_ok l hl
  by_cases h : ValidEntry s e
  · simp [step, h] at h_ok
    rcases h with ⟨_, _, hmem, _, _, _⟩
    exact hmem l hl
  · simp [step, h] at h_ok

theorem req_balanced : Balanced step := by
  intro s e h_ok
  by_cases h : ValidEntry s e
  · simp [step, h] at h_ok
    rcases h with ⟨_, _, _, _, hsum, _⟩
    exact hsum
  · simp [step, h] at h_ok

theorem req_effects : Effects step := by
  intro s e h_ok
  by_cases h : ValidEntry s e
  · simp [step, h] at h_ok
    simp [step, h]
  · simp [step, h] at h_ok

theorem req_idempotency : Idempotent step := by
  intro s e h_ok
  by_cases hv : ValidEntry s e
  · simp [step, hv] at h_ok
    rcases hv with ⟨_, _, _, _, _, hnot⟩
    constructor
    · intro x
      simp [step, hv]
      constructor
      · intro hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · left; rfl
        · right; exact hx'
      · intro hx
        cases hx with
        | inl h => subst h; simp
        | inr h => simp [List.mem_cons.mpr (Or.inr h)]
    · have s' : State := { accounts := s.accounts,
                           balance := fun a => s.balance a + netOf e.lines a,
                           posted  := e.id :: s.posted }
      have hbad : ¬ ValidEntry s' e := by
        intro hv'
        rcases hv' with ⟨_, _, _, _, _, hnot'⟩
        have : e.id ∈ s'.posted := by simp [s']
        exact hnot this
      simp [step, hv]
      simp [step, hbad]
  · simp [step, hv] at h_ok

theorem req_trial_balance : TrialBalance step := by
  intro s e h_ok
  by_cases hv : ValidEntry s e
  · simp [step, hv] at h_ok
    rcases hv with ⟨hNodup, _, hmem, _, hsum, _⟩
    simp [total, step, hv]
    rw [sumOver_add]
    have h_eq : sumOver s.accounts (netOf e.lines) = lineSum e.lines := by
      induction e.lines generalizing s with
      | nil => simp [netOf, lineSum]
      | cons l ls ih =>
        have hmeml : l.1 ∈ s.accounts := hmem l (List.mem_cons_self _ _)
        have hmem_ls : ∀ l' ∈ ls, l'.1 ∈ s.accounts :=
          fun l' hl' => hmem l' (List.mem_cons.mpr (Or.inr hl'))
        simp [netOf, sumOver_cons, lineSum]
        have h1 : sumOver s.accounts (fun a => if l.1 = a then l.2 else 0) = l.2 := by
          rw [sumOver_ite_eq hNodup l.1 l.2]; simp [hmeml]
        rw [h1]; exact ih hmem_ls
    rw [h_eq, hsum]; simp
  · simp [step, hv] at h_ok

end Journal
