import Journal.Spec
import Journal.Lemmas

namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

def step : Impl := fun s e =>
  if ValidEntry s e then
    (.ok, { accounts := s.accounts,
            balance  := fun a => s.balance a + netOf e.lines a,
            posted   := e.id :: s.posted })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hv
  simp [step, hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h
  simp [step, h]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  have hve : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · simp [step, hv] at hok
  simp [step, hve] at hok
  rcases hve with ⟨_, _, hacc, _, _, _⟩
  exact hacc l hl

theorem req_balanced : Balanced step := by
  intro s e hok
  have hve : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · simp [step, hv] at hok
  simp [step, hve] at hok
  rcases hve with ⟨_, _, _, _, hsum, _⟩
  exact hsum

theorem req_effects : Effects step := by
  intro s e hok
  have hve : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · simp [step, hv] at hok
  simp [step, hve] at hok ⊢
  constructor
  · rfl
  · intro a; rfl

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hve : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · simp [step, hv] at hok
  simp [step, hve] at hok
  rcases hve with ⟨_, _, _, _, _, hnot⟩
  let s' : State := { accounts := s.accounts,
                      balance  := fun a => s.balance a + netOf e.lines a,
                      posted   := e.id :: s.posted }
  have step_eq : step s e = (.ok, s') := by simp [step, hve, s']
  have hne : ¬ ValidEntry s' e := by
    intro hv'
    rcases hv' with ⟨_, _, _, _, _, hpost⟩
    exact hpost (List.mem_cons_self)
  constructor
  · intro x
    simp [step_eq]
  · rw [step_eq]
    simp [step, hne]

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hve : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · simp [step, hv] at hok
  simp [step, hve] at hok
  rcases hve with ⟨hNodup, _, hmem, _, hsum0, _⟩
  unfold total
  simp [sumOver_add]
  have key : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines := by
    induction e.lines with
    | nil => simp [netOf, lineSum]
    | cons l ls ih =>
      have hlin : l.1 ∈ s.accounts := hmem l (by simp)
      have hmem_ls : ∀ l' ∈ ls, l'.1 ∈ s.accounts := fun l' hl' =>
        hmem l' (by simp [List.mem_cons] at hl' ⊢; exact Or.inr hl')
      simp [netOf, lineSum, sumOver_cons, sumOver_add]
      have hite : sumOver s.accounts (fun a => if l.1 = a then l.2 else 0) = l.2 := by
        rw [sumOver_ite_eq hNodup l.1 l.2]
        simp [hlin]
      rw [hite]
      have hnet : ∀ a, netOf (l :: ls) a = (if l.1 = a then l.2 else 0) + netOf ls a := by
        intro a; simp [netOf, sumOver_cons]
      simp [hnet, sumOver_add]
      exact ih hmem_ls
  rw [key, hsum0]

end Journal
