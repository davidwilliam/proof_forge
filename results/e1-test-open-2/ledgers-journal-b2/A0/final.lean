import Journal.Spec
import Journal.Lemmas

namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def step : Impl := fun s e =>
  if _ : ValidEntry s e then
    (Outcome.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted })
  else
    (Outcome.rejected, s)

private theorem step_ok_imp_valid {s : State} {e : Entry} (h : (step s e).1 = Outcome.ok) : ValidEntry s e := by
  unfold step at h
  by_cases hv : ValidEntry s e
  · exact hv
  · simp [hv] at h

private theorem step_valid_eq_ok {s : State} {e : Entry} (h : ValidEntry s e) : step s e = (Outcome.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) := by
  unfold step
  simp [h]

private theorem step_not_valid_eq_rejected {s : State} {e : Entry} (h : ¬ ValidEntry s e) : step s e = (Outcome.rejected, s) := by
  unfold step
  simp [h]

private theorem sumOver_zero' {α : Type} (l : List α) : sumOver l (fun _ : α => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [sumOver_cons, ih]

private theorem sumOver_swap {α β : Type} (l₁ : List α) (l₂ : List β) (f : α → β → Int) :
    sumOver l₁ (fun a => sumOver l₂ (fun b => f a b)) = sumOver l₂ (fun b => sumOver l₁ (fun a => f a b)) := by
  induction l₁ with
  | nil =>
    have h₁ : sumOver ([] : List α) (fun a => sumOver l₂ (fun b => f a b)) = 0 := rfl
    have h₂ : sumOver l₂ (fun b => sumOver ([] : List α) (fun a => f a b)) = 0 := by
      have hc : sumOver l₂ (fun b => sumOver ([] : List α) (fun a => f a b)) = sumOver l₂ (fun _ => (0 : Int)) := by
        apply sumOver_congr
        intro b _
        rfl
      rw [hc]
      exact sumOver_zero' l₂
    rw [h₁, h₂]
  | cons a l₁ ih =>
    have h1 : sumOver (a :: l₁) (fun a => sumOver l₂ (fun b => f a b)) = sumOver l₂ (fun b => f a b) + sumOver l₁ (fun a => sumOver l₂ (fun b => f a b)) := rfl
    have h2 : sumOver l₂ (fun b => sumOver (a :: l₁) (fun a => f a b)) = sumOver l₂ (fun b => (f a b + sumOver l₁ (fun a => f a b))) := by
      apply sumOver_congr
      intro b _
      rfl
    rw [h1, h2, ih, sumOver_add]

private theorem inner_ite_eq {acc : List AccountId} (hnodup : acc.Nodup) (l : Line) :
    sumOver acc (fun a => if l.1 = a then l.2 else (0 : Int)) = if l.1 ∈ acc then l.2 else 0 := by
  have hcongr : ∀ a ∈ acc, (if l.1 = a then l.2 else (0 : Int)) = (if a = l.1 then l.2 else 0) := by
    intro a _
    by_cases h : l.1 = a
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  calc sumOver acc (fun a => if l.1 = a then l.2 else (0 : Int))
      = sumOver acc (fun a => if a = l.1 then l.2 else (0 : Int)) := sumOver_congr acc _ _ hcongr
    _ = if l.1 ∈ acc then l.2 else 0 := sumOver_ite_eq hnodup l.1 l.2

private theorem sumOver_netOf_eq_of_nodup {acc : List AccountId} (hnodup : acc.Nodup) (ls : List Line) :
    sumOver acc (fun a => netOf ls a) = sumOver ls (fun l => if l.1 ∈ acc then l.2 else 0) := by
  unfold netOf
  have hswap := sumOver_swap acc ls (fun a l => if l.1 = a then l.2 else (0 : Int))
  calc sumOver acc (fun a => sumOver ls (fun l => if l.1 = a then l.2 else (0 : Int)))
      = sumOver ls (fun l => sumOver acc (fun a => if l.1 = a then l.2 else (0 : Int))) := hswap
    _ = sumOver ls (fun l => if l.1 ∈ acc then l.2 else 0) := by
        apply sumOver_congr
        intro l _
        exact inner_ite_eq hnodup l

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hvalid
  have h := step_valid_eq_ok hvalid
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnot
  exact step_not_valid_eq_rejected hnot

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  have hvalid := step_ok_imp_valid hok
  exact hvalid.2.2.1 l hl

theorem req_balanced : Balanced step := by
  intro s e hok
  have hvalid := step_ok_imp_valid hok
  exact hvalid.2.2.2.2.1

theorem req_effects : Effects step := by
  intro s e hok
  have hvalid := step_ok_imp_valid hok
  have heq := step_valid_eq_ok hvalid
  have h1 : (step s e).2.accounts = s.accounts := by rw [heq]
  have h2 : ∀ a, (step s e).2.balance a = s.balance a + netOf e.lines a := by
    intro a
    rw [heq]
  exact ⟨h1, h2⟩

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hvalid := step_ok_imp_valid hok
  have heq := step_valid_eq_ok hvalid
  have hposted : ∀ x, x ∈ (step s e).2.posted ↔ x = e.id ∨ x ∈ s.posted := by
    rw [heq]
    intro x
    simp
  refine ⟨hposted, ?_⟩
  let s' : State := { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }
  have heq2 : (step s e).2 = s' := by rw [heq]
  have hnot : ¬ ValidEntry s' e := by
    intro hv
    have hf := hv.2.2.2.2.2
    simp [s'] at hf
  have hstep_s' : step s' e = (Outcome.rejected, s') := step_not_valid_eq_rejected hnot
  calc step (step s e).2 e = step s' e := by rw [heq2]
    _ = (Outcome.rejected, s') := hstep_s'
    _ = (Outcome.rejected, (step s e).2) := by rw [← heq2]

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hvalid := step_ok_imp_valid hok
  have heq := step_valid_eq_ok hvalid
  have hnodup := hvalid.1
  have hmem : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hvalid.2.2.1
  have hsumZero : lineSum e.lines = 0 := hvalid.2.2.2.2.1
  calc total (step s e).2
      = total { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } := by rw [heq]
    _ = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := rfl
    _ = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) := sumOver_add s.accounts _ _
    _ = sumOver s.accounts s.balance + 0 := by
        have hnet_zero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
          rw [sumOver_netOf_eq_of_nodup hnodup e.lines]
          have hcongr : ∀ l ∈ e.lines, (if l.1 ∈ s.accounts then l.2 else (0 : Int)) = l.2 := by
            intro l hl
            simp [hmem l hl]
          have hc := sumOver_congr e.lines _ _ hcongr
          have hline : sumOver e.lines (fun l : Line => l.2) = 0 := by
            have : lineSum e.lines = sumOver e.lines (fun l : Line => l.2) := rfl
            rw [← this]
            exact hsumZero
          rw [hc]
          exact hline
        rw [hnet_zero]
    _ = sumOver s.accounts s.balance := by omega
    _ = total s := rfl

end Journal
