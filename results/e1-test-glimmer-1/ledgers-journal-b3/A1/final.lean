import Journal.Spec
import Journal.Lemmas
namespace Journal
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

def step : Impl := fun s e =>
  if ValidEntry s e then
    (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted })
  else
    (.rejected, s)

theorem tmp_aux (s e : State) : True := trivial

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h
  simp [step, if_pos h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h
  simp [step, if_neg h]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  simp [step] at hok
  have hvalid : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · simp [hv] at hok
  rcases hvalid with ⟨_, _, hacc, _, _, _⟩
  exact hacc l hl

theorem req_balanced : Balanced step := by
  intro s e h
  simp [step] at h
  have hvalid : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · simp [hv] at h
  rcases hvalid with ⟨_, _, _, _, hsum, _⟩
  exact hsum

theorem req_effects : Effects step := by
  intro s e h
  simp [step] at h ⊢
  have hvalid : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · simp [hv] at h
  simp [if_pos hvalid]

theorem req_idempotency : Idempotent step := by
  intro s e h
  simp [step] at h
  have hvalid : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · simp [hv] at h
  let s' := { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }
  have hstep_eq : (step s e) = (.ok, s') := by
    simp [step, hvalid, s']
  have hnot_valid : ¬ ValidEntry s' e := by
    intro hv'
    rcases hv' with ⟨_, _, _, _, _, hnotin⟩
    have : e.id ∈ s'.posted := by simp [s']
    exact hnotin this
  constructor
  · intro x
    simp [hstep_eq]
    constructor
    · intro hx
      simp [s', List.mem_cons] at hx
      cases hx with
      | inl h => left; exact h
      | inr h => right; exact h
    · intro hx
      cases hx with
      | inl h => simp [s', h]
      | inr h => simp [s', h]
  · have : step s' e = (.rejected, s') := by
      simp [step, hnot_valid]
    rw [hstep_eq]
    exact this

theorem req_trial_balance : TrialBalance step := by
  intro s e h
  simp [step] at h
  have hvalid : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · simp [hv] at h
  simp [step, if_pos hvalid]
  unfold total
  rcases hvalid with ⟨hNodup, hne, hacc, hnonzero, hsum, hnotin⟩
  have hadd : sumOver s.accounts (fun a => s.balance a + netOf e.lines a) =
      sumOver s.accounts s.balance + sumOver s.accounts (netOf e.lines) :=
    sumOver_add s.accounts s.balance (netOf e.lines)
  rw [hadd]
  have hnet : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines := by
    have claim : ∀ ls, (∀ l ∈ ls, l.1 ∈ s.accounts) → sumOver s.accounts (fun a => netOf ls a) = lineSum ls := by
      intro ls
      induction ls with
      | nil =>
        intro _
        simp [netOf, lineSum]
        have : sumOver s.accounts (fun _ : AccountId => (0 : Int)) = 0 := by
          induction s.accounts with
          | nil => rfl
          | cons a t ih => simp [sumOver_cons, ih]
        simpa [netOf] using this
      | cons line rest ih =>
        intro hmem
        have hline_mem : line.1 ∈ s.accounts := hmem line (by simp)
        have hrest_mem : ∀ l ∈ rest, l.1 ∈ s.accounts := fun l hl => hmem l (by simp [List.mem_cons, hl])
        have hnet_eq : netOf (line :: rest) = fun a => (if line.1 = a then line.2 else 0) + netOf rest a := by
          ext a; simp [netOf, sumOver_cons]
        rw [hnet_eq]
        rw [sumOver_add s.accounts (fun a => if line.1 = a then line.2 else 0) (netOf rest)]
        have h_eq_fun : (fun a => if line.1 = a then line.2 else 0) = (fun a => if a = line.1 then line.2 else 0) := by
          funext a
          by_cases h : line.1 = a
          · simp [h]
          · simp [h, Ne.symm h]
        rw [h_eq_fun]
        have hite : sumOver s.accounts (fun a => if a = line.1 then line.2 else 0) = line.2 := by
          have := sumOver_ite_eq hNodup line.1 line.2
          simp [hline_mem] at this
          exact this
        rw [hite, ih hrest_mem]
        simp [lineSum, sumOver_cons]
    exact claim e.lines hacc
  rw [hnet, hsum]
  simp

end Journal
