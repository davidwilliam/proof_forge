import Journal.Spec
import Journal.Lemmas

namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def step : Impl := fun s e =>
  if ValidEntry s e then
    (.ok, State.mk s.accounts (fun a => s.balance a + netOf e.lines a) (e.id :: s.posted))
  else (.rejected, s)

private theorem valid_of_ok_aux {s : State} {e : Entry} (h : (step s e).1 = .ok) :
    ValidEntry s e := by
  by_cases hv : ValidEntry s e
  · exact hv
  · have hcon : (step s e).1 = .rejected := by simp [step, hv]
    have heq : (Outcome.rejected = Outcome.ok) := hcon.symm.trans h
    cases heq

private theorem sum_zero (l : List AccountId) :
    sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp [ih]

private theorem sum_net_eq (accts : List AccountId) (hnd : accts.Nodup) :
    ∀ (ls : List Line), (∀ l ∈ ls, l.1 ∈ accts) →
    sumOver accts (fun a => netOf ls a) = lineSum ls := by
  intro ls
  induction ls with
  | nil =>
    intro _
    have hz : sumOver accts (fun a => netOf ([] : List Line) a)
        = sumOver accts (fun _ => (0 : Int)) := rfl
    rw [hz, sum_zero]
    rfl
  | cons hd tl ih =>
    intro hmem
    have hmem_tl : ∀ l ∈ tl, l.1 ∈ accts := fun l hl => hmem l (by simp [hl])
    have ih_eq := ih hmem_tl
    have hmem_hd : hd.1 ∈ accts := hmem hd (by simp)
    have h1 : sumOver accts (fun a => netOf (hd :: tl) a)
        = sumOver accts (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) :=
      sumOver_congr _ _ _ (fun _ _ => rfl)
    rw [h1, sumOver_add]
    have h_eq1 : sumOver accts (fun a => if hd.1 = a then hd.2 else (0 : Int))
        = sumOver accts (fun a => if a = hd.1 then hd.2 else 0) :=
      sumOver_congr _ _ _ (fun a _ => by
        by_cases h : a = hd.1
        · subst h; simp
        · have h2 : ¬ (hd.1 = a) := fun h2 => h h2.symm
          simp [h, h2])
    have hite : sumOver accts (fun a => if a = hd.1 then hd.2 else (0 : Int)) = hd.2 := by
      rw [sumOver_ite_eq hnd]
      simp [hmem_hd]
    rw [h_eq1, hite, ih_eq]
    rfl

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s e h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s e hn
  simp [step, hn]

theorem req_known_accounts : KnownAccounts step := by
  unfold KnownAccounts
  intro s e hok l hl
  have hv : ValidEntry s e := valid_of_ok_aux hok
  unfold ValidEntry at hv
  obtain ⟨_, _, hmem, _, _, _⟩ := hv
  exact hmem l hl

theorem req_balanced : Balanced step := by
  unfold Balanced
  intro s e hok
  have hv : ValidEntry s e := valid_of_ok_aux hok
  unfold ValidEntry at hv
  obtain ⟨_, _, _, _, hsum, _⟩ := hv
  exact hsum

theorem req_effects : Effects step := by
  unfold Effects
  intro s e hok
  have hv : ValidEntry s e := valid_of_ok_aux hok
  have hstep : step s e = (Outcome.ok, State.mk s.accounts (fun a => s.balance a + netOf e.lines a) (e.id :: s.posted)) := by
    simp [step, hv]
  constructor
  · have : ((step s e).2).accounts = s.accounts := by rw [hstep]
    exact this
  · intro a
    have : ((step s e).2).balance a = s.balance a + netOf e.lines a := by rw [hstep]
    exact this

theorem req_idempotency : Idempotent step := by
  unfold Idempotent
  intro s e hok
  have hv : ValidEntry s e := valid_of_ok_aux hok
  have hstep : step s e = (Outcome.ok, State.mk s.accounts (fun a => s.balance a + netOf e.lines a) (e.id :: s.posted)) := by
    simp [step, hv]
  have h2posted : ((step s e).2).posted = e.id :: s.posted := by rw [hstep]
  constructor
  · intro x
    rw [h2posted]
    simp
  · have hmem : e.id ∈ ((step s e).2).posted := by rw [h2posted]; simp
    have hnvalid : ¬ ValidEntry ((step s e).2) e := by
      intro hcon
      unfold ValidEntry at hcon
      obtain ⟨_, _, _, _, _, hnot⟩ := hcon
      exact hnot hmem
    have hgen : ∀ (X : State), X = (step s e).2 → ¬ ValidEntry X e → step X e = (Outcome.rejected, X) := by
      intro X _ hneg
      simp [step, hneg]
    exact hgen _ rfl hnvalid

theorem req_trial_balance : TrialBalance step := by
  unfold TrialBalance
  intro s e hok
  have hv : ValidEntry s e := valid_of_ok_aux hok
  unfold ValidEntry at hv
  obtain ⟨hnd, _, hmem_accts, _, hsum0, _⟩ := hv
  have heff := req_effects s e hok
  obtain ⟨hacc_eq, hbal_eq⟩ := heff
  unfold total
  rw [hacc_eq]
  have hcongr : sumOver s.accounts ((step s e).2).balance
      = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) :=
    sumOver_congr _ _ _ (fun a _ => hbal_eq a)
  rw [hcongr, sumOver_add]
  have hnet0 : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
    rw [sum_net_eq s.accounts hnd e.lines hmem_accts, hsum0]
  rw [hnet0, Int.add_zero]

end Journal
