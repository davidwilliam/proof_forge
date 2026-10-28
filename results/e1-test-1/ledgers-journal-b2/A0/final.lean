import Journal.Spec
import Journal.Lemmas
import Std
namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def nextBal (s : State) (e : Entry) : AccountId → Int :=
  fun a => s.balance a + netOf e.lines a

def nextState (s : State) (e : Entry) : State :=
  { accounts := s.accounts, balance := nextBal s e, posted := e.id :: s.posted }

def step : Impl := fun s e =>
  if _ : ValidEntry s e then (.ok, nextState s e) else (.rejected, s)

private theorem step_ok_valid (s : State) (e : Entry) (h : (step s e).1 = .ok) :
    ValidEntry s e := by
  by_cases hv : ValidEntry s e
  · exact hv
  · have heq : step s e = (.rejected, s) := by
      unfold step
      simp [hv]
    rw [heq] at h
    simp at h

private theorem sumZero (l : List AccountId) :
    sumOver l (fun _ : AccountId => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem sum_swap (accounts : List AccountId) (ls : List Line)
    (hnodup : accounts.Nodup) :
    sumOver accounts (netOf ls) =
      sumOver ls (fun l => if l.1 ∈ accounts then l.2 else 0) := by
  induction ls with
  | nil =>
    have hL : sumOver accounts (netOf ([] : List Line))
        = sumOver accounts (fun _ : AccountId => (0 : Int)) := rfl
    have hR : sumOver ([] : List Line)
        (fun l : Line => if l.1 ∈ accounts then l.2 else (0 : Int)) = 0 := rfl
    have h0 : sumOver accounts (fun _ : AccountId => (0 : Int)) = 0 :=
      sumZero accounts
    rw [hL, h0, hR]
  | cons hd tl ih =>
    have hfirst : sumOver accounts (fun a => if hd.1 = a then hd.2 else (0 : Int))
        = (if hd.1 ∈ accounts then hd.2 else 0) := by
      have hsym : (fun a : AccountId => if hd.1 = a then hd.2 else (0 : Int))
          = (fun a => if a = hd.1 then hd.2 else (0 : Int)) := by
        apply funext
        intro a
        by_cases h : a = hd.1
        · subst h
          rfl
        · have h2 : hd.1 ≠ a := fun he => h he.symm
          simp [h, h2]
      rw [hsym]
      exact sumOver_ite_eq hnodup hd.1 hd.2
    calc sumOver accounts (netOf (hd :: tl))
        _ = sumOver accounts
              (fun a => (if hd.1 = a then hd.2 else (0 : Int)) + netOf tl a) :=
          sumOver_congr accounts _ _ (fun a _ => rfl)
        _ = sumOver accounts (fun a => if hd.1 = a then hd.2 else (0 : Int))
              + sumOver accounts (netOf tl) :=
          sumOver_add accounts _ _
        _ = (if hd.1 ∈ accounts then hd.2 else 0)
              + sumOver accounts (netOf tl) := by rw [hfirst]
        _ = (if hd.1 ∈ accounts then hd.2 else 0)
              + sumOver tl (fun l => if l.1 ∈ accounts then l.2 else 0) := by
          rw [ih]
        _ = sumOver (hd :: tl)
              (fun l => if l.1 ∈ accounts then l.2 else 0) := rfl

private theorem sum_netOf_eq_zero (accounts : List AccountId) (ls : List Line)
    (hnodup : accounts.Nodup) (hmem : ∀ l ∈ ls, l.1 ∈ accounts)
    (hsum : lineSum ls = 0) :
    sumOver accounts (netOf ls) = 0 := by
  calc sumOver accounts (netOf ls)
      _ = sumOver ls (fun l => if l.1 ∈ accounts then l.2 else 0) :=
        sum_swap accounts ls hnodup
      _ = sumOver ls (fun l : Line => l.2) :=
        sumOver_congr ls _ _ (fun l hl => if_pos (hmem l hl))
      _ = lineSum ls := rfl
      _ = 0 := hsum

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hval
  unfold step
  simp [hval]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnval
  unfold step
  simp [hnval]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  have hval : ValidEntry s e := step_ok_valid s e hok
  obtain ⟨_, _, hmem, _, _, _⟩ := hval
  exact hmem l hl

theorem req_balanced : Balanced step := by
  intro s e hok
  have hval : ValidEntry s e := step_ok_valid s e hok
  obtain ⟨_, _, _, _, hbal, _⟩ := hval
  exact hbal

theorem req_effects : Effects step := by
  intro s e hok
  have hval : ValidEntry s e := step_ok_valid s e hok
  have hstep : step s e = (.ok, nextState s e) := by
    unfold step
    simp [hval]
  rw [hstep]
  constructor
  · rfl
  · intro a
    rfl

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hval : ValidEntry s e := step_ok_valid s e hok
  have hstep : step s e = (.ok, nextState s e) := by
    unfold step
    simp [hval]
  constructor
  · intro x
    rw [hstep]
    simp [nextState]
  · have hneg : ¬ ValidEntry (nextState s e) e := by
      intro hcon
      obtain ⟨_, _, _, _, _, hnot⟩ := hcon
      apply hnot
      simp [nextState]
    have h2 : step (nextState s e) e = (.rejected, nextState s e) := by
      unfold step
      simp [hneg]
    rw [hstep]
    simp [h2]

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hval : ValidEntry s e := step_ok_valid s e hok
  have hstep : step s e = (.ok, nextState s e) := by
    unfold step
    simp [hval]
  have hnodup : s.accounts.Nodup := hval.1
  have hmem : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hval.2.2.1
  have hsum : lineSum e.lines = 0 := hval.2.2.2.2.1
  have htotal : total (step s e).2 = total s := by
    rw [hstep]
    show total (nextState s e) = total s
    unfold total nextState nextBal
    simp only []
    have hsplit : sumOver s.accounts (fun a => s.balance a + netOf e.lines a)
        = sumOver s.accounts s.balance + sumOver s.accounts (netOf e.lines) :=
      sumOver_add s.accounts s.balance (netOf e.lines)
    rw [hsplit, sum_netOf_eq_zero s.accounts e.lines hnodup hmem hsum]
    simp
  exact htotal

end Journal
