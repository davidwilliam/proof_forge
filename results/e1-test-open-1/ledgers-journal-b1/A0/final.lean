import Journal.Spec
import Journal.Lemmas

namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def step : Impl := fun s e =>
  if ValidEntry s e then
    (.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted })
  else
    (.rejected, s)

theorem step_ok_iff (s : State) (e : Entry) : (step s e).1 = .ok ↔ ValidEntry s e := by
  unfold step
  constructor
  · intro h
    by_cases hv : ValidEntry s e
    · exact hv
    · simp [hv] at h
  · intro hv
    simp [hv]

theorem step_eq_of_valid {s : State} {e : Entry} (h : ValidEntry s e) :
    step s e = (.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) := by
  unfold step
  simp [h]

theorem step_eq_of_invalid {s : State} {e : Entry} (h : ¬ ValidEntry s e) :
    step s e = (.rejected, s) := by
  unfold step
  simp [h]

theorem sumOver_zero {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp [sumOver_cons, ih]

theorem sumOver_netOf_eq_lineSum (accounts : List AccountId) (ls : List Line)
    (hcover : ∀ l ∈ ls, l.1 ∈ accounts) (hNodup : accounts.Nodup) :
    sumOver accounts (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    unfold netOf lineSum
    simp [sumOver_nil]
    exact sumOver_zero accounts
  | cons hd tl ih =>
    have hhd : hd.1 ∈ accounts := hcover hd (by simp)
    have htl : ∀ l ∈ tl, l.1 ∈ accounts := fun l hl => hcover l (by simp [hl])
    have ih' := ih htl
    have h_eq : (fun a => netOf (hd :: tl) a) = (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by
      funext a
      unfold netOf
      simp
    rw [h_eq]
    rw [sumOver_add]
    have h_ite : sumOver accounts (fun a => if hd.1 = a then hd.2 else (0 : Int)) = hd.2 := by
      have h1 : (fun a => if hd.1 = a then hd.2 else (0 : Int)) = (fun a => if a = hd.1 then hd.2 else 0) := by
        funext a
        by_cases ha : hd.1 = a
        · subst ha; simp
        · have h2 : a ≠ hd.1 := fun h => ha h.symm
          simp [ha, h2]
      rw [h1]
      rw [sumOver_ite_eq hNodup hd.1 hd.2]
      simp [hhd]
    rw [h_ite, ih']
    unfold lineSum
    simp

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h
  exact (step_ok_iff s e).mpr h

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h
  exact step_eq_of_invalid h

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  have hV : ValidEntry s e := (step_ok_iff s e).mp hok
  exact hV.2.2.1 l hl

theorem req_balanced : Balanced step := by
  intro s e hok
  have hV : ValidEntry s e := (step_ok_iff s e).mp hok
  exact hV.2.2.2.2.1

theorem req_effects : Effects step := by
  intro s e hok
  have hV : ValidEntry s e := (step_ok_iff s e).mp hok
  rw [step_eq_of_valid hV]
  simp

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hV : ValidEntry s e := (step_ok_iff s e).mp hok
  have hEq : step s e = (.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) := step_eq_of_valid hV
  rw [hEq]
  constructor
  · intro x
    simp
  · have hNotValid : ¬ ValidEntry { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } e := by
      intro hV2
      obtain ⟨_, _, _, _, _, hNotMem⟩ := hV2
      exact hNotMem (by simp)
    rw [step_eq_of_invalid hNotValid]

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hV : ValidEntry s e := (step_ok_iff s e).mp hok
  have hEq : step s e = (.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) := step_eq_of_valid hV
  rw [hEq]
  simp only
  unfold total
  have h_add : sumOver s.accounts (fun a => s.balance a + netOf e.lines a) = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) :=
    sumOver_add s.accounts s.balance (fun a => netOf e.lines a)
  rw [h_add]
  have h_sum_zero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
    rw [sumOver_netOf_eq_lineSum s.accounts e.lines hV.2.2.1 hV.1]
    exact hV.2.2.2.2.1
  rw [h_sum_zero]
  simp

end Journal
