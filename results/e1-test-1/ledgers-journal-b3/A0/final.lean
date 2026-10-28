import Journal.Spec
import Journal.Lemmas
namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

def step : Impl := fun s e =>
  if ValidEntry s e then
    (.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted })
  else (.rejected, s)

theorem step_ok_valid_aux (s : State) (e : Entry) (h : (step s e).1 = .ok) : ValidEntry s e := by
  by_cases hv : ValidEntry s e
  · exact hv
  · unfold step at h
    simp [hv] at h

theorem step_eq_ok (s : State) (e : Entry) (hv : ValidEntry s e) :
    step s e = (.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) := by
  unfold step
  simp [hv]

theorem aux_zero (acc : List AccountId) : sumOver acc (fun _ : AccountId => (0 : Int)) = 0 := by
  induction acc with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem aux_ite_swap (acc : List AccountId) (hnd : acc.Nodup) (x : AccountId) (c : Int) :
    sumOver acc (fun a => if x = a then c else 0) = if x ∈ acc then c else 0 := by
  have hcongr : ∀ a ∈ acc, (fun a => if x = a then c else (0 : Int)) a = (fun a => if a = x then c else 0) a := by
    intro a _
    by_cases h : a = x
    · subst h; simp
    · have h' : ¬ (x = a) := fun he => h he.symm
      simp [h, h']
  rw [sumOver_congr acc _ _ hcongr]
  exact sumOver_ite_eq hnd x c

theorem aux_double (acc : List AccountId) (hnd : acc.Nodup) (ls : List Line) :
    sumOver acc (fun a => netOf ls a) = sumOver ls (fun l => if l.1 ∈ acc then l.2 else 0) := by
  induction ls with
  | nil =>
    have h0 : ∀ a ∈ acc, (fun a => netOf ([] : List Line) a) a = (fun _ : AccountId => (0 : Int)) a := by
      intro a _
      rfl
    have heq : sumOver acc (fun a => netOf ([] : List Line) a) = 0 := by
      rw [sumOver_congr acc _ _ h0, aux_zero acc]
    rw [heq]
    rfl
  | cons hd tl ih =>
    have hcongr : ∀ a ∈ acc, (fun a => netOf (hd :: tl) a) a = (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) a := by
      intro a _
      rfl
    rw [sumOver_congr acc _ _ hcongr, sumOver_add, aux_ite_swap acc hnd hd.1 hd.2, ih, sumOver_cons]

theorem aux_mem (acc : List AccountId) (ls : List Line) (hall : ∀ l ∈ ls, l.1 ∈ acc) :
    sumOver ls (fun l : Line => if l.1 ∈ acc then l.2 else 0) = lineSum ls := by
  have hcongr : ∀ l ∈ ls, (fun l : Line => if l.1 ∈ acc then l.2 else (0 : Int)) l = (fun l : Line => l.2) l := by
    intro l hl
    simp [hall l hl]
  rw [sumOver_congr ls _ _ hcongr]
  rfl

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h
  unfold step
  simp [h]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  have hv : ValidEntry s e := step_ok_valid_aux s e hok
  obtain ⟨_, _, hmem, _, _, _⟩ := hv
  exact hmem l hl

theorem req_balanced : Balanced step := by
  intro s e hok
  have hv : ValidEntry s e := step_ok_valid_aux s e hok
  obtain ⟨_, _, _, _, hsum, _⟩ := hv
  exact hsum

theorem req_effects : Effects step := by
  intro s e hok
  have hv : ValidEntry s e := step_ok_valid_aux s e hok
  have hstep : step s e = (.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) :=
    step_eq_ok s e hv
  constructor
  · rw [hstep]
  · intro a
    rw [hstep]

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hv : ValidEntry s e := step_ok_valid_aux s e hok
  have hstep : step s e = (.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) :=
    step_eq_ok s e hv
  have hposted : (step s e).2.posted = e.id :: s.posted := by
    have h1 := congrArg Prod.snd hstep
    have h2 := congrArg State.posted h1
    simpa using h2
  constructor
  · intro x
    rw [hposted]
    simp
  · have hnvalid : ¬ ValidEntry (step s e).2 e := by
      intro hcon
      obtain ⟨_, _, _, _, _, hnid2⟩ := hcon
      rw [hposted] at hnid2
      simp at hnid2
    exact req_invalid_noop _ _ hnvalid

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hv : ValidEntry s e := step_ok_valid_aux s e hok
  have hstep : step s e = (.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) :=
    step_eq_ok s e hv
  obtain ⟨hnodup, _, hmem, _, hsum, _⟩ := hv
  have htotal : total (step s e).2 = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    rw [hstep]
    rfl
  have hadd : sumOver s.accounts (fun a => s.balance a + netOf e.lines a) = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) :=
    sumOver_add s.accounts s.balance (fun a => netOf e.lines a)
  have h4 : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
    rw [aux_double s.accounts hnodup e.lines, aux_mem s.accounts e.lines hmem, hsum]
  rw [htotal, hadd, h4, Int.add_zero]
  rfl

end Journal
