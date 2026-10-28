import Journal.Spec
import Journal.Lemmas
namespace Journal
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance
/-- Add `amt` to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b
def step : Impl := fun s e =>
  if ValidEntry s e then
    let bal := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance
    (.ok, { s with balance := bal, posted := e.id :: s.posted })
  else (.rejected, s)

theorem foo_test : True := trivial

theorem foldl_adjust_eq7 (ls : List Line) (bal : AccountId → Int) (a : AccountId) :
    (ls.foldl (fun b l => adjust b l.1 l.2) bal) a = bal a + netOf ls a := by
  induction ls generalizing bal with
  | nil => simp [netOf]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih (adjust bal hd.1 hd.2)]
    have hadj : adjust bal hd.1 hd.2 a = (if a = hd.1 then bal a + hd.2 else bal a) := rfl
    rw [hadj]
    simp only [netOf, sumOver_cons]
    by_cases h : a = hd.1
    · have h2 : hd.1 = a := Eq.symm h
      rw [if_pos h, if_pos h2]
      omega
    · have h2 : ¬ hd.1 = a := fun hh => h (Eq.symm hh)
      rw [if_neg h, if_neg h2]
      omega

theorem idem_helper1 (s : State) (e : Entry) (hok : (step s e).1 = Outcome.ok) : ValidEntry s e := by
  by_cases h : ValidEntry s e
  · exact h
  · unfold step at hok
    simp [h] at hok

theorem step_ok_eq (s : State) (e : Entry) (h : ValidEntry s e) :
    step s e = (.ok, { s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted }) := by
  unfold step
  simp [h]

theorem idem_helper2b (s : State) (e : Entry) (_h : ValidEntry s e) :
    ¬ ValidEntry { s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } e := by
  intro hV
  obtain ⟨_, _, _, _, _, hni⟩ := hV
  simp at hni

theorem step_rej_eq (s : State) (e : Entry) (h : ¬ ValidEntry s e) :
    step s e = (.rejected, s) := by
  unfold step
  simp [h]

theorem tb_sumZero (l : List AccountId) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [sumOver_cons]; rw [ih]; omega

theorem tb_swap (as : List AccountId) (ls : List Line) (F : AccountId → Line → Int) :
    sumOver as (fun a => sumOver ls (fun l => F a l)) = sumOver ls (fun l => sumOver as (fun a => F a l)) := by
  induction ls with
  | nil =>
    simp only [sumOver_nil]
    exact tb_sumZero as
  | cons hd tl ih =>
    simp only [sumOver_cons]
    have h1 : (fun a => F a hd + sumOver tl (fun l => F a l)) = (fun a => (fun a' => F a' hd) a + (fun a' => sumOver tl (fun l => F a' l)) a) := rfl
    rw [h1, sumOver_add]
    rw [ih]

theorem tb_if_symm (x a : AccountId) (c : Int) : (if x = a then c else 0) = (if a = x then c else 0) := by
  by_cases h : a = x
  · subst h; simp
  · have h2 : ¬ x = a := fun hh => h hh.symm
    simp [h, h2]

theorem tb_perLine (accounts : List AccountId) (hNodup : accounts.Nodup) (l : Line) (hmem : l.1 ∈ accounts) :
    sumOver accounts (fun a => if l.1 = a then l.2 else 0) = l.2 := by
  have hcongr : ∀ a ∈ accounts, (if l.1 = a then l.2 else (0 : Int)) = (if a = l.1 then l.2 else 0) := by
    intro a _; exact tb_if_symm l.1 a l.2
  rw [sumOver_congr _ _ _ hcongr, sumOver_ite_eq hNodup l.1 l.2, if_pos hmem]

theorem tb_sumNet_eq_lineSum (accounts : List AccountId) (hNodup : accounts.Nodup) (ls : List Line) (hmem : ∀ l ∈ ls, l.1 ∈ accounts) :
    sumOver accounts (fun a => netOf ls a) = lineSum ls := by
  unfold netOf lineSum
  rw [tb_swap]
  apply sumOver_congr
  intro l hl
  exact tb_perLine accounts hNodup l (hmem l hl)

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
  unfold step at hok
  by_cases h : ValidEntry s e
  · simp [h] at hok
    obtain ⟨_, _, hmem, _, _, _⟩ := h
    exact hmem l hl
  · simp [h] at hok

theorem req_balanced : Balanced step := by
  intro s e hok
  unfold step at hok
  by_cases h : ValidEntry s e
  · obtain ⟨_, _, _, _, hsum, _⟩ := h
    exact hsum
  · simp [h] at hok

theorem req_effects : Effects step := by
  intro s e hok
  unfold step at hok ⊢
  by_cases h : ValidEntry s e
  · simp only [if_pos h] at hok ⊢
    exact ⟨trivial, fun a => foldl_adjust_eq7 e.lines s.balance a⟩
  · simp [h] at hok

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have h : ValidEntry s e := idem_helper1 s e hok
  rw [step_ok_eq s e h]
  simp only
  constructor
  · intro x
    simp
  · rw [step_rej_eq _ _ (idem_helper2b s e h)]

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hV : ValidEntry s e := idem_helper1 s e hok
  obtain ⟨hNodup, _, hmem, _, hsum, _⟩ := hV
  have hEff := req_effects s e hok
  obtain ⟨hacc, hbal⟩ := hEff
  unfold total
  rw [hacc]
  have hsplit : ∀ a ∈ s.accounts, (step s e).2.balance a = s.balance a + netOf e.lines a := fun a _ => hbal a
  rw [sumOver_congr s.accounts _ _ hsplit, sumOver_add]
  have hnet : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
    rw [tb_sumNet_eq_lineSum s.accounts hNodup e.lines hmem]
    unfold lineSum at hsum ⊢
    exact hsum
  rw [hnet]
  omega

end Journal
