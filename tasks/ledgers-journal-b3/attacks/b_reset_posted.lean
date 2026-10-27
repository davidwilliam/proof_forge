import Journal.Spec
import Journal.Lemmas

namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

/-- Add `amt` to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

/-- Post every line, first to last. -/
def postLines : List Line → (AccountId → Int) → (AccountId → Int)
  | [], bal => bal
  | l :: ls, bal => postLines ls (adjust bal l.1 l.2)

def refStep : Impl := fun s e =>
  if ValidEntry s e then
    (.ok, { s with balance := postLines e.lines s.balance, posted := e.id :: s.posted })
  else (.rejected, s)

theorem step_of_valid {s : State} {e : Entry} (h : ValidEntry s e) :
    refStep s e = (.ok, { s with balance := postLines e.lines s.balance, posted := e.id :: s.posted }) := by
  simp [refStep, h]

theorem step_of_invalid {s : State} {e : Entry} (h : ¬ ValidEntry s e) :
    refStep s e = (.rejected, s) := by
  simp [refStep, h]

theorem ok_valid {s : State} {e : Entry} (h : (refStep s e).1 = .ok) : ValidEntry s e := by
  by_cases hv : ValidEntry s e
  · exact hv
  · rw [step_of_invalid hv] at h; cases h

theorem postLines_eq : ∀ (ls : List Line) (bal : AccountId → Int) (a : AccountId),
    postLines ls bal a = bal a + netOf ls a := by
  intro ls
  induction ls with
  | nil => intro bal a; simp [postLines, netOf]
  | cons l ls ih =>
    intro bal a
    simp only [postLines, ih, adjust, netOf, sumOver_cons]
    by_cases h : a = l.1
    · subst h; simp; omega
    · have : l.1 ≠ a := fun h' => h h'.symm
      simp [h, this]

theorem sumOver_zero {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Summing the net effect of the lines over the universe gives the sum of the lines. -/
theorem sum_netOf {accts : List AccountId} (hnd : accts.Nodup) : ∀ (ls : List Line),
    (∀ l ∈ ls, l.1 ∈ accts) → sumOver accts (netOf ls) = lineSum ls := by
  intro ls
  induction ls with
  | nil => intro _; exact sumOver_zero accts
  | cons l ls ih =>
    intro hk
    have h1 : netOf (l :: ls) = fun a => (if a = l.1 then l.2 else 0) + netOf ls a := by
      funext a
      simp only [netOf, sumOver_cons]
      by_cases h : a = l.1
      · subst h; simp
      · have : l.1 ≠ a := fun h' => h h'.symm
        simp [h, this]
    rw [h1, sumOver_add, sumOver_ite_eq hnd, ih (fun x hx => hk x (by simp [hx]))]
    simp [lineSum, hk l (by simp)]

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s e h; rw [step_of_valid h]

theorem ref_req_invalid_noop : InvalidNoop refStep := by
  intro s e h; exact step_of_invalid h

theorem ref_req_known_accounts : KnownAccounts refStep := by
  intro s e h; exact (ok_valid h).2.2.1

theorem ref_req_balanced : Balanced refStep := by
  intro s e h; exact (ok_valid h).2.2.2.2.1

theorem ref_req_effects : Effects refStep := by
  intro s e h
  rw [step_of_valid (ok_valid h)]
  exact ⟨rfl, fun a => postLines_eq _ _ a⟩

theorem ref_req_idempotency : Idempotent refStep := by
  intro s e h
  rw [step_of_valid (ok_valid h)]
  refine ⟨fun x => by simp, ?_⟩
  apply step_of_invalid
  intro h'
  exact h'.2.2.2.2.2 (by simp)

theorem ref_req_trial_balance : TrialBalance refStep := by
  intro s e h
  have hv := ok_valid h
  rw [step_of_valid hv]
  unfold total
  simp only
  rw [sumOver_congr _ _ _ (fun a _ => postLines_eq e.lines s.balance a), sumOver_add,
    sum_netOf hv.1 e.lines hv.2.2.1, hv.2.2.2.2.1]
  omega

/-! Attack: balances are right, but a successful posting replaces the posted-ID history
with the new ID alone. REQ-IDEMPOTENCY is restated. -/

def step : Impl := fun s e =>
  if (refStep s e).1 = .ok then (.ok, { (refStep s e).2 with posted := [e.id] })
  else refStep s e

theorem step_ok {s : State} {e : Entry} (h : (step s e).1 = .ok) :
    (refStep s e).1 = .ok ∧ step s e = (.ok, { (refStep s e).2 with posted := [e.id] }) := by
  by_cases hr : (refStep s e).1 = .ok
  · exact ⟨hr, by simp [step, hr]⟩
  · simp [step, hr] at h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h; simp [step, ref_req_valid_succeeds s e h]
theorem req_invalid_noop : InvalidNoop step := by
  intro s e h; simp [step, ref_req_invalid_noop s e h]
theorem req_known_accounts : KnownAccounts step := by
  intro s e h; exact ref_req_known_accounts s e (step_ok h).1
theorem req_balanced : Balanced step := by
  intro s e h; exact ref_req_balanced s e (step_ok h).1
theorem req_effects : Effects step := by
  intro s e h
  have ⟨hr, he⟩ := step_ok h
  rw [he]; exact ref_req_effects s e hr
theorem req_idempotency : ∀ s e, (step s e).1 = .ok →
    e.id ∈ (step s e).2.posted ∧ step (step s e).2 e = (.rejected, (step s e).2) := by
  intro s e h
  have ⟨_, he⟩ := step_ok h
  rw [he]
  refine ⟨by simp, ?_⟩
  have hinv := ref_req_invalid_noop { (refStep s e).2 with posted := [e.id] } e
    (fun hv => hv.2.2.2.2.2 (by simp))
  simp [step, hinv]
theorem req_trial_balance : TrialBalance step := by
  intro s e h
  have ⟨hr, he⟩ := step_ok h
  rw [he]; exact ref_req_trial_balance s e hr

end Journal
