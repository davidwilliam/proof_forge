import Journal.Spec
import Journal.Lemmas
/-!
# Reference solution B (hidden from agents)

Boolean validation, a left fold over the lines, and the new ID appended at the end of the
posted list.
-/

namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

/-- Boolean form of the validity check. -/
def checkEntry (s : State) (e : Entry) : Bool :=
  decide s.accounts.Nodup && !e.lines.isEmpty &&
  e.lines.all (fun l => s.accounts.contains l.1 && l.2 != 0) &&
  decide (lineSum e.lines = 0) && !s.posted.contains e.id

/-- Fold the lines into the balance function. -/
def applyAll (bal : AccountId → Int) (ls : List Line) : AccountId → Int :=
  ls.foldl (fun b l => fun x => if x == l.1 then b x + l.2 else b x) bal

def step : Impl := fun s e =>
  if checkEntry s e then
    (.ok, { accounts := s.accounts, balance := applyAll s.balance e.lines,
            posted := s.posted ++ [e.id] })
  else (.rejected, s)

theorem checkEntry_iff (s : State) (e : Entry) : checkEntry s e = true ↔ ValidEntry s e := by
  simp only [checkEntry, ValidEntry, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true, List.contains_iff_mem, bne_iff_ne,
    ne_eq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨h1, h2, fun l hl => (h3 l hl).1, fun l hl => (h3 l hl).2, h4, ?_⟩
    simpa using h5
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨⟨⟨h1, h2⟩, fun l hl => ⟨h3 l hl, h4 l hl⟩⟩, h5⟩, ?_⟩
    simpa using h6

theorem step_of_valid {s : State} {e : Entry} (h : ValidEntry s e) :
    step s e = (.ok, { accounts := s.accounts, balance := applyAll s.balance e.lines,
                       posted := s.posted ++ [e.id] }) := by
  simp [step, (checkEntry_iff s e).mpr h]

theorem step_of_invalid {s : State} {e : Entry} (h : ¬ ValidEntry s e) :
    step s e = (.rejected, s) := by
  have : checkEntry s e = false := by
    cases hc : checkEntry s e
    · rfl
    · exact absurd ((checkEntry_iff s e).mp hc) h
  simp [step, this]

theorem ok_valid {s : State} {e : Entry} (h : (step s e).1 = .ok) : ValidEntry s e := by
  by_cases hv : ValidEntry s e
  · exact hv
  · rw [step_of_invalid hv] at h; cases h

theorem applyAll_eq : ∀ (ls : List Line) (bal : AccountId → Int) (a : AccountId),
    applyAll bal ls a = bal a + netOf ls a := by
  intro ls
  induction ls with
  | nil => intro bal a; simp [applyAll, netOf]
  | cons l ls ih =>
    intro bal a
    have : applyAll bal (l :: ls) = applyAll (fun x => if x == l.1 then bal x + l.2 else bal x) ls := rfl
    rw [this, ih]
    simp only [netOf, sumOver_cons]
    by_cases h : a = l.1
    · subst h; simp; omega
    · have : l.1 ≠ a := fun h' => h h'.symm
      simp [h, this]

/-- Net effect of the lines summed over a duplicate-free universe that contains them. -/
theorem sum_netOf {accts : List AccountId} (hnd : accts.Nodup) : ∀ (ls : List Line),
    (∀ l ∈ ls, l.1 ∈ accts) → sumOver accts (netOf ls) = lineSum ls := by
  intro ls
  induction ls with
  | nil =>
    intro _
    have : ∀ l : List AccountId, sumOver l (netOf []) = 0 := by
      intro l; induction l with
      | nil => rfl
      | cons x xs ih => rw [sumOver_cons, ih]; rfl
    exact this accts
  | cons l ls ih =>
    intro hk
    have hsplit : sumOver accts (netOf (l :: ls))
        = sumOver accts (fun a => if a = l.1 then l.2 else 0) + sumOver accts (netOf ls) := by
      rw [← sumOver_add]
      apply sumOver_congr
      intro a _
      simp only [netOf, sumOver_cons]
      by_cases h : a = l.1
      · subst h; simp
      · have : l.1 ≠ a := fun h' => h h'.symm
        simp [h, this]
    rw [hsplit, sumOver_ite_eq hnd, ih (fun x hx => hk x (List.mem_cons_of_mem _ hx))]
    simp [hk l List.mem_cons_self, lineSum]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h; rw [step_of_valid h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h; exact step_of_invalid h

theorem req_known_accounts : KnownAccounts step := by
  intro s e h; exact (ok_valid h).2.2.1

theorem req_balanced : Balanced step := by
  intro s e h; exact (ok_valid h).2.2.2.2.1

theorem req_effects : Effects step := by
  intro s e h
  rw [step_of_valid (ok_valid h)]
  exact ⟨rfl, fun a => applyAll_eq _ _ a⟩

theorem req_idempotency : Idempotent step := by
  intro s e h
  rw [step_of_valid (ok_valid h)]
  refine ⟨fun x => by simp [or_comm], ?_⟩
  apply step_of_invalid
  intro h'
  exact h'.2.2.2.2.2 (by simp)

theorem req_trial_balance : TrialBalance step := by
  intro s e h
  have hv := ok_valid h
  rw [step_of_valid hv]
  show sumOver s.accounts (applyAll s.balance e.lines) = sumOver s.accounts s.balance
  rw [sumOver_congr _ _ _ (fun a _ => applyAll_eq e.lines s.balance a), sumOver_add,
    sum_netOf hv.1 e.lines hv.2.2.1, hv.2.2.2.2.1]
  omega

end Journal
