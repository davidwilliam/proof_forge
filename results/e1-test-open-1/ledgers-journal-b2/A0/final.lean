import Journal.Spec
import Journal.Lemmas
namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def acceptable (s : State) (e : Entry) : Bool :=
  decide (s.accounts.Nodup) && !e.lines.isEmpty && e.lines.all (fun l => decide (l.1 ∈ s.accounts)) && e.lines.all (fun l => decide (l.2 ≠ 0)) && decide (lineSum e.lines = 0) && !decide (e.id ∈ s.posted)

def step : Impl := fun s e =>
  if acceptable s e then
    (.ok, { accounts := s.accounts,
            balance := fun a => s.balance a + netOf e.lines a,
            posted := e.id :: s.posted })
  else (.rejected, s)

theorem all_mem_iff {l : List Line} {s : State} :
    (l.all (fun x => decide (x.1 ∈ s.accounts)) = true) ↔ ∀ x ∈ l, x.1 ∈ s.accounts := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · exact of_decide_eq_true h1
      · exact ih.mp h2
    · rintro ⟨h1, h2⟩
      constructor
      · exact decide_eq_true h1
      · exact ih.mpr h2

theorem all_nonzero_iff {l : List Line} :
    (l.all (fun x => decide (x.2 ≠ 0)) = true) ↔ ∀ x ∈ l, x.2 ≠ 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · exact of_decide_eq_true h1
      · exact ih.mp h2
    · rintro ⟨h1, h2⟩
      constructor
      · exact decide_eq_true h1
      · exact ih.mpr h2

theorem not_empty_iff' {l : List Line} : ((!l.isEmpty) = true) ↔ l ≠ [] := by
  cases l with
  | nil => simp
  | cons _ _ => simp

theorem not_mem_iff' {s : State} {e : Entry} : ((!decide (e.id ∈ s.posted)) = true) ↔ e.id ∉ s.posted := by
  simp [decide_eq_true_iff]

theorem acceptable_iff (s : State) (e : Entry) : (acceptable s e = true) ↔ ValidEntry s e := by
  unfold acceptable ValidEntry
  simp only [Bool.and_eq_true, not_empty_iff', all_mem_iff, all_nonzero_iff, decide_eq_true_iff, not_mem_iff']
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

theorem acceptable_true_of_valid {s e} (h : ValidEntry s e) : acceptable s e = true :=
  (acceptable_iff s e).mpr h

theorem acceptable_false_of_invalid {s e} (h : ¬ ValidEntry s e) : acceptable s e = false := by
  have h1 : acceptable s e ≠ true := fun ht => h ((acceptable_iff s e).mp ht)
  cases hb : acceptable s e with
  | true => exact absurd hb h1 | false => rfl

theorem step_ok_of_true {s e} (h : acceptable s e = true) :
    step s e = (.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) := by
  unfold step; simp [h]

theorem step_rejected_of_false {s e} (h : acceptable s e = false) : step s e = (.rejected, s) := by
  unfold step; simp [h]

theorem ok_imp_valid {s e} (h : (step s e).1 = .ok) : ValidEntry s e := by
  have h1 : ¬ ¬ValidEntry s e := by
    intro hnv
    have hf := acceptable_false_of_invalid hnv
    rw [step_rejected_of_false hf] at h
    simp at h
  exact Classical.byContradiction (fun h2 => h1 h2)

theorem sumOver_zero {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ tl ih => simp [sumOver_cons, ih]

theorem netOf_cons (hd : Line) (tl : List Line) (a : AccountId) :
    netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
  simp [netOf, sumOver_cons]

theorem sumOver_netOf_eq_lineSum_aux (accounts : List AccountId) (ls : List Line) (hnodup : accounts.Nodup) (hmem : ∀ l ∈ ls, l.1 ∈ accounts) :
    sumOver accounts (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    simp [netOf, lineSum, sumOver_zero]
  | cons hd tl ih =>
    have hm_tl : ∀ l ∈ tl, l.1 ∈ accounts := fun l hl => hmem l (by simp [hl])
    have ih' := ih hm_tl
    have h_step : ∀ a, netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := fun a => netOf_cons hd tl a
    calc sumOver accounts (fun a => netOf (hd :: tl) a)
        = sumOver accounts (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by
            apply sumOver_congr; intro a _; exact h_step a
        _ = sumOver accounts (fun a => (if hd.1 = a then hd.2 else 0)) + sumOver accounts (fun a => netOf tl a) := sumOver_add _ _ _
        _ = sumOver accounts (fun a => (if hd.1 = a then hd.2 else 0)) + lineSum tl := by rw [ih']
        _ = sumOver accounts (fun a => (if a = hd.1 then hd.2 else 0)) + lineSum tl := by
            have heq : (fun a => (if hd.1 = a then hd.2 else (0 : Int))) = (fun a => if a = hd.1 then hd.2 else 0) := by
              funext a; by_cases heq : hd.1 = a
              · subst heq; simp
              · have hne : ¬ (a = hd.1) := fun h => heq h.symm
                simp [heq, hne]
            rw [heq]
        _ = (if hd.1 ∈ accounts then hd.2 else 0) + lineSum tl := by rw [sumOver_ite_eq hnodup hd.1 hd.2]
        _ = hd.2 + lineSum tl := by
            have hmem_hd : hd.1 ∈ accounts := hmem hd (by simp)
            simp [hmem_hd]
        _ = lineSum (hd :: tl) := by simp [lineSum, sumOver_cons]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hv
  have hac := acceptable_true_of_valid hv
  have hs := step_ok_of_true hac
  simp [hs]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hn
  exact step_rejected_of_false (acceptable_false_of_invalid hn)

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  have hv := ok_imp_valid hok
  exact hv.2.2.1 l hl

theorem req_balanced : Balanced step := by
  intro s e hok
  have hv := ok_imp_valid hok
  exact hv.2.2.2.2.1

theorem req_effects : Effects step := by
  intro s e hok
  have hv := ok_imp_valid hok
  have hac := acceptable_true_of_valid hv
  have hs := step_ok_of_true hac
  constructor
  · simp [hs]
  · intro a; simp [hs]

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hv := ok_imp_valid hok
  have hac := acceptable_true_of_valid hv
  have hs_ok := step_ok_of_true hac
  have hposted_def : (step s e).2.posted = e.id :: s.posted := by simp [hs_ok]
  constructor
  · intro x; rw [hposted_def]; simp
  · have h2state : (step s e).2 = { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } := by simp [hs_ok]
    have hvalid_false : ¬ ValidEntry (step s e).2 e := by
      intro hcontra
      have hmem : e.id ∈ (step s e).2.posted := by rw [hposted_def]; simp
      have hnot : e.id ∉ (step s e).2.posted := hcontra.2.2.2.2.2
      exact hnot hmem
    have hacc_false : acceptable (step s e).2 e = false := acceptable_false_of_invalid hvalid_false
    exact step_rejected_of_false hacc_false

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hv := ok_imp_valid hok
  have hac := acceptable_true_of_valid hv
  have hs := step_ok_of_true hac
  have h_eq : total (step s e).2 = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    simp [total, hs]
  rw [h_eq, sumOver_add]
  have hsum : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines :=
    sumOver_netOf_eq_lineSum_aux s.accounts e.lines hv.1 hv.2.2.1
  rw [hsum, hv.2.2.2.2.1]
  simp [total]

end Journal
