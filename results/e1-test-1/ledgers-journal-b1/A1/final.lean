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

theorem test_adjust_eq (bal : AccountId → Int) (a : Nat) (c : Int) :
    adjust bal a c a = bal a + c := by
  unfold adjust
  simp

theorem test_adjust_ne (bal : AccountId → Int) (a b : Nat) (c : Int) (h : b ≠ a) :
    adjust bal a c b = bal b := by
  unfold adjust
  simp [h]

theorem foldl_dbg3 (bal : AccountId → Int) (hd : Line) (tl : List Line) (a : AccountId)
    (h : a = hd.1) :
    (adjust bal hd.1 hd.2) a + sumOver tl (fun l => if l.1 = a then l.2 else 0) =
    bal a + ((if hd.1 = a then hd.2 else 0) + sumOver tl (fun l => if l.1 = a then l.2 else 0)) := by
  have h2 : hd.1 = a := h.symm
  have hadj : adjust bal hd.1 hd.2 a = bal a + hd.2 := by
    unfold adjust
    rw [if_pos h]
  rw [hadj, if_pos h2]
  omega

theorem foldl_adjust_eq_full (ls : List Line) (bal : AccountId → Int) (a : AccountId) :
    (ls.foldl (fun b l => adjust b l.1 l.2) bal) a = bal a + netOf ls a := by
  induction ls generalizing bal with
  | nil => simp [netOf]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih]
    have hadj : adjust bal hd.1 hd.2 a = bal a + (if hd.1 = a then hd.2 else 0) := by
      unfold adjust
      by_cases h : a = hd.1
      · subst h; simp
      · have h2 : ¬ (a = hd.1) := h
        have h3 : ¬ (hd.1 = a) := fun hh => h hh.symm
        simp [h2, h3]
    have hnet : netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
      unfold netOf
      simp only [sumOver_cons]
    rw [hnet, hadj]
    unfold netOf at *
    omega

theorem swap_zero_aux {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [sumOver_cons]; omega

theorem swap_sum_aux (accs : List AccountId) (ls : List Line) (F : AccountId → Line → Int) :
    sumOver accs (fun a => sumOver ls (fun l => F a l)) =
    sumOver ls (fun l => sumOver accs (fun a => F a l)) := by
  induction accs with
  | nil => simp only [sumOver_nil]; rw [swap_zero_aux]
  | cons a t ih =>
    simp only [sumOver_cons, ih]
    rw [sumOver_add]

theorem sum_net_aux (accs : List AccountId) (ls : List Line)
    (hall : ∀ l ∈ ls, l.1 ∈ accs) (hnd : accs.Nodup) :
    sumOver accs (fun a => netOf ls a) = lineSum ls := by
  unfold netOf lineSum
  rw [swap_sum_aux]
  apply sumOver_congr
  intro l hl
  have hmem : l.1 ∈ accs := hall l hl
  have hswap : (sumOver accs fun a => (if l.1 = a then l.2 else (0 : Int))) =
      sumOver accs (fun a => if a = l.1 then l.2 else 0) := by
    apply sumOver_congr
    intro a _
    by_cases heq : a = l.1
    · subst heq; rfl
    · have hne : ¬ (l.1 = a) := fun hh => heq hh.symm
      simp only [hne, heq]
  rw [hswap, sumOver_ite_eq hnd _ _]
  rw [if_pos hmem]

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
  by_cases h : ValidEntry s e
  · obtain ⟨_, _, hmem, _, _, _⟩ := h
    exact hmem _ hl
  · unfold step at hok
    simp [h] at hok

theorem req_balanced : Balanced step := by
  intro s e hok
  by_cases h : ValidEntry s e
  · obtain ⟨_, _, _, _, hbal, _⟩ := h
    exact hbal
  · unfold step at hok
    simp [h] at hok

theorem req_effects : Effects step := by
  intro s e hok
  by_cases h : ValidEntry s e
  · have hstep : step s e = (.ok, ({ s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State)) := by
      unfold step; simp [h]
    have h2 : (step s e).2 = ({ s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State) := by
      rw [hstep]
    constructor
    · rw [h2]
    · intro a
      rw [h2]
      exact foldl_adjust_eq_full e.lines s.balance a
  · unfold step at hok; simp [h] at hok

theorem req_idempotency : Idempotent step := by
  intro s e hok
  by_cases h : ValidEntry s e
  · have hstep : step s e = (.ok, ({ s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State)) := by
      unfold step
      simp only [h, ↓reduceIte]
    have h2 : (step s e).2 = ({ s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State) := by
      rw [hstep]
    constructor
    · intro x
      rw [h2]
      simp
    · have hmem : e.id ∈ (({ s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State).posted) := by
        simp
      have hnotvalid : ¬ ValidEntry ({ s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State) e := by
        intro hc
        obtain ⟨_, _, _, _, _, hnid⟩ := hc
        exact hnid hmem
      have hstep2 : step ({ s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State) e = (.rejected, ({ s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State)) := by
        unfold step
        simp [hnotvalid]
      rw [← h2] at hstep2
      exact hstep2
  · unfold step at hok
    simp [h] at hok

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  by_cases h : ValidEntry s e
  · have hstep : step s e = (.ok, ({ s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State)) := by
      unfold step; simp [h]
    have hbal : ∀ a, (step s e).2.balance a = s.balance a + netOf e.lines a := by
      intro a
      have hfold := foldl_adjust_eq_full e.lines s.balance a
      rw [hstep] at *
      exact hfold
    have hacc : (step s e).2.accounts = s.accounts := by
      rw [hstep]
    obtain ⟨hnd, _, hall_mem, _, hbal0, _⟩ := h
    unfold total
    rw [hacc]
    have hcongr : sumOver s.accounts (step s e).2.balance = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
      apply sumOver_congr; intro a _; exact hbal a
    rw [hcongr, sumOver_add, sum_net_aux s.accounts e.lines hall_mem hnd, hbal0, Int.add_zero]
  · unfold step at hok; simp [h] at hok

end Journal
