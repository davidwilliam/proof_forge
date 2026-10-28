import Journal.Spec
import Journal.Lemmas
namespace Journal
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance
def step : Impl := fun s e =>
  if ValidEntry s e then
    (.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted })
  else (.rejected, s)

theorem req_idempotency_aux_test3 : Idempotent step := by
  intro s e hok
  have hV : ValidEntry s e := by
    by_cases h : ValidEntry s e
    · exact h
    · unfold step at hok
      simp [h] at hok
  have hStep : step s e = (.ok, ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State)) := by
    unfold step
    simp [hV]
  have hSnd : (step s e).2 = ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State) := by
    rw [hStep]
  have hN' : ¬ ValidEntry ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State) e := by
    intro hC
    obtain ⟨_, _, _, _, _, hNotMem⟩ := hC
    simp at hNotMem
  have hStep2 : step ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State) e
      = (.rejected, ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State)) := by
    unfold step
    simp [hN']
  constructor
  · rw [hSnd]
    intro x
    simp
  · rw [hSnd]
    exact hStep2

theorem myIdemHelper : Idempotent step := by
  intro s e hok
  have hV : ValidEntry s e := by
    by_cases h : ValidEntry s e
    · exact h
    · unfold step at hok
      simp [h] at hok
  have hStep : step s e = (.ok, ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State)) := by
    unfold step
    simp [hV]
  have hSnd : (step s e).2 = ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State) := by
    rw [hStep]
  have hN' : ¬ ValidEntry ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State) e := by
    intro hC
    obtain ⟨_, _, _, _, _, hNotMem⟩ := hC
    simp at hNotMem
  have hStep2 : step ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State) e
      = (.rejected, ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State)) := by
    unfold step
    simp [hN']
  constructor
  · rw [hSnd]
    intro x
    simp
  · rw [hSnd]
    exact hStep2

theorem trial_test : True := trivial

theorem myZeroLemma : True := trivial

theorem myFlip (l : List Nat) (x : Nat) (c : Int) :
    sumOver l (fun a => if x = a then c else 0) = sumOver l (fun a => if a = x then c else 0) := by
  apply sumOver_congr
  intro a _ha
  by_cases h : x = a
  · subst h; simp
  · have h2 : ¬ (a = x) := fun hh => h hh.symm
    simp [h, h2]

theorem myZero (S : List Nat) : sumOver S (fun _ => (0 : Int)) = 0 := by
  induction S with
  | nil => rfl
  | cons a t ih => simp [sumOver_cons, ih]

theorem mySwap (S : List Nat) (hl : S.Nodup) (ls : List Line) :
    sumOver S (fun a => netOf ls a) = sumOver ls (fun l => if l.1 ∈ S then l.2 else 0) := by
  induction ls with
  | nil =>
    have h0 : ∀ a ∈ S, netOf ([] : List Line) a = 0 := by
      intro a _ha
      rfl
    rw [sumOver_congr S _ _ h0, myZero S]
    rfl
  | cons h t ih =>
    have hnet : ∀ a, netOf (h :: t) a = (if h.1 = a then h.2 else 0) + netOf t a := by
      intro a
      unfold netOf
      simp [sumOver_cons]
    have h1 : sumOver S (fun a => netOf (h :: t) a)
        = sumOver S (fun a => (if h.1 = a then h.2 else 0) + netOf t a) := by
      apply sumOver_congr
      intro a _ha
      exact hnet a
    rw [h1, sumOver_add, ih]
    have h2 : sumOver S (fun a => if h.1 = a then h.2 else 0)
        = (if h.1 ∈ S then h.2 else 0) := by
      have hflip := myFlip S h.1 h.2
      rw [hflip]
      exact sumOver_ite_eq hl h.1 h.2
    rw [h2]
    simp [sumOver_cons]

theorem myFilt (S : List Nat) (ls : List Line) (hmem : ∀ l ∈ ls, l.1 ∈ S) :
    sumOver ls (fun l => if l.1 ∈ S then l.2 else 0) = lineSum ls := by
  apply sumOver_congr
  intro l hl
  simp [hmem l hl]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
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
  · simp [h] at hok
    obtain ⟨_, _, _, _, hsum, _⟩ := h
    exact hsum
  · simp [h] at hok

theorem req_effects : Effects step := by
  intro s e hok
  unfold step at hok ⊢
  by_cases h : ValidEntry s e
  · simp [h]
  · simp [h] at hok

theorem req_idempotency : Idempotent step := by
  exact myIdemHelper

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  unfold step at hok ⊢
  by_cases h : ValidEntry s e
  · simp only [h, ↓reduceIte] at hok ⊢
    obtain ⟨hNodup, _hne, hmem, _hnz, hsum, _hnmem⟩ := h
    unfold total
    simp only []
    have hsplit : sumOver s.accounts (fun a => s.balance a + netOf e.lines a)
        = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) :=
      sumOver_add s.accounts s.balance (fun a => netOf e.lines a)
    rw [hsplit]
    have hzero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
      rw [mySwap s.accounts hNodup e.lines, myFilt s.accounts e.lines hmem]
      unfold lineSum at hsum ⊢
      exact hsum
    rw [hzero, Int.add_zero]
  · simp [h] at hok

end Journal
