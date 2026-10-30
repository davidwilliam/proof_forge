import Journal.Spec
import Journal.Lemmas
namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def step : Impl := fun s e =>
  if ValidEntry s e then
    (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted })
  else
    (.rejected, s)

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
    exact h.2.2.1 l hl
  · simp [h] at hok

theorem req_balanced : Balanced step := by
  intro s e hok
  unfold step at hok
  by_cases h : ValidEntry s e
  · simp [h] at hok
    exact h.2.2.2.2.1
  · simp [h] at hok

theorem req_effects : Effects step := by
  intro s e hok
  have hValid : ValidEntry s e := by
    by_cases h : ValidEntry s e
    · exact h
    · unfold step at hok
      simp [h] at hok
  have hStep : step s e = (Outcome.ok, { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) := by
    unfold step; simp [hValid]
  rw [hStep]
  constructor
  · rfl
  · intro a; rfl

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hValid : ValidEntry s e := by
    by_cases h : ValidEntry s e
    · exact h
    · unfold step at hok; simp [h] at hok
  have hStep : step s e = (Outcome.ok, { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) := by
    unfold step; simp [hValid]
  rw [hStep]
  constructor
  · intro x; simp
  · show step { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } e = (Outcome.rejected, { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted })
    have hNotValid : ¬ ValidEntry { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } e := by
      intro hV
      have hmem : e.id ∉ e.id :: s.posted := hV.2.2.2.2.2
      simp at hmem
    unfold step
    simp [hNotValid]

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hValid : ValidEntry s e := by
    by_cases h : ValidEntry s e
    · exact h
    · unfold step at hok; simp [h] at hok
  have hNodup : s.accounts.Nodup := hValid.1
  have hAllIn : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hValid.2.2.1
  have hSumZero : lineSum e.lines = 0 := hValid.2.2.2.2.1
  have hStep : step s e = (Outcome.ok, { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted }) := by
    unfold step; simp [hValid]
  have hNetCons : ∀ (a0 : AccountId) (c : Int) (ls : List Line) (a : AccountId),
      netOf ((a0, c) :: ls) a = (if a0 = a then c else 0) + netOf ls a := by
    intro a0 c ls a
    unfold netOf
    simp [sumOver_cons]
  have hIndicator : ∀ (accounts : List AccountId) (hl : accounts.Nodup) (x : AccountId) (c : Int),
      sumOver accounts (fun a => if x = a then c else 0) = if x ∈ accounts then c else 0 := by
    intro accounts hl x c
    have hcongr : ∀ a, (if x = a then c else (0 : Int)) = (if a = x then c else 0) := by
      intro a; by_cases h : x = a
      · subst h; simp
      · have h2 : a ≠ x := fun hh => h hh.symm
        simp [h, h2]
    have h1 : sumOver accounts (fun a => if x = a then c else 0) = sumOver accounts (fun a => if a = x then c else 0) := by
      apply sumOver_congr; intro a _; exact hcongr a
    rw [h1]
    exact sumOver_ite_eq hl x c
  have hZeroSum : ∀ (accounts : List AccountId), sumOver accounts (fun _ => (0 : Int)) = 0 := by
    intro accounts
    induction accounts with
    | nil => simp
    | cons a l ih => simp [ih]
  have hSumNetOf : ∀ (ls : List Line) (accounts : List AccountId) (hl : accounts.Nodup),
      sumOver accounts (fun a => netOf ls a) = sumOver ls (fun l => if l.1 ∈ accounts then l.2 else 0) := by
    intro ls
    induction ls with
    | nil =>
      intro accounts hl
      unfold netOf
      simp [hZeroSum accounts, sumOver_nil]
    | cons hd ls ih =>
      intro accounts hl
      have h1 : ∀ a, netOf (hd :: ls) a = (if hd.1 = a then hd.2 else 0) + netOf ls a := by
        intro a; exact hNetCons hd.1 hd.2 ls a
      have h2 : sumOver accounts (fun a => netOf (hd :: ls) a) =
                sumOver accounts (fun a => (if hd.1 = a then hd.2 else 0) + netOf ls a) := by
        apply sumOver_congr; intro a _; exact h1 a
      rw [h2, sumOver_add, hIndicator accounts hl hd.1 hd.2, ih accounts hl]
      simp [sumOver_cons]
  have hTotalEq : total { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } = total s := by
    unfold total
    have hAdd : sumOver s.accounts (fun a => s.balance a + netOf e.lines a) =
                sumOver s.accounts (fun a => s.balance a) + sumOver s.accounts (fun a => netOf e.lines a) := by
      exact sumOver_add s.accounts (fun a => s.balance a) (fun a => netOf e.lines a)
    rw [hAdd, hSumNetOf e.lines s.accounts hNodup]
    have hZero : sumOver e.lines (fun l => if l.1 ∈ s.accounts then l.2 else 0) = 0 := by
      have hcongr : sumOver e.lines (fun l => if l.1 ∈ s.accounts then l.2 else 0) = sumOver e.lines (fun l => l.2) := by
        apply sumOver_congr
        intro l hl
        have hmem : l.1 ∈ s.accounts := hAllIn l hl
        simp [hmem]
      rw [hcongr]
      unfold lineSum at hSumZero
      exact hSumZero
    rw [hZero]
    simp
  have hStepTotal : total (step s e).2 = total { s with balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } := by
    rw [hStep]
  rw [hStepTotal, hTotalEq]

end Journal
