import Journal.Spec
import Journal.Lemmas
namespace Journal

def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

def acceptable (s : State) (e : Entry) : Bool :=
  decide s.accounts.Nodup && !e.lines.isEmpty && e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) &&
  decide (lineSum e.lines = 0) && !s.posted.contains e.id

def step : Impl := fun s e =>
  if acceptable s e then
    (.ok, { accounts := s.accounts,
            balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance,
            posted := e.id :: s.posted })
  else (.rejected, s)

theorem fold_balance_aux (bal : AccountId → Int) (ls : List Line) (a : AccountId) :
    (ls.foldl (fun b l => adjust b l.1 l.2) bal) a = bal a + netOf ls a := by
  induction ls generalizing bal with
  | nil =>
    simp [netOf, sumOver_nil]
  | cons hd tl ih =>
    -- unfold netOf cons
    have hNet : netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
      unfold netOf; simp
    rw [hNet]
    have hAdj : (adjust bal hd.1 hd.2) a = bal a + if hd.1 = a then hd.2 else 0 := by
      unfold adjust
      by_cases ha : a = hd.1
      · subst ha; simp
      · have h1 : ¬ (a = hd.1) := ha
        have h2 : ¬ (hd.1 = a) := fun h => h1 h.symm
        simp [h1, h2]
    have ih2 := ih (adjust bal hd.1 hd.2)
    simp only [List.foldl_cons] at *
    rw [ih2, hAdj]
    omega

theorem step_ok_acc (s : State) (e : Entry) (hOk : (step s e).1 = .ok) : acceptable s e = true := by
  unfold step at hOk
  by_cases ha : acceptable s e = true
  · exact ha
  · have hf : acceptable s e = false := by cases hc : acceptable s e <;> simp_all
    simp [hf] at hOk

def dummyX : Nat := 1

theorem myLemmaTest : 1 + 1 = 2 := by rfl

theorem sumOver_zero (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp [ih]

theorem sumOver_netOf_known (acc : List AccountId) (hNodup : acc.Nodup) (ls : List Line) (hK : ∀ l ∈ ls, l.1 ∈ acc) :
    sumOver acc (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have h : ∀ a, netOf ([] : List Line) a = 0 := by intro a; simp [netOf]
    have : sumOver acc (fun a => netOf ([] : List Line) a) = sumOver acc (fun _ => (0 : Int)) := by
      apply sumOver_congr; intro a _; rw [h]
    rw [this, sumOver_zero]
    simp [lineSum]
  | cons hd tl ih =>
    have hNetCons : ∀ a, netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
      intro a; unfold netOf; simp
    have h1 : sumOver acc (fun a => netOf (hd :: tl) a) = sumOver acc (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by
      apply sumOver_congr; intro a _; exact hNetCons a
    rw [h1, sumOver_add]
    have hSingle : sumOver acc (fun a => if hd.1 = a then hd.2 else 0) = hd.2 := by
      have hcomm : (fun a => if hd.1 = a then hd.2 else 0) = (fun a => if a = hd.1 then hd.2 else 0) := by
        funext a
        by_cases ha : a = hd.1
        · simp [ha]
        · have hb : ¬ (hd.1 = a) := fun h => ha h.symm
          simp [ha, hb]
      rw [hcomm, sumOver_ite_eq hNodup hd.1 hd.2, if_pos (hK hd (by simp))]
    rw [hSingle]
    have hKtl : ∀ l ∈ tl, l.1 ∈ acc := fun l hl => hK l (by simp [hl])
    rw [ih hKtl]
    unfold lineSum
    simp

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hV
  obtain ⟨hNodup, hNe, hMem, hNz, hSum, hNotPosted⟩ := hV
  have h1 : decide s.accounts.Nodup = true := by simp [hNodup]
  have h2 : (!e.lines.isEmpty) = true := by
    cases he : e.lines
    · contradiction
    · simp
  have h3 : e.lines.all (fun l => s.accounts.contains l.1) = true := by
    simp only [List.all_eq_true]
    intro l hl
    simp [List.contains_eq_mem, hMem l hl]
  have h4 : e.lines.all (fun l => l.2 != 0) = true := by
    simp only [List.all_eq_true]
    intro l hl
    simp [hNz l hl]
  have h5 : decide (lineSum e.lines = 0) = true := by simp [hSum]
  have h6 : (!s.posted.contains e.id) = true := by
    simp [List.contains_eq_mem, hNotPosted]
  have hAcc : acceptable s e = true := by
    unfold acceptable
    simp only [h1, h2, h3, h4, h5, h6, Bool.true_and, Bool.and_true]
  unfold step
  simp [hAcc]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hInv
  unfold step
  cases hc : acceptable s e with
  | true =>
    exfalso
    apply hInv
    unfold acceptable at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.contains_eq_mem] at hc
    obtain ⟨⟨⟨⟨⟨hNodup, hNotEmpty⟩, hMem⟩, hNonZero⟩, hSum⟩, hNotPosted⟩ := hc
    refine ⟨hNodup, ?_, ?_, ?_, hSum, ?_⟩
    · intro hNil
      simp [hNil] at hNotEmpty
    · intro l hl; exact hMem l hl
    · intro l hl; have := hNonZero l hl; simpa using this
    · simpa using hNotPosted
  | false =>
    simp [hc]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hOk
  unfold step at hOk
  split at hOk
  · next hc =>
    unfold acceptable at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_eq_mem] at hc
    obtain ⟨⟨⟨⟨⟨hNodup, hNotEmpty⟩, hMem⟩, hNonZero⟩, hSum⟩, hNotPosted⟩ := hc
    intro l hl
    exact hMem l hl
  · simp at hOk

theorem req_balanced : Balanced step := by
  intro s e hOk
  unfold step at hOk
  split at hOk
  · next hAcc =>
    unfold acceptable at hAcc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_eq_mem] at hAcc
    obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hSum⟩, _⟩ := hAcc
    exact hSum
  · simp at hOk

theorem req_effects : Effects step := by
  intro s e hOk
  have hAcc := step_ok_acc s e hOk
  constructor
  · show (step s e).2.accounts = s.accounts
    unfold step; simp [hAcc]
  · intro a
    show (step s e).2.balance a = s.balance a + netOf e.lines a
    unfold step; simp [hAcc, fold_balance_aux]

theorem req_idempotency : Idempotent step := by
  intro s e hOk
  have hAcc : acceptable s e = true := step_ok_acc s e hOk
  have hS2_eq : (step s e).2 = { accounts := s.accounts, balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } := by
    unfold step
    simp [hAcc]
  constructor
  · intro x
    rw [hS2_eq]
    simp
  · have hNotAccept2 : acceptable ({ accounts := s.accounts, balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State) e = false := by
      unfold acceptable
      simp
    have hEq : (step s e).2 = { accounts := s.accounts, balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } := hS2_eq
    rw [hEq] at *
    unfold step
    simp [hNotAccept2]

theorem req_trial_balance : TrialBalance step := by
  intro s e hOk
  have hAcc := step_ok_acc s e hOk
  have hEff := req_effects s e hOk
  obtain ⟨hAccEq, hBal⟩ := hEff
  have hNodup : s.accounts.Nodup := by
    unfold acceptable at hAcc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAcc
    obtain ⟨⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩, _⟩ := hAcc
    exact h
  have hKnown : ∀ l ∈ e.lines, l.1 ∈ s.accounts := fun l hl => req_known_accounts s e hOk l hl
  have hBalanced : lineSum e.lines = 0 := req_balanced s e hOk
  show total (step s e).2 = total s
  unfold total
  rw [hAccEq]
  have hSum : sumOver s.accounts (step s e).2.balance = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    apply sumOver_congr; intro a _; exact hBal a
  rw [hSum, sumOver_add, sumOver_netOf_known s.accounts hNodup e.lines hKnown, hBalanced, Int.add_zero]

end Journal
