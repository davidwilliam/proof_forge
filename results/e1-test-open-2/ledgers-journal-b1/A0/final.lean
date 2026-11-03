import Journal.Spec
import Journal.Lemmas
namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

def step : Impl := fun s e =>
  if _h : ValidEntry s e then
    let bal := e.lines.foldl (fun b (l : Line) => adjust b l.1 l.2) s.balance
    (.ok, { s with balance := bal, posted := e.id :: s.posted })
  else (.rejected, s)

private theorem step_eq_of_valid {s : State} {e : Entry} (hV : ValidEntry s e) :
    step s e = (.ok, { s with balance := e.lines.foldl (fun b (l : Line) => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted }) := by
  unfold step
  simp only [dif_pos hV]

private theorem step_eq_of_invalid {s : State} {e : Entry} (hNV : ¬ ValidEntry s e) :
    step s e = (.rejected, s) := by
  unfold step
  simp only [dif_neg hNV]

private theorem ok_imp_valid {s : State} {e : Entry} (h : (step s e).1 = .ok) : ValidEntry s e := by
  by_cases hV : ValidEntry s e
  · exact hV
  · have heq := step_eq_of_invalid hV
    have h2 : (step s e).1 = .rejected := by rw [heq]
    rw [h2] at h
    cases h

private theorem adjust_eq (bal : AccountId → Int) (a : AccountId) (amt : Int) (x : AccountId) :
    adjust bal a amt x = bal x + if a = x then amt else 0 := by
  unfold adjust
  by_cases hx : x = a
  · have ha : a = x := hx.symm
    rw [if_pos hx, if_pos ha]
  · have ha : ¬ a = x := fun h => hx h.symm
    rw [if_neg hx, if_neg ha, Int.add_zero]

private theorem adjust_swap (bal : AccountId → Int) (hd : Line) (a : AccountId) :
    adjust bal hd.1 hd.2 a = bal a + if hd.1 = a then hd.2 else 0 := by
  exact adjust_eq bal hd.1 hd.2 a

private theorem foldl_adjust_eq (ls : List Line) (bal : AccountId → Int) (a : AccountId) :
    (ls.foldl (fun b (l : Line) => adjust b l.1 l.2) bal) a = bal a + netOf ls a := by
  induction ls generalizing bal with
  | nil =>
    simp only [List.foldl_nil, netOf, sumOver_nil, Int.add_zero]
  | cons hd tl ih =>
    have hFold : List.foldl (fun b (l : Line) => adjust b l.1 l.2) bal (hd :: tl) =
                List.foldl (fun b (l : Line) => adjust b l.1 l.2) (adjust bal hd.1 hd.2) tl := rfl
    rw [hFold]
    have h1 := ih (adjust bal hd.1 hd.2)
    rw [adjust_swap bal hd a] at h1
    have hNet : netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := rfl
    rw [hNet]
    omega

private theorem sumOver_zero (l : List AccountId) : sumOver l (fun _ : AccountId => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have : sumOver (hd :: tl) (fun _ => (0 : Int)) = (0 : Int) + sumOver tl (fun _ => (0 : Int)) := rfl
    rw [this, ih, Int.add_zero]

private theorem if_congr_hd (hd : Line) (a : AccountId) :
    (if hd.1 = a then hd.2 else (0 : Int)) = (if a = hd.1 then hd.2 else 0) := by
  by_cases h : a = hd.1
  · have h2 : hd.1 = a := h.symm
    rw [if_pos h, if_pos h2]
  · have h2 : ¬ hd.1 = a := fun h2 => h h2.symm
    rw [if_neg h, if_neg h2]

private theorem sumOver_netOf_eq_lineSum (accounts : List AccountId) (ls : List Line)
    (hNodup : accounts.Nodup) (hMem : ∀ l ∈ ls, l.1 ∈ accounts) :
    sumOver accounts (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have h1 : (fun a => netOf [] a) = (fun _ : AccountId => (0 : Int)) := by
      funext a; rfl
    rw [h1]
    have h2 : lineSum [] = 0 := rfl
    rw [h2]
    exact sumOver_zero accounts
  | cons hd tl ihTl =>
    have hMemTl : ∀ l ∈ tl, l.1 ∈ accounts := fun l hl => hMem l (List.mem_cons_of_mem hd hl)
    have ih := ihTl hMemTl
    have hEq : ∀ a ∈ accounts, netOf (hd :: tl) a = (if a = hd.1 then hd.2 else (0 : Int)) + netOf tl a := by
      intro a _
      have hNet : netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := rfl
      rw [hNet, if_congr_hd hd a]
    have hConj := sumOver_congr accounts
        (fun a => netOf (hd :: tl) a)
        (fun a => (if a = hd.1 then hd.2 else (0 : Int)) + netOf tl a)
        hEq
    rw [hConj]
    have hAdd := sumOver_add accounts
        (fun a => if a = hd.1 then hd.2 else (0 : Int))
        (fun a => netOf tl a)
    rw [hAdd, ih]
    have hIte := sumOver_ite_eq hNodup hd.1 hd.2
    rw [hIte]
    have hMemHd : hd.1 ∈ accounts := hMem hd List.mem_cons_self
    rw [if_pos hMemHd]
    have hLine : lineSum (hd :: tl) = hd.2 + lineSum tl := rfl
    rw [hLine]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hV
  have hEq := step_eq_of_valid hV
  rw [hEq]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hNV
  exact step_eq_of_invalid hNV

theorem req_known_accounts : KnownAccounts step := by
  intro s e hOk l hl
  have hV := ok_imp_valid hOk
  unfold ValidEntry at hV
  exact hV.2.2.1 l hl

theorem req_balanced : Balanced step := by
  intro s e hOk
  have hV := ok_imp_valid hOk
  unfold ValidEntry at hV
  exact hV.2.2.2.2.1

theorem req_effects : Effects step := by
  intro s e hOk
  have hV := ok_imp_valid hOk
  have hEq := step_eq_of_valid hV
  rw [hEq]
  constructor
  · rfl
  · intro a
    exact foldl_adjust_eq e.lines s.balance a

theorem req_idempotency : Idempotent step := by
  intro s e hOk
  have hV := ok_imp_valid hOk
  have hEq := step_eq_of_valid hV
  rw [hEq]
  constructor
  · intro x
    simp only [List.mem_cons]
  · have hNotValid : ¬ ValidEntry { s with balance := e.lines.foldl (fun b (l : Line) => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } e := by
      intro hC
      unfold ValidEntry at hC
      have hMem : e.id ∈ (e.id :: s.posted) := List.mem_cons_self
      exact hC.2.2.2.2.2 hMem
    show step { s with balance := e.lines.foldl (fun b (l : Line) => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } e =
        (.rejected, { s with balance := e.lines.foldl (fun b (l : Line) => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted })
    exact step_eq_of_invalid hNotValid

theorem req_trial_balance : TrialBalance step := by
  intro s e hOk
  have hV := ok_imp_valid hOk
  have hEff := req_effects (s:=s) (e:=e) hOk
  have hAccounts : (step s e).2.accounts = s.accounts := hEff.1
  have hBal : ∀ a, (step s e).2.balance a = s.balance a + netOf e.lines a := hEff.2
  unfold total
  rw [hAccounts]
  have hConj : sumOver s.accounts (step s e).2.balance = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    apply sumOver_congr
    intro a ha
    rw [hBal a]
  rw [hConj]
  have hAdd := sumOver_add s.accounts s.balance (fun a => netOf e.lines a)
  rw [hAdd]
  unfold ValidEntry at hV
  have hNodup := hV.1
  have hMemAccounts : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hV.2.2.1
  have hLineSumZero : lineSum e.lines = 0 := hV.2.2.2.2.1
  have hSumNet := sumOver_netOf_eq_lineSum s.accounts e.lines hNodup hMemAccounts
  rw [hSumNet, hLineSumZero, Int.add_zero]

end Journal
