import Journal.Spec
import Journal.Lemmas
namespace Journal

def isValid (s : State) (e : Entry) : Bool :=
  decide s.accounts.Nodup && decide (e.lines != []) && e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && decide (lineSum e.lines = 0) && !s.posted.contains e.id

def step : Impl := fun s e =>
  if isValid s e then
    let bal := e.lines.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) s.balance
    (.ok, { s with balance := bal, posted := e.id :: s.posted })
  else (.rejected, s)

private instance decValid (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def step2 : Impl := fun s e =>
  if _h : ValidEntry s e then
    let bal := e.lines.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) s.balance
    (.ok, { s with balance := bal, posted := e.id :: s.posted })
  else (.rejected, s)

theorem req_invalid_noop2 : InvalidNoop step2 := by
  intro s e hNot
  unfold step2
  simp [hNot]

theorem isValid_of_ValidEntry_aux (s : State) (e : Entry) (h : ValidEntry s e) : isValid s e = true := by
  unfold ValidEntry at h
  unfold isValid
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?h1, ?h2⟩, ?h3⟩, ?h4⟩, ?h5⟩, ?h6⟩
  · simp [h.1]
  · simp [h.2.1]
  · rw [List.all_eq_true]
    intro l hl
    have hm := h.2.2.1 l hl
    simp [hm]
  · rw [List.all_eq_true]
    intro l hl
    simp
    exact h.2.2.2.1 l hl
  · simp [h.2.2.2.2.1]
  · simp
    exact h.2.2.2.2.2

theorem test_contains (s : State) (l : Line) (h : s.accounts.contains l.1 = true) : l.1 ∈ s.accounts := by
  simp [List.contains_eq_mem] at h
  exact h

theorem isValid_true_imp_ValidEntry2 (s : State) (e : Entry) (h : isValid s e = true) : ValidEntry s e := by
  unfold isValid at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hNodup, hNe⟩, hAllAcc⟩, hAllNz⟩, hSum⟩, hNotPosted⟩ := h
  unfold ValidEntry
  refine ⟨hNodup, ?_, ?_, ?_, hSum, ?_⟩
  · simpa using hNe
  · intro l hl
    have hh : s.accounts.contains l.1 = true := by
      have := (List.all_eq_true.mp hAllAcc) l hl
      simpa using this
    simp [List.contains_eq_mem] at hh
    exact hh
  · intro l hl
    have hh : decide (l.2 ≠ 0) = true := by
      have := (List.all_eq_true.mp hAllNz) l hl
      simpa using this
    simpa using hh
  · simp at hNotPosted
    exact hNotPosted

theorem sumOver_zero (accs : List AccountId) : sumOver accs (fun _ : AccountId => (0:Int)) = 0 := by
  induction accs with
  | nil => rfl
  | cons h t ih => simp [sumOver_cons, ih]

theorem netOf_sum_eq_lineSum (accs : List AccountId) (ls : List Line) (hl : accs.Nodup) (hk : ∀ l ∈ ls, l.1 ∈ accs) :
    sumOver accs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    simp [netOf, lineSum]
    exact sumOver_zero accs
  | cons hd tl ih =>
    have hkHd : hd.1 ∈ accs := hk hd (by simp)
    have hkTl : ∀ l ∈ tl, l.1 ∈ accs := fun l hl2 => hk l (by simp [hl2])
    have ihH := ih hkTl
    simp only [netOf, lineSum, sumOver_cons] at ihH ⊢
    have hAdd : sumOver accs (fun a => (if hd.1 = a then hd.2 else (0:Int)) + sumOver tl fun l => if l.1 = a then l.2 else 0) = sumOver accs (fun a => if hd.1 = a then hd.2 else 0) + sumOver accs (fun a => sumOver tl fun l => if l.1 = a then l.2 else 0) := by
      exact sumOver_add accs _ _
    rw [hAdd, ihH]
    have hIte : sumOver accs (fun a => if hd.1 = a then hd.2 else (0:Int)) = hd.2 := by
      have hEq : (fun a => if hd.1 = a then hd.2 else (0:Int)) = (fun a => if a = hd.1 then hd.2 else 0) := by
        funext a; by_cases h : hd.1 = a
        · simp [h]
        · simp [h, Ne.symm h]
      rw [hEq, sumOver_ite_eq hl hd.1 hd.2, if_pos hkHd]
    rw [hIte]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hV
  have hIs := isValid_of_ValidEntry_aux s e hV
  unfold step
  simp [hIs]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hNot
  have hIs : isValid s e = false := by
    by_cases hb : isValid s e = true
    · exfalso; exact hNot (isValid_true_imp_ValidEntry2 s e hb)
    · simp at hb ⊢
      exact hb
  unfold step
  simp [hIs]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  have hv : isValid s e = true := by
    by_cases h : isValid s e
    · exact h
    · exfalso; unfold step at hok; simp [h] at hok
  unfold isValid at hv
  simp at hv
  have hAll := hv.1.1.1.2
  exact hAll _ _ hl

theorem req_balanced : Balanced step := by
  intro s e hok
  have hv : isValid s e = true := by
    by_cases h : isValid s e
    · exact h
    · exfalso; unfold step at hok; simp [h] at hok
  unfold isValid at hv
  simp at hv
  exact hv.left.right

theorem req_effects : Effects step := by
  intro s e hok
  have hv : isValid s e = true := by
    by_cases h : isValid s e
    · exact h
    · exfalso; unfold step at hok; simp [h] at hok
  have hstep : step s e = (.ok, { s with balance := e.lines.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) s.balance, posted := e.id :: s.posted }) := by
    unfold step; simp [hv]
  rw [hstep]
  constructor
  · rfl
  · intro a
    have key : ∀ (ls : List Line) (b : AccountId → Int), (ls.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) b) a = b a + netOf ls a := by
      intro ls b
      induction ls generalizing b with
      | nil => simp [netOf]
      | cons hd tl ih =>
        simp only [List.foldl_cons, netOf, sumOver_cons] at *
        have htl := ih (fun x => if x = hd.1 then b x + hd.2 else b x)
        rw [htl]
        by_cases h : hd.1 = a
        · simp [h]
          omega
        · have h2 : ¬ a = hd.1 := fun heq => h heq.symm
          simp [h, h2]
    exact key e.lines s.balance

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hv : isValid s e = true := by
    by_cases hh : isValid s e
    · exact hh
    · exfalso; unfold step at hok; simp [hh] at hok
  have hStepEq : step s e = (.ok, { s with balance := e.lines.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) s.balance, posted := e.id :: s.posted }) := by
    unfold step; simp [hv]
  rw [hStepEq] at hok ⊢
  simp at hok
  constructor
  · intro x; simp
  · show step { s with balance := e.lines.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) s.balance, posted := e.id :: s.posted } e = (.rejected, { s with balance := e.lines.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) s.balance, posted := e.id :: s.posted })
    unfold step
    have hfalse : isValid { s with balance := e.lines.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) s.balance, posted := e.id :: s.posted } e = false := by
      unfold isValid
      simp
    simp [hfalse]

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hBal : lineSum e.lines = 0 := req_balanced s e hok
  have hEff := req_effects s e hok
  obtain ⟨hAccEq, hBalEq⟩ := hEff
  unfold total
  have hTotalEq : sumOver (step s e).2.accounts (step s e).2.balance = sumOver s.accounts ((step s e).2.balance) := by
    rw [hAccEq]
  rw [hTotalEq]
  have hEq : sumOver s.accounts (step s e).2.balance = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    apply sumOver_congr
    intro a _; exact hBalEq a
  rw [hEq, sumOver_add]
  have hKnown : ∀ l ∈ e.lines, l.1 ∈ s.accounts := req_known_accounts s e hok
  by_cases hV : ValidEntry s e
  · have hNodup : s.accounts.Nodup := hV.1
    have hNetZero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
      rw [netOf_sum_eq_lineSum s.accounts e.lines hNodup hKnown, hBal]
    rw [hNetZero]
    simp
  · have hStep := req_invalid_noop s e hV
    rw [hStep] at hok
    simp at hok

end Journal
