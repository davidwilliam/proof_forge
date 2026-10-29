import Journal.Spec
import Journal.Lemmas

namespace Journal

def memBoolNat : Nat → List Nat → Bool
  | _, [] => false
  | a, x :: xs => decide (a = x) || memBoolNat a xs

def nodupBool : List Nat → Bool
  | [] => true
  | a :: l => (!memBoolNat a l) && nodupBool l

def validBool (s : State) (e : Entry) : Bool :=
  nodupBool s.accounts &&
  (!e.lines.isEmpty) &&
  (e.lines.all (fun l => memBoolNat l.1 s.accounts)) &&
  (e.lines.all (fun l => decide (l.2 ≠ 0))) &&
  decide (lineSum e.lines = 0) &&
  (!memBoolNat e.id s.posted)

def step : Impl := fun s e =>
  if validBool s e then
    (Outcome.ok,
      { accounts := s.accounts
        balance := fun a => s.balance a + netOf e.lines a
        posted := e.id :: s.posted })
  else
    (Outcome.rejected, s)

def fooTest : Nat := 1

theorem fooTest_thm : 1 = 1 := rfl

theorem memBoolNat_true_iff_aux2 (a : Nat) (l : List Nat) : (memBoolNat a l = true ↔ a ∈ l) := by
  induction l with
  | nil => simp [memBoolNat]
  | cons x xs ih =>
    simp only [memBoolNat, Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]

theorem memBoolNat_false_iff_aux3 (a : Nat) (l : List Nat) : (memBoolNat a l = false ↔ a ∉ l) := by
  have h : memBoolNat a l = true ↔ a ∈ l := memBoolNat_true_iff_aux2 a l
  by_cases hm : memBoolNat a l = true
  · simp [hm, h.mp hm]
  · have hb : memBoolNat a l = false := by cases hmb : memBoolNat a l <;> simp_all
    have hnotin : a ∉ l := fun hmem => hm (h.mpr hmem)
    simp [hb, hnotin]

theorem nodupBool_true_iff_aux4 (l : List Nat) : (nodupBool l = true ↔ l.Nodup) := by
  induction l with
  | nil => simp [nodupBool]
  | cons x xs ih =>
    simp only [nodupBool, Bool.and_eq_true, ih]
    constructor
    · intro h
      have h1 : memBoolNat x xs = false := by
        cases hm : memBoolNat x xs <;> simp_all
      have hn : x ∉ xs := (memBoolNat_false_iff_aux3 _ _).mp h1
      exact List.nodup_cons.mpr ⟨hn, h.2⟩
    · intro h
      have hn : x ∉ xs := (List.nodup_cons.mp h).1
      have h1 : memBoolNat x xs = false := (memBoolNat_false_iff_aux3 _ _).mpr hn
      constructor
      · cases hm : memBoolNat x xs <;> simp_all
      · exact (List.nodup_cons.mp h).2

theorem all_true_iff_aux2 (l : List Line) (p : Line → Bool) : (l.all p = true ↔ ∀ x ∈ l, p x = true) := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    simp only [List.all_cons, Bool.and_eq_true, List.mem_cons, ih]
    constructor
    · intro h y0 hy0
      rcases hy0 with rfl | hm
      · exact h.1
      · exact h.2 y0 hm
    · intro h
      exact ⟨h y (by simp), fun y0 hm => h y0 (by simp [hm])⟩

theorem isEmpty_false_aux2 (l : List Line) : ((!l.isEmpty) = true ↔ l ≠ []) := by
  cases l with
  | nil => simp
  | cons y ys => simp

theorem validBool_true_iff (s : State) (e : Entry) : (validBool s e = true ↔ ValidEntry s e) := by
  unfold validBool ValidEntry
  simp only [Bool.and_eq_true, nodupBool_true_iff_aux4, isEmpty_false_aux2,
    all_true_iff_aux2, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨hN, hNE⟩, hMem⟩, hNz⟩, hSum⟩, hNotPost⟩
    refine ⟨hN, hNE, ?_, ?_, hSum, ?_⟩
    · intro l hl
      have h1 := hMem l hl
      exact (memBoolNat_true_iff_aux2 _ _).mp h1
    · intro l hl
      have h1 := hNz l hl
      exact h1
    · have hfalse : memBoolNat e.id s.posted = false := by
        cases hm : memBoolNat e.id s.posted with
        | true => simp [hm] at hNotPost
        | false => rfl
      exact (memBoolNat_false_iff_aux3 _ _).mp hfalse
  · rintro ⟨hN, hNE, hMem, hNz, hSum, hNotPost⟩
    refine ⟨⟨⟨⟨⟨hN, hNE⟩, ?_⟩, ?_⟩, hSum⟩, ?_⟩
    · intro l hl
      exact (memBoolNat_true_iff_aux2 _ _).mpr (hMem l hl)
    · intro l hl
      exact hNz l hl
    · show (!memBoolNat e.id s.posted) = true
      have h1 : memBoolNat e.id s.posted = false :=
        (memBoolNat_false_iff_aux3 _ _).mpr hNotPost
      simp [h1]

theorem req_valid_succeeds_aux : ValidSucceeds step := by
  intro s e hV
  have hv : validBool s e = true := (validBool_true_iff s e).mpr hV
  unfold step
  simp [hv]

theorem step_ok_of_validBool (s : State) (e : Entry) (hv : validBool s e = true) : (step s e).1 = .ok := by
  unfold step
  simp [hv]

theorem sumOver_zero_aux (l : List α) : sumOver l (fun _ : α => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [sumOver_cons, ih, Int.add_zero]

theorem idem_test_aux : True := trivial
#check validBool
#check memBoolNat_true_iff_aux2

theorem idem_helper_valid_false (s : State) (e : Entry) (f : AccountId → Int) :
    validBool { accounts := s.accounts, balance := f, posted := e.id :: s.posted } e = false := by
  unfold validBool
  have hm : memBoolNat e.id (e.id :: s.posted) = true := by simp [memBoolNat]
  simp [hm]

theorem idem_probe (s : State) (e : Entry) (hmt : memBoolNat e.id ((step s e).2.posted) = true) :
    validBool (step s e).2 e = false := by
  unfold validBool
  have hF : (!memBoolNat e.id ((step s e).2.posted)) = false := by simp [hmt]
  simp [hF]

theorem idem_probe4 (s2 : State) (e : Entry) (hv2 : validBool s2 e = false) :
    step s2 e = (.rejected, s2) := by
  simp [step, hv2]

theorem trial_if_swap_aux99 (x : Nat) (c : Int) (a : Nat) :
    (if x = a then c else 0) = (if a = x then c else 0) := by
  by_cases h : a = x
  · subst h; simp
  · have h' : x ≠ a := fun h2 => h h2.symm
    simp [h, h']

theorem trial_inner_aux99 (accs : List Nat) (hN : accs.Nodup) (l : Line) :
    sumOver accs (fun a => if l.1 = a then l.2 else 0) = if l.1 ∈ accs then l.2 else 0 := by
  have hcong : ∀ a ∈ accs, (if l.1 = a then l.2 else 0) = (if a = l.1 then l.2 else 0) := by
    intro a _; exact trial_if_swap_aux99 l.1 l.2 a
  rw [sumOver_congr accs _ _ hcong]
  exact sumOver_ite_eq hN l.1 l.2

theorem trial_sumNet_aux99 (ls : List Line) (accs : List Nat) (hN : accs.Nodup)
    (hMem : ∀ l ∈ ls, l.1 ∈ accs) :
    sumOver accs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have h0 : ∀ a ∈ accs, netOf [] a = 0 := by intro a _; rfl
    have heq := sumOver_congr accs (fun a => netOf [] a) (fun _ => 0) h0
    rw [heq]
    exact sumOver_zero_aux accs
  | cons hd tl ih =>
    have hMemTl : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hMem l (by simp [hl])
    have hHeadMem : hd.1 ∈ accs := hMem hd (by simp)
    have hNetUnfold : ∀ a, netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
      intro a; simp [netOf]
    have hStep : sumOver accs (fun a => netOf (hd :: tl) a)
        = sumOver accs (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by
      apply sumOver_congr
      intro a _; rw [hNetUnfold a]
    have hStep2 : sumOver accs (fun a => netOf (hd :: tl) a)
        = sumOver accs (fun a => (if hd.1 = a then hd.2 else 0)) + sumOver accs (fun a => netOf tl a) := by
      rw [hStep, sumOver_add]
    rw [hStep2, trial_inner_aux99 accs hN hd, if_pos hHeadMem, ih hMemTl]
    simp [lineSum]

theorem req_valid_succeeds : ValidSucceeds step := req_valid_succeeds_aux

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hInv
  have hv : validBool s e = false := by
    cases hvb : validBool s e
    · rfl
    · exfalso; apply hInv; exact (validBool_true_iff s e).mp hvb
  unfold step
  simp [hv]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hOk l hl
  have hv : validBool s e = true := by
    cases hvv : validBool s e
    · have hstep : (step s e).1 = Outcome.rejected := by unfold step; simp [hvv]
      rw [hstep] at hOk
      cases hOk
    · rfl
  have hV : ValidEntry s e := (validBool_true_iff s e).mp hv
  exact hV.2.2.1 l hl

theorem req_balanced : Balanced step := by
  intro s e hOk
  have hv : validBool s e = true := by
    cases hvv : validBool s e
    · have hstep : (step s e).1 = Outcome.rejected := by unfold step; simp [hvv]
      rw [hstep] at hOk
      cases hOk
    · rfl
  have hV : ValidEntry s e := (validBool_true_iff s e).mp hv
  obtain ⟨hN, hNE, hMem, hNz, hSum, hNotPost⟩ := hV
  exact hSum

theorem req_effects : Effects step := by
  intro s e hOk
  have hv : validBool s e = true := by
    cases hvv : validBool s e with
    | false =>
      have hstep : (step s e).1 = Outcome.rejected := by unfold step; simp [hvv]
      rw [hstep] at hOk
      cases hOk
    | true => rfl
  have hst : step s e = (Outcome.ok,
      { accounts := s.accounts,
        balance := fun a => s.balance a + netOf e.lines a,
        posted := e.id :: s.posted }) := by unfold step; simp [hv]
  rw [hst]
  exact ⟨rfl, fun a => rfl⟩

theorem req_idempotency : Idempotent step := by
  intro s e hOk
  have hv : validBool s e = true := by
    cases hvv : validBool s e with
    | false =>
      have hstep : (step s e).1 = Outcome.rejected := by unfold step; simp [hvv]
      rw [hstep] at hOk
      cases hOk
    | true => rfl
  have hst : step s e = (Outcome.ok,
      { accounts := s.accounts,
        balance := fun a => s.balance a + netOf e.lines a,
        posted := e.id :: s.posted }) := by unfold step; simp [hv]
  have hmem : memBoolNat e.id ((step s e).2.posted) = true := by
    rw [hst]
    simp [memBoolNat]
  have hv2 : validBool (step s e).2 e = false := idem_probe s e hmem
  have hstep2 : step (step s e).2 e = (.rejected, (step s e).2) := idem_probe4 _ _ hv2
  constructor
  · intro x
    rw [hst]
    simp
  · exact hstep2

theorem req_trial_balance : TrialBalance step := by
  intro s e hOk
  have hv : validBool s e = true := by
    cases hvv : validBool s e with
    | false =>
      have hstep : (step s e).1 = Outcome.rejected := by unfold step; simp [hvv]
      rw [hstep] at hOk
      cases hOk
    | true => rfl
  have hV : ValidEntry s e := (validBool_true_iff s e).mp hv
  obtain ⟨hN, hNE, hMem, hNz, hSum, hNotPost⟩ := hV
  have hst : step s e = (Outcome.ok,
      { accounts := s.accounts,
        balance := fun a => s.balance a + netOf e.lines a,
        posted := e.id :: s.posted }) := by unfold step; simp [hv]
  have hTot : total (step s e).2 = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    rw [hst]; rfl
  rw [hTot, sumOver_add]
  have hZero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
    rw [trial_sumNet_aux99 e.lines s.accounts hN hMem, hSum]
  rw [hZero, Int.add_zero]
  rfl

end Journal
