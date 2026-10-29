import Journal.Spec
import Journal.Lemmas

namespace Journal

def nodupB : List AccountId → Bool
  | [] => true
  | a :: l => if a ∈ l then false else nodupB l

def allKnownB : List AccountId → List Line → Bool
  | _, [] => true
  | accs, l :: ls => if l.1 ∈ accs then allKnownB accs ls else false

def allNzB : List Line → Bool
  | [] => true
  | l :: ls => if l.2 = 0 then false else allNzB ls

def freshB (posted : List EntryId) (id : EntryId) : Bool :=
  if id ∈ posted then false else true

def isValid (s : State) (e : Entry) : Bool :=
  nodupB s.accounts && !e.lines.isEmpty && allKnownB s.accounts e.lines && allNzB e.lines && decide (lineSum e.lines = 0) && freshB s.posted e.id

def step : Impl := fun s e =>
  if isValid s e then
    (Outcome.ok,
      { accounts := s.accounts,
        balance := fun a => s.balance a + netOf e.lines a,
        posted := e.id :: s.posted })
  else
    (Outcome.rejected, s)

def fooTest : Nat := 1

theorem fooTestThm : 1 = 1 := rfl

theorem fooA : 2 = 2 := rfl

theorem fooB : 3 = 3 := rfl

theorem nodupB_true_of_nodup (l : List AccountId) (h : l.Nodup) : nodupB l = true := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.nodup_cons] at h
    obtain ⟨hMem, hNodup⟩ := h
    simp only [nodupB, hMem, ↓reduceIte, ih hNodup]

theorem allKnownB_true_of_mem (accs : List AccountId) (ls : List Line) (h : ∀ l ∈ ls, l.1 ∈ accs) : allKnownB accs ls = true := by
  induction ls with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : hd.1 ∈ accs := h hd (by simp)
    have htl : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => h l (by simp [hl])
    simp only [allKnownB, hhd, ↓reduceIte, ih htl]

theorem allNzB_true_of_ne (ls : List Line) (h : ∀ l ∈ ls, l.2 ≠ 0) : allNzB ls = true := by
  induction ls with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : hd.2 ≠ 0 := h hd (by simp)
    have htl : ∀ l ∈ tl, l.2 ≠ 0 := fun l hl => h l (by simp [hl])
    simp only [allNzB]
    have hne : ¬ (hd.2 = 0) := hhd
    simp [hne, ih htl]

theorem freshB_true_of_not_mem (posted : List EntryId) (id : EntryId) (h : id ∉ posted) : freshB posted id = true := by
  simp only [freshB, h, ↓reduceIte]

theorem isEmpty_neg_true_of_ne_nil (ls : List Line) (h : ls ≠ []) : ((!ls.isEmpty) = true) := by
  cases ls with
  | nil => simp at h
  | cons hd tl => rfl

theorem myAndHelper {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem myNodupOfB (l : List AccountId) (h : nodupB l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    simp only [nodupB] at h
    by_cases hm : a ∈ t
    · simp [hm] at h
    · simp [hm] at h
      rw [List.nodup_cons]
      exact ⟨hm, ih h⟩

theorem myMemOfKnown (accs : List AccountId) (ls : List Line)
    (h : allKnownB accs ls = true) : ∀ l ∈ ls, l.1 ∈ accs := by
  induction ls with
  | nil => intro l hl; simp at hl
  | cons hd tl ih =>
    simp only [allKnownB] at h
    by_cases hm : hd.1 ∈ accs
    · simp [hm] at h
      intro l hl
      simp at hl
      cases hl with
      | inl heq => rw [heq]; exact hm
      | inr hmem => exact ih h l hmem
    · simp [hm] at h

theorem myNeOfNz (ls : List Line) (h : allNzB ls = true) :
    ∀ l ∈ ls, l.2 ≠ 0 := by
  induction ls with
  | nil => intro l hl; simp at hl
  | cons hd tl ih =>
    simp only [allNzB] at h
    by_cases hz : hd.2 = 0
    · simp [hz] at h
    · simp [hz] at h
      intro l hl
      simp at hl
      cases hl with
      | inl heq => rw [heq]; exact hz
      | inr hmem => exact ih h l hmem

theorem myNotMemOfFresh (posted : List EntryId) (id : EntryId)
    (h : freshB posted id = true) : id ∉ posted := by
  simp only [freshB] at h
  by_cases hm : id ∈ posted
  · simp [hm] at h
  · exact hm

theorem myNeNilOfNotEmpty (ls : List Line) (h : (!ls.isEmpty) = true) :
    ls ≠ [] := by
  cases ls with
  | nil => simp at h
  | cons hd tl => simp

theorem mySumOfDecide (ls : List Line)
    (h : decide (lineSum ls = 0) = true) : lineSum ls = 0 := by
  simp at h
  exact h

theorem myValidOfIsValid (s : State) (e : Entry) (h : isValid s e = true) :
    ValidEntry s e := by
  unfold isValid at h
  obtain ⟨h_rest5, h6⟩ := myAndHelper h
  obtain ⟨h_rest4, h5⟩ := myAndHelper h_rest5
  obtain ⟨h_rest3, h4⟩ := myAndHelper h_rest4
  obtain ⟨h_rest2, h3⟩ := myAndHelper h_rest3
  obtain ⟨h1, h2⟩ := myAndHelper h_rest2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact myNodupOfB _ h1
  · exact myNeNilOfNotEmpty _ h2
  · exact myMemOfKnown _ _ h3
  · exact myNeOfNz _ h4
  · exact mySumOfDecide _ h5
  · exact myNotMemOfFresh _ _ h6

theorem isValid_false_of_fresh_aux2 (s : State) (e : Entry)
    (h : freshB s.posted e.id = false) : isValid s e = false := by
  unfold isValid
  simp [h]

theorem step_rejected_aux (s : State) (e : Entry) (h : isValid s e = false) :
    step s e = (Outcome.rejected, s) := by
  simp [step, h]

theorem req_idempotency_aux6 : Idempotent step := by
  intro s e hOk
  have hIs : isValid s e = true := by
    unfold step at hOk
    by_cases h : isValid s e = true
    · exact h
    · have hF : isValid s e = false := by
        cases hb : isValid s e with
        | true => simp [hb] at h
        | false => rfl
      simp [hF] at hOk
  have hPosted : (step s e).2.posted = e.id :: s.posted := by
    simp [step, hIs]
  refine ⟨?_, ?_⟩
  · intro x
    rw [hPosted]
    simp
  · have hFreshFalse : freshB (step s e).2.posted e.id = false := by
      rw [hPosted]
      unfold freshB
      simp
    have hIs2 : isValid (step s e).2 e = false :=
      isValid_false_of_fresh_aux2 _ _ hFreshFalse
    exact step_rejected_aux _ _ hIs2

theorem sumOver_zero_fun (l : List AccountId) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem netOf_nil_eq2 (a : AccountId) : netOf [] a = 0 := rfl

theorem trialSwapAux2 (accs : List AccountId) (ls : List Line) (hNodup : accs.Nodup) :
    sumOver accs (fun a => netOf ls a) = sumOver ls (fun l => if l.1 ∈ accs then l.2 else 0) := by
  induction ls with
  | nil =>
    simp only [netOf_nil_eq2]
    rw [sumOver_zero_fun]
    simp
  | cons hd tl ih =>
    have h1 : (fun a => netOf (hd :: tl) a) = (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by
      funext a; rfl
    rw [h1, sumOver_add]
    have h2 : sumOver accs (fun a => if hd.1 = a then hd.2 else 0) = if hd.1 ∈ accs then hd.2 else 0 := by
      have hSwap : (fun a => (if hd.1 = a then hd.2 else 0)) = (fun a => if a = hd.1 then hd.2 else 0) := by
        funext a
        by_cases h : a = hd.1
        · subst h; simp
        · have h2 : ¬ (hd.1 = a) := fun hh => h hh.symm
          simp [h, h2]
      rw [hSwap]
      exact sumOver_ite_eq hNodup hd.1 hd.2
    rw [h2, ih, sumOver_cons]

theorem trialSumZero2 (s : State) (e : Entry) (hNodup : s.accounts.Nodup)
    (hKnown : ∀ l ∈ e.lines, l.1 ∈ s.accounts) (hSum : lineSum e.lines = 0) :
    sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
  rw [trialSwapAux2 s.accounts e.lines hNodup]
  have hCon : sumOver e.lines (fun l => if l.1 ∈ s.accounts then l.2 else 0) = sumOver e.lines (fun l => l.2) := by
    apply sumOver_congr
    intro l hl
    simp [hKnown l hl]
  rw [hCon]
  have hLine : sumOver e.lines (fun l => l.2) = lineSum e.lines := rfl
  rw [hLine, hSum]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hV
  obtain ⟨hNodup, hNe, hKnown, hNz, hSum, hFresh⟩ := hV
  have h1 : nodupB s.accounts = true := nodupB_true_of_nodup _ hNodup
  have h2 : ((!e.lines.isEmpty) = true) := isEmpty_neg_true_of_ne_nil _ hNe
  have h3 : allKnownB s.accounts e.lines = true := allKnownB_true_of_mem _ _ hKnown
  have h4 : allNzB e.lines = true := allNzB_true_of_ne _ hNz
  have h5 : decide (lineSum e.lines = 0) = true := by simp [hSum]
  have h6 : freshB s.posted e.id = true := freshB_true_of_not_mem _ _ hFresh
  have hIs : isValid s e = true := by unfold isValid; simp [h1, h2, h3, h4, h5, h6]
  show (step s e).1 = Outcome.ok
  simp only [step, hIs, ↓reduceIte]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hInv
  have hF : isValid s e = false := by
    cases hb : isValid s e with
    | true => exfalso; exact hInv (myValidOfIsValid s e hb)
    | false => rfl
  exact step_rejected_aux s e hF

theorem req_known_accounts : KnownAccounts step := by
  intro s e hOk
  have hIs : isValid s e = true := by
    unfold step at hOk
    by_cases h : isValid s e = true
    · exact h
    · have hF : isValid s e = false := by
        cases hb : isValid s e with
        | true => simp [hb] at h
        | false => rfl
      simp [hF] at hOk
  have hV := myValidOfIsValid s e hIs
  obtain ⟨_, _, hKnown, _, _, _⟩ := hV
  exact hKnown

theorem req_balanced : Balanced step := by
  intro s e hOk
  have hIs : isValid s e = true := by
    unfold step at hOk
    by_cases h : isValid s e = true
    · exact h
    · have hF : isValid s e = false := by
        cases hb : isValid s e with
        | true => simp [hb] at h
        | false => rfl
      simp [hF] at hOk
  have hV := myValidOfIsValid s e hIs
  obtain ⟨_, _, _, _, hSum, _⟩ := hV
  exact hSum

theorem req_effects : Effects step := by
  intro s e hOk
  have hIs : isValid s e = true := by
    unfold step at hOk
    by_cases h : isValid s e = true
    · exact h
    · have hF : isValid s e = false := by
        cases hb : isValid s e with
        | true => simp [hb] at h
        | false => rfl
      simp [hF] at hOk
  have hStep : step s e = (Outcome.ok,
      { accounts := s.accounts,
        balance := fun a => s.balance a + netOf e.lines a,
        posted := e.id :: s.posted }) := by
    unfold step
    simp [hIs]
  constructor
  · have : (step s e).2.accounts = s.accounts := by rw [hStep]
    exact this
  · intro a
    have : (step s e).2.balance a = s.balance a + netOf e.lines a := by rw [hStep]
    exact this

theorem req_idempotency    : Idempotent step := by
  intro s e hOk
  have hIs : isValid s e = true := by
    unfold step at hOk
    by_cases h : isValid s e = true
    · exact h
    · have hF : isValid s e = false := by
        cases hb : isValid s e with
        | true => simp [hb] at h
        | false => rfl
      simp [hF] at hOk
  have hPosted : (step s e).2.posted = e.id :: s.posted := by
    simp [step, hIs]
  refine ⟨?_, ?_⟩
  · intro x
    rw [hPosted]
    simp
  · have hFreshFalse : freshB (step s e).2.posted e.id = false := by
      rw [hPosted]
      unfold freshB
      simp
    have hIs2 : isValid (step s e).2 e = false :=
      isValid_false_of_fresh_aux2 _ _ hFreshFalse
    exact step_rejected_aux _ _ hIs2

theorem req_trial_balance : TrialBalance step := by
  intro s e hOk
  have hIs : isValid s e = true := by
    unfold step at hOk
    by_cases h : isValid s e = true
    · exact h
    · have hF : isValid s e = false := by
        cases hb : isValid s e with
        | true => simp [hb] at h
        | false => rfl
      simp [hF] at hOk
  have hV := myValidOfIsValid s e hIs
  obtain ⟨hNodup, _, hKnown, _, hSum, _⟩ := hV
  have hEq : step s e = (Outcome.ok,
      { accounts := s.accounts,
        balance := fun a => s.balance a + netOf e.lines a,
        posted := e.id :: s.posted }) := by
    unfold step
    simp [hIs]
  have hAcc : (step s e).2.accounts = s.accounts := by rw [hEq]
  have hBalEq : ∀ a, (step s e).2.balance a = s.balance a + netOf e.lines a := by
    intro a; rw [hEq]
  have hTot : total (step s e).2 = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    unfold total
    rw [hAcc]
    apply sumOver_congr
    intro a _
    exact hBalEq a
  rw [hTot, sumOver_add, trialSumZero2 s e hNodup hKnown hSum]
  unfold total
  omega

end Journal
