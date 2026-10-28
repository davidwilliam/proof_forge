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

theorem req_known_accounts_aux : KnownAccounts step := by
  intro s e hok l hl
  by_cases hV : ValidEntry s e
  · exact hV.2.2.1 l hl
  · unfold step at hok
    simp [hV] at hok

theorem adjust_apply (base : AccountId → Int) (x : AccountId) (amt : Int) (a : AccountId) :
    (adjust base x amt) a = base a + (if x = a then amt else 0) := by
  unfold adjust
  by_cases h : a = x
  · subst h; simp
  · simp [h, Ne.symm h]

theorem foldl_adjust_correct2 (ls : List Line) (base : AccountId → Int) (a : AccountId) :
    (ls.foldl (fun b l => adjust b l.1 l.2) base) a = base a + netOf ls a := by
  induction ls generalizing base with
  | nil =>
    simp [netOf]
  | cons hd tl ih =>
    have hstep : ((hd :: tl).foldl (fun b l => adjust b l.1 l.2) base) a
      = (tl.foldl (fun b l => adjust b l.1 l.2) (adjust base hd.1 hd.2)) a := rfl
    rw [hstep, ih]
    have hnet : netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := rfl
    rw [hnet]
    have hadj := adjust_apply base hd.1 hd.2 a
    rw [hadj]
    omega

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
  by_cases hV : ValidEntry s e
  · exact hV.2.2.1 l hl
  · unfold step at hok
    simp [hV] at hok

theorem req_balanced : Balanced step := by
  intro s e hok
  by_cases hV : ValidEntry s e
  · exact hV.2.2.2.2.1
  · unfold step at hok
    simp [hV] at hok

theorem req_effects : Effects step := by
  intro s e hok
  by_cases hV : ValidEntry s e
  · unfold step
    simp only [hV, ↓reduceIte]
    refine ⟨trivial, ?_⟩
    intro a
    exact foldl_adjust_correct2 e.lines s.balance a
  · unfold step at hok
    simp [hV] at hok

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hV : ValidEntry s e := by
    by_cases h : ValidEntry s e
    · exact h
    · unfold step at hok
      simp [h] at hok
  have hstep : step s e = (.ok, ({ s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State)) := by
    unfold step
    simp [hV]
  have h2 : (step s e).2 = ({ s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State) := by
    rw [hstep]
  refine ⟨?_, ?_⟩
  · intro x
    rw [h2]
    simp
  · have hNotValid : ¬ ValidEntry (step s e).2 e := by
      rw [h2]
      intro hC
      have hmem : e.id ∉ (({ s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } : State).posted) := hC.2.2.2.2.2
      simp at hmem
    exact req_invalid_noop _ _ hNotValid

theorem req_trial_balance : TrialBalance step := by
  have hzero : ∀ (xs : List AccountId), sumOver xs (fun _ : AccountId => (0 : Int)) = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons hd2 tl2 ih2 => simp [ih2]
  have aux : ∀ (accs : List AccountId) (ls : List Line),
      accs.Nodup → (∀ l ∈ ls, l.1 ∈ accs) →
      sumOver accs (fun a => netOf ls a) = lineSum ls := by
    intro accs ls
    induction ls generalizing accs with
    | nil =>
      intro hnodup hknown
      have hnet0 : (fun a : AccountId => netOf [] a) = (fun _ : AccountId => (0 : Int)) := by
        funext a
        rfl
      rw [hnet0, hzero]
      rfl
    | cons hd tl ih =>
      intro hnodup hknown
      have hhd : hd.1 ∈ accs := hknown hd (by simp)
      have htl : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hknown l (by simp [hl])
      have hswap : ∀ a : AccountId, (if hd.1 = a then hd.2 else (0 : Int)) = (if a = hd.1 then hd.2 else 0) := by
        intro a
        by_cases h : a = hd.1
        · subst h
          rfl
        · have h' : ¬ (hd.1 = a) := fun hh => h hh.symm
          simp only [h, h', ↓reduceIte]
      have hcongr : sumOver accs (fun a => netOf (hd :: tl) a)
          = sumOver accs (fun a => (if a = hd.1 then hd.2 else 0) + netOf tl a) := by
        apply sumOver_congr
        intro a _
        show (if hd.1 = a then hd.2 else 0) + netOf tl a = _
        rw [hswap]
      have hline : lineSum (hd :: tl) = hd.2 + lineSum tl := rfl
      rw [hcongr, sumOver_add, sumOver_ite_eq hnodup hd.1 hd.2, if_pos hhd, ih _ hnodup htl, hline]
  intro s e hok
  have hV : ValidEntry s e := by
    by_cases h : ValidEntry s e
    · exact h
    · have hstep := req_invalid_noop s e h
      rw [hstep] at hok
      simp at hok
  have hEff := req_effects s e hok
  obtain ⟨hAccEq, hBalEq⟩ := hEff
  unfold total
  rw [hAccEq]
  have h1 : sumOver s.accounts (step s e).2.balance
      = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    apply sumOver_congr
    intro a _
    exact hBalEq a
  rw [h1, sumOver_add]
  have h2 : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines :=
    aux s.accounts e.lines hV.1 hV.2.2.1
  rw [h2, hV.2.2.2.2.1]
  omega

end Journal
