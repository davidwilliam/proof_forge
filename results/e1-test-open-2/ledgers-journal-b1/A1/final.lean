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

theorem sumOver_adjust_aux (l : List AccountId) (hl : l.Nodup) (bal : AccountId → Int) (a : AccountId) (amt : Int) :
    sumOver l (adjust bal a amt) = sumOver l bal + if a ∈ l then amt else 0 := by
  have h_eq : ∀ b ∈ l, adjust bal a amt b = bal b + if b = a then amt else 0 := by
    intro b _
    unfold adjust
    by_cases hb : b = a
    · simp [hb]
    · simp [hb]
  have h1 : sumOver l (adjust bal a amt) = sumOver l (fun b => bal b + if b = a then amt else 0) :=
    sumOver_congr l _ _ h_eq
  have h2 : sumOver l (fun b => bal b + if b = a then amt else 0) = sumOver l bal + sumOver l (fun b => if b = a then amt else 0) :=
    sumOver_add l _ _
  rw [h1, h2]
  have h3 : sumOver l (fun b => if b = a then amt else 0) = if a ∈ l then amt else 0 :=
    sumOver_ite_eq hl a amt
  rw [h3]

theorem sumOver_post_aux2 (l : List AccountId) (hl : l.Nodup) (bal : AccountId → Int) (ls : List Line) (hk : ∀ p ∈ ls, p.1 ∈ l) :
    sumOver l (ls.foldl (fun b p => adjust b p.1 p.2) bal) = sumOver l bal + lineSum ls := by
  induction ls generalizing bal with
  | nil => simp [lineSum]
  | cons hd tl ih =>
    have hk_hd : hd.1 ∈ l := hk hd (by simp)
    have hk_tl : ∀ p ∈ tl, p.1 ∈ l := fun p hp => hk p (by simp [hp])
    have h_step : sumOver l (adjust bal hd.1 hd.2) = sumOver l bal + hd.2 := by
      have h := sumOver_adjust_aux l hl bal hd.1 hd.2
      simp [hk_hd] at h
      exact h
    have h_fold : (hd :: tl).foldl (fun b p => adjust b p.1 p.2) bal = tl.foldl (fun b p => adjust b p.1 p.2) (adjust bal hd.1 hd.2) := by simp
    calc sumOver l ((hd :: tl).foldl (fun b p => adjust b p.1 p.2) bal)
        = sumOver l (tl.foldl (fun b p => adjust b p.1 p.2) (adjust bal hd.1 hd.2)) := by rw [h_fold]
      _ = sumOver l (adjust bal hd.1 hd.2) + lineSum tl := ih (adjust bal hd.1 hd.2) hk_tl
      _ = (sumOver l bal + hd.2) + lineSum tl := by rw [h_step]
      _ = sumOver l bal + (hd.2 + lineSum tl) := by omega
      _ = sumOver l bal + lineSum (hd :: tl) := by simp [lineSum, sumOver_cons]

theorem foldl_adjust_eq_aux (bal : AccountId → Int) (ls : List Line) (a : AccountId) :
    (ls.foldl (fun b l => adjust b l.1 l.2) bal) a = bal a + netOf ls a := by
  induction ls generalizing bal with
  | nil => simp [netOf]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h_adj : (adjust bal hd.1 hd.2) a = bal a + if hd.1 = a then hd.2 else 0 := by
      unfold adjust
      by_cases h : hd.1 = a
      · simp [h]
      · have ha : ¬ a = hd.1 := fun hh => h hh.symm
        simp [ha, h]
    have h_net : netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
      simp [netOf]
    calc (tl.foldl (fun b l => adjust b l.1 l.2) (adjust bal hd.1 hd.2)) a
        = (adjust bal hd.1 hd.2) a + netOf tl a := ih (adjust bal hd.1 hd.2)
      _ = (bal a + if hd.1 = a then hd.2 else 0) + netOf tl a := by rw [h_adj]
      _ = bal a + ((if hd.1 = a then hd.2 else 0) + netOf tl a) := by omega
      _ = bal a + netOf (hd :: tl) a := by rw [h_net]

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
  · have hv := h
    unfold ValidEntry at hv
    obtain ⟨_, _, hmem, _, _, _⟩ := hv
    exact hmem l hl
  · simp [h] at hok

theorem req_balanced : Balanced step := by
  intro s e hok
  unfold step at hok
  by_cases h : ValidEntry s e
  · unfold ValidEntry at h
    obtain ⟨_, _, _, _, hsum, _⟩ := h
    exact hsum
  · simp [h] at hok

theorem req_effects : Effects step := by
  intro s e hok
  unfold step at hok
  by_cases h : ValidEntry s e
  · have hstep_eq : (step s e).2 = { s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } := by
      unfold step; simp [h]
    constructor
    · simp [hstep_eq]
    · intro a
      rw [hstep_eq]
      simp
      exact foldl_adjust_eq_aux s.balance e.lines a
  · simp [h] at hok

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hValid : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · exfalso
      unfold step at hok
      simp [hv] at hok
  have hSnd : (step s e).2 = { s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } := by
    unfold step; simp [hValid]
  have hSnd2 : step s e = (.ok, { s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted }) := by
    unfold step; simp [hValid]
  constructor
  · intro x; rw [hSnd]; simp
  · have hNotValid : ¬ ValidEntry (step s e).2 e := by
      rw [hSnd]; unfold ValidEntry; simp
    -- Need to rewrite goal to use hNotValid
    have hEq : (step s e).2 = { s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } := hSnd
    rw [hEq]
    unfold step
    simp [show ¬ ValidEntry { s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } e from by unfold ValidEntry; simp]

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  unfold step at hok
  by_cases h : ValidEntry s e
  · have hk : ∀ p ∈ e.lines, p.1 ∈ s.accounts := by
      unfold ValidEntry at h; obtain ⟨_, _, hmem, _, _, _⟩ := h; exact hmem
    have hb : lineSum e.lines = 0 := by
      unfold ValidEntry at h; obtain ⟨_, _, _, _, hsum, _⟩ := h; exact hsum
    have hl : s.accounts.Nodup := by
      unfold ValidEntry at h; obtain ⟨hnd, _, _, _, _, _⟩ := h; exact hnd
    have hbal : sumOver s.accounts (e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance) = sumOver s.accounts s.balance := by
      have hpost := sumOver_post_aux2 s.accounts hl s.balance e.lines hk
      rw [hb] at hpost; simp at hpost; exact hpost
    have hstep_eq : (step s e).2 = { s with balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } := by
      unfold step; simp [h]
    have htotal : total (step s e).2 = sumOver s.accounts (e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance) := by
      rw [hstep_eq]; simp [total]
    rw [htotal, hbal]; simp [total]
  · simp [h] at hok

end Journal
