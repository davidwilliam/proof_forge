import Journal.Spec
import Journal.Lemmas
namespace Journal
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

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

theorem step_of_false (t : State) (e : Entry) (h : acceptable t e = false) : step t e = (.rejected, t) := by
  unfold step; simp [h]

theorem valid_imp_acceptable (s : State) (e : Entry) (h : ValidEntry s e) : acceptable s e = true := by
  unfold ValidEntry at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold acceptable
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩, h5⟩, ?_⟩
  · simp; intro heq; exact h2 heq
  · rw [List.all_eq_true]
    intro l hl
    have := h3 l hl
    simp [this]
  · rw [List.all_eq_true]
    intro l hl
    have := h4 l hl
    simp [this]
  · simp [h6]

theorem acceptable_imp_valid (s : State) (e : Entry) (h : acceptable s e = true) : ValidEntry s e := by
  unfold acceptable at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, ?_, ?_, ?_, h5, ?_⟩
  · intro heq; simp [heq] at h2
  · intro l hl
    have := List.all_eq_true.mp h3 l hl
    simp at this
    exact this
  · intro l hl
    have := List.all_eq_true.mp h4 l hl
    simp at this
    exact this
  · simp at h6
    exact h6

theorem netOf_cons' (hd : Line) (tl : List Line) (a : AccountId) :
    netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
  unfold netOf; simp only [sumOver_cons]

theorem lineSum_cons' (hd : Line) (tl : List Line) :
    lineSum (hd :: tl) = hd.2 + lineSum tl := by
  unfold lineSum; simp only [sumOver_cons]

theorem sumOver_zero_eq (l : List AccountId) : sumOver l (fun _ : AccountId => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem sumOver_netOf_eq_lineSum' (accs : List AccountId) (hNodup : accs.Nodup) (ls : List Line)
    (hMem : ∀ l ∈ ls, l.1 ∈ accs) : sumOver accs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    unfold netOf lineSum
    simp only [sumOver_nil]
    exact sumOver_zero_eq accs
  | cons hd tl ih =>
    have hMem_hd : hd.1 ∈ accs := hMem hd (by simp)
    have hMem_tl : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hMem l (by simp [hl])
    have ih' := ih hMem_tl
    have h1 : (fun a => netOf (hd :: tl) a) = (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by
      funext a; exact netOf_cons' hd tl a
    rw [h1]
    rw [sumOver_add]
    have h2 : sumOver accs (fun a => if hd.1 = a then hd.2 else 0) = hd.2 := by
      have hEq : (fun a => if hd.1 = a then hd.2 else (0 : Int)) = (fun a => if a = hd.1 then hd.2 else 0) := by
        funext a; by_cases h : hd.1 = a
        · subst h; simp
        · have h' : ¬ a = hd.1 := fun h' => h h'.symm
          simp [h, h']
      rw [hEq]
      have h3 := sumOver_ite_eq hNodup hd.1 hd.2
      simp [hMem_hd] at h3
      exact h3
    rw [h2, ih']
    rw [lineSum_cons']

theorem acceptable_of_success2 (s : State) (e : Entry) (hok : (step s e).1 = .ok) : acceptable s e = true := by
  by_cases ha : acceptable s e = true
  · exact ha
  · unfold step at hok; simp [ha] at hok

theorem step_posted_eq2 (s : State) (e : Entry) (ha : acceptable s e = true) :
  (step s e).2.posted = e.id :: s.posted := by unfold step; simp [ha]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hv
  have ha := valid_imp_acceptable s e hv
  unfold step; simp [ha]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hInv
  unfold step
  have hfalse : acceptable s e = false := by
    by_cases ha : acceptable s e = true
    · exfalso; exact hInv (acceptable_imp_valid s e ha)
    · simp at ha ⊢; exact ha
  simp [hfalse]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok
  unfold step at hok
  by_cases ha : acceptable s e = true
  · have hv := acceptable_imp_valid s e ha
    exact hv.2.2.1
  · simp [ha] at hok

theorem req_balanced : Balanced step := by
  intro s e hok
  unfold step at hok
  by_cases ha : acceptable s e = true
  · have hv := acceptable_imp_valid s e ha
    exact hv.2.2.2.2.1
  · simp [ha] at hok

theorem req_effects : Effects step := by
  intro s e hok
  unfold step at hok
  by_cases ha : acceptable s e = true
  · have hacc : (step s e).2.accounts = s.accounts := by unfold step; simp [ha]
    have hbal : ∀ a, (step s e).2.balance a = s.balance a + netOf e.lines a := by
      intro a
      unfold step; simp [ha]
      have key : ∀ (ls : List Line) (bal : AccountId → Int),
        (ls.foldl (fun b l => adjust b l.1 l.2) bal) a = bal a + netOf ls a := by
          intro ls
          induction ls with
          | nil =>
            intro bal
            simp only [List.foldl, netOf, sumOver_nil, Int.add_zero]
          | cons hd tl ih =>
            intro bal
            have ih2 := ih (adjust bal hd.1 hd.2)
            have eq1 : (List.foldl (fun b l => adjust b l.1 l.2) bal (hd :: tl)) a = (List.foldl (fun b l => adjust b l.1 l.2) (adjust bal hd.1 hd.2) tl) a := rfl
            rw [eq1, ih2]
            have hadj : (adjust bal hd.1 hd.2) a = bal a + if hd.1 = a then hd.2 else (0 : Int) := by
              unfold adjust
              by_cases h' : a = hd.1
              · have h1 : hd.1 = a := h'.symm; simp only [if_pos h', if_pos h1]
              · have h1 : ¬ hd.1 = a := fun h1 => h' h1.symm; simp only [if_neg h', if_neg h1, Int.add_zero]
            rw [hadj]
            have hnet : netOf (hd :: tl) a = (if hd.1 = a then hd.2 else (0 : Int)) + netOf tl a := by
              unfold netOf
              simp only [sumOver_cons]
            rw [hnet]; omega
      exact key e.lines s.balance
    exact ⟨hacc, hbal⟩
  · simp [ha] at hok

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have ha : acceptable s e = true := acceptable_of_success2 s e hok
  have hPost : (step s e).2.posted = e.id :: s.posted := step_posted_eq2 s e ha
  have h_snd_eq : (step s e).2 = { accounts := s.accounts, balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance, posted := e.id :: s.posted } := by
    unfold step; simp [ha]
  have h_iff : (∀ x, x ∈ (step s e).2.posted ↔ x = e.id ∨ x ∈ s.posted) := by
    intro x
    rw [hPost]
    simp
  refine ⟨h_iff, ?_⟩
  have hAccFalse : acceptable (step s e).2 e = false := by
    rw [h_snd_eq]
    unfold acceptable
    simp
  exact step_of_false _ _ hAccFalse

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hEff := req_effects s e hok
  obtain ⟨hAcc, hBal⟩ := hEff
  unfold total
  have hNodup : s.accounts.Nodup := by
    have ha : acceptable s e = true := by
      by_cases ha : acceptable s e = true
      · exact ha
      · unfold step at hok; simp [ha] at hok
    exact (acceptable_imp_valid s e ha).1
  have hMem : ∀ l ∈ e.lines, l.1 ∈ s.accounts := by
    have ha : acceptable s e = true := by
      by_cases ha : acceptable s e = true
      · exact ha
      · unfold step at hok; simp [ha] at hok
    exact (acceptable_imp_valid s e ha).2.2.1
  have hBalanced : lineSum e.lines = 0 := req_balanced s e hok
  have hEq : sumOver s.accounts (fun a => s.balance a + netOf e.lines a) = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) := by
    exact sumOver_add s.accounts (fun a => s.balance a) (fun a => netOf e.lines a)
  have hCong : sumOver (step s e).2.accounts (step s e).2.balance = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    rw [hAcc]
    apply sumOver_congr
    intro a ha_mem
    rw [hBal]
  rw [hCong, hEq]
  have hSumNet : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines := sumOver_netOf_eq_lineSum' s.accounts hNodup e.lines hMem
  rw [hSumNet, hBalanced, Int.add_zero]

end Journal
