import Journal.Spec
import Journal.Lemmas
namespace Journal
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance
def step : Impl := fun s e =>
  if ValidEntry s e then
    (.ok, { accounts := s.accounts,
            balance := fun a => s.balance a + netOf e.lines a,
            posted := e.id :: s.posted })
  else (.rejected, s)

theorem req_known_accounts_aux_test : True := by trivial

theorem req_idempotency_aux : Idempotent step := by
  intro s e hok
  by_cases hv : ValidEntry s e
  · have hstep : step s e = (Outcome.ok, ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State)) := by
      unfold step; simp [hv]
    have hnot : ¬ ValidEntry ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State) e := by
      intro hcon
      unfold ValidEntry at hcon
      obtain ⟨_, _, _, _, _, hmem⟩ := hcon
      simp at hmem
    rw [hstep]
    constructor
    · intro x
      simp
    · have hstep2 : step ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State) e = (Outcome.rejected, ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State)) := by
        unfold step; simp [hnot]
      exact hstep2
  · have hstep2 : step s e = (Outcome.rejected, s) := by unfold step; simp [hv]
    rw [hstep2] at hok
    simp at hok

theorem req_idempotency_foo : True := trivial

theorem mytest_thm : True := trivial

theorem tb_zero_test2 : (1 : Int) = 1 := by rfl

theorem tb_zero_aux : ∀ {α : Type} (l : List α), sumOver l (fun _ : α => (0 : Int)) = 0 := by
  intro α l
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem tb_swap_aux2 (acc : List AccountId) (ls : List Line) (hnd : acc.Nodup) :
    sumOver acc (fun a => netOf ls a) = sumOver ls (fun l => if l.1 ∈ acc then l.2 else 0) := by
  induction ls with
  | nil =>
    have h1 : (fun a : AccountId => netOf [] a) = (fun _ : AccountId => (0 : Int)) := by
      funext a; rfl
    rw [h1]
    rw [tb_zero_aux]
    rfl
  | cons hd tl ih =>
    have hfun : (fun a : AccountId => netOf (hd :: tl) a) = (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by
      funext a; rfl
    rw [hfun]
    rw [sumOver_add]
    rw [ih]
    have hswap : (fun a : AccountId => (if hd.1 = a then hd.2 else (0 : Int))) = (fun a => if a = hd.1 then hd.2 else 0) := by
      funext a
      by_cases h : hd.1 = a
      · subst h; simp
      · have h2 : ¬ (a = hd.1) := fun he => h he.symm
        simp [h, h2]
    rw [hswap]
    rw [sumOver_ite_eq hnd hd.1 hd.2]
    rw [sumOver_cons]

theorem tb_if_eq_aux (acc : List AccountId) (ls : List Line) (hall : ∀ l ∈ ls, l.1 ∈ acc) :
    sumOver ls (fun l => if l.1 ∈ acc then l.2 else (0 : Int)) = lineSum ls := by
  unfold lineSum
  apply sumOver_congr
  intro a ha
  have hm : a.1 ∈ acc := hall a ha
  simp [hm]

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
  by_cases hv : ValidEntry s e
  · exact hv.2.2.1 l hl
  · have hstep : step s e = (.rejected, s) := by unfold step; simp [hv]
    rw [hstep] at hok
    simp at hok

theorem req_balanced : Balanced step := by
  intro s e hok
  by_cases hv : ValidEntry s e
  · exact hv.2.2.2.2.1
  · have hstep : step s e = (.rejected, s) := by unfold step; simp [hv]
    rw [hstep] at hok
    simp at hok

theorem req_effects : Effects step := by
  intro s e hok
  by_cases hv : ValidEntry s e
  · have hstep : step s e = (Outcome.ok, ⟨s.accounts, fun a => s.balance a + netOf e.lines a, e.id :: s.posted⟩) := by
      unfold step
      simp [hv]
    rw [hstep]
    constructor
    · rfl
    · intro a
      rfl
  · have hstep2 : step s e = (Outcome.rejected, s) := by
      unfold step
      simp [hv]
    rw [hstep2] at hok
    simp at hok

theorem req_idempotency : Idempotent step := by
  intro s e hok
  by_cases hv : ValidEntry s e
  · have hstep : step s e = (Outcome.ok, ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State)) := by
      unfold step; simp [hv]
    have hnot : ¬ ValidEntry ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State) e := by
      intro hcon
      unfold ValidEntry at hcon
      obtain ⟨_, _, _, _, _, hmem⟩ := hcon
      simp at hmem
    rw [hstep]
    constructor
    · intro x
      simp
    · have hstep2 : step ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State) e = (Outcome.rejected, ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State)) := by
        unfold step; simp [hnot]
      exact hstep2
  · have hstep2 : step s e = (Outcome.rejected, s) := by unfold step; simp [hv]
    rw [hstep2] at hok
    simp at hok

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  by_cases hv : ValidEntry s e
  · have hnd : s.accounts.Nodup := hv.1
    have hmem : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hv.2.2.1
    have hbal : lineSum e.lines = 0 := hv.2.2.2.2.1
    have hstep : step s e = (Outcome.ok, ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State)) := by
      unfold step
      simp [hv]
    rw [hstep]
    unfold total
    simp only
    have hadd := sumOver_add s.accounts s.balance (fun a => netOf e.lines a)
    have hex : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
      rw [tb_swap_aux2 s.accounts e.lines hnd]
      rw [tb_if_eq_aux s.accounts e.lines hmem]
      exact hbal
    omega
  · have hstep2 : step s e = (Outcome.rejected, s) := by
      unfold step
      simp [hv]
    rw [hstep2] at hok
    simp at hok

end Journal
