import Journal.Spec
import Journal.Lemmas

namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def step : Impl := fun s e =>
  if ValidEntry s e then
    let bal' := e.lines.foldl (fun b (l : Line) => fun x => if x = l.1 then b x + l.2 else b x) s.balance
    (.ok, { s with balance := bal', posted := e.id :: s.posted })
  else
    (.rejected, s)

private theorem foldl_apply_aux (ls : List Line) (bal : AccountId → Int) (a : AccountId) :
    (ls.foldl (fun b (l : Line) => fun x => if x = l.1 then b x + l.2 else b x) bal) a
      = bal a + netOf ls a := by
  induction ls generalizing bal with
  | nil =>
    show bal a = bal a + netOf [] a
    have h : netOf ([] : List Line) a = 0 := rfl
    rw [h, Int.add_zero]
  | cons hd tl ih =>
    show (List.foldl (fun b (l : Line) => fun x => if x = l.1 then b x + l.2 else b x) (fun x => if x = hd.1 then bal x + hd.2 else bal x) tl) a
        = bal a + netOf (hd :: tl) a
    rw [ih]
    have hnet : netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := rfl
    rw [hnet]
    by_cases heq : a = hd.1
    · have heq' : hd.1 = a := heq.symm
      rw [if_pos heq']
      rw [if_pos heq]
      rw [Int.add_assoc]
    · have heq' : ¬ hd.1 = a := fun h => heq h.symm
      rw [if_neg heq']
      rw [if_neg heq]
      rw [Int.zero_add]

private theorem foldl_balance_eq (s : State) (e : Entry) (a : AccountId) :
    (e.lines.foldl (fun b (l : Line) => fun x => if x = l.1 then b x + l.2 else b x) s.balance) a
      = s.balance a + netOf e.lines a :=
  foldl_apply_aux e.lines s.balance a

private theorem sumOver_zero {α : Type} (l : List α) :
    sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih =>
    show (0 : Int) + sumOver _ (fun _ => (0 : Int)) = 0
    rw [ih, Int.add_zero]

private theorem step_ok_of_valid (s : State) (e : Entry) (hv : ValidEntry s e) :
    (step s e).1 = .ok := by
  unfold step
  simp only [if_pos hv]

private theorem step_valid_iff_ok (s : State) (e : Entry) :
    (step s e).1 = .ok ↔ ValidEntry s e := by
  constructor
  · intro hok
    by_cases hv : ValidEntry s e
    · exact hv
    · have h1 : (step s e).1 = .rejected := by
        unfold step
        simp only [if_neg hv]
      rw [h1] at hok
      have : Outcome.rejected ≠ Outcome.ok := by decide
      exact absurd hok this
  · intro hv
    exact step_ok_of_valid s e hv

private theorem step_state_of_valid (s : State) (e : Entry) (hv : ValidEntry s e) :
    step s e = (.ok,
      { s with balance := e.lines.foldl (fun b (l : Line) => fun x => if x = l.1 then b x + l.2 else b x) s.balance,
               posted := e.id :: s.posted }) := by
  unfold step
  simp only [if_pos hv]

private theorem step_state_of_invalid (s : State) (e : Entry) (hv : ¬ ValidEntry s e) :
    step s e = (.rejected, s) := by
  unfold step
  simp only [if_neg hv]

private theorem sum_netOf_eq_lineSum (accounts : List AccountId) (ls : List Line)
    (hnodup : accounts.Nodup) (hcover : ∀ l ∈ ls, l.1 ∈ accounts) :
    sumOver accounts (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have h1 : (fun a => netOf ([] : List Line) a) = (fun _ : AccountId => (0 : Int)) := by
      funext a; rfl
    rw [h1, sumOver_zero]
    rfl
  | cons hd tl ih =>
    have hcover_tl : ∀ l ∈ tl, l.1 ∈ accounts := fun l hl => hcover l (List.mem_cons_of_mem hd hl)
    have ih' := ih hcover_tl
    have hadd : sumOver accounts (fun a => netOf (hd :: tl) a)
                = sumOver accounts (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by
      apply sumOver_congr
      intro a _
      rfl
    rw [hadd]
    have hswap : (fun a => (if hd.1 = a then hd.2 else (0 : Int)) + netOf tl a)
        = (fun a => (if a = hd.1 then hd.2 else (0 : Int)) + netOf tl a) := by
      funext a
      by_cases h : a = hd.1
      · have h' : hd.1 = a := h.symm
        rw [if_pos h, if_pos h']
      · have h' : ¬ hd.1 = a := fun he => h he.symm
        rw [if_neg h, if_neg h']
    rw [hswap]
    have hsplit := sumOver_add accounts (fun a => if a = hd.1 then hd.2 else (0 : Int)) (fun a => netOf tl a)
    rw [hsplit, ih']
    have hmem : hd.1 ∈ accounts := hcover hd (by simp)
    have hsum_ite : sumOver accounts (fun a => if a = hd.1 then hd.2 else 0) = hd.2 := by
      have h := sumOver_ite_eq hnodup hd.1 hd.2
      have hif : (if hd.1 ∈ accounts then hd.2 else (0 : Int)) = hd.2 := if_pos hmem
      rw [hif] at h
      exact h
    rw [hsum_ite]
    rfl

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hv; exact step_ok_of_valid s e hv

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hv; exact step_state_of_invalid s e hv

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  have hv : ValidEntry s e := (step_valid_iff_ok s e).mp hok
  exact hv.2.2.1 l hl

theorem req_balanced : Balanced step := by
  intro s e hok
  have hv : ValidEntry s e := (step_valid_iff_ok s e).mp hok
  exact hv.2.2.2.2.1

theorem req_effects : Effects step := by
  intro s e hok
  have hv : ValidEntry s e := (step_valid_iff_ok s e).mp hok
  have hst := step_state_of_valid s e hv
  constructor
  · have : (step s e).2.accounts = s.accounts := by rw [hst]
    exact this
  · intro a
    have hb : (step s e).2.balance a =
        (e.lines.foldl (fun b (l : Line) => fun x => if x = l.1 then b x + l.2 else b x) s.balance) a := by
      rw [hst]
    rw [hb]
    exact foldl_balance_eq s e a

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hv : ValidEntry s e := (step_valid_iff_ok s e).mp hok
  have hst := step_state_of_valid s e hv
  constructor
  · intro x
    have hposted : (step s e).2.posted = e.id :: s.posted := by rw [hst]
    rw [hposted]
    simp only [List.mem_cons]
  · let s' : State := (step s e).2
    have hs'eq : s' = { s with balance := e.lines.foldl (fun b (l : Line) => fun x => if x = l.1 then b x + l.2 else b x) s.balance, posted := e.id :: s.posted } := by
      have : (step s e).2 = { s with balance := e.lines.foldl (fun b (l : Line) => fun x => if x = l.1 then b x + l.2 else b x) s.balance, posted := e.id :: s.posted } := by
        rw [hst]
      exact this
    have hmem : e.id ∈ s'.posted := by rw [hs'eq]; simp
    have hnotValid' : ¬ ValidEntry s' e := by
      intro hvalid'
      have hnotmem : e.id ∉ s'.posted := hvalid'.2.2.2.2.2
      exact hnotmem hmem
    have hstep2 : step s' e = (.rejected, s') := step_state_of_invalid s' e hnotValid'
    exact hstep2

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hv : ValidEntry s e := (step_valid_iff_ok s e).mp hok
  have hst := step_state_of_valid s e hv
  have hacc : (step s e).2.accounts = s.accounts := by rw [hst]
  have hbal : ∀ a, (step s e).2.balance a = s.balance a + netOf e.lines a := by
    intro a
    have hb : (step s e).2.balance a =
        (e.lines.foldl (fun b (l : Line) => fun x => if x = l.1 then b x + l.2 else b x) s.balance) a := by
      rw [hst]
    rw [hb]
    exact foldl_balance_eq s e a
  show total (step s e).2 = total s
  unfold total
  rw [hacc]
  have hcongr : sumOver s.accounts (step s e).2.balance = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    apply sumOver_congr; intro a _; exact hbal a
  rw [hcongr]
  have hsplit : sumOver s.accounts (fun a => s.balance a + netOf e.lines a) = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) := by
    rw [← sumOver_add]
  rw [hsplit]
  have hcover : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hv.2.2.1
  have hnodup : s.accounts.Nodup := hv.1
  have hsum : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines := sum_netOf_eq_lineSum s.accounts e.lines hnodup hcover
  have hzero : lineSum e.lines = 0 := hv.2.2.2.2.1
  rw [hsum, hzero, Int.add_zero]

end Journal
