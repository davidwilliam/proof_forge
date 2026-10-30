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
    let bal := e.lines.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) s.balance
    (.ok, { s with balance := bal, posted := e.id :: s.posted })
  else (.rejected, s)

theorem req_valid_succeeds_aux : ValidSucceeds step := by
  intro s e h
  unfold step
  simp [h]

theorem fold_balance_aux (bal : AccountId → Int) (ls : List Line) (a : AccountId) :
  (ls.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) bal) a = bal a + netOf ls a := by
  induction ls generalizing bal with
  | nil => simp [netOf, sumOver_nil]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have ih' := ih (fun x => if x = hd.1 then bal x + hd.2 else bal x)
    have h_at : (fun x => if x = hd.1 then bal x + hd.2 else bal x) a = bal a + (if hd.1 = a then hd.2 else 0) := by
      by_cases h : a = hd.1
      · subst h; simp
      · simp [h, show hd.1 ≠ a from fun h' => h h'.symm]
    have h_net : netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
      unfold netOf; simp [sumOver_cons]
    calc (List.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) (fun x => if x = hd.1 then bal x + hd.2 else bal x) tl) a
        = ((fun x => if x = hd.1 then bal x + hd.2 else bal x) a) + netOf tl a := ih'
      _ = (bal a + (if hd.1 = a then hd.2 else 0)) + netOf tl a := by rw [h_at]
      _ = bal a + ((if hd.1 = a then hd.2 else 0) + netOf tl a) := by omega
      _ = bal a + netOf (hd :: tl) a := by rw [h_net]

theorem sumOver_const_zero2 {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem sumOver_accounts_netOf_eq2 (accounts : List AccountId) (hNodup : accounts.Nodup) (ls : List Line) :
    sumOver accounts (fun a => netOf ls a) = sumOver ls (fun l : Line => if l.1 ∈ accounts then l.2 else (0 : Int)) := by
  unfold netOf
  have swap : ∀ ls' : List Line, sumOver accounts (fun a => sumOver ls' (fun l : Line => if l.1 = a then l.2 else 0)) = sumOver ls' (fun l : Line => sumOver accounts (fun a => if l.1 = a then l.2 else (0 : Int))) := by
    intro ls'
    induction ls' with
    | nil =>
      simp only [sumOver_nil]
      exact sumOver_const_zero2 accounts
    | cons hd tl ih =>
      simp only [sumOver_cons]
      have hAdd : sumOver accounts (fun a => (if hd.1 = a then hd.2 else (0 : Int)) + sumOver tl (fun l : Line => if l.1 = a then l.2 else (0 : Int))) = sumOver accounts (fun a => if hd.1 = a then hd.2 else (0 : Int)) + sumOver accounts (fun a => sumOver tl (fun l : Line => if l.1 = a then l.2 else (0 : Int))) := by
        exact sumOver_add accounts (fun a => if hd.1 = a then hd.2 else (0 : Int)) (fun a => sumOver tl (fun l : Line => if l.1 = a then l.2 else (0 : Int)))
      rw [hAdd, ih]
  rw [swap ls]
  apply sumOver_congr
  intro l hl
  have h1 : sumOver accounts (fun a => if l.1 = a then l.2 else (0 : Int)) = sumOver accounts (fun a => if a = l.1 then l.2 else (0 : Int)) := by
    apply sumOver_congr
    intro a ha
    by_cases h : a = l.1
    · subst h; simp
    · have h' : l.1 ≠ a := fun h' => h h'.symm
      simp [h, h']
  rw [h1]
  exact sumOver_ite_eq hNodup l.1 l.2

theorem sumOver_accounts_netOf_eq_lineSum2 (accounts : List AccountId) (hNodup : accounts.Nodup) (ls : List Line) (hAll : ∀ l ∈ ls, l.1 ∈ accounts) :
    sumOver accounts (fun a => netOf ls a) = lineSum ls := by
  rw [sumOver_accounts_netOf_eq2 accounts hNodup ls]
  unfold lineSum
  apply sumOver_congr
  intro l hl
  have hmem : l.1 ∈ accounts := hAll l hl
  simp [hmem]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h
  simp [step, h]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  unfold step at hok
  split at hok
  · rename_i hvalid
    exact hvalid.2.2.1 l hl
  · simp at hok

theorem req_balanced : Balanced step := by
  intro s e hok
  unfold step at hok
  split at hok
  · rename_i hvalid
    exact hvalid.2.2.2.2.1
  · simp at hok

theorem req_effects : Effects step := by
  intro s e hok
  have hvalid : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · exfalso
      have hstep : (step s e).1 = .rejected := by unfold step; simp [hv]
      rw [hstep] at hok; simp at hok
  constructor
  · unfold step; simp [hvalid]
  · intro a
    have hbal := fold_balance_aux s.balance e.lines a
    unfold step; simp [hvalid, hbal]

theorem req_idempotency    : Idempotent step := by
  intro s e hok
  have hvalid : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · exfalso
      have hstep : (step s e).1 = .rejected := by unfold step; simp [hv]
      rw [hstep] at hok; simp at hok
  have hstep_eq : step s e = (.ok, { s with balance := e.lines.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) s.balance, posted := e.id :: s.posted }) := by
    unfold step; simp [hvalid]
  have hs2 : (step s e).2 = { s with balance := e.lines.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) s.balance, posted := e.id :: s.posted } := by rw [hstep_eq]
  constructor
  · intro x
    rw [hs2]
    simp
  · let s' : State := { s with balance := e.lines.foldl (fun b l => fun x => if x = l.1 then b x + l.2 else b x) s.balance, posted := e.id :: s.posted }
    have hs' : (step s e).2 = s' := hs2
    have hnotValid_s' : ¬ ValidEntry s' e := by
      intro hV
      have h1 := hV.2.2.2.2.2
      simp [s'] at h1
    have heq : step s' e = (.rejected, s') := by
      unfold step; simp [hnotValid_s']
    rw [hs']
    exact heq

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hvalid : ValidEntry s e := by
    by_cases hv : ValidEntry s e
    · exact hv
    · exfalso
      have hstep : (step s e).1 = .rejected := by unfold step; simp [hv]
      rw [hstep] at hok; simp at hok
  have hNodup : s.accounts.Nodup := hvalid.1
  have hAll : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hvalid.2.2.1
  have hLineSum : lineSum e.lines = 0 := hvalid.2.2.2.2.1
  have hEffects := req_effects s e hok
  have hAcc : (step s e).2.accounts = s.accounts := hEffects.1
  have hBal : ∀ a, (step s e).2.balance a = s.balance a + netOf e.lines a := hEffects.2
  unfold total
  rw [hAcc]
  have hCong : sumOver s.accounts ((step s e).2.balance) = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    apply sumOver_congr
    intro a ha
    exact hBal a
  rw [hCong]
  rw [sumOver_add]
  have hNetZero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
    rw [sumOver_accounts_netOf_eq_lineSum2 s.accounts hNodup e.lines hAll, hLineSum]
  rw [hNetZero, Int.add_zero]

end Journal
