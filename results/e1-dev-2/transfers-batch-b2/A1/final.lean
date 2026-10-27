import Batch.Spec
import Batch.Lemmas
namespace Batch
/-- Admission check of one leg against the running balances. -/
def legAllowed (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && decide (l.source ≠ l.target) &&
  s.accounts.contains l.source &&
  s.accounts.contains l.target &&
  decide (-(s.limit l.source : Int) ≤ bal l.source - l.amount)

/-- Sequential check of all legs, threading running balances. -/
def checkLegs (s : State) : (AccountId → Int) → List Leg → Bool
  | _, [] => true
  | bal, l :: ls => legAllowed s bal l && checkLegs s (shift bal l) ls

def step : Impl := fun s r =>
  if decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else (.rejected, s)

theorem foo_test2 : True := trivial

theorem check_contains_thm : ∀ (l : List Nat) (x : Nat), l.contains x = decide (x ∈ l) := by intro l x; rfl

theorem legAllowed_of_LegOk_aux2 : ∀ (s : State) (bal : AccountId → Int) (l : Leg), LegOk s bal l → legAllowed s bal l = true := by intro s bal l h; unfold LegOk at h; unfold legAllowed; obtain ⟨hpos, hne, hsrc, htgt, hlim⟩ := h; simp_all

theorem checkLegs_of_LegsOk_aux : ∀ (s : State) (bal : AccountId → Int) (legs : List Leg), LegsOk s bal legs → checkLegs s bal legs = true := by intro s bal legs h; induction legs generalizing bal with | nil => rfl | cons l ls ih => unfold LegsOk at h; obtain ⟨hok, hrest⟩ := h; unfold checkLegs; have h1 : legAllowed s bal l = true := legAllowed_of_LegOk_aux2 s bal l hok; have h2 : checkLegs s (shift bal l) ls = true := ih _ hrest; simp [h1, h2]

theorem tmp_and_test : ∀ (a b : Bool), a && b = true → a = true ∧ b = true := by
  intro a b h
  cases ha : a with
  | true =>
    cases hb : b with
    | true => exact ⟨rfl, rfl⟩
    | false => simp [ha, hb] at h
  | false => simp [ha] at h
#check @of_decide_eq_true
#check @if_neg

theorem legAllowed_true_imp_auxB : ∀ (s : State) (bal : AccountId → Int) (l : Leg), legAllowed s bal l = true → LegOk s bal l := by
  intro s bal l h
  unfold legAllowed at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hpos', hne'⟩, hsrc'⟩, htgt'⟩, hlim'⟩ := h
  have hpos : 0 < l.amount := of_decide_eq_true hpos'
  have hne : l.source ≠ l.target := of_decide_eq_true hne'
  have hlim : -(s.limit l.source : Int) ≤ bal l.source - l.amount := of_decide_eq_true hlim'
  have hsrc_contains : s.accounts.contains l.source = decide (l.source ∈ s.accounts) := check_contains_thm s.accounts l.source
  have htgt_contains : s.accounts.contains l.target = decide (l.target ∈ s.accounts) := check_contains_thm s.accounts l.target
  have hsrc : l.source ∈ s.accounts := by
    have hdec : decide (l.source ∈ s.accounts) = true := by rw [← hsrc_contains]; exact hsrc'
    exact of_decide_eq_true hdec
  have htgt : l.target ∈ s.accounts := by
    have hdec : decide (l.target ∈ s.accounts) = true := by rw [← htgt_contains]; exact htgt'
    exact of_decide_eq_true hdec
  exact ⟨hpos, hne, hsrc, htgt, hlim⟩

theorem probe_rw_test : ∀ (s : State) (r : Request),
    (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = false →
    step s r = (.rejected, s) := by
  intro s r h
  have h1 : step s r = (if (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) then (Outcome.ok, ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State)) else ((Outcome.rejected, s) : Outcome × State)) := rfl
  rw [h1, h]
  simp

theorem cond_ok_of_success : ∀ (s : State) (r : Request),
    (step s r).1 = .ok →
    (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = true := by
  intro s r hok
  cases hc : (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) with
  | true => rfl
  | false =>
    have hrs := probe_rw_test s r hc
    rw [hrs] at hok
    simp at hok

theorem bal_ok_of_success : ∀ (s : State) (r : Request),
    (step s r).1 = .ok →
    (step s r).2.balance = applyLegs s.balance r.legs := by
  intro s r hok
  have hc := cond_ok_of_success s r hok
  have h1 : step s r = (if (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) then (Outcome.ok, ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State)) else ((Outcome.rejected, s) : Outcome × State)) := rfl
  rw [h1, hc] at *
  simp

theorem acc_ok_of_success : ∀ (s : State) (r : Request),
    (step s r).1 = .ok →
    (step s r).2.accounts = s.accounts := by
  intro s r hok
  have hc := cond_ok_of_success s r hok
  have h1 : step s r = (if (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) then (Outcome.ok, ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State)) else ((Outcome.rejected, s) : Outcome × State)) := rfl
  rw [h1, hc] at *
  simp

theorem lim_ok_of_success : ∀ (s : State) (r : Request),
    (step s r).1 = .ok →
    (step s r).2.limit = s.limit := by
  intro s r hok
  have hc := cond_ok_of_success s r hok
  have h1 : step s r = (if (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) then (Outcome.ok, ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State)) else ((Outcome.rejected, s) : Outcome × State)) := rfl
  rw [h1, hc] at *
  simp

theorem applied_ok_of_success_aux : ∀ (s : State) (r : Request),
    (step s r).1 = .ok →
    (step s r).2.applied = r.batchId :: s.applied := by
  intro s r hok
  have hc := cond_ok_of_success s r hok
  have h1 : step s r = (if (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) then (Outcome.ok, ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State)) else ((Outcome.rejected, s) : Outcome × State)) := rfl
  rw [h1, hc] at *
  simp

theorem idem_mem_aux : ∀ (s : State) (r : Request),
    (step s r).1 = .ok →
    ∀ x, x ∈ (step s r).2.applied ↔ x = r.batchId ∨ x ∈ s.applied := by
  intro s r hok x
  have happ := applied_ok_of_success_aux s r hok
  rw [happ]
  simp

theorem idem_reapply_aux : ∀ (s : State) (r : Request),
    (step s r).1 = .ok →
    step (step s r).2 r = (.rejected, (step s r).2) := by
  intro s r hok
  have happ := applied_ok_of_success_aux s r hok
  have hmem : r.batchId ∈ (step s r).2.applied := by rw [happ]; simp
  have hdec_false : decide ((step s r).2.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ (step s r).2.applied) = false := by
    rw [decide_eq_false]
    intro hcon
    obtain ⟨_, _, hnotin⟩ := hcon
    exact hnotin hmem
  have hcond_false : (decide ((step s r).2.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ (step s r).2.applied) && checkLegs (step s r).2 ((step s r).2.balance) r.legs) = false := by
    rw [hdec_false]
    simp
  exact probe_rw_test (step s r).2 r hcond_false

theorem shift_sum_auxC : ∀ (acc : List Nat) (bal : AccountId → Int) (l : Leg),
    acc.Nodup → l.source ∈ acc → l.target ∈ acc →
    sumOver acc (shift bal l) = sumOver acc bal := by
  intro acc bal l hnod hsrc htgt
  have hdef : (shift bal l) = (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0)) := rfl
  rw [hdef]
  have h1 : sumOver acc (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0))
    = sumOver acc (fun a => bal a - (if a = l.source then (l.amount : Int) else 0)) + sumOver acc (fun a => (if a = l.target then (l.amount : Int) else 0)) := sumOver_add _ _ _
  rw [h1]
  have h2 : sumOver acc (fun a => bal a - (if a = l.source then (l.amount : Int) else 0)) = sumOver acc bal - sumOver acc (fun a => (if a = l.source then (l.amount : Int) else 0)) := sumOver_sub _ _ _
  rw [h2]
  have hs : sumOver acc (fun a => (if a = l.source then (l.amount : Int) else 0)) = (l.amount : Int) := by
    have h := sumOver_ite_eq hnod l.source (l.amount : Int)
    simpa [hsrc] using h
  have ht : sumOver acc (fun a => (if a = l.target then (l.amount : Int) else 0)) = (l.amount : Int) := by
    have h := sumOver_ite_eq hnod l.target (l.amount : Int)
    simpa [htgt] using h
  rw [hs, ht]
  omega

theorem legAllowed_mem_auxC : ∀ (s : State) (bal : AccountId → Int) (l : Leg),
    legAllowed s bal l = true → l.source ∈ s.accounts ∧ l.target ∈ s.accounts := by
  intro s bal l h
  unfold legAllowed at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, _⟩, hsrc'⟩, htgt'⟩, _⟩ := h
  have hsrc_contains : s.accounts.contains l.source = decide (l.source ∈ s.accounts) := check_contains_thm s.accounts l.source
  have htgt_contains : s.accounts.contains l.target = decide (l.target ∈ s.accounts) := check_contains_thm s.accounts l.target
  have hsrc : l.source ∈ s.accounts := by
    have hdec : decide (l.source ∈ s.accounts) = true := by rw [← hsrc_contains]; exact hsrc'
    exact of_decide_eq_true hdec
  have htgt : l.target ∈ s.accounts := by
    have hdec : decide (l.target ∈ s.accounts) = true := by rw [← htgt_contains]; exact htgt'
    exact of_decide_eq_true hdec
  exact ⟨hsrc, htgt⟩

theorem checkLegs_sum_auxC : ∀ (s : State) (bal : AccountId → Int) (legs : List Leg),
    s.accounts.Nodup → checkLegs s bal legs = true →
    sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  intro s bal legs hnod hchk
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    unfold checkLegs at hchk
    simp only [Bool.and_eq_true] at hchk
    obtain ⟨hallow, hrest⟩ := hchk
    have hmem := legAllowed_mem_auxC s bal l hallow
    obtain ⟨hsrc, htgt⟩ := hmem
    have hshift : sumOver s.accounts (shift bal l) = sumOver s.accounts bal :=
      shift_sum_auxC s.accounts bal l hnod hsrc htgt
    have hstep : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    rw [hstep]
    rw [ih (shift bal l) hrest, hshift]

theorem shift_preserves_limits_auxA : ∀ (s : State) (bal : AccountId → Int) (l : Leg),
    (∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) → legAllowed s bal l = true →
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ (shift bal l) a := by
  intro s bal l hwithin hallow a hamem
  have hok := legAllowed_true_imp_auxB s bal l hallow
  obtain ⟨hpos, hne, hsrc, htgt, hlim⟩ := hok
  have hshift_eq : (shift bal l) a = bal a - (if a = l.source then (l.amount : Int) else 0)
    + (if a = l.target then (l.amount : Int) else 0) := rfl
  rw [hshift_eq]
  by_cases hs : a = l.source
  · subst hs
    rw [if_pos rfl]
    have ht2 : ¬ (l.source = l.target) := hne
    rw [if_neg ht2]
    have := hlim
    omega
  · rw [if_neg hs]
    by_cases ht : a = l.target
    · rw [if_pos ht]
      have hle := hwithin a hamem
      omega
    · rw [if_neg ht]
      have hle := hwithin a hamem
      omega

theorem take_within_auxB : ∀ (s : State) (bal : AccountId → Int) (legs : List Leg),
    (∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) → checkLegs s bal legs = true →
    ∀ (k : Nat) (a : AccountId), a ∈ s.accounts → -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  intro s bal legs hwithin hchk k
  induction legs generalizing bal k with
  | nil =>
    intro a hamem
    simp only [List.take_nil, applyLegs]
    exact hwithin a hamem
  | cons l ls ih =>
    intro a hamem
    have hallow : legAllowed s bal l = true := by
      unfold checkLegs at hchk
      simp only [Bool.and_eq_true] at hchk
      exact hchk.1
    have hrest : checkLegs s (shift bal l) ls = true := by
      unfold checkLegs at hchk
      simp only [Bool.and_eq_true] at hchk
      exact hchk.2
    have hwithin' : ∀ b ∈ s.accounts, -(s.limit b : Int) ≤ (shift bal l) b :=
      shift_preserves_limits_auxA s bal l hwithin hallow
    cases k with
    | zero =>
      simp only [List.take_zero, applyLegs]
      exact hwithin a hamem
    | succ n =>
      have htake_eq : ((l :: ls).take (n + 1)) = l :: (ls.take n) := by simp
      rw [htake_eq]
      have happ_eq : applyLegs bal (l :: ls.take n) = applyLegs (shift bal l) (ls.take n) := rfl
      rw [happ_eq]
      exact ih (shift bal l) hwithin' hrest n a hamem

theorem cond_true_gives_ok_auxD : ∀ (s : State) (r : Request),
    (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = true →
    (step s r).1 = .ok := by
  intro s r hcond
  have h1 : step s r = (if (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) then (Outcome.ok, ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State)) else ((Outcome.rejected, s) : Outcome × State)) := rfl
  rw [h1, hcond]
  rfl

theorem checkLegs_true_imp_auxD2 : ∀ (s : State) (bal : AccountId → Int) (legs : List Leg),
    checkLegs s bal legs = true → LegsOk s bal legs := by
  intro s bal legs
  induction legs generalizing bal with
  | nil => intro _; trivial
  | cons l ls ih =>
    intro hchk
    unfold checkLegs at hchk
    simp only [Bool.and_eq_true] at hchk
    obtain ⟨hallow, hrest⟩ := hchk
    have hok : LegOk s bal l := legAllowed_true_imp_auxB s bal l hallow
    have htail : LegsOk s (shift bal l) ls := ih (shift bal l) hrest
    show LegOk s bal l ∧ LegsOk s (shift bal l) ls
    exact ⟨hok, htail⟩

theorem req_atomicity_tryB : Atomicity step := by
  intro s r hneg
  have himp : (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = true →
      ValidBatch s r := by
    intro ht
    have hboth := tmp_and_test _ _ ht
    obtain ⟨hdecT, hchkT⟩ := hboth
    have hP : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied :=
      of_decide_eq_true hdecT
    obtain ⟨hnod, hne, hnotmem⟩ := hP
    have hlegsok : LegsOk s s.balance r.legs := checkLegs_true_imp_auxD2 s s.balance r.legs hchkT
    exact ⟨hnod, hne, hnotmem, hlegsok⟩
  have hcond_false : (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = false := by
    cases hc : (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) with
    | true =>
      have hval : ValidBatch s r := himp hc
      have hcontra : False := hneg hval
      cases hcontra
    | false => rfl
  exact probe_rw_test s r hcond_false

theorem req_valid_succeeds   : ValidSucceeds step := by
  intro s r hval
  obtain ⟨hnod, hne, hnotmem, hlegsok⟩ := hval
  have hchk : checkLegs s s.balance r.legs = true :=
    checkLegs_of_LegsOk_aux s s.balance r.legs hlegsok
  have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = true := by
    rw [decide_eq_true_eq]
    exact ⟨hnod, hne, hnotmem⟩
  have hcond : (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = true := by
    simp [hdec, hchk]
  exact cond_true_gives_ok_auxD s r hcond

theorem req_atomicity : Atomicity step := by
  intro s r hneg
  have himp : (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = true →
      ValidBatch s r := by
    intro ht
    have hboth := tmp_and_test _ _ ht
    obtain ⟨hdecT, hchkT⟩ := hboth
    have hP : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied :=
      of_decide_eq_true hdecT
    obtain ⟨hnod, hne, hnotmem⟩ := hP
    have hlegsok : LegsOk s s.balance r.legs := checkLegs_true_imp_auxD2 s s.balance r.legs hchkT
    exact ⟨hnod, hne, hnotmem, hlegsok⟩
  have hcond_false : (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = false := by
    cases hc : (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) with
    | true =>
      have hval : ValidBatch s r := himp hc
      have hcontra : False := hneg hval
      cases hcontra
    | false => rfl
  exact probe_rw_test s r hcond_false

theorem req_single_leg : SingleLeg step := by
  intro s r l hlegs hok
  have hbal := bal_ok_of_success s r hok
  have hc := cond_ok_of_success s r hok
  have hboth := tmp_and_test _ _ hc
  obtain ⟨hdecT, hchkT⟩ := hboth
  have hlegsok : LegsOk s s.balance r.legs := checkLegs_true_imp_auxD2 s s.balance r.legs hchkT
  rw [hlegs] at hlegsok
  unfold LegsOk at hlegsok
  obtain ⟨hok_leg, _⟩ := hlegsok
  obtain ⟨hpos, hne, hsrc, htgt, hlim⟩ := hok_leg
  have hbal_eq : (step s r).2.balance = applyLegs s.balance r.legs := hbal
  rw [hlegs] at hbal_eq
  have happ_single : ∀ (bal : AccountId → Int) (m : Leg), applyLegs bal [m] = shift bal m := by
    intro bal m; rfl
  rw [happ_single] at hbal_eq
  constructor
  · have h1 : (step s r).2.balance l.source = (shift s.balance l) l.source := by rw [hbal_eq]
    unfold shift at h1
    rw [if_pos rfl] at h1
    have hif_neg : (if l.source = l.target then (l.amount : Int) else 0) = 0 := if_neg hne
    rw [hif_neg] at h1
    -- h1 : ... = bal source - amount + 0
    omega
  · have h1 : (step s r).2.balance l.target = (shift s.balance l) l.target := by rw [hbal_eq]
    unfold shift at h1
    have hif_s : (if l.target = l.source then (l.amount : Int) else 0) = 0 := by
      apply if_neg
      exact fun h => hne h.symm
    rw [hif_s] at h1
    rw [if_pos rfl] at h1
    omega

theorem req_effects : Effects step := by
  intro s r hok
  refine ⟨acc_ok_of_success s r hok, lim_ok_of_success s r hok, ?_⟩
  have hb := bal_ok_of_success s r hok
  intro a
  rw [hb]

theorem req_idempotency : Idempotent step := by
  intro s r hok
  exact ⟨idem_mem_aux s r hok, idem_reapply_aux s r hok⟩

theorem req_conservation : Conserves step := by
  intro s r hok
  have hc := cond_ok_of_success s r hok
  have hboth := tmp_and_test _ _ hc
  obtain ⟨hdecT, hchkT⟩ := hboth
  have hP : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied :=
    of_decide_eq_true hdecT
  obtain ⟨hnod, _, _⟩ := hP
  have hacc := acc_ok_of_success s r hok
  have hbal := bal_ok_of_success s r hok
  show total (step s r).2 = total s
  unfold total
  rw [hacc, hbal]
  exact checkLegs_sum_auxC s s.balance r.legs hnod hchkT

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hwithin
  constructor
  · cases hc : (decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) with
    | false =>
      have hstep : step s r = (.rejected, s) := probe_rw_test s r hc
      rw [hstep]
      exact hwithin
    | true =>
      have hboth := tmp_and_test _ _ hc
      obtain ⟨hdecT, hchkT⟩ := hboth
      have hok : (step s r).1 = .ok := cond_true_gives_ok_auxD s r hc
      have hacc := acc_ok_of_success s r hok
      have hlim := lim_ok_of_success s r hok
      have hbal := bal_ok_of_success s r hok
      unfold WithinLimits at hwithin ⊢
      intro a hamem
      have hmem_old : a ∈ s.accounts := by rw [← hacc]; exact hamem
      have hgen := take_within_auxB s s.balance r.legs hwithin hchkT r.legs.length a hmem_old
      have htake : r.legs.take r.legs.length = r.legs := by simp
      rw [htake] at hgen
      have hbal_a : (step s r).2.balance a = applyLegs s.balance r.legs a := by rw [hbal]
      have hlim_a : (step s r).2.limit a = s.limit a := by rw [hlim]
      rw [hlim_a, hbal_a]
      exact hgen
  · intro hok k a hamem
    have hc := cond_ok_of_success s r hok
    have hboth := tmp_and_test _ _ hc
    obtain ⟨hdecT, hchkT⟩ := hboth
    exact take_within_auxB s s.balance r.legs hwithin hchkT k a hamem

end Batch
