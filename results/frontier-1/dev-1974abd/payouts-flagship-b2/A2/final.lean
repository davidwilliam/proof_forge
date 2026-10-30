import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    let n := r.recipients.length
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (match indexOf? r.recipients a with
                             | some i => ((fairShare r.amount n i : Nat) : Int)
                             | none => 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)
def extraCount (rem o m : Nat) : Nat :=
  match m with
  | 0 => 0
  | Nat.succ m => (if o < rem then 1 else 0) + extraCount rem (o + 1) m
def fairSum (amount n o m : Nat) : Nat :=
  match m with
  | 0 => 0
  | Nat.succ m => fairShare amount n o + fairSum amount n (o + 1) m
theorem fairSum_eq (amount n o m : Nat) :
    fairSum amount n o m = m * (amount / n) + extraCount (amount % n) o m := by
  induction m generalizing o with
  | zero => simp [fairSum, extraCount]
  | succ m ih =>
    simp only [fairSum, extraCount]
    rw [ih (o + 1)]
    unfold fairShare
    by_cases h : o < amount % n
    · simp only [h, if_true]
      rw [Nat.succ_mul]
      ac_rfl
    · simp only [h, if_false]
      rw [Nat.succ_mul]
      ac_rfl
theorem extraCount_eq_min_sub (rem o m : Nat) :
    extraCount rem o m = min (o + m) rem - o := by
  induction m generalizing o with
  | zero =>
    simp only [extraCount, Nat.add_zero]
    omega
  | succ m ih =>
    simp only [extraCount]
    rw [ih (o + 1)]
    have heq : o + (m + 1) = (o + 1) + m := by omega
    rw [heq]
    by_cases h : o < rem
    · simp only [h, if_true]
      omega
    · simp only [h, if_false]
      omega
theorem sumOver_const_zero (L : List Nat) : sumOver L (fun _ => (0 : Int)) = 0 := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp [sumOver_cons, ih]
theorem sumOver_swap (A R : List Nat) (g : Nat → Nat → Int) :
    sumOver A (fun a => sumOver R (fun y => g a y))
      = sumOver R (fun y => sumOver A (fun a => g a y)) := by
  induction A with
  | nil =>
    simp only [sumOver_nil]
    rw [sumOver_const_zero]
  | cons x xs ih =>
    simp only [sumOver_cons]
    rw [ih, ← sumOver_add]
theorem sumOver_subset (A R : List Nat) (f : Nat → Int) (hA : A.Nodup) (hR : R.Nodup)
    (hz : ∀ a, a ∉ R → f a = 0) (hsub : ∀ x ∈ R, x ∈ A) :
    sumOver A f = sumOver R f := by
  have hexp : ∀ a, f a = sumOver R (fun y => if y = a then f y else 0) := by
    intro a
    have heq : (fun y => if y = a then f y else (0 : Int))
        = (fun y => if y = a then f a else (0 : Int)) := by
      funext y
      by_cases h : y = a
      · subst h; rfl
      · simp [h]
    rw [heq]
    have h := sumOver_ite_eq hR a (f a)
    rw [h]
    by_cases ha : a ∈ R
    · simp [ha]
    · simp [ha, hz a ha]
  have h1 : sumOver A f
      = sumOver A (fun a => sumOver R (fun y => if y = a then f y else (0 : Int))) := by
    apply sumOver_congr
    intro a _
    exact hexp a
  rw [h1, sumOver_swap]
  have hinner : ∀ y ∈ R, sumOver A (fun a => if y = a then f y else (0 : Int)) = f y := by
    intro y hy
    have h := sumOver_ite_eq hA y (f y)
    have heq2 : (fun a => if y = a then f y else (0 : Int))
        = (fun a => if a = y then f y else (0 : Int)) := by
      funext a
      by_cases h2 : y = a
      · subst h2; simp
      · have h3 : a ≠ y := fun heq => h2 heq.symm
        simp [h2, h3]
    rw [heq2, h]
    simp [hsub y hy]
  apply sumOver_congr
  intro y hy
  exact hinner y hy
theorem sumOver_list_eq_fairSum (amount n : Nat) (L : List Nat) (o : Nat) (hl : L.Nodup) :
    sumOver L (fun a => match indexOf? L a with
      | some i => ((fairShare amount n (o + i) : Nat) : Int)
      | none => 0)
    = ((fairSum amount n o L.length : Nat) : Int) := by
  induction L generalizing o with
  | nil => simp [sumOver, fairSum]
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hxmem, hxs⟩ := hl
    have hx0 : indexOf? (x :: xs) x = some 0 := by simp [indexOf?]
    have hsum_cons : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with
          | some i => ((fairShare amount n (o + i) : Nat) : Int)
          | none => 0)
        = ((fairShare amount n o : Nat) : Int)
          + sumOver xs (fun a => match indexOf? (x :: xs) a with
            | some i => ((fairShare amount n (o + i) : Nat) : Int)
            | none => 0) := by
      simp only [sumOver_cons, hx0]
      have hz : o + 0 = o := Nat.add_zero o
      rw [hz]
    rw [hsum_cons]
    have hcongr : sumOver xs (fun a => match indexOf? (x :: xs) a with
          | some i => ((fairShare amount n (o + i) : Nat) : Int)
          | none => 0)
        = sumOver xs (fun a => match indexOf? xs a with
          | some i => ((fairShare amount n ((o + 1) + i) : Nat) : Int)
          | none => 0) := by
      apply sumOver_congr
      intro a ha
      have hne : x ≠ a := fun heq => hxmem (heq ▸ ha)
      have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
        simp [indexOf?, hne]
      rw [hidx]
      cases hix : indexOf? xs a with
      | none => rfl
      | some i =>
        simp only [Option.map_some]
        have heq : o + (i + 1) = (o + 1) + i := by omega
        rw [heq]
    rw [hcongr, ih _ hxs]
    have hlen2 : (x :: xs).length = xs.length + 1 := rfl
    rw [hlen2]
    have hfair_unfold : fairSum amount n o (xs.length + 1)
        = fairShare amount n o + fairSum amount n (o + 1) xs.length := by
      simp [fairSum]
    rw [hfair_unfold]
    have hcast : ((fairShare amount n o + fairSum amount n (o + 1) xs.length : Nat) : Int)
        = ((fairShare amount n o : Nat) : Int) + ((fairSum amount n (o + 1) xs.length : Nat) : Int) := by
      omega
    rw [hcast]
theorem arch0_sum_debit_eq (s : State) (r : Request) (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by
  unfold ValidPayout at hv
  obtain ⟨hNodup, _, _, _, _, hSrcMem, _, _, _, _⟩ := hv
  have h := sumOver_ite_eq hNodup r.source (r.amount : Int)
  simp [hSrcMem] at h
  exact h
theorem arch0_sum_credit_eq (s : State) (r : Request) (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int))
      = (r.amount : Int) := by
  obtain ⟨hNodup, hpos, hne, hnd, hsrc_not, hsrc_mem, hsub, hauth, hle, hfresh⟩ := hv
  have hz : ∀ a, a ∉ r.recipients → ((shareOf r a : Nat) : Int) = 0 := by
    intro a ha
    unfold shareOf
    rw [indexOf?_eq_none ha]
    rfl
  have hsub_eq : sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int))
      = sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int)) :=
    sumOver_subset s.accounts r.recipients _ hNodup hnd hz hsub
  rw [hsub_eq]
  have hdecomp : ∃ x xs, r.recipients = x :: xs := by
    cases hr : r.recipients with
    | nil => exact absurd hr hne
    | cons x xs => exact ⟨x, xs, rfl⟩
  obtain ⟨x, xs, hr⟩ := hdecomp
  have hlen_pos : 0 < r.recipients.length := by rw [hr]; simp
  have hmod : r.amount % r.recipients.length < r.recipients.length :=
    Nat.mod_lt _ hlen_pos
  have hextra : extraCount (r.amount % r.recipients.length) 0 r.recipients.length
      = r.amount % r.recipients.length := by
    have h := extraCount_eq_min_sub (r.amount % r.recipients.length) 0 r.recipients.length
    have hzadd : (0 : Nat) + r.recipients.length = r.recipients.length := Nat.zero_add _
    rw [hzadd] at h
    rw [h]
    have hmin : min r.recipients.length (r.amount % r.recipients.length)
        = r.amount % r.recipients.length := by omega
    rw [hmin, Nat.sub_zero]
  have hfairNat : fairSum r.amount r.recipients.length 0 r.recipients.length = r.amount := by
    rw [fairSum_eq, hextra]
    exact Nat.div_add_mod r.amount r.recipients.length
  have h1 : sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int))
      = sumOver r.recipients (fun a => match indexOf? r.recipients a with
        | some i => ((fairShare r.amount r.recipients.length (0 + i) : Nat) : Int)
        | none => 0) := by
    apply sumOver_congr
    intro a _
    unfold shareOf
    cases hIx : indexOf? r.recipients a with
    | none => rfl
    | some i => simp [Nat.zero_add]
  rw [h1, sumOver_list_eq_fairSum _ _ _ _ hnd, hfairNat]
theorem arch0_expected_nonneg (s : State) (r : Request) (hv : ValidPayout s r)
    (hnon : ∀ a ∈ s.accounts, 0 ≤ s.balance a) :
    ∀ a ∈ s.accounts, 0 ≤ expectedBalance s r a := by
  obtain ⟨hNodup, hpos, hne, hnd, hsrc_not, hsrc_mem, hsub, hauth, hle, hfresh⟩ := hv
  intro a ha
  unfold expectedBalance
  by_cases heq : a = r.source
  · subst heq
    have hidx : indexOf? r.recipients r.source = none := indexOf?_eq_none hsrc_not
    have hshare : shareOf r r.source = 0 := by unfold shareOf; rw [hidx]
    rw [hshare]
    simp
    omega
  · have hif : (if a = r.source then (r.amount : Int) else 0) = 0 := by simp [heq]
    rw [hif]
    have hbal := hnon a ha
    omega
theorem arch0_valid_of_ok (s : State) (r : Request) :
    (step s r).1 = .ok → ValidPayout s r := by
  intro h
  by_cases hV : ValidPayout s r
  · exact hV
  · exfalso
    have hrej : (step s r).1 = .rejected := by
      unfold step
      simp [hV]
    rw [hrej] at h
    simp at h
theorem arch0_sum_expected_eq (s : State) (r : Request) (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance := by
  have hdebit := arch0_sum_debit_eq s r hv
  have hcredit := arch0_sum_credit_eq s r hv
  have h1 : (fun a => expectedBalance s r a)
      = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + ((shareOf r a : Nat) : Int)) := by
    funext a
    rfl
  rw [h1]
  have h2 : sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + ((shareOf r a : Nat) : Int))
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) + sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by
    exact sumOver_add _ _ _
  rw [h2, hcredit]
  have h3 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) := by
    exact sumOver_sub _ _ _
  rw [h3, hdebit]
  omega
theorem arch1_balance_eq_of_ok (s : State) (r : Request)
    (hok : (step s r).1 = .ok) :
    ∀ a, (step s r).2.balance a = expectedBalance s r a := by
  have hv : ValidPayout s r := arch0_valid_of_ok s r hok
  have hstep : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (match indexOf? r.recipients a with
                             | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int)
                             | none => 0),
      applied := r.txId :: s.applied }) := by
    unfold step
    simp [hv]
  have h2 : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (match indexOf? r.recipients a with
                             | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int)
                             | none => 0),
      applied := r.txId :: s.applied } : State) := by rw [hstep]
  intro a
  rw [h2]
  show s.balance a - (if a = r.source then (r.amount : Int) else 0) +
      (match indexOf? r.recipients a with | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int) | none => 0)
    = expectedBalance s r a
  unfold expectedBalance shareOf
  cases hIx : indexOf? r.recipients a <;> rfl
theorem arch1_accounts_eq_of_ok (s : State) (r : Request)
    (hok : (step s r).1 = .ok) :
    (step s r).2.accounts = s.accounts := by
  have hv : ValidPayout s r := arch0_valid_of_ok s r hok
  unfold step
  simp [hv]
theorem arch1_sum_expected_eq (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = total s :=
  arch0_sum_expected_eq s r hv
theorem arch2_total_step_eq_sum_expected (s : State) (r : Request)
    (hok : (step s r).1 = .ok) :
    total (step s r).2 = sumOver s.accounts (fun a => expectedBalance s r a) := by
  have hacc := arch1_accounts_eq_of_ok s r hok
  have hbal := arch1_balance_eq_of_ok s r hok
  unfold total
  rw [hacc]
  exact sumOver_congr s.accounts _ _ (fun a _ => hbal a)
theorem arch2_sum_expected_eq_total (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = total s :=
  arch1_sum_expected_eq s r hv

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  show step s r = _
  unfold step
  simp [h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hA : s.auth r.requester r.source = true
  · exact hA
  · exfalso
    have hNV : ¬ ValidPayout s r := by
      intro hV
      exact hA hV.2.2.2.2.2.2.2.1
    have hstep : (step s r).1 = .rejected := by
      unfold step
      simp [hNV]
    rw [hstep] at h
    simp at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hV : ValidPayout s r
  · have hstep : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (match indexOf? r.recipients a with
                             | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int)
                             | none => 0),
      applied := r.txId :: s.applied }) := by
      unfold step
      simp [hV]
    have h2 : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (match indexOf? r.recipients a with
                             | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int)
                             | none => 0),
      applied := r.txId :: s.applied } : State) := by rw [hstep]
    rw [h2]
    refine ⟨rfl, rfl, ?_⟩
    intro a
    show s.balance a - (if a = r.source then (r.amount : Int) else 0) +
        (match indexOf? r.recipients a with | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int) | none => 0)
      = expectedBalance s r a
    unfold expectedBalance shareOf
    cases hIx : indexOf? r.recipients a <;> rfl
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hV]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [h1] at h
    simp at h

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hV : ValidPayout s r
  · have hEq : step s r = (.ok, ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (match indexOf? r.recipients a with
                               | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int)
                               | none => 0),
        applied := r.txId :: s.applied } : State)) := by
      unfold step
      simp [hV]
    have h2Eq : (step s r).2 = (({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (match indexOf? r.recipients a with
                               | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int)
                               | none => 0),
        applied := r.txId :: s.applied } : State)) := by
      rw [hEq]
    refine ⟨?_, ?_⟩
    · intro x
      rw [h2Eq]
      simp
    · have hNotValid : ¬ ValidPayout (step s r).2 r := by
        rw [h2Eq]
        intro hV2
        obtain ⟨_, _, _, _, _, _, _, _, _, hNotIn⟩ := hV2
        apply hNotIn
        simp
      have hInv := req_invalid_noop _ _ hNotValid
      exact hInv
  · have hrej : (step s r).1 = .rejected := by
      unfold step
      simp [hV]
    rw [hrej] at hok
    simp at hok

theorem req_nonnegative : NonNegative step := by
  intro s r hnon a ha
  by_cases hv : ValidPayout s r
  · have hok : (step s r).1 = .ok := req_valid_succeeds s r hv
    have heff := req_effects s r hok
    have ha' : a ∈ s.accounts := by
      rw [← heff.1]
      exact ha
    have hb : (step s r).2.balance a = expectedBalance s r a := heff.2.2 a
    rw [hb]
    exact arch0_expected_nonneg s r hv hnon a ha'
  · have hstep := req_invalid_noop s r hv
    rw [hstep] at ha
    rw [hstep]
    exact hnon a ha

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  by_cases hV : ValidPayout s r
  · have hEq : step s r = (.ok, ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (match indexOf? r.recipients a with
                               | some j => ((fairShare r.amount r.recipients.length j : Nat) : Int)
                               | none => 0),
        applied := r.txId :: s.applied } : State)) := by
      unfold step
      simp [hV]
    have h2Eq : (step s r).2 = (({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (match indexOf? r.recipients a with
                               | some j => ((fairShare r.amount r.recipients.length j : Nat) : Int)
                               | none => 0),
        applied := r.txId :: s.applied } : State)) := by
      rw [hEq]
    obtain ⟨hNodup, _, hNeNil, hRnodup, hSrcNot, _, _, _, _, _⟩ := hV
    have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hne : r.recipients[i] ≠ r.source := fun heq => hSrcNot (heq ▸ hmem)
    have hIdx : indexOf? r.recipients r.recipients[i] = some i :=
      indexOf?_getElem hRnodup i hi
    rw [h2Eq]
    show (s.balance r.recipients[i] - (if r.recipients[i] = r.source then (r.amount : Int) else 0)
        + (match indexOf? r.recipients r.recipients[i] with | some j => ((fairShare r.amount r.recipients.length j : Nat) : Int) | none => 0))
        - s.balance r.recipients[i] = _
    simp only [hne, hIdx]
    simp
    omega
  · have hrej : (step s r).1 = .rejected := by
      unfold step
      simp [hV]
    rw [hrej] at hok
    simp at hok

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv : ValidPayout s r := arch0_valid_of_ok s r hok
  rw [arch2_total_step_eq_sum_expected s r hok, arch2_sum_expected_eq_total s r hv]

end Payout
