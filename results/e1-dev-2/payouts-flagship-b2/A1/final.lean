import Payout.Spec
import Payout.Lemmas
namespace Payout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance

def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem sumOver_append_aux {α : Type} (l1 l2 : List α) (f : α → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a t ih => simp only [List.cons_append, sumOver_cons, ih]; omega

theorem sumOver_const_range (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, sumOver_append_aux, ih]
    simp only [sumOver_cons, sumOver_nil, Int.add_zero]
    have hcast : ((((Nat.succ n : Nat))) : Int) = ((n : Int) + 1) := by simp
    rw [hcast, Int.add_mul, Int.one_mul]

theorem sumOver_range_head (m k : Nat) (g : Nat → Int) :
    sumOver (List.range (Nat.succ m)) (fun i => g (k + i)) =
    g k + sumOver (List.range m) (fun i => g (k + 1 + i)) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    have eL : sumOver (List.range (Nat.succ (Nat.succ m))) (fun i => g (k + i)) =
        sumOver (List.range (Nat.succ m)) (fun i => g (k + i)) + g (k + Nat.succ m) := by
      rw [List.range_succ, sumOver_append_aux]
      simp only [sumOver_cons, sumOver_nil, Int.add_zero]
    have eR : sumOver (List.range (Nat.succ m)) (fun i => g (k + 1 + i)) =
        sumOver (List.range m) (fun i => g (k + 1 + i)) + g (k + 1 + m) := by
      rw [List.range_succ, sumOver_append_aux]
      simp only [sumOver_cons, sumOver_nil, Int.add_zero]
    rw [eL, eR, ih k]
    have hkm : k + Nat.succ m = k + 1 + m := by omega
    rw [hkm]
    omega

theorem indexOf?_mem_ne_none {l : List Nat} {a : Nat} (h : a ∈ l) :
    indexOf? l a ≠ none := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [indexOf?]
    by_cases heq : x = a
    · simp [heq]
    · simp [heq]
      have hOr := List.mem_cons.mp h
      cases hOr with
      | inl heq' => exact absurd heq'.symm heq
      | inr hm =>
        have hne := ih hm
        cases hmo : indexOf? xs a with
        | none => exact absurd hmo hne
        | some v => simp [hmo]

theorem indexOf?_cons_map {x : Nat} {xs : List Nat} {a : Nat} (hne : x ≠ a) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  simp [indexOf?, hne]

theorem sum_recips_offset (l : List Nat) (hl : l.Nodup) (k amount n0 : Nat) :
    sumOver l (fun a => ((fairShare amount n0 (k + (indexOf? l a).getD 0) : Nat) : Int)) =
    sumOver (List.range l.length) (fun i => ((fairShare amount n0 (k + i) : Nat) : Int)) := by
  induction l generalizing k with
  | nil => simp
  | cons x xs ih =>
    have hmem := List.nodup_cons.mp hl
    obtain ⟨hxnotin, hxs⟩ := hmem
    have hx : ∀ a' ∈ xs, x ≠ a' := by
      intro a' ha' heq
      subst heq
      exact hxnotin ha'
    simp only [sumOver_cons]
    have hhead : (indexOf? (x :: xs) x).getD 0 = 0 := by
      simp [indexOf?]
    have hheadFair : ((fairShare amount n0 (k + (indexOf? (x :: xs) x).getD 0) : Nat) : Int) =
        ((fairShare amount n0 (k + 0) : Nat) : Int) := by rw [hhead]
    have htailEq : sumOver xs (fun a => ((fairShare amount n0 (k + (indexOf? (x :: xs) a).getD 0) : Nat) : Int)) =
        sumOver xs (fun a => ((fairShare amount n0 ((k + 1) + (indexOf? xs a).getD 0) : Nat) : Int)) := by
      apply sumOver_congr
      intro a ha
      have hne : x ≠ a := hx a ha
      have h1 : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) :=
        indexOf?_cons_map hne
      have hneNone := indexOf?_mem_ne_none ha
      cases hmv : indexOf? xs a with
      | none => exact absurd hmv hneNone
      | some v =>
        have h2 : indexOf? (x :: xs) a = some (v + 1) := by simp [h1, hmv]
        rw [h2]
        simp only [Option.getD_some]
        have hkk : k + (v + 1) = (k + 1) + v := by omega
        rw [hkk]
    rw [htailEq, ih hxs (k + 1)]
    simp only [List.length_cons]
    have hrw := sumOver_range_head xs.length k (fun j => ((fairShare amount n0 j : Nat) : Int))
    have hhead0 : k + 0 = k := by omega
    rw [hheadFair, hhead0, hrw]

theorem sum_ite_range_min (n r : Nat) :
    sumOver (List.range n) (fun i => if i < r then (1 : Int) else 0) =
    ((Nat.min n r : Nat) : Int) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, sumOver_append_aux, ih]
    simp only [sumOver_cons, sumOver_nil, Int.add_zero]
    by_cases h : n < r
    · have hle : n ≤ r := Nat.le_of_lt h
      have hle2 : n + 1 ≤ r := Nat.succ_le_of_lt h
      have h1 : Nat.min n r = n := Nat.min_eq_left hle
      have h2 : Nat.min (Nat.succ n) r = n + 1 := Nat.min_eq_left hle2
      rw [h1, h2, if_pos h]
      simp
    · have hle : r ≤ n := Nat.le_of_not_gt h
      have hle2 : r ≤ Nat.succ n := Nat.le_trans hle (Nat.le_succ n)
      have h1 : Nat.min n r = r := Nat.min_eq_right hle
      have h2 : Nat.min (Nat.succ n) r = r := Nat.min_eq_right hle2
      rw [h1, h2, if_neg h]
      simp

theorem fairShare_cast (amount n i : Nat) :
    ((fairShare amount n i : Nat) : Int) =
    ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) := by
  unfold fairShare
  by_cases h : i < amount % n
  · simp [h]
  · simp [h]

theorem sum_fairShare_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int)) =
    (amount : Int) := by
  have hsum : sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int)) =
      sumOver (List.range n) (fun _ => ((amount / n : Nat) : Int)) +
      sumOver (List.range n) (fun i => if i < amount % n then (1 : Int) else 0) := by
    rw [← sumOver_add]
    apply sumOver_congr
    intro i hi
    rw [fairShare_cast]
  rw [hsum, sumOver_const_range, sum_ite_range_min]
  have hmod : amount % n < n := Nat.mod_lt _ hn
  have hle : amount % n ≤ n := Nat.le_of_lt hmod
  have hmin : Nat.min n (amount % n) = amount % n := Nat.min_eq_right hle
  rw [hmin]
  have hdiv := Nat.div_add_mod amount n
  have h2 := congrArg (fun x : Nat => ((x : Int))) hdiv
  simp at h2
  omega

theorem filter_not_mem_eq_self (l : List Nat) (a : Nat) (h : a ∉ l) :
    l.filter (fun b => decide (b ≠ a)) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ a := by
      intro heq
      apply h
      rw [heq]
      exact List.mem_cons.mpr (Or.inl rfl)
    have hxs : a ∉ xs := by
      intro hm
      apply h
      exact List.mem_cons.mpr (Or.inr hm)
    have hflt : (x :: xs).filter (fun b => decide (b ≠ a)) =
        x :: xs.filter (fun b => decide (b ≠ a)) := by
      simp [hx]
    rw [hflt, ih hxs]

theorem filter_mem_to_mem (R : List Nat) (p : Nat → Bool) (x : Nat)
    (h : x ∈ R.filter p) : x ∈ R :=
  (List.mem_filter.mp h).1

theorem nodup_filter_aux (R : List Nat) (p : Nat → Bool) (hR : R.Nodup) :
    (R.filter p).Nodup := by
  induction R with
  | nil => simp
  | cons y ys ih =>
    have hmem := List.nodup_cons.mp hR
    obtain ⟨hynotin, hys⟩ := hmem
    have hih := ih hys
    by_cases hpy : p y = true
    · have hflt : (y :: ys).filter p = y :: (ys.filter p) := by simp [hpy]
      rw [hflt]
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        have hmxs : y ∈ ys := filter_mem_to_mem ys p y hm
        exact hynotin hmxs
      · exact hih
    · have hfb : p y = false := by simp [hpy]
      have hflt : (y :: ys).filter p = ys.filter p := by simp [hfb]
      rw [hflt]
      exact hih

theorem filter_mem_of_mem_ne (R : List Nat) (a x : Nat)
    (hxR : x ∈ R) (hne : x ≠ a) : x ∈ R.filter (fun b => decide (b ≠ a)) := by
  apply List.mem_filter.mpr
  constructor
  · exact hxR
  · simp [hne]

theorem filter_mem_ne (R : List Nat) (a x : Nat)
    (hx : x ∈ R.filter (fun b => decide (b ≠ a))) : x ≠ a := by
  have h2 := (List.mem_filter.mp hx).2
  simp at h2
  exact h2

theorem sumOver_mem_split (R : List Nat) (f : Nat → Int) (a : Nat)
    (hR : R.Nodup) (hmem : a ∈ R) :
    sumOver R f = f a + sumOver (R.filter (fun b => decide (b ≠ a))) f := by
  induction R with
  | nil => simp at hmem
  | cons x xs ih =>
    have hmem2 := List.nodup_cons.mp hR
    obtain ⟨hxnotin, hxs⟩ := hmem2
    have hOr := List.mem_cons.mp hmem
    cases hOr with
    | inl he =>
      subst he
      have hnotin : a ∉ xs := by
        intro hm
        apply hxnotin
        simp [hm]
      have hflt2 : xs.filter (fun b => decide (b ≠ a)) = xs :=
        filter_not_mem_eq_self xs a hnotin
      have hflt : (a :: xs).filter (fun b => decide (b ≠ a)) = xs.filter (fun b => decide (b ≠ a)) := by
        simp
      rw [hflt, hflt2]
      simp only [sumOver_cons]
    | inr hm =>
      have hne : x ≠ a := by
        intro heq
        subst heq
        exact hxnotin hm
      have hflt : (x :: xs).filter (fun b => decide (b ≠ a)) =
          x :: xs.filter (fun b => decide (b ≠ a)) := by simp [hne]
      rw [hflt]
      have hih := ih hxs hm
      simp only [sumOver_cons] at hih ⊢
      omega

theorem sumOver_subset_eq_aux (f : Nat → Int) (S : List Nat) (hS : S.Nodup) (R : List Nat) :
    R.Nodup → (∀ x ∈ R, x ∈ S) → (∀ x ∈ S, x ∉ R → f x = 0) →
      sumOver S f = sumOver R f := by
  induction S generalizing R with
  | nil =>
    intro hR hsub hzero
    have hRnil : R = [] := by
      cases R with
      | nil => rfl
      | cons b bs =>
        have hc := hsub b (by simp)
        simp at hc
    subst hRnil
    simp
  | cons a s ih =>
    intro hR hsub hzero
    have hmem := List.nodup_cons.mp hS
    obtain ⟨ha_notin, hsNodup⟩ := hmem
    by_cases haR : a ∈ R
    · have hRfltNodup : (R.filter (fun b => decide (b ≠ a))).Nodup :=
        nodup_filter_aux R _ hR
      have hsub' : ∀ x ∈ R.filter (fun b => decide (b ≠ a)), x ∈ s := by
        intro x hx
        have hxR : x ∈ R := filter_mem_to_mem R _ x hx
        have hne : x ≠ a := filter_mem_ne R a x hx
        have hxS : x ∈ a :: s := hsub x hxR
        have hOr := List.mem_cons.mp hxS
        cases hOr with
        | inl he => exact absurd he hne
        | inr hms => exact hms
      have hzero' : ∀ x ∈ s, x ∉ R.filter (fun b => decide (b ≠ a)) → f x = 0 := by
        intro x hxs hxNot
        apply hzero x (by simp [hxs])
        intro hxR
        apply hxNot
        have hne : x ≠ a := by
          intro heq
          subst heq
          exact ha_notin hxs
        exact filter_mem_of_mem_ne R a x hxR hne
      have hih := ih hsNodup (R.filter (fun b => decide (b ≠ a))) hRfltNodup hsub' hzero'
      have hsplit := sumOver_mem_split R f a hR haR
      simp only [sumOver_cons] at hih ⊢
      omega
    · have hfa : f a = 0 := hzero a (by simp) haR
      have hsub' : ∀ x ∈ R, x ∈ s := by
        intro x hx
        have hxS : x ∈ a :: s := hsub x hx
        have hOr := List.mem_cons.mp hxS
        cases hOr with
        | inl he =>
          subst he
          exact absurd hx haR
        | inr hms => exact hms
      have hzero' : ∀ x ∈ s, x ∉ R → f x = 0 := by
        intro x hxs hxNot
        exact hzero x (by simp [hxs]) hxNot
      have hih := ih hsNodup R hR hsub' hzero'
      simp only [sumOver_cons, hfa] at hih ⊢
      omega

theorem sumOver_subset_eq (S R : List Nat) (f : Nat → Int)
    (hS : S.Nodup) (hR : R.Nodup) (hsub : ∀ x ∈ R, x ∈ S)
    (hzero : ∀ x ∈ S, x ∉ R → f x = 0) :
    sumOver S f = sumOver R f :=
  sumOver_subset_eq_aux f S hS R hR hsub hzero

theorem sumShare_eq (s : State) (r : Request) (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) = (r.amount : Int) := by
  obtain ⟨hNodup, hpos, hne, hRnodup, hsrcNot, hsrcMem, hsub, hauth, hle, hfresh⟩ := hv
  have npos : 0 < r.recipients.length := by
    cases hr : r.recipients with
    | nil =>
      simp [hr] at hne
    | cons _ _ => simp
  have hzero : ∀ x ∈ s.accounts, x ∉ r.recipients →
      ((shareOf r x : Nat) : Int) = 0 := by
    intro x hx hxNot
    unfold shareOf
    rw [indexOf?_eq_none hxNot]
    rfl
  have hsubSet : sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) =
      sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int)) :=
    sumOver_subset_eq s.accounts r.recipients _ hNodup hRnodup hsub hzero
  rw [hsubSet]
  have hcongr : sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int)) =
      sumOver r.recipients (fun a => ((fairShare r.amount r.recipients.length ((indexOf? r.recipients a).getD 0) : Nat) : Int)) := by
    apply sumOver_congr
    intro a ha
    unfold shareOf
    have hneNone := indexOf?_mem_ne_none ha
    cases hmo : indexOf? r.recipients a with
    | none => exact absurd hmo hneNone
    | some v => rfl
  rw [hcongr]
  have hoff := sum_recips_offset r.recipients hRnodup 0 r.amount r.recipients.length
  simp only [Nat.zero_add] at hoff
  rw [hoff]
  exact sum_fairShare_range r.amount r.recipients.length npos

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · have h2 : (step s r).1 = .rejected := by simp [step, hv]
    rw [h2] at h
    exact absurd h (by decide)

theorem req_effects : Effects step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      simp [step, hv]
    have h2 : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
      rw [hstep]
    rw [h2]
    refine ⟨rfl, rfl, fun a => rfl⟩
  · have hrej : (step s r).1 = .rejected := by simp [step, hv]
    rw [hrej] at h
    contradiction

theorem req_idempotency : Idempotent step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      simp [step, hv]
    have h2 : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
      rw [hstep]
    constructor
    · intro x
      rw [h2]
      simp
    · have hNotValid : ¬ ValidPayout (step s r).2 r := by
        rw [h2]
        intro hcon
        obtain ⟨_, _, _, _, _, _, _, _, _, hmem⟩ := hcon
        exact hmem (by simp)
      have hEq := req_invalid_noop (step s r).2 r hNotValid
      exact hEq
  · have hrej : (step s r).1 = .rejected := by simp [step, hv]
    rw [hrej] at h
    contradiction

theorem req_nonnegative : NonNegative step := by
  intro s r hnonneg a ha
  by_cases hv : ValidPayout s r
  · have hstep2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      simp [step, hv]
    rw [hstep2] at ha ⊢
    simp at ha ⊢
    have hbal : 0 ≤ s.balance a := hnonneg a ha
    unfold expectedBalance
    by_cases hsrc : a = r.source
    · subst hsrc
      have hle : (r.amount : Int) ≤ s.balance r.source := hv.2.2.2.2.2.2.2.2.1
      have hshare0 : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none (fun hm => hv.2.2.2.2.1 hm)]
      rw [hshare0]
      simp
      omega
    · simp [hsrc]
      have hshare_nonneg : (0 : Int) ≤ (((shareOf r a : Nat)) : Int) := by
        exact_mod_cast Nat.zero_le (shareOf r a)
      omega
  · have hstep2 : (step s r).2 = s := by simp [step, hv]
    rw [hstep2] at ha ⊢
    exact hnonneg a ha

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  by_cases hv : ValidPayout s r
  · have hstep2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      simp [step, hv]
    rw [hstep2]
    show expectedBalance s r r.recipients[i] - s.balance r.recipients[i] = _
    have hsrcNot : r.source ∉ r.recipients := hv.2.2.2.2.1
    have hrnodup : r.recipients.Nodup := hv.2.2.2.1
    have hane : r.recipients[i] ≠ r.source := fun heq => hsrcNot (heq ▸ List.getElem_mem hi)
    have hidx : indexOf? r.recipients r.recipients[i] = some i :=
      indexOf?_getElem hrnodup i hi
    unfold expectedBalance shareOf
    rw [hidx]
    simp [hane]
    omega
  · have hrej : (step s r).1 = .rejected := by simp [step, hv]
    rw [hrej] at hok
    cases hok

-- Conservation helpers

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hstep2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      simp [step, hv]
    have hNodup : s.accounts.Nodup := hv.1
    have hsrcMem : r.source ∈ s.accounts := hv.2.2.2.2.2.1
    have hshare := sumShare_eq s r hv
    have hrfl : (sumOver s.accounts fun a => s.balance a) = total s := rfl
    unfold total
    rw [hstep2]
    simp only
    have hexp : ∀ a, expectedBalance s r a =
        (s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int)) := by
      intro a
      rfl
    have hsumEq : sumOver s.accounts (fun a => expectedBalance s r a) =
        sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int)) := by
      apply sumOver_congr
      intro a ha
      rw [hexp]
    rw [hsumEq]
    have hsplit : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int)) =
        (sumOver s.accounts (fun a => s.balance a) - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) +
        sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int))) := by
      have h1 : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int)) =
          (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + ((shareOf r a : Nat) : Int)) := by
        funext a; omega
      rw [h1, sumOver_add]
      congr 1
      rw [sumOver_sub]
    rw [hsplit, hshare]
    have hsrc : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
      have h := sumOver_ite_eq hNodup r.source (r.amount : Int)
      simp [hsrcMem] at h
      exact h
    rw [hsrc, hrfl]
    omega
  · have hrej : (step s r).1 = .rejected := by simp [step, hv]
    rw [hrej] at hok
    cases hok

end Payout
