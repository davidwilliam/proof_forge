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

theorem tmp_nonneg_test (s : State) (r : Request) (hvalid : ValidPayout s r) :
    ((if ValidPayout s r then (1 : Nat) else 2) = 1) := by
  simp [hvalid]

theorem fair_aux : FairShares step := by
  unfold FairShares
  intro s r hok i hi
  by_cases hv : ValidPayout s r
  · have hStepEq : step s r = (Outcome.ok, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by
      simp [step, hv]
    have hBal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
      rw [hStepEq]
    rw [hBal]
    obtain ⟨h1, hpos, hne, hNodupRec, hSrcNot, h6, h7, h8, h9, h10⟩ := hv
    have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hne_src : r.recipients[i] ≠ r.source := fun h => hSrcNot (h ▸ hmem)
    have hidx : indexOf? r.recipients r.recipients[i] = some i :=
      indexOf?_getElem hNodupRec i hi
    unfold expectedBalance shareOf
    rw [hidx]
    simp only [hne_src, ↓reduceIte]
    omega
  · have hRej : (step s r).1 = Outcome.rejected := by simp [step, hv]
    rw [hRej] at hok
    contradiction

theorem t1 (n : Nat) : n * (5:Nat) = 5*n := by omega
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @List.range_succ
#check @List.range_zero

theorem sum_append (l1 l2 : List Nat) (f : Nat → Int) : sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by induction l1 with | nil => simp | cons a l ih => simp [ih]; omega



theorem arch0_step_of_valid (s : State) (r : Request) :
    ValidPayout s r →
      step s r =
        (.ok, { s with
          balance := fun a => expectedBalance s r a,
          applied := r.txId :: s.applied }) := by
  intro h
  simp [step, h]


theorem arch0_sum_deduction (s : State) (r : Request) :
    ValidPayout s r →
      sumOver s.accounts
          (fun a => if a = r.source then (r.amount : Int) else 0)
        = (r.amount : Int) := by
  intro h
  obtain ⟨hnodup, _, _, _, _, hmem, _, _, _, _⟩ := h
  have hh := sumOver_ite_eq hnodup r.source ((r.amount : Int))
  simp [hmem] at hh
  exact hh


theorem arch0_sum_range_const (n : Nat) (q : Int) :
    sumOver (List.range n) (fun _ => q) = (n : Int) * q := by sorry

theorem arch0_sum_range_indicator (n m : Nat) (hm : m ≤ n) :
    sumOver (List.range n)
        (fun i => if i < m then (1 : Int) else 0)
      = (m : Int) := by sorry

theorem arch0_fairShare_sum_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n)
        (fun i => (fairShare amount n i : Int))
      = (amount : Int) := by sorry

theorem arch0_sum_recipients_eq_range (r : Request) :
    r.recipients.Nodup →
      sumOver r.recipients (fun a => (shareOf r a : Int)) =
        sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by sorry

theorem arch0_sum_recipients_shareOf (r : Request) :
    r.recipients.Nodup →
    r.recipients ≠ [] →
      sumOver r.recipients (fun a => (shareOf r a : Int))
        = (r.amount : Int) := by sorry

theorem arch0_sumOver_subset_of_zero_outside
    (l sub : List AccountId) (f : AccountId → Int) :
    l.Nodup →
    sub.Nodup →
    (∀ x ∈ sub, x ∈ l) →
    (∀ a, a ∉ sub → f a = 0) →
      sumOver l f = sumOver sub f := by sorry

theorem arch0_sum_accounts_shares (s : State) (r : Request) :
    ValidPayout s r →
      sumOver s.accounts (fun a => (shareOf r a : Int))
        = (r.amount : Int) := by
  intro hV
  obtain ⟨hNodupAcc, _hamt, hNe, hNodupRec, _hsrcNot, _hsrcMem, hSub, _hauth, _hle, _htx⟩ := hV
  have hZero : ∀ a, a ∉ r.recipients → ((shareOf r a : Int) = 0) := by
    intro a ha
    have hnone : indexOf? r.recipients a = none := indexOf?_eq_none ha
    unfold shareOf
    rw [hnone]
    rfl
  have hSubEq := arch0_sumOver_subset_of_zero_outside s.accounts r.recipients
    (fun a => (shareOf r a : Int)) hNodupAcc hNodupRec hSub hZero
  have hRec := arch0_sum_recipients_shareOf r hNodupRec hNe
  rw [hSubEq]
  exact hRec


theorem arch0_sum_expected (s : State) (r : Request) :
    ValidPayout s r →
      sumOver s.accounts (fun a => expectedBalance s r a)
        = sumOver s.accounts s.balance := by
  intro hv
  have hded := arch0_sum_deduction s r hv
  have hsh := arch0_sum_accounts_shares s r hv
  have heq : (fun a => expectedBalance s r a) = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int))) := by
    funext a; rfl
  rw [heq]
  have hadd := sumOver_add s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) (fun a => (shareOf r a : Int))
  have hsub := sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
  have hcongr : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int))
      = sumOver s.accounts s.balance - (r.amount : Int) + (r.amount : Int) := by
    rw [hadd, hsub, hded, hsh]
  rw [hcongr]
  omega




theorem arch0_valid_of_ok (s : State) (r : Request) :
    (step s r).1 = .ok → ValidPayout s r := by
  intro h
  by_cases hv : ValidPayout s r
  · exact hv
  · have hstep : (step s r).1 = .rejected := by
      unfold step
      simp [hv]
    rw [hstep] at h
    simp at h

theorem arch0_total_of_valid_test (s : State) (r : Request) :
    ValidPayout s r → total (step s r).2 = total s := by
  intro hv
  have hstep := arch0_step_of_valid s r hv
  have hsum := arch0_sum_expected s r hv
  have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
    rw [hstep]
  rw [h2]
  unfold total
  exact hsum

theorem arch0_total_of_valid (s : State) (r : Request) :
    ValidPayout s r → total (step s r).2 = total s := by
  intro hv
  have hstep := arch0_step_of_valid s r hv
  have hsum := arch0_sum_expected s r hv
  have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
    rw [hstep]
  rw [h2]
  unfold total
  exact hsum

theorem arch0_step_of_valid_test_tmp (s : State) (r : Request) :
    ValidPayout s r →
      step s r =
        (.ok, { s with
          balance := fun a => expectedBalance s r a,
          applied := r.txId :: s.applied }) := by
  intro h
  simp [step, h]

theorem tprobe_addmul (a b c : Int) : (a + b) * c = a * c + b * c := by
  exact Int.add_mul a b c







theorem plan0_sum_deduction_of_components {l : List AccountId}
    (hl : l.Nodup) {source : AccountId} (hsrc : source ∈ l) (amount : Nat) :
    sumOver l (fun a => if a = source then (amount : Int) else 0)
      = (amount : Int) := by
  have h := sumOver_ite_eq hl source ((amount : Int))
  simp [hsrc] at h
  exact h


theorem plan0_accounts_nodup_of_valid (s : State) (r : Request) :
    ValidPayout s r → s.accounts.Nodup := by
  intro h
  unfold ValidPayout at h
  exact h.1

theorem plan0_source_mem_of_valid_aux (s : State) (r : Request) :
    ValidPayout s r → r.source ∈ s.accounts := by
  intro h
  unfold ValidPayout at h
  obtain ⟨_, _, _, _, _, hmem, _, _, _, _⟩ := h
  exact hmem

theorem plan0_source_mem_of_valid (s : State) (r : Request) :
    ValidPayout s r → r.source ∈ s.accounts := by
  intro h
  unfold ValidPayout at h
  obtain ⟨_, _, _, _, _, hmem, _, _, _, _⟩ := h
  exact hmem

theorem plan0_sumOver_ite_eq_of_mem_proof : ∀ {l : List AccountId} (_hl : l.Nodup) {x : AccountId} (_hx : x ∈ l) (c : Int), sumOver l (fun a => if a = x then c else 0) = c := by
  intro l hl x hx c
  have h := sumOver_ite_eq hl x c
  simp [hx] at h
  exact h

theorem plan0_sumOver_ite_eq_of_mem {l : List AccountId} (hl : l.Nodup)
    {x : AccountId} (hx : x ∈ l) (c : Int) :
    sumOver l (fun a => if a = x then c else 0) = c := by
  have h := sumOver_ite_eq hl x c
  simp [hx] at h
  exact h

theorem plan0_test_lemma {l : List AccountId}
    (hl : l.Nodup) {source : AccountId} (hsrc : source ∈ l) (amount : Nat) :
    sumOver l (fun a => if a = source then (amount : Int) else 0)
      = (amount : Int) := by
  have h := sumOver_ite_eq hl source ((amount : Int))
  simp [hsrc] at h
  exact h

theorem plan0_sum_deduction_of_components2 {l : List AccountId}
    (hl : l.Nodup) {source : AccountId} (hsrc : source ∈ l) (amount : Nat) :
    sumOver l (fun a => if a = source then (amount : Int) else 0)
      = (amount : Int) := by
  have h := sumOver_ite_eq hl source ((amount : Int))
  simp [hsrc] at h
  exact h

theorem arch0_sum_deduction_proof (s : State) (r : Request) :
    ValidPayout s r →
      sumOver s.accounts
          (fun a => if a = r.source then (r.amount : Int) else 0)
        = (r.amount : Int) := by
  intro h
  exact plan0_sum_deduction_of_components (plan0_accounts_nodup_of_valid s r h) (plan0_source_mem_of_valid s r h) r.amount

theorem arch0_sum_deduction_check (s : State) (r : Request) (h : ValidPayout s r) :
      sumOver s.accounts
          (fun a => if a = r.source then (r.amount : Int) else 0)
        = (r.amount : Int) := by
  obtain ⟨hnodup, _, _, _, _, hmem, _, _, _, _⟩ := h
  have hh := sumOver_ite_eq hnodup r.source ((r.amount : Int))
  simp [hmem] at hh
  exact hh

theorem probe_addmul2 (a b c : Int) : (a + b) * c = a * c + b * c := by
  exact Int.add_mul a b c

theorem arch0_sum_range_const_proof3 (n : Nat) (q : Int) :
    sumOver (List.range n) (fun _ => q) = (n : Int) * q := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n.succ) = List.range n ++ [n] := List.range_succ
    have h2 : List.range (n + 1) = List.range (n.succ) := by rfl
    rw [h2, h1, sum_append, ih]
    simp only [sumOver_cons, sumOver_nil]
    simp only [Int.add_zero]
    have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
    rw [hcast, Int.add_mul, Int.one_mul]

theorem probe_min_test (n m : Nat) : Nat.min n m ≤ n := Nat.min_le_left n m
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @Nat.min_def

theorem aux_sum_range_const (n : Nat) (q : Int) :
    sumOver (List.range n) (fun _ => q) = (n : Int) * q := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n.succ) = List.range n ++ [n] := List.range_succ
    rw [h1, sum_append, ih]
    simp only [sumOver_cons, sumOver_nil, Int.add_zero]
    have hcast : ((n.succ : Nat) : Int) = (n : Int) + 1 := by simp
    rw [hcast, Int.add_mul, Int.one_mul]

theorem aux_sum_zero (l : List Nat) : sumOver l (fun _ : Nat => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]



theorem plan1_sumOver_via_indexOf (l : List AccountId) (f : Nat → Int)
    (hl : l.Nodup) :
    sumOver l
        (fun a => match indexOf? l a with
          | some i => f i
          | none => (0 : Int)) =
      sumOver (List.range l.length) (fun i => f i) := by
  have hshift : ∀ (n : Nat) (g : Nat → Int),
      sumOver (List.range (n + 1)) g =
        g 0 + sumOver (List.range n) (fun i => g (i + 1)) := by
    intro n
    induction n with
    | zero =>
      intro g
      simp
    | succ n ih =>
      intro g
      have h1 : List.range (n + 1 + 1) = List.range (n+1) ++ [n+1] := by simp [List.range_succ]
      have h2 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
      have hLHS : sumOver (List.range (n+1+1)) g = sumOver (List.range (n+1)) g + g (n+1) := by
        rw [h1, sum_append]; simp
      have hRHS : sumOver (List.range (n+1)) (fun i => g (i+1)) = sumOver (List.range n) (fun i => g (i+1)) + g (n+1) := by
        rw [h2, sum_append]
        simp
      have ihf := ih g
      omega
  induction l generalizing f with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hmem, hnodup⟩ := hl
    have h0 : (match indexOf? (x :: xs) x with | some i => f i | none => (0 : Int)) = f 0 := by
      simp [indexOf?]
    have htail : ∀ a ∈ xs, (match indexOf? (x :: xs) a with | some i => f i | none => (0 : Int))
        = (match indexOf? xs a with | some i => f (i + 1) | none => (0 : Int)) := by
      intro a ha
      have hxa : x ≠ a := by intro h; subst h; exact hmem ha
      have heq : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
        simp [indexOf?, hxa]
      rw [heq]
      cases h : indexOf? xs a with
      | none => simp
      | some i => simp
    have hsum_tail : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => f i | none => (0 : Int))
        = sumOver xs (fun a => match indexOf? xs a with | some i => f (i+1) | none => (0 : Int)) := by
      apply sumOver_congr
      intro a ha
      exact htail a ha
    have ih' := ih (fun i => f (i + 1)) hnodup
    have hLHS : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with | some i => f i | none => (0 : Int))
        = f 0 + sumOver xs (fun a => match indexOf? xs a with | some i => f (i+1) | none => (0 : Int)) := by
      simp only [sumOver_cons]
      rw [h0, hsum_tail]
    have hRHS : sumOver (List.range (xs.length + 1)) (fun i => f i)
        = f 0 + sumOver (List.range xs.length) (fun i => f (i + 1)) :=
      hshift xs.length _
    simp only [List.length_cons] at *
    rw [hLHS, hRHS, ih']


theorem plan1_fairShare_cast (amount n i : Nat) :
    (fairShare amount n i : Int) =
      (amount / n : Int) + (if i < amount % n then (1 : Int) else 0) := by
  unfold fairShare
  by_cases h : i < amount % n <;> simp [h]


theorem plan1_sum_range_indicator (n m : Nat) (hm : m ≤ n) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) =
      (m : Int) := by
  induction n generalizing m with
  | zero =>
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    rfl
  | succ n ih =>
    have hrw : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    have hs : sumOver (List.range (n + 1)) (fun i => if i < m then (1 : Int) else 0)
      = sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0)
        + sumOver [n] (fun i => if i < m then (1 : Int) else 0) := by
      rw [hrw, sum_append]
    have hsimp : sumOver [n] (fun i => if i < m then (1 : Int) else 0) = (if n < m then (1:Int) else 0) := by
      simp
    rw [hsimp] at hs
    by_cases hle : m ≤ n
    · have hih := ih m hle
      have hn : ¬ (n < m) := by omega
      simp only [hn, ↓reduceIte] at hs
      simp only [Int.add_zero] at hs
      rw [hs, hih]
    · have hmeq : m = n + 1 := by omega
      subst hmeq
      have hn : n < n + 1 := Nat.lt_succ_self n
      simp only [hn, ↓reduceIte] at hs
      have hcong : ∀ i ∈ List.range n, (if i < n + 1 then (1:Int) else 0) = 1 := by
        intro i hi
        have hmem : i < n := List.mem_range.mp hi
        have hilt : i < n + 1 := by omega
        simp [hilt]
      have h1 := sumOver_congr (List.range n) (fun i => if i < n + 1 then (1:Int) else 0) (fun _ => (1:Int)) hcong
      have h2 := aux_sum_range_const n (1:Int)
      simp only [Int.mul_one] at h2
      rw [hs, h1, h2]
      simp


theorem plan1_fairShare_sum_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) =
      (amount : Int) := by sorry



theorem plan1_sum_range_succ_shift (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f =
      f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n+1) ++ [n+1] := by simp [List.range_succ]
    have h2 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    have hLHS : sumOver (List.range (n+1+1)) f = sumOver (List.range (n+1)) f + f (n+1) := by
      rw [h1, sum_append]; simp
    have hRHS : sumOver (List.range (n+1)) (fun i => f (i+1)) = sumOver (List.range n) (fun i => f (i+1)) + f (n+1) := by
      rw [h2, sum_append]
      simp
    have ihf := ih f
    omega

theorem plan1_sumOver_via_indexOf_proof2 : True := trivial

theorem plan1_check_selfcontained_aux (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f =
      f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n+1) ++ [n+1] := by simp [List.range_succ]
    have h2 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    have hLHS : sumOver (List.range (n+1+1)) f = sumOver (List.range (n+1)) f + f (n+1) := by
      rw [h1, sum_append]; simp
    have hRHS : sumOver (List.range (n+1)) (fun i => f (i+1)) = sumOver (List.range n) (fun i => f (i+1)) + f (n+1) := by
      rw [h2, sum_append]
      simp
    have ihf := ih f
    omega

theorem plan1_via_test2 (l : List AccountId) (f : Nat → Int)
    (hl : l.Nodup) :
    sumOver l
        (fun a => match indexOf? l a with
          | some i => f i
          | none => (0 : Int)) =
      sumOver (List.range l.length) (fun i => f i) := by
  have hshift : ∀ (n : Nat) (g : Nat → Int),
      sumOver (List.range (n + 1)) g =
        g 0 + sumOver (List.range n) (fun i => g (i + 1)) := by
    intro n
    induction n with
    | zero =>
      intro g
      simp
    | succ n ih =>
      intro g
      have h1 : List.range (n + 1 + 1) = List.range (n+1) ++ [n+1] := by simp [List.range_succ]
      have h2 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
      have hLHS : sumOver (List.range (n+1+1)) g = sumOver (List.range (n+1)) g + g (n+1) := by
        rw [h1, sum_append]; simp
      have hRHS : sumOver (List.range (n+1)) (fun i => g (i+1)) = sumOver (List.range n) (fun i => g (i+1)) + g (n+1) := by
        rw [h2, sum_append]
        simp
      have ihf := ih g
      omega
  induction l generalizing f with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hmem, hnodup⟩ := hl
    have h0 : (match indexOf? (x :: xs) x with | some i => f i | none => (0 : Int)) = f 0 := by
      simp [indexOf?]
    have htail : ∀ a ∈ xs, (match indexOf? (x :: xs) a with | some i => f i | none => (0 : Int))
        = (match indexOf? xs a with | some i => f (i + 1) | none => (0 : Int)) := by
      intro a ha
      have hxa : x ≠ a := by intro h; subst h; exact hmem ha
      have heq : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
        simp [indexOf?, hxa]
      rw [heq]
      cases h : indexOf? xs a with
      | none => simp
      | some i => simp
    have hsum_tail : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => f i | none => (0 : Int))
        = sumOver xs (fun a => match indexOf? xs a with | some i => f (i+1) | none => (0 : Int)) := by
      apply sumOver_congr
      intro a ha
      exact htail a ha
    have ih' := ih (fun i => f (i + 1)) hnodup
    have hLHS : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with | some i => f i | none => (0 : Int))
        = f 0 + sumOver xs (fun a => match indexOf? xs a with | some i => f (i+1) | none => (0 : Int)) := by
      simp only [sumOver_cons]
      rw [h0, hsum_tail]
    have hRHS : sumOver (List.range (xs.length + 1)) (fun i => f i)
        = f 0 + sumOver (List.range xs.length) (fun i => f (i + 1)) :=
      hshift xs.length _
    simp only [List.length_cons] at *
    rw [hLHS, hRHS, ih']

theorem plan1_fairShare_cast_proof (amount n i : Nat) :
    (fairShare amount n i : Int) =
      (amount / n : Int) + (if i < amount % n then (1 : Int) else 0) := by
  unfold fairShare
  by_cases h : i < amount % n <;> simp [h]

theorem plan1_ind_selftest2 (n m : Nat) (hm : m ≤ n) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) =
      (m : Int) := by
  induction n generalizing m with
  | zero =>
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    rfl
  | succ n ih =>
    have hrw : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    have hs : sumOver (List.range (n + 1)) (fun i => if i < m then (1 : Int) else 0)
      = sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0)
        + sumOver [n] (fun i => if i < m then (1 : Int) else 0) := by
      rw [hrw, sum_append]
    have hsimp : sumOver [n] (fun i => if i < m then (1 : Int) else 0) = (if n < m then (1:Int) else 0) := by
      simp
    rw [hsimp] at hs
    by_cases hle : m ≤ n
    · have hih := ih m hle
      have hn : ¬ (n < m) := by omega
      simp only [hn, ↓reduceIte] at hs
      simp only [Int.add_zero] at hs
      rw [hs, hih]
    · have hmeq : m = n + 1 := by omega
      subst hmeq
      have hn : n < n + 1 := Nat.lt_succ_self n
      simp only [hn, ↓reduceIte] at hs
      have hcong : ∀ i ∈ List.range n, (if i < n + 1 then (1:Int) else 0) = 1 := by
        intro i hi
        have hmem : i < n := List.mem_range.mp hi
        have hilt : i < n + 1 := by omega
        simp [hilt]
      have h1 := sumOver_congr (List.range n) (fun i => if i < n + 1 then (1:Int) else 0) (fun _ => (1:Int)) hcong
      have h2 := aux_sum_range_const n (1:Int)
      simp only [Int.mul_one] at h2
      rw [hs, h1, h2]
      simp

theorem probe_cast2 (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp

theorem probe_cast3 (a b c : Nat) (h : a * b + c = a + b) :
    (a : Int) * (b : Int) + (c : Int) = (a : Int) + (b : Int) := by
  have h2 : ((a * b + c : Nat) : Int) = ((a + b : Nat) : Int) := by rw [h]
  simp at h2
  exact h2

theorem probe_fair_decomp (amount n i : Nat) :
    (fairShare amount n i : Int) =
      ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) := by
  unfold fairShare
  by_cases h : i < amount % n <;> simp [h]

theorem test_fair_final (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) =
      (amount : Int) := by
  have hcongr : sumOver (List.range n) (fun i => (fairShare amount n i : Int)) =
      sumOver (List.range n) (fun i => (((amount / n : Nat)) : Int) + (if i < amount % n then (1 : Int) else 0)) :=
    sumOver_congr _ _ _ (fun a _ => probe_fair_decomp amount n a)
  rw [hcongr, sumOver_add]
  have h1 : sumOver (List.range n) (fun i => ((((amount / n : Nat))) : Int)) = (n : Int) * ((((amount / n : Nat))) : Int) :=
    aux_sum_range_const n _
  rw [h1]
  have hmod_le : amount % n ≤ n := Nat.le_of_lt (Nat.mod_lt amount hn)
  have h2 : sumOver (List.range n) (fun i => if i < amount % n then (1 : Int) else 0) = ((((amount % n : Nat))) : Int) :=
    plan1_sum_range_indicator n (amount % n) hmod_le
  rw [h2]
  have hdiv : n * (amount / n) + amount % n = amount := Nat.div_add_mod amount n
  have h := congrArg (fun k : Nat => (k : Int)) hdiv
  simp at h
  exact h

theorem plan1_fairShare_sum_range_proof (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) =
      (amount : Int) :=
  test_fair_final amount n hn

theorem test_inline_ok (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) =
      (amount : Int) := by
  have hcongr : sumOver (List.range n) (fun i => (fairShare amount n i : Int)) =
      sumOver (List.range n) (fun i => (((amount / n : Nat)) : Int) + (if i < amount % n then (1 : Int) else 0)) :=
    sumOver_congr _ _ _ (fun a _ => probe_fair_decomp amount n a)
  rw [hcongr, sumOver_add]
  have h1 : sumOver (List.range n) (fun i => ((((amount / n : Nat))) : Int)) = (n : Int) * ((((amount / n : Nat))) : Int) :=
    aux_sum_range_const n _
  rw [h1]
  have hmod_le : amount % n ≤ n := Nat.le_of_lt (Nat.mod_lt amount hn)
  have h2 : sumOver (List.range n) (fun i => if i < amount % n then (1 : Int) else 0) = ((((amount % n : Nat))) : Int) :=
    plan1_sum_range_indicator n (amount % n) hmod_le
  rw [h2]
  have hdiv : n * (amount / n) + amount % n = amount := Nat.div_add_mod amount n
  have h := congrArg (fun k : Nat => (k : Int)) hdiv
  simp at h
  exact h

theorem plan1_sum_recipients_shareOf_eq_range (r : Request)
    (hl : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) =
      sumOver (List.range r.recipients.length)
        (fun i => (fairShare r.amount r.recipients.length i : Int)) := by
  have h := plan1_sumOver_via_indexOf r.recipients (fun i => (fairShare r.amount r.recipients.length i : Int)) hl
  have h2 : (fun a => (shareOf r a : Int)) = (fun a => match indexOf? r.recipients a with | some i => (fairShare r.amount r.recipients.length i : Int) | none => (0 : Int)) := by
    funext a
    unfold shareOf
    cases hidx : indexOf? r.recipients a <;> rfl
  rw [h2]
  exact h

theorem arch0_sum_recipients_shareOf_aux_test (r : Request) (hl : r.recipients.Nodup) (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have h1 : sumOver r.recipients (fun a => (shareOf r a : Int)) =
      sumOver (List.range r.recipients.length)
        (fun i => (fairShare r.amount r.recipients.length i : Int)) :=
    plan1_sum_recipients_shareOf_eq_range r hl
  have hlen : 0 < r.recipients.length := by
    cases h : r.recipients with
    | nil => simp_all
    | cons x xs => simp
  have h2 : sumOver (List.range r.recipients.length)
        (fun i => (fairShare r.amount r.recipients.length i : Int)) = (r.amount : Int) :=
    plan1_fairShare_sum_range_proof r.amount r.recipients.length hlen
  rw [h1, h2]

theorem arch0_sum_range_const_check (n : Nat) (q : Int) :
    sumOver (List.range n) (fun _ => q) = (n : Int) * q := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n.succ) = List.range n ++ [n] := List.range_succ
    rw [h1, sum_append, ih]
    simp only [sumOver_cons, sumOver_nil, Int.add_zero]
    have hcast : ((n.succ : Nat) : Int) = (n : Int) + 1 := by simp
    rw [hcast, Int.add_mul, Int.one_mul]

theorem arch0_const_inline_check (n : Nat) (q : Int) :
    sumOver (List.range n) (fun _ => q) = (n : Int) * q := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n.succ) = List.range n ++ [n] := List.range_succ
    rw [h1, sum_append, ih]
    simp only [sumOver_cons, sumOver_nil, Int.add_zero]
    have hcast : ((n.succ : Nat) : Int) = (n : Int) + 1 := by simp
    rw [hcast, Int.add_mul, Int.one_mul]

theorem probe_list_avail : True := trivial
#check @List.mem_cons
#check @List.nodup_cons
#check @List.filter_cons
#check @List.mem_filter
#check List.nodup_nil
#check @Decidable.em

theorem arch0_subset_helper_tmp2 (l sub : List AccountId) (f : AccountId → Int) :
    l.Nodup →
    sub.Nodup →
    (∀ x ∈ sub, x ∈ l) →
    (∀ a, a ∉ sub → f a = 0) →
      sumOver l f = sumOver sub f := by
  induction sub generalizing l f with
  | nil =>
    intro hl _ _ hz
    simp only [sumOver_nil]
    have h0 : ∀ a ∈ l, f a = (fun _ : AccountId => (0 : Int)) a := fun a _ => hz a (by simp)
    have hcon : sumOver l f = sumOver l (fun _ : AccountId => (0 : Int)) :=
      sumOver_congr l f _ h0
    rw [hcon, aux_sum_zero]
  | cons b sub' ih =>
    intro hl hsub hmem hz
    rw [List.nodup_cons] at hsub
    obtain ⟨hb_notin, hsub_nodup⟩ := hsub
    have hb_mem_l : b ∈ l := hmem b (by simp)
    have hsub'_sub : ∀ x ∈ sub', x ∈ l := fun x hx => hmem x (by simp [hx])
    have hz' : ∀ a, a ∉ sub' → (fun a => if a = b then (0 : Int) else f a) a = 0 := by
      intro a ha
      simp only
      by_cases hab : a = b
      · simp [hab]
      · simp [hab]
        apply hz a
        simp [hab, ha]
    have hcongr_sub : sumOver sub' (fun a => if a = b then (0 : Int) else f a) = sumOver sub' f := by
      apply sumOver_congr
      intro a ha
      have hne : a ≠ b := fun h => hb_notin (h ▸ ha)
      simp [hne]
    have hIH : sumOver l (fun a => if a = b then (0 : Int) else f a) = sumOver sub' (fun a => if a = b then (0 : Int) else f a) :=
      ih l _ hl hsub_nodup hsub'_sub hz'
    have hdecomp : ∀ a : AccountId, f a = (if a = b then (f b) else 0) + (if a = b then (0 : Int) else f a) := by
      intro a
      by_cases hab : a = b
      · simp [hab]
      · simp [hab]
    have hsum_l : sumOver l f = sumOver l (fun a => if a = b then (f b) else 0) + sumOver l (fun a => if a = b then (0 : Int) else f a) := by
      have h1 : sumOver l f = sumOver l (fun a => (if a = b then (f b) else 0) + (if a = b then (0 : Int) else f a)) := by
        apply sumOver_congr
        intro a _
        exact hdecomp a
      rw [h1, sumOver_add]
    have hsum_ind : sumOver l (fun a : AccountId => if a = b then (f b) else (0 : Int)) = f b := by
      have h2 : sumOver l (fun a : AccountId => if a = b then (f b) else (0 : Int)) = if b ∈ l then f b else 0 :=
        sumOver_ite_eq hl b (f b)
      rw [h2, if_pos hb_mem_l]
    have hsum_sub : sumOver (b :: sub') f = f b + sumOver sub' f := rfl
    rw [hsum_l, hsum_ind, hIH, hcongr_sub, hsum_sub]

theorem arch0_subset_selfcontained_check (l sub : List AccountId) (f : AccountId → Int) :
    l.Nodup →
    sub.Nodup →
    (∀ x ∈ sub, x ∈ l) →
    (∀ a, a ∉ sub → f a = 0) →
      sumOver l f = sumOver sub f := by
  induction sub generalizing l f with
  | nil =>
    intro hl _ _ hz
    simp only [sumOver_nil]
    have h0 : ∀ a ∈ l, f a = (fun _ : AccountId => (0 : Int)) a := fun a _ => hz a (by simp)
    have hcon : sumOver l f = sumOver l (fun _ : AccountId => (0 : Int)) :=
      sumOver_congr l f _ h0
    rw [hcon, aux_sum_zero]
  | cons b sub' ih =>
    intro hl hsub hmem hz
    rw [List.nodup_cons] at hsub
    obtain ⟨hb_notin, hsub_nodup⟩ := hsub
    have hb_mem_l : b ∈ l := hmem b (by simp)
    have hsub'_sub : ∀ x ∈ sub', x ∈ l := fun x hx => hmem x (by simp [hx])
    have hz' : ∀ a, a ∉ sub' → (fun a => if a = b then (0 : Int) else f a) a = 0 := by
      intro a ha
      simp only
      by_cases hab : a = b
      · simp [hab]
      · simp [hab]
        apply hz a
        simp [hab, ha]
    have hcongr_sub : sumOver sub' (fun a => if a = b then (0 : Int) else f a) = sumOver sub' f := by
      apply sumOver_congr
      intro a ha
      have hne : a ≠ b := fun h => hb_notin (h ▸ ha)
      simp [hne]
    have hIH : sumOver l (fun a => if a = b then (0 : Int) else f a) = sumOver sub' (fun a => if a = b then (0 : Int) else f a) :=
      ih l _ hl hsub_nodup hsub'_sub hz'
    have hdecomp : ∀ a : AccountId, f a = (if a = b then (f b) else 0) + (if a = b then (0 : Int) else f a) := by
      intro a
      by_cases hab : a = b
      · simp [hab]
      · simp [hab]
    have hsum_l : sumOver l f = sumOver l (fun a => if a = b then (f b) else 0) + sumOver l (fun a => if a = b then (0 : Int) else f a) := by
      have h1 : sumOver l f = sumOver l (fun a => (if a = b then (f b) else 0) + (if a = b then (0 : Int) else f a)) := by
        apply sumOver_congr
        intro a _
        exact hdecomp a
      rw [h1, sumOver_add]
    have hsum_ind : sumOver l (fun a : AccountId => if a = b then (f b) else (0 : Int)) = f b := by
      have h2 : sumOver l (fun a : AccountId => if a = b then (f b) else (0 : Int)) = if b ∈ l then f b else 0 :=
        sumOver_ite_eq hl b (f b)
      rw [h2, if_pos hb_mem_l]
    have hsum_sub : sumOver (b :: sub') f = f b + sumOver sub' f := rfl
    rw [hsum_l, hsum_ind, hIH, hcongr_sub, hsum_sub]



theorem plan2_sumOver_erase_add (l : List AccountId) (f : AccountId → Int)
    (hl : l.Nodup) {a : AccountId} (ha : a ∈ l) :
    sumOver l f = f a + sumOver (List.erase l a) f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [sumOver_cons]
    rw [List.nodup_cons] at hl
    have hmem : a = x ∨ a ∈ xs := List.mem_cons.mp ha
    by_cases hx : x = a
    · have herase : List.erase (x :: xs) a = xs := by simp [hx]
      rw [herase]
      have hax : a = x := hx.symm
      subst hax
      omega
    · have ha_mem : a ∈ xs := by
        cases hmem with
        | inl h => exact absurd h.symm hx
        | inr h => exact h
      have ih' := ih hl.2 ha_mem
      have herase : List.erase (x :: xs) a = x :: List.erase xs a := by simp [hx]
      rw [herase]
      simp only [sumOver_cons]
      omega




theorem plan2_nodup_erase_of_nodup (l : List AccountId) (a : AccountId)
    (hl : l.Nodup) :
    (List.erase l a).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.erase_cons]
    by_cases h : x == a
    · simp [h, (List.nodup_cons.mp hl).2]
    · simp [h]
      have hcons := List.nodup_cons.mp hl
      have ih2 := ih hcons.2
      constructor
      · intro hmem
        have hmem2 : x ∈ xs := List.mem_of_mem_erase hmem
        exact hcons.1 hmem2
      · exact ih2


theorem plan2_sumOver_subset_of_zero_in_list (l sub : List AccountId)
    (f : AccountId → Int)
    (hl : l.Nodup) (hsub : sub.Nodup)
    (hsubset : ∀ x ∈ sub, x ∈ l)
    (hzero : ∀ a ∈ l, a ∉ sub → f a = 0) :
    sumOver l f = sumOver sub f := by sorry

theorem plan2_sumOver_eq_zero_of_all_zero (l : List AccountId) (f : AccountId → Int)
    (h : ∀ a ∈ l, f a = 0) :
    sumOver l f = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [sumOver_cons]
    have ha : f a = 0 := h a (by simp)
    have htl : ∀ b ∈ l, f b = 0 := fun b hb => h b (by simp [hb])
    rw [ha, ih htl, Int.add_zero]

theorem plan2_sumOver_erase_add_probe (l : List AccountId) (f : AccountId → Int)
    (hl : l.Nodup) {a : AccountId} (ha : a ∈ l) :
    sumOver l f = f a + sumOver (List.erase l a) f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [sumOver_cons]
    rw [List.nodup_cons] at hl
    have hmem : a = x ∨ a ∈ xs := List.mem_cons.mp ha
    by_cases hx : x = a
    · have herase : List.erase (x :: xs) a = xs := by simp [hx]
      rw [herase]
      have hax : a = x := hx.symm
      subst hax
      omega
    · have ha_mem : a ∈ xs := by
        cases hmem with
        | inl h => exact absurd h.symm hx
        | inr h => exact h
      have ih' := ih hl.2 ha_mem
      have herase : List.erase (x :: xs) a = x :: List.erase xs a := by simp [hx]
      rw [herase]
      simp only [sumOver_cons]
      omega

theorem plan2_mem_erase_of_mem_ne_proof {l : List AccountId} {a x : AccountId}
    (hx : x ∈ l) (hne : x ≠ a) :
    x ∈ List.erase l a := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    by_cases hya : y = a
    · subst hya
      simp only [List.erase_cons_head] at *
      -- here erase (a :: ys) a = ys ?
      simp at hx
      cases hx with
      | inl h => exact absurd h hne
      | inr h => exact h
    · have herase : List.erase (y :: ys) a = y :: List.erase ys a := by
        simp [hya]
      rw [herase]
      simp at hx ⊢
      cases hx with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (ih h)

theorem plan2_mem_erase_of_mem_ne {l : List AccountId} {a x : AccountId}
    (hx : x ∈ l) (hne : x ≠ a) :
    x ∈ List.erase l a := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    by_cases hya : y = a
    · subst hya
      simp only [List.erase_cons_head] at *
      simp at hx
      cases hx with
      | inl h => exact absurd h hne
      | inr h => exact h
    · have herase : List.erase (y :: ys) a = y :: List.erase ys a := by
        simp [hya]
      rw [herase]
      simp at hx ⊢
      cases hx with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (ih h)

theorem plan2_nodup_erase_of_nodup_aux3 (l : List AccountId) (a : AccountId)
    (hl : l.Nodup) :
    (List.erase l a).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.erase_cons]
    by_cases h : x == a
    · simp [h, (List.nodup_cons.mp hl).2]
    · simp [h]
      have hcons := List.nodup_cons.mp hl
      have ih2 := ih hcons.2
      constructor
      · intro hmem
        have hmem2 : x ∈ xs := List.mem_of_mem_erase hmem
        exact hcons.1 hmem2
      · exact ih2

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · have hrej : (step s r).1 = .rejected := by simp [step, hv]
    rw [hrej] at h
    contradiction

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · simp [step, hv]
  · have hrej : (step s r).1 = .rejected := by simp [step, hv]
    rw [hrej] at hok
    contradiction

theorem req_idempotency : Idempotent step := by
  unfold Idempotent step
  intro s r h
  by_cases hV : ValidPayout s r
  · simp only [hV, ↓reduceIte] at h ⊢
    constructor
    · intro x
      simp only [List.mem_cons]
    · have hNot : ¬ ValidPayout ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r := by
        intro hC
        unfold ValidPayout at hC
        obtain ⟨_, _, _, _, _, _, _, _, _, hMem⟩ := hC
        exact hMem (by simp)
      simp only [hNot, ↓reduceIte]
  · simp only [hV, ↓reduceIte] at h
    simp at h

theorem req_nonnegative : NonNegative step := by
  unfold NonNegative step
  intro s r hnonneg a ha
  by_cases hV : ValidPayout s r
  · have hv := hV
  -- extract pieces without destroying hv
    obtain ⟨hnodup, hpos, hne, hrnodup, hsrc_not, hsrc_mem, hmem, hauth, hle, hfresh⟩ := hV
    simp only [hv, ↓reduceIte] at ha ⊢
    unfold expectedBalance
    by_cases hsrc : a = r.source
    · subst hsrc
      have hbal : 0 ≤ s.balance r.source := hnonneg _ hsrc_mem
      have hshare : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hsrc_not]
      simp only [hshare, if_true] at ⊢
      omega
    · simp only [hsrc, ↓reduceIte] at ⊢
      have hbal : 0 ≤ s.balance a := hnonneg a ha
      omega
  · simp only [hV, ↓reduceIte] at ha ⊢
    exact hnonneg a ha

theorem req_fair_shares : FairShares step := fair_aux

theorem req_conservation   : Conserves step := by
  intro s r hok
  exact arch0_total_of_valid s r (arch0_valid_of_ok s r hok)

end Payout
