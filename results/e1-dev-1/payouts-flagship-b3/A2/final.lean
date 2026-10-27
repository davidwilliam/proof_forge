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
                             | some i => (fairShare r.amount n i : Int)
                             | none => 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_valid_succeeds_test : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem my_test_range : List.range 3 = [0,1,2] := by rfl

theorem sumOver_append_test (l1 l2 : List Nat) (f : Nat → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem conserv_tmp_check1 (m n : Nat) : n * (m / n) + m % n = m :=
  Nat.div_add_mod m n

theorem conserv_tmp_check2 (a : Nat) (n : Nat) (h : 0 < n) : a % n < n :=
  Nat.mod_lt a h

theorem conserv_tmp_check3 : List.range 0 = ([] : List Nat) := by rfl

theorem conserv_tmp_check4 (n : Nat) : (n : Int) = n := by simp

theorem conserv_probe1 : ∀ (a b c : Int), (a + b) * c = a * c + b * c :=
  fun a b c => Int.add_mul a b c

theorem conserv_probe2 : ∀ (c : Int), 1 * c = c :=
  fun c => Int.one_mul c

theorem conserv_probe3 (n : Nat) : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by
  simp

theorem conserv_sum_const3 (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsing : sumOver [n] (fun _ => c) = c := by simp
    have happ : sumOver (List.range n ++ [n]) (fun _ => c)
        = sumOver (List.range n) (fun _ => c) + sumOver [n] (fun _ => c) :=
      sumOver_append_test _ _ _
    rw [List.range_succ, happ, ih, hsing]
    rw [conserv_probe3 n, conserv_probe1, conserv_probe2]

theorem conserv_probe_range (n i : Nat) : (i ∈ List.range n) = (i < n) := by
  simp [List.mem_range]

theorem conserv_sum_zero (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem conserv_probe_cast (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by
  simp

theorem conserv_probe_cast2 (a b : Nat) : (((a + b : Nat)) : Int) = (a : Int) + (b : Int) := by
  simp

theorem conserv_probe_divmod (m n : Nat) : n * (m / n) + m % n = m :=
  Nat.div_add_mod m n
#check Nat.div_add_mod
#check Nat.mod_le

theorem conserv_sum_ite_range_aux3 (n t : Nat) :
    sumOver (List.range n) (fun i => if i < t then (1 : Int) else 0) = ((min t n : Nat) : Int) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have happ : sumOver (List.range (n+1)) (fun i => if i < t then (1 : Int) else 0)
        = sumOver (List.range n) (fun i => if i < t then (1 : Int) else 0) + (if n < t then (1:Int) else 0) := by
      rw [List.range_succ]
      have h2 := sumOver_append_test (List.range n) [n] (fun i => if i < t then (1 : Int) else 0)
      rw [h2]
      congr 1
      simp
    rw [happ, ih]
    by_cases h : n < t
    · simp only [h, ↓reduceIte]
      have h1 : min t (n+1) = min t n + 1 := by omega
      rw [h1]
      simp
    · simp only [h, ↓reduceIte]
      have h1 : min t (n+1) = min t n := by omega
      rw [h1]
      simp

theorem conserv_fairShare_unfold (m n i : Nat) :
    ((fairShare m n i : Nat) : Int) = (m / n : Nat) + (if i < m % n then (1:Int) else 0) := by
  unfold fairShare
  by_cases h : i < m % n
  · simp [h]
  · simp [h]

theorem conserv_cast_probe_a (a b : Nat) : (((a + b : Nat)) : Int) = (a : Int) + (b : Int) := by
  simp

theorem conserv_cast_probe_b (a b : Nat) : (((a * b : Nat)) : Int) = (a : Int) * (b : Int) := by
  simp
#check Nat.div_add_mod

theorem conserv_sum_fair_eq2 (m n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare m n i : Nat) : Int)) = (m : Int) := by
  have hcongr : sumOver (List.range n) (fun i => ((fairShare m n i : Nat) : Int))
      = sumOver (List.range n) (fun i => ((m / n : Nat) : Int) + (if i < m % n then (1:Int) else 0)) := by
    apply sumOver_congr
    intro a ha
    exact conserv_fairShare_unfold m n a
  rw [hcongr, sumOver_add]
  have hconst : sumOver (List.range n) (fun _ => ((m / n : Nat) : Int)) = (n : Int) * ((m / n : Nat) : Int) := by
    exact conserv_sum_const3 n _
  rw [hconst]
  have hite : sumOver (List.range n) (fun i => (if i < m % n then (1:Int) else 0)) = ((min (m % n) n : Nat) : Int) := by
    exact conserv_sum_ite_range_aux3 n (m % n)
  rw [hite]
  have hmin : min (m % n) n = m % n := by
    apply Nat.min_eq_left
    apply Nat.le_of_lt
    exact Nat.mod_lt m hn
  rw [hmin]
  have hdiv : (n : Int) * ((m / n : Nat) : Int) + ((m % n : Nat) : Int) = (m : Int) := by
    have h := Nat.div_add_mod m n
    have hcast : (((n * (m / n) + m % n : Nat)) : Int) = (m : Int) := by rw [h]
    rw [conserv_cast_probe_a, conserv_cast_probe_b] at hcast
    exact hcast
  exact hdiv

theorem conserv_idx_cons_self2 (x : Nat) (xs : List Nat) : indexOf? (x :: xs) x = some 0 := by
  simp [indexOf?]

theorem conserv_sum_zero_any (l : List Nat) (f : Nat → Int) (h : ∀ a ∈ l, f a = 0) : sumOver l f = 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [sumOver_cons]
    rw [h x (by simp)]
    have h2 : ∀ a ∈ xs, f a = 0 := fun a ha => h a (by simp [ha])
    rw [ih h2]
    simp





theorem plan0_sum_share_recipients (r : Request) (hnd : r.recipients.Nodup)
    (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have hlen : 0 < r.recipients.length := by
    have hne2 : r.recipients.length ≠ 0 := by
      intro hz
      have hempty : r.recipients = [] := List.length_eq_zero_iff.mp hz
      exact hne hempty
    omega
  have hcongr : sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => match indexOf? r.recipients a with | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int) | none => 0) := by
    apply sumOver_congr
    intro a ha
    unfold shareOf
    cases hIdx : indexOf? r.recipients a <;> rfl
  rw [hcongr]
  have hshift : ∀ (n : Nat) (g : Nat → Int),
      sumOver (List.range (n+1)) g = g 0 + sumOver (List.range n) (fun i => g (i+1)) := by
    intro n g
    induction n generalizing g with
    | zero => simp
    | succ n ih =>
      have h1 : List.range (n + 1 + 1) = List.range (n+1) ++ [n+1] := List.range_succ
      have e1 := sumOver_append_test (List.range (n+1)) [n+1] g
      have e2 := sumOver_append_test (List.range n) [n] (fun i => g (i+1))
      have h2 : List.range (n+1) = List.range n ++ [n] := List.range_succ
      calc sumOver (List.range (n + 1 + 1)) g
          = sumOver (List.range (n+1)) g + sumOver [n+1] g := by rw [h1]; exact e1
        _ = (g 0 + sumOver (List.range n) (fun i => g (i+1))) + g (n+1) := by
            rw [ih g]
            simp
        _ = g 0 + (sumOver (List.range n) (fun i => g (i+1)) + g (n+1)) := by omega
        _ = g 0 + sumOver (List.range (n+1)) (fun i => g (i+1)) := by
            congr 1
            rw [h2]
            rw [e2]
            simp
  have haux : ∀ (x : Nat) (xs : List Nat) (a : Nat), x ≠ a →
      indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
    intro x xs a h
    simp [indexOf?, h]
  have hreindex : ∀ (l : List AccountId) (hl : l.Nodup) (g : Nat → Int),
      sumOver l (fun a => match indexOf? l a with | some i => g i | none => 0)
        = sumOver (List.range l.length) (fun i => g i) := by
    intro l
    induction l with
    | nil => intro hl g; rfl
    | cons x xs ih =>
      intro hl g
      rw [List.nodup_cons] at hl
      obtain ⟨hxnotin, hxsNodup⟩ := hl
      have hhead : (match indexOf? (x :: xs) x with | some i => g i | none => 0) = g 0 := by
        have h0 : indexOf? (x :: xs) x = some 0 := conserv_idx_cons_self2 x xs
        rw [h0]
      have hEq : ∀ a ∈ xs, (match indexOf? (x :: xs) a with | some i => g i | none => 0)
          = (match indexOf? xs a with | some i => g (i + 1) | none => 0) := by
        intro a ha
        have hxa : x ≠ a := fun h => hxnotin (h ▸ ha)
        have hmap : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := haux x xs a hxa
        rw [hmap]
        cases indexOf? xs a with
        | none => rfl
        | some i => rfl
      have hcongr2 : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0)
          = sumOver xs (fun a => match indexOf? xs a with | some i => g (i + 1) | none => 0) :=
        sumOver_congr xs _ _ hEq
      have hLHS : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0)
          = g 0 + sumOver xs (fun a => match indexOf? xs a with | some i => g (i + 1) | none => 0) := by
        simp only [sumOver_cons, hhead, hcongr2]
      rw [hLHS]
      have hIH := ih hxsNodup (fun i => g (i + 1))
      have hRHS : sumOver (List.range (x :: xs).length) (fun i => g i)
          = g 0 + sumOver (List.range xs.length) (fun i => g (i + 1)) := by
        simp only [List.length_cons]
        exact hshift xs.length g
      rw [hRHS, hIH]
  have hidx := hreindex r.recipients hnd (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int))
  rw [hidx]
  exact conserv_sum_fair_eq2 r.amount r.recipients.length hlen


theorem plan0_sumOver_eq_of_subset (l sub : List AccountId) (hl : l.Nodup) (hsubnd : sub.Nodup)
    (hsub : ∀ x ∈ sub, x ∈ l) (f : AccountId → Int) (hf : ∀ a, a ∉ sub → f a = 0) :
    sumOver l f = sumOver sub f := by
  induction sub generalizing l f with
  | nil =>
    have h0 : ∀ a ∈ l, f a = 0 := fun a _ => hf a (by simp)
    have hl0 := conserv_sum_zero_any l f h0
    simp only [sumOver_nil] at hl0 ⊢
    exact hl0
  | cons y ys ih =>
    rw [List.nodup_cons] at hsubnd
    obtain ⟨hy_notin, hys_nodup⟩ := hsubnd
    have hy_in_l : y ∈ l := hsub y (by simp)
    have hys_sub : ∀ x ∈ ys, x ∈ l := fun x hx => hsub x (by simp [hx])
    let f1 : AccountId → Int := fun a => if a = y then 0 else f a
    have hf1 : ∀ a, a ∉ ys → f1 a = 0 := by
      intro a ha
      simp only [f1]
      by_cases hay : a = y
      · simp [hay]
      · have hnotin : a ∉ y :: ys := by simp [hay, ha]
        have hfa : f a = 0 := hf a hnotin
        simp [hay, hfa]
    have hIH := ih (l := l) (f := f1) hl hys_nodup hys_sub hf1
    have hcongr_ys : sumOver ys f1 = sumOver ys f := by
      apply sumOver_congr
      intro a ha
      have hne : a ≠ y := by
        intro heq
        subst heq
        exact hy_notin ha
      simp only [f1, hne, ↓reduceIte]
    rw [hcongr_ys] at hIH
    have hdecomp : ∀ a ∈ l, f a = (if a = y then f y else 0) + f1 a := by
      intro a _
      simp only [f1]
      by_cases hay : a = y
      · simp [hay]
      · simp [hay]
    have hrewrite : sumOver l f = sumOver l (fun a => (if a = y then f y else 0) + f1 a) :=
      sumOver_congr l f _ hdecomp
    rw [hrewrite, sumOver_add]
    have hite : sumOver l (fun a => if a = y then f y else 0) = f y := by
      rw [sumOver_ite_eq hl y (f y)]
      simp [hy_in_l]
    rw [hite, hIH]
    simp only [sumOver_cons]




theorem plan0_sum_expectedBalance (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = sumOver s.accounts s.balance := by
  obtain ⟨hAccNodup, _, hne, hRecNodup, _, hsrcIn, hSub, _, _, _⟩ := hV
  have hf : ∀ a, a ∉ r.recipients → (shareOf r a : Int) = 0 := by
    intro a ha
    have hidx : indexOf? r.recipients a = none := indexOf?_eq_none ha
    unfold shareOf
    rw [hidx]
    simp
  have hShare : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
    have hTrans : sumOver s.accounts (fun a => (shareOf r a : Int))
        = sumOver r.recipients (fun a => (shareOf r a : Int)) :=
      plan0_sumOver_eq_of_subset s.accounts r.recipients hAccNodup hRecNodup hSub _ hf
    rw [hTrans]
    exact plan0_sum_share_recipients r hRecNodup hne
  have hDebit : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) = (r.amount : Int) := by
    rw [sumOver_ite_eq hAccNodup r.source (r.amount : Int)]
    simp [hsrcIn]
  have hExp : ∀ a ∈ s.accounts, expectedBalance s r a = (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (shareOf r a : Int) := by
    intro a _
    unfold expectedBalance
    rfl
  have hRewrite : sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (shareOf r a : Int)) :=
    sumOver_congr s.accounts _ _ hExp
  rw [hRewrite, sumOver_add, sumOver_sub, hDebit, hShare]
  omega


theorem plan0_sum_fairShare_range_check (m n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare m n i : Nat) : Int)) = (m : Int) :=
  conserv_sum_fair_eq2 m n hn

theorem plan0_sum_fairShare_range (m n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare m n i : Nat) : Int)) = (m : Int) :=
  conserv_sum_fair_eq2 m n hn

theorem probe_range_succ_test (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by
  exact List.range_succ

theorem aux_shift_bar (n : Nat) (g : Nat → Int) :
    sumOver (List.range (n+1)) g = g 0 + sumOver (List.range n) (fun i => g (i+1)) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n+1) ++ [n+1] := List.range_succ
    have e1 := sumOver_append_test (List.range (n+1)) [n+1] g
    have e2 := sumOver_append_test (List.range n) [n] (fun i => g (i+1))
    have h2 : List.range (n+1) = List.range n ++ [n] := List.range_succ
    calc sumOver (List.range (n + 1 + 1)) g
        = sumOver (List.range (n+1)) g + sumOver [n+1] g := by rw [h1]; exact e1
      _ = (g 0 + sumOver (List.range n) (fun i => g (i+1))) + g (n+1) := by
          rw [ih g]
          simp
      _ = g 0 + (sumOver (List.range n) (fun i => g (i+1)) + g (n+1)) := by omega
      _ = g 0 + sumOver (List.range (n+1)) (fun i => g (i+1)) := by
          congr 1
          rw [h2]
          rw [e2]
          simp

theorem plan0_sumOver_indexOf_range_aux (x : Nat) (xs : List Nat) (a : Nat) (h : x ≠ a) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  simp [indexOf?, h]

theorem plan0_sumOver_indexOf_range (l : List AccountId) (hl : l.Nodup) (g : Nat → Int) :
    sumOver l (fun a => match indexOf? l a with | some i => g i | none => 0)
      = sumOver (List.range l.length) (fun i => g i) := by
  induction l generalizing g with
  | nil => rfl
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hxnotin, hxsNodup⟩ := hl
    have hhead : (match indexOf? (x :: xs) x with | some i => g i | none => 0) = g 0 := by
      have h0 : indexOf? (x :: xs) x = some 0 := conserv_idx_cons_self2 x xs
      rw [h0]
    have hEq : ∀ a ∈ xs, (match indexOf? (x :: xs) a with | some i => g i | none => 0)
        = (match indexOf? xs a with | some i => g (i + 1) | none => 0) := by
      intro a ha
      have hxa : x ≠ a := fun h => hxnotin (h ▸ ha)
      have hmap : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) :=
        plan0_sumOver_indexOf_range_aux x xs a hxa
      rw [hmap]
      cases indexOf? xs a with
      | none => rfl
      | some i => rfl
    have hcongr : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0)
        = sumOver xs (fun a => match indexOf? xs a with | some i => g (i + 1) | none => 0) :=
      sumOver_congr xs _ _ hEq
    have hLHS : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0)
        = g 0 + sumOver xs (fun a => match indexOf? xs a with | some i => g (i + 1) | none => 0) := by
      simp only [sumOver_cons, hhead, hcongr]
    rw [hLHS]
    have hIH := ih hxsNodup (fun i => g (i + 1))
    have hRHS : sumOver (List.range (x :: xs).length) (fun i => g i)
        = g 0 + sumOver (List.range xs.length) (fun i => g (i + 1)) := by
      simp only [List.length_cons]
      exact aux_shift_bar xs.length g
    rw [hRHS, hIH]

theorem plan0_share_selfcontained_aux (r : Request) (hnd : r.recipients.Nodup)
    (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have hlen : 0 < r.recipients.length := by
    have hne2 : r.recipients.length ≠ 0 := by
      intro hz
      have hempty : r.recipients = [] := List.length_eq_zero_iff.mp hz
      exact hne hempty
    omega
  have hcongr : sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => match indexOf? r.recipients a with | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int) | none => 0) := by
    apply sumOver_congr
    intro a ha
    unfold shareOf
    cases indexOf? r.recipients a <;> rfl
  rw [hcongr]
  have hshift : ∀ (n : Nat) (g : Nat → Int),
      sumOver (List.range (n+1)) g = g 0 + sumOver (List.range n) (fun i => g (i+1)) := by
    intro n g
    induction n generalizing g with
    | zero => simp
    | succ n ih =>
      have h1 : List.range (n + 1 + 1) = List.range (n+1) ++ [n+1] := List.range_succ
      have e1 := sumOver_append_test (List.range (n+1)) [n+1] g
      have e2 := sumOver_append_test (List.range n) [n] (fun i => g (i+1))
      have h2 : List.range (n+1) = List.range n ++ [n] := List.range_succ
      calc sumOver (List.range (n + 1 + 1)) g
          = sumOver (List.range (n+1)) g + sumOver [n+1] g := by rw [h1]; exact e1
        _ = (g 0 + sumOver (List.range n) (fun i => g (i+1))) + g (n+1) := by
            rw [ih g]
            simp
        _ = g 0 + (sumOver (List.range n) (fun i => g (i+1)) + g (n+1)) := by omega
        _ = g 0 + sumOver (List.range (n+1)) (fun i => g (i+1)) := by
            congr 1
            rw [h2]
            rw [e2]
            simp
  have haux : ∀ (x : Nat) (xs : List Nat) (a : Nat), x ≠ a →
      indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
    intro x xs a h
    simp [indexOf?, h]
  have hreindex : ∀ (l : List AccountId) (hl : l.Nodup) (g : Nat → Int),
      sumOver l (fun a => match indexOf? l a with | some i => g i | none => 0)
        = sumOver (List.range l.length) (fun i => g i) := by
    intro l
    induction l with
    | nil => intro hl g; rfl
    | cons x xs ih =>
      intro hl g
      rw [List.nodup_cons] at hl
      obtain ⟨hxnotin, hxsNodup⟩ := hl
      have hhead : (match indexOf? (x :: xs) x with | some i => g i | none => 0) = g 0 := by
        have h0 : indexOf? (x :: xs) x = some 0 := conserv_idx_cons_self2 x xs
        rw [h0]
      have hEq : ∀ a ∈ xs, (match indexOf? (x :: xs) a with | some i => g i | none => 0)
          = (match indexOf? xs a with | some i => g (i + 1) | none => 0) := by
        intro a ha
        have hxa : x ≠ a := fun h => hxnotin (h ▸ ha)
        have hmap : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := haux x xs a hxa
        rw [hmap]
        cases indexOf? xs a with
        | none => rfl
        | some i => rfl
      have hcongr2 : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0)
          = sumOver xs (fun a => match indexOf? xs a with | some i => g (i + 1) | none => 0) :=
        sumOver_congr xs _ _ hEq
      have hLHS : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0)
          = g 0 + sumOver xs (fun a => match indexOf? xs a with | some i => g (i + 1) | none => 0) := by
        simp only [sumOver_cons, hhead, hcongr2]
      rw [hLHS]
      have hIH := ih hxsNodup (fun i => g (i + 1))
      have hRHS : sumOver (List.range (x :: xs).length) (fun i => g i)
          = g 0 + sumOver (List.range xs.length) (fun i => g (i + 1)) := by
        simp only [List.length_cons]
        exact hshift xs.length g
      rw [hRHS, hIH]
  have hidx := hreindex r.recipients hnd (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int))
  rw [hidx]
  exact conserv_sum_fair_eq2 r.amount r.recipients.length hlen

theorem plan0_sumOver_eq_of_subset_aux (l sub : List AccountId) (hl : l.Nodup) (hsubnd : sub.Nodup)
    (hsub : ∀ x ∈ sub, x ∈ l) (f : AccountId → Int) (hf : ∀ a, a ∉ sub → f a = 0) :
    sumOver l f = sumOver sub f := by
  induction sub generalizing l f with
  | nil =>
    have h0 : ∀ a ∈ l, f a = 0 := fun a _ => hf a (by simp)
    have hl0 := conserv_sum_zero_any l f h0
    simp only [sumOver_nil] at hl0 ⊢
    exact hl0
  | cons y ys ih =>
    rw [List.nodup_cons] at hsubnd
    obtain ⟨hy_notin, hys_nodup⟩ := hsubnd
    have hy_in_l : y ∈ l := hsub y (by simp)
    have hys_sub : ∀ x ∈ ys, x ∈ l := fun x hx => hsub x (by simp [hx])
    let f1 : AccountId → Int := fun a => if a = y then 0 else f a
    have hf1 : ∀ a, a ∉ ys → f1 a = 0 := by
      intro a ha
      simp only [f1]
      by_cases hay : a = y
      · simp [hay]
      · have hnotin : a ∉ y :: ys := by simp [hay, ha]
        have hfa : f a = 0 := hf a hnotin
        simp [hay, hfa]
    have hIH := ih (l := l) (f := f1) hl hys_nodup hys_sub hf1
    have hcongr_ys : sumOver ys f1 = sumOver ys f := by
      apply sumOver_congr
      intro a ha
      have hne : a ≠ y := by
        intro heq
        subst heq
        exact hy_notin ha
      simp only [f1, hne, ↓reduceIte]
    rw [hcongr_ys] at hIH
    have hdecomp : ∀ a ∈ l, f a = (if a = y then f y else 0) + f1 a := by
      intro a _
      simp only [f1]
      by_cases hay : a = y
      · simp [hay]
      · simp [hay]
    have hrewrite : sumOver l f = sumOver l (fun a => (if a = y then f y else 0) + f1 a) :=
      sumOver_congr l f _ hdecomp
    rw [hrewrite, sumOver_add]
    have hite : sumOver l (fun a => if a = y then f y else 0) = f y := by
      rw [sumOver_ite_eq hl y (f y)]
      simp [hy_in_l]
    rw [hite, hIH]
    simp only [sumOver_cons]

theorem plan0_sumOver_eq_of_subset_reprover (l sub : List AccountId) (hl : l.Nodup) (hsubnd : sub.Nodup)
    (hsub : ∀ x ∈ sub, x ∈ l) (f : AccountId → Int) (hf : ∀ a, a ∉ sub → f a = 0) :
    sumOver l f = sumOver sub f :=
  plan0_sumOver_eq_of_subset_aux l sub hl hsubnd hsub f hf

theorem plan0_subset_direct (l sub : List AccountId) (hl : l.Nodup) (hsubnd : sub.Nodup)
    (hsub : ∀ x ∈ sub, x ∈ l) (f : AccountId → Int) (hf : ∀ a, a ∉ sub → f a = 0) :
    sumOver l f = sumOver sub f := by
  induction sub generalizing l f with
  | nil =>
    have h0 : ∀ a ∈ l, f a = 0 := fun a _ => hf a (by simp)
    have hl0 := conserv_sum_zero_any l f h0
    simp only [sumOver_nil] at hl0 ⊢
    exact hl0
  | cons y ys ih =>
    rw [List.nodup_cons] at hsubnd
    obtain ⟨hy_notin, hys_nodup⟩ := hsubnd
    have hy_in_l : y ∈ l := hsub y (by simp)
    have hys_sub : ∀ x ∈ ys, x ∈ l := fun x hx => hsub x (by simp [hx])
    let f1 : AccountId → Int := fun a => if a = y then 0 else f a
    have hf1 : ∀ a, a ∉ ys → f1 a = 0 := by
      intro a ha
      simp only [f1]
      by_cases hay : a = y
      · simp [hay]
      · have hnotin : a ∉ y :: ys := by simp [hay, ha]
        have hfa : f a = 0 := hf a hnotin
        simp [hay, hfa]
    have hIH := ih (l := l) (f := f1) hl hys_nodup hys_sub hf1
    have hcongr_ys : sumOver ys f1 = sumOver ys f := by
      apply sumOver_congr
      intro a ha
      have hne : a ≠ y := by
        intro heq
        subst heq
        exact hy_notin ha
      simp only [f1, hne, ↓reduceIte]
    rw [hcongr_ys] at hIH
    have hdecomp : ∀ a ∈ l, f a = (if a = y then f y else 0) + f1 a := by
      intro a _
      simp only [f1]
      by_cases hay : a = y
      · simp [hay]
      · simp [hay]
    have hrewrite : sumOver l f = sumOver l (fun a => (if a = y then f y else 0) + f1 a) :=
      sumOver_congr l f _ hdecomp
    rw [hrewrite, sumOver_add]
    have hite : sumOver l (fun a => if a = y then f y else 0) = f y := by
      rw [sumOver_ite_eq hl y (f y)]
      simp [hy_in_l]
    rw [hite, hIH]
    simp only [sumOver_cons]

theorem plan0_sum_share_accounts (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  obtain ⟨hAccNodup, _, hne, hRecNodup, _, _, hSub, _, _, _⟩ := hV
  have hf : ∀ a, a ∉ r.recipients → (shareOf r a : Int) = 0 := by
    intro a ha
    have hidx : indexOf? r.recipients a = none := indexOf?_eq_none ha
    unfold shareOf
    rw [hidx]
    simp
  have hTrans : sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => (shareOf r a : Int)) :=
    plan0_subset_direct s.accounts r.recipients hAccNodup hRecNodup hSub _ hf
  rw [hTrans]
  exact plan0_sum_share_recipients r hRecNodup hne

theorem plan0_sum_expectedBalance_check (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = sumOver s.accounts s.balance := by
  have hShare : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
    plan0_sum_share_accounts s r hV
  obtain ⟨hAccNodup, _, _, _, _, hsrcIn, _, _, _, _⟩ := hV
  have hDebit : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) = (r.amount : Int) := by
    rw [sumOver_ite_eq hAccNodup r.source (r.amount : Int)]
    simp [hsrcIn]
  have hExp : ∀ a ∈ s.accounts, expectedBalance s r a = (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (shareOf r a : Int) := by
    intro a _
    unfold expectedBalance
    rfl
  have hRewrite : sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (shareOf r a : Int)) :=
    sumOver_congr s.accounts _ _ hExp
  rw [hRewrite, sumOver_add, sumOver_sub, hDebit, hShare]
  omega

theorem plan0_sum_expectedBalance_fwdcheck (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = sumOver s.accounts s.balance := by
  obtain ⟨hAccNodup, _, hne, hRecNodup, _, hsrcIn, hSub, _, _, _⟩ := hV
  have hf : ∀ a, a ∉ r.recipients → (shareOf r a : Int) = 0 := by
    intro a ha
    have hidx : indexOf? r.recipients a = none := indexOf?_eq_none ha
    unfold shareOf
    rw [hidx]
    simp
  have hShare : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
    have hTrans : sumOver s.accounts (fun a => (shareOf r a : Int))
        = sumOver r.recipients (fun a => (shareOf r a : Int)) :=
      plan0_sumOver_eq_of_subset s.accounts r.recipients hAccNodup hRecNodup hSub _ hf
    rw [hTrans]
    exact plan0_sum_share_recipients r hRecNodup hne
  have hDebit : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) = (r.amount : Int) := by
    rw [sumOver_ite_eq hAccNodup r.source (r.amount : Int)]
    simp [hsrcIn]
  have hExp : ∀ a ∈ s.accounts, expectedBalance s r a = (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (shareOf r a : Int) := by
    intro a _
    unfold expectedBalance
    rfl
  have hRewrite : sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (shareOf r a : Int)) :=
    sumOver_congr s.accounts _ _ hExp
  rw [hRewrite, sumOver_add, sumOver_sub, hDebit, hShare]
  omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hV : ValidPayout s r
  · unfold ValidPayout at hV
    obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hV
    exact hauth
  · simp [hV] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hV : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (match indexOf? r.recipients a with | some i => (fairShare r.amount r.recipients.length i : Int) | none => 0), applied := r.txId :: s.applied }) := by
      unfold step
      simp [hV]
    rw [hstep]
    refine ⟨rfl, rfl, fun a => ?_⟩
    simp only [expectedBalance, shareOf]
    cases hIdx : indexOf? r.recipients a <;> rfl
  · unfold step at h
    simp [hV] at h

theorem req_idempotency : Idempotent step := by
  intro s r h
  by_cases hV : ValidPayout s r
  · have happs : (step s r).2.applied = r.txId :: s.applied := by
      unfold step
      simp [hV]
    have hV2 : ¬ ValidPayout (step s r).2 r := by
      intro hCon
      obtain ⟨_, _, _, _, _, _, _, _, _, hFresh⟩ := hCon
      exact hFresh (happs ▸ List.mem_cons.mpr (Or.inl rfl))
    exact ⟨fun x => by rw [happs]; simp, req_invalid_noop _ _ hV2⟩
  · unfold step at h
    simp [hV] at h

theorem req_nonnegative : NonNegative step := by
  intro s r hNonneg a ha
  by_cases hV : ValidPayout s r
  · have hok : (step s r).1 = Outcome.ok := by unfold step; simp [hV]
    have heff := req_effects s r hok
    obtain ⟨haccEq, _, hbalEq⟩ := heff
    have hmem : a ∈ s.accounts := haccEq ▸ ha
    have h0 : 0 ≤ s.balance a := hNonneg a hmem
    have hbal : (step s r).2.balance a = expectedBalance s r a := hbalEq a
    rw [hbal]
    obtain ⟨_, _, _, _, hsrcNot, _, _, _, hle, _⟩ := hV
    unfold expectedBalance shareOf
    by_cases heq : a = r.source
    · subst heq
      have hidx : indexOf? r.recipients r.source = none :=
        indexOf?_eq_none hsrcNot
      rw [hidx]
      simp
      omega
    · simp [heq]
      cases hX : indexOf? r.recipients a
      · simp
        omega
      · simp
        omega
  · have hstep : step s r = (.rejected, s) := req_invalid_noop s r hV
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have hbaleq : (step s r).2.balance = s.balance := by rw [hstep]
    rw [hacc] at ha
    rw [hbaleq]
    exact hNonneg a ha

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  have hV : ValidPayout s r := by
    by_cases hN : ValidPayout s r
    · exact hN
    · have hstep := req_invalid_noop s r hN
      rw [hstep] at hok
      simp at hok
  obtain ⟨_, _, _, hnodup, hsrcNot, _, _, _, _, _⟩ := hV
  have heff := req_effects s r hok
  obtain ⟨_, _, hbalEq⟩ := heff
  have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := hbalEq _
  have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hne_src : r.recipients[i] ≠ r.source := fun h => hsrcNot (h ▸ hmem)
  have hidx : indexOf? r.recipients r.recipients[i] = some i :=
    indexOf?_getElem hnodup i hi
  have hshare : shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
    unfold shareOf
    rw [hidx]
  have hexp : expectedBalance s r r.recipients[i] = s.balance r.recipients[i] + (fairShare r.amount r.recipients.length i : Int) := by
    unfold expectedBalance
    rw [if_neg hne_src, hshare]
    simp
  rw [hexp] at hbal
  omega

theorem req_conservation   : Conserves step := by
  intro s r hok
  by_cases hV : ValidPayout s r
  · have heff := req_effects s r hok
    obtain ⟨haccEq, _, hbalEq⟩ := heff
    unfold total
    rw [haccEq]
    have hcongr : sumOver s.accounts (step s r).2.balance
        = sumOver s.accounts (fun a => expectedBalance s r a) :=
      sumOver_congr s.accounts _ _ (fun a _ => hbalEq a)
    rw [hcongr]
    exact plan0_sum_expectedBalance_check s r hV
  · have hstep := req_invalid_noop s r hV
    rw [hstep] at hok
    simp at hok

end Payout
