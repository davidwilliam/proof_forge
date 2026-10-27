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

theorem foo_test : True := trivial

theorem step_ok_imp_valid (s : State) (r : Request) (h : (step s r).1 = .ok) : ValidPayout s r := by
  unfold step at h
  by_cases hv : ValidPayout s r
  · exact hv
  · simp [hv] at h

theorem sumOver_append_test (l1 l2 : List Nat) (f : Nat → Int) : sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a t ih => simp [ih]; omega

theorem sum_append2 (l1 l2 : List Nat) (f : Nat → Int) : sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a t ih => simp [ih]; omega

theorem range_append_test (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]

theorem aux_range_append (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by
  simp [List.range_succ]

theorem aux_sum_append (l1 l2 : List Nat) (f : Nat → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a t ih => simp only [List.cons_append, sumOver_cons, ih]; omega

theorem aux_range_succ (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n+1)) f = sumOver (List.range n) f + f n := by
  rw [aux_range_append, aux_sum_append]
  simp

theorem t1 (n : Nat) (c : Int) : (↑n + 1) * c = ↑n * c + c := by
  simp only [Int.add_mul, Int.one_mul]

theorem plan0_sumOver_erase_eq (l : List Nat) (f : Nat → Int) (a : Nat)
    (hl : l.Nodup) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [sumOver_cons]
    by_cases hxa : x = a
    · subst hxa
      simp
    · have hmem : a ∈ xs := by
        cases List.mem_cons.mp ha with
        | inl h_eq => exact absurd h_eq.symm hxa
        | inr h_mem => exact h_mem
      have hl' : xs.Nodup := (List.nodup_cons.mp hl).2
      have ih' := ih hl' hmem
      have herase : (x :: xs).erase a = x :: xs.erase a := by simp [hxa]
      rw [herase, sumOver_cons]
      omega




theorem plan0_sum_range_shift_succ (f : Nat → Int) (n : Nat) :
    f 0 + sumOver (List.range n) (fun i => f (i + 1))
      = sumOver (List.range (n + 1)) f := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : sumOver (List.range (n+1)) (fun i => f (i+1))
      = sumOver (List.range n) (fun i => f (i+1)) + f (n+1) := by
      have := aux_range_succ n (fun i => f (i+1))
      simpa using this
    have h2 : sumOver (List.range (n+1+1)) f
      = sumOver (List.range (n+1)) f + f (n+1) := by
      have := aux_range_succ (n+1) f
      simpa using this
    omega


theorem plan0_sumOver_indexOf_fairShare_offset (l : List Nat)
    (amount n offset : Nat) (hl : l.Nodup) :
    sumOver l (fun a => match indexOf? l a with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0)
      = sumOver (List.range l.length)
          (fun i => (fairShare amount n (offset + i) : Int)) := by
  induction l generalizing offset with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotmem, hnodup⟩ := hl
    have hhead : (match indexOf? (x :: xs) x with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0) = (fairShare amount n (offset + 0) : Int) := by
      simp [indexOf?]
    have htail : sumOver xs (fun a => match indexOf? (x :: xs) a with
        | some i => (fairShare amount n (offset + i) : Int)
        | none => 0)
      = sumOver xs (fun a => match indexOf? xs a with
        | some i => (fairShare amount n ((offset + 1) + i) : Int)
        | none => 0) := by
      apply sumOver_congr
      intro a ha
      have hxa : x ≠ a := by
        intro heq; subst heq; exact hnotmem ha
      have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
        simp [indexOf?, hxa]
      rw [hidx]
      cases hxs : indexOf? xs a with
      | none => rfl
      | some v =>
        simp only [Option.map_some]
        have heq : offset + (v + 1) = (offset + 1) + v := by omega
        rw [heq]
    have hLHS : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with
        | some i => (fairShare amount n (offset + i) : Int)
        | none => 0)
      = (fairShare amount n (offset + 0) : Int) + sumOver xs (fun a => match indexOf? xs a with
        | some i => (fairShare amount n ((offset + 1) + i) : Int)
        | none => 0) := by
      simp only [sumOver_cons]
      rw [hhead, htail]
    rw [hLHS]
    have hIH := ih (offset + 1) hnodup
    have hshift := plan0_sum_range_shift_succ (fun i => (fairShare amount n (offset + i) : Int)) xs.length
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    have hcongr : sumOver (List.range xs.length) (fun i => (fairShare amount n (offset + (i + 1)) : Int))
      = sumOver (List.range xs.length) (fun i => (fairShare amount n ((offset + 1) + i) : Int)) := by
      apply sumOver_congr
      intro a ha
      congr 1
      congr 1
      omega
    rw [hlen]
    omega


theorem plan0_sum_range_const (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := aux_range_succ n (fun _ => c)
    rw [h, ih]
    push_cast
    exact (t1 n c).symm


theorem plan0_sum_range_if_lt (n m : Nat) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0)
      = ((min m n : Nat) : Int) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := aux_range_succ n (fun i => if i < m then (1 : Int) else 0)
    rw [h, ih]
    by_cases hn : n < m
    · simp only [hn, ↓reduceIte]
      omega
    · simp only [hn, ↓reduceIte, Int.add_zero]
      omega


theorem erase_test1 (x : Nat) (xs : List Nat) : (x :: xs).erase x = xs := by
  simp

theorem erase_test2 (a : Nat) (xs : List Nat) : (a :: xs).erase a = xs := by
  simp

theorem erase_test3 (x a : Nat) (xs : List Nat) (h : x ≠ a) : (x :: xs).erase a = x :: xs.erase a := by
  simp [h]

theorem erase_probe (x a : Nat) (xs : List Nat) (h : x ≠ a) : (x :: xs).erase a = x :: (xs.erase a) := by
  simp [h]

theorem erase_probe2 (y b : Nat) (ys : List Nat) (h2 : y ≠ b) : (y :: ys).erase b = y :: ys.erase b := by
  simp [h2]

theorem plan0_sumOver_erase_eq_fix3 (l : List Nat) (f : Nat → Int) (a : Nat)
    (hl : l.Nodup) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [sumOver_cons]
    by_cases hxa : x = a
    · subst hxa
      simp
    · have hmem : a ∈ xs := by
        cases List.mem_cons.mp ha with
        | inl h_eq => exact absurd h_eq.symm hxa
        | inr h_mem => exact h_mem
      have hl' : xs.Nodup := (List.nodup_cons.mp hl).2
      have ih' := ih hl' hmem
      have herase : (x :: xs).erase a = x :: xs.erase a := by simp [hxa]
      rw [herase, sumOver_cons]
      omega

theorem erase_mem_of_mem {l : List Nat} {a b : Nat} (h : a ∈ l.erase b) : a ∈ l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hxb : x = b
    · subst hxb
      simp at h ⊢
      exact Or.inr h
    · have her : (x :: xs).erase b = x :: (xs.erase b) := by simp [hxb]
      rw [her] at h
      simp at h ⊢
      cases h with
      | inl heq => exact Or.inl heq
      | inr hmem => exact Or.inr (ih hmem)

theorem probe_nodup_erase (l : List Nat) (a : Nat) (h : l.Nodup) : (l.erase a).Nodup := by
  exact h.sublist List.erase_sublist
#check probe_nodup_erase

theorem probe_erase_simp1 (x : Nat) (xs : List Nat) : (x :: xs).erase x = xs := by simp

theorem probe_erase_simp2 (x y : Nat) (xs : List Nat) (h : x ≠ y) : (x :: xs).erase y = x :: xs.erase y := by simp [h]

theorem mem_erase_of_mem_ne_aux (l : List Nat) : ∀ (x y : Nat), x ∈ l → x ≠ y → x ∈ l.erase y := by
  induction l with
  | nil =>
    intro x y hmem hne
    simp at hmem
  | cons z zs ih =>
    intro x y hmem hne
    simp at hmem
    cases hmem with
    | inl heq =>
      have hzy : z ≠ y := by rw [← heq]; exact hne
      have her : (z :: zs).erase y = z :: (zs.erase y) := by simp [hzy]
      rw [her]
      simp [heq]
    | inr hmem2 =>
      by_cases hzy : z = y
      · subst hzy
        simp
        exact hmem2
      · have her : (z :: zs).erase y = z :: (zs.erase y) := by simp [hzy]
        rw [her]
        simp
        exact Or.inr (ih x y hmem2 hne)

theorem erase_ne_of_mem_erase_aux2 (l : List Nat) (x y : Nat) (hl : l.Nodup) (hmem : x ∈ l.erase y) : x ≠ y := by
  induction l with
  | nil => simp at hmem
  | cons z zs ih =>
    rw [List.nodup_cons] at hl
    by_cases hzy : z = y
    · subst hzy
      simp at hmem
      intro hxy
      subst hxy
      exact hl.1 hmem
    · have her : (z :: zs).erase y = z :: (zs.erase y) := by simp [hzy]
      rw [her] at hmem
      simp at hmem
      cases hmem with
      | inl heq => rw [heq]; exact hzy
      | inr hmem2 => exact ih hl.2 hmem2



theorem plan1_nodup_erase (l : List Nat) (a : Nat) (h : l.Nodup) :
    (l.erase a).Nodup := by exact h.sublist List.erase_sublist


theorem plan1_mem_erase_of_mem_ne (l : List Nat) (x y : Nat)
    (hmem : x ∈ l) (hne : x ≠ y) :
    x ∈ l.erase y := by
  exact mem_erase_of_mem_ne_aux l x y hmem hne




theorem plan1_sumOver_erase_eq (l : List Nat) (f : Nat → Int) (a : Nat)
    (hl : l.Nodup) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [sumOver_cons]
    by_cases hxa : x = a
    · subst hxa
      simp
    · have hmem : a ∈ xs := by
        cases List.mem_cons.mp ha with
        | inl h_eq => exact absurd h_eq.symm hxa
        | inr h_mem => exact h_mem
      have hl' : xs.Nodup := (List.nodup_cons.mp hl).2
      have ih' := ih hl' hmem
      have herase : (x :: xs).erase a = x :: xs.erase a := by simp [hxa]
      rw [herase, sumOver_cons]
      omega




theorem plan1_sumOver_eq_zero (l : List Nat) (f : Nat → Int)
    (h : ∀ x ∈ l, f x = 0) :
    sumOver l f = 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [sumOver_cons]
    have hx : f x = 0 := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    omega

theorem plan1_nodup_erase_test (l : List Nat) (a : Nat) (h : l.Nodup) :
    (l.erase a).Nodup := by exact h.sublist List.erase_sublist

theorem plan1_mem_erase_of_mem_ne_check (l : List Nat) (x y : Nat)
    (hmem : x ∈ l) (hne : x ≠ y) :
    x ∈ l.erase y := by
  exact mem_erase_of_mem_ne_aux l x y hmem hne

theorem plan1_mem_of_mem_erase_of_nodup (l : List Nat) (x y : Nat)
    (hl : l.Nodup) (h : x ∈ l.erase y) :
    x ∈ l ∧ x ≠ y := by
  constructor
  · exact erase_mem_of_mem h
  · exact erase_ne_of_mem_erase_aux2 l x y hl h

theorem plan1_sumOver_erase_eq_test (l : List Nat) (f : Nat → Int) (a : Nat)
    (hl : l.Nodup) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [sumOver_cons]
    by_cases hxa : x = a
    · subst hxa
      simp
    · have hmem : a ∈ xs := by
        cases List.mem_cons.mp ha with
        | inl h_eq => exact absurd h_eq.symm hxa
        | inr h_mem => exact h_mem
      have hl' : xs.Nodup := (List.nodup_cons.mp hl).2
      have ih' := ih hl' hmem
      have herase : (x :: xs).erase a = x :: xs.erase a := by simp [hxa]
      rw [herase, sumOver_cons]
      omega

theorem plan1_erase_preserves_support (big small : List Nat) (f : Nat → Int)
    (a : Nat) (hbig : big.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hne : ∀ x ∈ small, x ≠ a)
    (hzero : ∀ x ∈ big, x ∉ a :: small → f x = 0) :
    (∀ x ∈ small, x ∈ big.erase a) ∧
      (∀ x ∈ big.erase a, x ∉ small → f x = 0) := by
  constructor
  · intro x hx
    exact mem_erase_of_mem_ne_aux big x a (hsub x hx) (hne x hx)
  · intro x hxmem hxnot
    have hbigmem : x ∈ big := erase_mem_of_mem hxmem
    have hne' : x ≠ a := erase_ne_of_mem_erase_aux2 big x a hbig hxmem
    apply hzero x hbigmem
    simp [hne', hxnot]

theorem plan0_sumOver_eq_of_subset_support_aux (big small : List Nat) (f : Nat → Int)
    (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hzero : ∀ x ∈ big, x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by
  induction small generalizing big with
  | nil =>
    have hz : ∀ x ∈ big, f x = 0 := by
      intro x hx
      exact hzero x hx (by simp)
    have h1 : sumOver big f = 0 := plan1_sumOver_eq_zero big f hz
    simp [h1]
  | cons a small' ih =>
    have hsmall_cons : (a :: small').Nodup := hsmall
    rw [List.nodup_cons] at hsmall_cons
    obtain ⟨hnotmem, hsmall'_nodup⟩ := hsmall_cons
    have ha_big : a ∈ big := hsub a (by simp)
    have hsplit : sumOver big f = f a + sumOver (big.erase a) f :=
      plan1_sumOver_erase_eq big f a hbig ha_big
    have hne : ∀ x ∈ small', x ≠ a := by
      intro x hxmem heq
      subst heq
      exact hnotmem hxmem
    have hsub' : ∀ x ∈ small', x ∈ big := by
      intro x hx
      exact hsub x (by simp [hx])
    have hzero_cons : ∀ x ∈ big, x ∉ a :: small' → f x = 0 := hzero
    have hpres := plan1_erase_preserves_support big small' f a hbig hsub' hne hzero_cons
    obtain ⟨hsub_erase, hzero_erase⟩ := hpres
    have ih_eq := ih (big.erase a) (plan1_nodup_erase big a hbig) hsmall'_nodup hsub_erase hzero_erase
    simp only [sumOver_cons]
    omega

theorem plan0_sumOver_eq_of_subset_support (big small : List Nat) (f : Nat → Int)
    (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hzero : ∀ x ∈ big, x ∉ small → f x = 0) :
    sumOver big f = sumOver small f :=
  plan0_sumOver_eq_of_subset_support_aux big small f hbig hsmall hsub hzero

theorem plan0_sum_range_shift_succ_aux2 (f : Nat → Int) (n : Nat) :
    f 0 + sumOver (List.range n) (fun i => f (i + 1))
      = sumOver (List.range (n + 1)) f := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : sumOver (List.range (n+1)) (fun i => f (i+1))
      = sumOver (List.range n) (fun i => f (i+1)) + f (n+1) := by
      have := aux_range_succ n (fun i => f (i+1))
      simpa using this
    have h2 : sumOver (List.range (n+1+1)) f
      = sumOver (List.range (n+1)) f + f (n+1) := by
      have := aux_range_succ (n+1) f
      simpa using this
    omega

theorem plan0_sum_range_shift_succ_fix (f : Nat → Int) (n : Nat) :
    f 0 + sumOver (List.range n) (fun i => f (i + 1))
      = sumOver (List.range (n + 1)) f :=
  plan0_sum_range_shift_succ_aux2 f n

theorem plan0_shift_inline_check (f : Nat → Int) (n : Nat) :
    f 0 + sumOver (List.range n) (fun i => f (i + 1))
      = sumOver (List.range (n + 1)) f := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : sumOver (List.range (n+1)) (fun i => f (i+1))
      = sumOver (List.range n) (fun i => f (i+1)) + f (n+1) := by
      have := aux_range_succ n (fun i => f (i+1))
      simpa using this
    have h2 : sumOver (List.range (n+1+1)) f
      = sumOver (List.range (n+1)) f + f (n+1) := by
      have := aux_range_succ (n+1) f
      simpa using this
    omega

theorem tmp_index_cons_self2 (x : Nat) (xs : List Nat) :
    indexOf? (x :: xs) x = some 0 := by
  unfold indexOf?
  simp

theorem tmp_idx_cons_eq (x : Nat) (xs : List Nat) (a : Nat) (h : a ∈ xs) (hx : x ∉ xs) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  simp only [indexOf?]
  have hxa : ¬ (x = a) := by
    intro heq
    subst heq
    exact hx h
  simp [hxa]

theorem tmp_map_match (o : Option Nat) (g : Nat → Int) :
    (match o.map (· + 1) with | some i => g i | none => 0)
      = (match o with | some i => g (i + 1) | none => 0) := by
  cases o with
  | none => rfl
  | some v => rfl

theorem tmp_probe_shift (offset amount n m : Nat) :
    (plan0_sum_range_shift_succ_aux2
        (fun i => (fairShare amount n (offset + i) : Int)) m)
    = (plan0_sum_range_shift_succ_aux2
        (fun i => (fairShare amount n (offset + i) : Int)) m) := by
  rfl

theorem tmp_sum_cons_check (x : Nat) (xs : List Nat) (offset amount n : Nat) :
    sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0)
    = (match indexOf? (x :: xs) x with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0) + sumOver xs (fun a => match indexOf? (x :: xs) a with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0) := by
  rw [sumOver_cons]

theorem tmp_beta_test (offset amount n : Nat) :
    (fun i => (fairShare amount n (offset + i) : Int)) 0 = (fairShare amount n (offset + 0) : Int) := by
  rfl



theorem plan2_indexOf_cons_ne (x a : Nat) (xs : List Nat) (h : x ≠ a) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by simp [indexOf?, h]




theorem plan2_sumOver_tail_index_shift (x : Nat) (xs : List Nat)
    (amount n offset : Nat) (h : x ∉ xs) :
    sumOver xs (fun a => match indexOf? (x :: xs) a with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0)
      =
    sumOver xs (fun a => match indexOf? xs a with
      | some i => (fairShare amount n ((offset + 1) + i) : Int)
      | none => 0) := by
  apply sumOver_congr
  intro a ha
  have hxa : x ≠ a := by
    intro heq
    subst heq
    exact h ha
  have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
    simp [indexOf?, hxa]
  rw [hidx]
  cases hxs : indexOf? xs a with
  | none => rfl
  | some v =>
    simp only [Option.map_some]
    have heq : offset + (v + 1) = (offset + 1) + v := by omega
    rw [heq]




theorem plan2_indexOf_cons_self (x : Nat) (xs : List Nat) :
    indexOf? (x :: xs) x = some 0 := by
  simp [indexOf?]

theorem plan2_indexOf_cons_ne_aux_unique (x a : Nat) (xs : List Nat) (h : x ≠ a) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  simp [indexOf?, h]

theorem plan2_match_map_add_one (o : Option Nat) (g : Nat → Int) :
    (match o.map (· + 1) with
     | some i => g i
     | none => (0 : Int))
      =
    (match o with
     | some i => g (i + 1)
     | none => (0 : Int)) := by
  cases o with
  | none => rfl
  | some v => rfl

theorem plan2_sumOver_tail_index_shift_proof (x : Nat) (xs : List Nat)
    (amount n offset : Nat) (h : x ∉ xs) :
    sumOver xs (fun a => match indexOf? (x :: xs) a with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0)
      =
    sumOver xs (fun a => match indexOf? xs a with
      | some i => (fairShare amount n ((offset + 1) + i) : Int)
      | none => 0) := by
  apply sumOver_congr
  intro a ha
  have hxa : x ≠ a := by
    intro heq
    subst heq
    exact h ha
  have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
    simp [indexOf?, hxa]
  rw [hidx]
  cases hxs : indexOf? xs a with
  | none => rfl
  | some v =>
    simp only [Option.map_some]
    have heq : offset + (v + 1) = (offset + 1) + v := by omega
    rw [heq]

theorem plan2_range_sum_shift (f : Nat → Int) (m : Nat) :
    sumOver (List.range (m + 1)) f
      = f 0 + sumOver (List.range m) (fun i => f (i + 1)) := by
  exact (plan0_sum_range_shift_succ_aux2 f m).symm

theorem my_rhs_helper (xs : List Nat) (amount n offset : Nat) :
    sumOver (List.range (xs.length + 1))
        (fun i => (fairShare amount n (offset + i) : Int))
      = (fairShare amount n (offset + 0) : Int) + sumOver (List.range xs.length)
          (fun i => (fairShare amount n ((offset + 1) + i) : Int)) := by
  have hshift := plan2_range_sum_shift (fun i => (fairShare amount n (offset + i) : Int)) xs.length
  rw [hshift]
  congr 1
  apply sumOver_congr
  intro a ha
  congr 1
  congr 1
  omega

theorem my_offset_proof2 (l : List Nat)
    (amount n offset : Nat) (hl : l.Nodup) :
    sumOver l (fun a => match indexOf? l a with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0)
      = sumOver (List.range l.length)
          (fun i => (fairShare amount n (offset + i) : Int)) := by
  induction l generalizing offset with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotmem, hnodup⟩ := hl
    have hhead : (match indexOf? (x :: xs) x with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0) = (fairShare amount n (offset + 0) : Int) := by
      rw [plan2_indexOf_cons_self]
    have hLHS : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with
        | some i => (fairShare amount n (offset + i) : Int)
        | none => 0)
      = (fairShare amount n (offset + 0) : Int) + sumOver xs (fun a => match indexOf? xs a with
        | some i => (fairShare amount n ((offset + 1) + i) : Int)
        | none => 0) := by
      simp only [sumOver_cons]
      rw [hhead, plan2_sumOver_tail_index_shift x xs amount n offset hnotmem]
    rw [hLHS]
    have hIH := ih (offset + 1) hnodup
    have hRHS := my_rhs_helper xs amount n offset
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    rw [hlen, hRHS, hIH]

theorem my_test_offset2 (l : List Nat)
    (amount n offset : Nat) (hl : l.Nodup) :
    sumOver l (fun a => match indexOf? l a with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0)
      = sumOver (List.range l.length)
          (fun i => (fairShare amount n (offset + i) : Int)) := by
  induction l generalizing offset with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotmem, hnodup⟩ := hl
    have hhead : (match indexOf? (x :: xs) x with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0) = (fairShare amount n (offset + 0) : Int) := by
      simp [indexOf?]
    have htail : sumOver xs (fun a => match indexOf? (x :: xs) a with
        | some i => (fairShare amount n (offset + i) : Int)
        | none => 0)
      = sumOver xs (fun a => match indexOf? xs a with
        | some i => (fairShare amount n ((offset + 1) + i) : Int)
        | none => 0) := by
      apply sumOver_congr
      intro a ha
      have hxa : x ≠ a := by
        intro heq; subst heq; exact hnotmem ha
      have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
        simp [indexOf?, hxa]
      rw [hidx]
      cases hxs : indexOf? xs a with
      | none => rfl
      | some v =>
        simp only [Option.map_some]
        have heq : offset + (v + 1) = (offset + 1) + v := by omega
        rw [heq]
    have hLHS : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with
        | some i => (fairShare amount n (offset + i) : Int)
        | none => 0)
      = (fairShare amount n (offset + 0) : Int) + sumOver xs (fun a => match indexOf? xs a with
        | some i => (fairShare amount n ((offset + 1) + i) : Int)
        | none => 0) := by
      simp only [sumOver_cons]
      rw [hhead, htail]
    rw [hLHS]
    have hIH := ih (offset + 1) hnodup
    have hshift := plan0_sum_range_shift_succ (fun i => (fairShare amount n (offset + i) : Int)) xs.length
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    have hcongr : sumOver (List.range xs.length) (fun i => (fairShare amount n (offset + (i + 1)) : Int))
      = sumOver (List.range xs.length) (fun i => (fairShare amount n ((offset + 1) + i) : Int)) := by
      apply sumOver_congr
      intro a ha
      congr 1
      congr 1
      omega
    rw [hlen]
    omega

theorem plan0_sum_range_const_aux_check2 (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := aux_range_succ n (fun _ => c)
    rw [h, ih]
    push_cast
    exact (t1 n c).symm

theorem my_sum_range_if_lt_test (n m : Nat) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0)
      = ((min m n : Nat) : Int) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := aux_range_succ n (fun i => if i < m then (1 : Int) else 0)
    rw [h, ih]
    by_cases hn : n < m
    · simp only [hn, ↓reduceIte]
      omega
    · simp only [hn, ↓reduceIte, Int.add_zero]
      omega

theorem fairShare_int2 (amount n i : Nat) :
    ((fairShare amount n i : Nat) : Int) = ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) := by
  unfold fairShare
  by_cases h : i < amount % n <;> simp [h]

theorem cast_probe1 (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp

theorem cast_probe2 (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by simp
#check Nat.div_add_mod

theorem sum_range_fair_aux2 (r : Request) (hn : 0 < r.recipients.length) :
    ((r.recipients.length : Nat) : Int) * (((r.amount / r.recipients.length : Nat)) : Int) + (((r.amount % r.recipients.length : Nat)) : Int) = ((r.amount : Nat) : Int) := by
  have hpos : 0 < r.recipients.length := hn
  have hdiv : r.recipients.length * (r.amount / r.recipients.length) + r.amount % r.recipients.length = r.amount := Nat.div_add_mod r.amount r.recipients.length
  have hcast : (((r.recipients.length * (r.amount / r.recipients.length) + r.amount % r.recipients.length : Nat)) : Int) = (((r.amount : Nat)) : Int) := by rw [hdiv]
  simp at hcast
  exact hcast

theorem sum_range_fair_full2 (r : Request) (hn : 0 < r.recipients.length) :
    sumOver (List.range r.recipients.length) (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int)) = (r.amount : Int) := by
  have hsplit : sumOver (List.range r.recipients.length) (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int))
    = sumOver (List.range r.recipients.length) (fun _ => (((r.amount / r.recipients.length : Nat)) : Int))
      + sumOver (List.range r.recipients.length) (fun i => (if i < r.amount % r.recipients.length then (1 : Int) else 0)) := by
    rw [← sumOver_add]
    apply sumOver_congr
    intro a ha
    rw [fairShare_int2]
  rw [hsplit, plan0_sum_range_const, my_sum_range_if_lt_test]
  have hmod_lt : r.amount % r.recipients.length < r.recipients.length := Nat.mod_lt _ hn
  have hmin : min (r.amount % r.recipients.length) r.recipients.length = r.amount % r.recipients.length := Nat.min_eq_left (Nat.le_of_lt hmod_lt)
  rw [hmin]
  have hdiv := sum_range_fair_aux2 r hn
  exact hdiv

theorem shareOf_match_int (r : Request) (a : AccountId) :
    ((shareOf r a : Nat) : Int) = match indexOf? r.recipients a with
      | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int)
      | none => (0 : Int) := by
  unfold shareOf
  cases h : indexOf? r.recipients a <;> rfl

theorem credit_sum_eq3 (s : State) (r : Request) (hNodupAcc : s.accounts.Nodup) (hNodupRec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) (hne : r.recipients ≠ []) :
    sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) = (r.amount : Int) := by
  have hzero : ∀ x ∈ s.accounts, x ∉ r.recipients → (fun a => ((shareOf r a : Nat) : Int)) x = 0 := by
    intro x hxmem hxnot
    simp only
    rw [shareOf_match_int]
    rw [indexOf?_eq_none hxnot]
  have hsup := plan0_sumOver_eq_of_subset_support s.accounts r.recipients (fun a => ((shareOf r a : Nat) : Int)) hNodupAcc hNodupRec hsub hzero
  rw [hsup]
  have hcongr : sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int))
    = sumOver r.recipients (fun a => match indexOf? r.recipients a with
      | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int)
      | none => (0 : Int)) := by
    apply sumOver_congr
    intro a ha
    rw [shareOf_match_int]
  rw [hcongr]
  have hoff := my_offset_proof2 r.recipients r.amount r.recipients.length 0 hNodupRec
  simp only [Nat.zero_add] at hoff
  rw [hoff]
  have hn : 0 < r.recipients.length := by
    have hlen_ne : r.recipients.length ≠ 0 := by
      intro hz
      exact hne (List.length_eq_zero_iff.mp hz)
    exact Nat.pos_of_ne_zero hlen_ne
  exact sum_range_fair_full2 r hn

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
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · unfold step at h
    simp [hv] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have heq : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step
      simp [hv]
    rw [heq]
    exact ⟨rfl, rfl, fun a => rfl⟩
  · unfold step at h
    simp [hv] at h

theorem req_idempotency    : Idempotent step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have heq : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step
      simp [hv]
    rw [heq] at h ⊢
    simp at h
    constructor
    · intro x
      simp
    · have hinvalid : ¬ ValidPayout { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } r := by
        intro hc
        obtain ⟨_, _, _, _, _, _, _, _, _, hmem⟩ := hc
        simp at hmem
      have hstep : step { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } r
        = (.rejected, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
        unfold step
        simp [hinvalid]
      exact hstep
  · unfold step at h
    simp [hv] at h

theorem req_nonnegative : NonNegative step := by
  intro s r hpos a ha
  by_cases hv : ValidPayout s r
  · have heq : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step
      simp [hv]
    rw [heq] at ha
    simp at ha
    rw [heq]
    simp
    show 0 ≤ expectedBalance s r a
    have h0 : 0 ≤ s.balance a := hpos a ha
    have hshare_nn : (0 : Int) ≤ (shareOf r a : Int) := by
      exact_mod_cast Nat.zero_le _
    unfold ValidPayout at hv
    obtain ⟨_, _, _, _, hnsrc, _, _, _, hle, _⟩ := hv
    unfold expectedBalance
    by_cases heq2 : a = r.source
    · subst heq2
      have hnone : indexOf? r.recipients r.source = none := indexOf?_eq_none hnsrc
      unfold shareOf at *
      rw [hnone] at *
      simp
      omega
    · simp [heq2]
      omega
  · have heq : step s r = (.rejected, s) := by
      unfold step
      simp [hv]
    rw [heq] at ha ⊢
    simp at ha ⊢
    exact hpos a ha

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  by_cases hv : ValidPayout s r
  · have heq : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step
      simp [hv]
    obtain ⟨hNodupAcc, hpos, hne, hNodupRec, hnsrc, hsrcAcc, hmemAcc, hauth, hle, htx⟩ := hv
    have hget_mem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hne_src : r.recipients[i] ≠ r.source := fun h => hnsrc (h ▸ hget_mem)
    have hidx : indexOf? r.recipients r.recipients[i] = some i :=
      indexOf?_getElem hNodupRec i hi
    have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
      rw [heq]
    rw [hbal]
    unfold expectedBalance shareOf
    rw [hidx]
    simp only [hne_src, ↓reduceIte]
    omega
  · unfold step at hok
    simp [hv] at hok

theorem req_conservation   : Conserves step := sorry

end Payout
