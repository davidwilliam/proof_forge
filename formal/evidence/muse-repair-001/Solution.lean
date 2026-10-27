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

theorem req_effects_tmp : True := trivial

theorem myTestLem : True := trivial

theorem test_bycases (p : Prop) [Decidable p] : True := by
  by_cases hv : p
  · trivial
  · trivial

theorem myNonneg7 : NonNegative step := by
  intro s r hpos a ha
  by_cases hv : ValidPayout s r
  · have hvCopy := hv
    obtain ⟨_, _, _, _, hsrcNotIn, hsrcMem, _, _, hle, _⟩ := hvCopy
    have ha' : a ∈ s.accounts := by
      have hEqAcc : (step s r).2.accounts = s.accounts := by simp [step, hv]
      rw [hEqAcc] at ha
      exact ha
    have hGoal : (step s r).2.balance a = expectedBalance s r a := by simp [step, hv]
    rw [hGoal]
    unfold expectedBalance
    by_cases hs : a = r.source
    · subst hs
      have hshare : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hsrcNotIn]
      simp [hshare]
      have hbal : 0 ≤ s.balance r.source := hpos _ hsrcMem
      omega
    · simp [hs]
      have hbal : 0 ≤ s.balance a := hpos a ha'
      have hshareNN : (0 : Int) ≤ (((shareOf r a : Nat) : Int)) := Int.natCast_nonneg _
      omega
  · have hEq : (step s r).2 = s := by simp [step, hv]
    have ha' : a ∈ s.accounts := by
      have hAcc : (step s r).2.accounts = s.accounts := by rw [hEq]
      rw [hAcc] at ha
      exact ha
    have hBal : (step s r).2.balance a = s.balance a := by rw [hEq]
    rw [hBal]
    exact hpos a ha'

theorem range_test : List.range 3 = [0,1,2] := by rfl
#check @List.range_succ
#check @List.range_zero

theorem chk_range_api : True := by trivial
#check List.range_succ
#check List.nodup_range
#check List.getElem_mem
#check List.mem_range

theorem sumOver_append_lem {α : Type} (l₁ l₂ : List α) (f : α → Int) :
    sumOver (l₁ ++ l₂) f = sumOver l₁ f + sumOver l₂ f := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem int_mul_test (n : Nat) (c : Int) : ((n + 1 : Nat) : Int) * c = (n : Int) * c + c := by
  have h : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
  rw [h]
  simp [Int.add_mul, Int.one_mul]



theorem plan0_sumOver_indexOf?_range (l : List AccountId) (g : Nat → Nat) (hl : l.Nodup) :
    sumOver l (fun a => (((match indexOf? l a with | some i => g i | none => 0) : Nat) : Int))
      = sumOver (List.range l.length) (fun i => ((g i : Nat) : Int)) := by
  have shift : ∀ (gg : Nat → Int) (n : Nat),
      sumOver (List.range (n + 1)) gg
        = gg 0 + sumOver (List.range n) (fun i => gg (i + 1)) := by
    intro gg n
    induction n with
    | zero => simp [sumOver]
    | succ n ih =>
      have h1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by
        rw [List.range_succ]
      have h2 : List.range (n + 1) = List.range n ++ [n] := by
        rw [List.range_succ]
      calc sumOver (List.range (n + 1 + 1)) gg
          = sumOver (List.range (n + 1)) gg + sumOver [n + 1] gg := by
            rw [h1, sumOver_append_lem]
        _ = (gg 0 + sumOver (List.range n) (fun i => gg (i + 1))) + gg (n + 1) := by
            rw [ih]; simp [sumOver]
        _ = gg 0 + (sumOver (List.range n) (fun i => gg (i + 1)) + gg (n + 1)) := by omega
        _ = gg 0 + sumOver (List.range (n + 1)) (fun i => gg (i + 1)) := by
            rw [h2, sumOver_append_lem]; simp [sumOver]
  induction l generalizing g with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotmem, hnodup⟩ := hl
    have hterm0 : (match indexOf? (x :: xs) x with | some i => g i | none => 0) = g 0 := by
      simp [indexOf?]
    have hcongr : ∀ a ∈ xs,
        ((((match indexOf? (x :: xs) a with | some i => g i | none => 0 : Nat)) : Int)
        = ((((match indexOf? xs a with | some i => g (i + 1) | none => 0 : Nat))) : Int)) := by
      intro a ha
      have hne : ¬ (x = a) := fun heq => hnotmem (heq ▸ ha)
      have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
        simp [indexOf?, hne]
      rw [hidx]
      cases h : indexOf? xs a with
      | none => simp
      | some i => simp
    have hleft : sumOver (x :: xs) (fun a => ((match indexOf? (x :: xs) a with | some i => g i | none => 0 : Nat) : Int))
        = ((g 0 : Nat) : Int) + sumOver xs (fun a => ((match indexOf? xs a with | some i => g (i + 1) | none => 0 : Nat) : Int)) := by
      simp only [sumOver_cons]
      rw [hterm0]
      congr 1
      exact sumOver_congr xs _ _ hcongr
    rw [hleft]
    have hright : sumOver (List.range (List.length (x :: xs))) (fun i => ((g i : Nat) : Int))
        = ((g 0 : Nat) : Int) + sumOver (List.range xs.length) (fun i => ((g (i + 1) : Nat) : Int)) := by
      simp only [List.length]
      exact shift (fun i => ((g i : Nat) : Int)) xs.length
    rw [hright]
    congr 1
    exact ih (fun i => g (i + 1)) hnodup







theorem plan0_sumOver_erase_add (l : List AccountId) (f : AccountId → Int) (a : AccountId)
    (hl : l.Nodup) (ha : a ∈ l) :
    f a + sumOver (l.erase a) f = sumOver l f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotmem, hnodup⟩ := hl
    have hmem : a = x ∨ a ∈ xs := by simpa using ha
    rw [List.erase_cons]
    have hbeq : ((x == a) = true) ↔ x = a := beq_iff_eq
    by_cases hxa : x = a
    · have htrue : (x == a) = true := hbeq.mpr hxa
      rw [if_pos htrue]
      subst hxa
      simp only [sumOver_cons]
    · have hfalse : ¬ ((x == a) = true) := fun ht => hxa (hbeq.mp ht)
      rw [if_neg hfalse]
      have ha_xs : a ∈ xs := by
        cases hmem with
        | inl h => exact absurd h.symm hxa
        | inr h => exact h
      have hih := ih hnodup ha_xs
      simp only [sumOver_cons] at *
      omega




theorem my_shift_test (g : Nat → Int) (n : Nat) :
    sumOver (List.range (n + 1)) g
      = g 0 + sumOver (List.range n) (fun i => g (i + 1)) := by
  induction n with
  | zero => simp [sumOver]
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by
      rw [List.range_succ]
    have h2 : List.range (n + 1) = List.range n ++ [n] := by
      rw [List.range_succ]
    calc sumOver (List.range (n + 1 + 1)) g
        = sumOver (List.range (n + 1)) g + sumOver [n + 1] g := by
          rw [h1, sumOver_append_lem]
      _ = (g 0 + sumOver (List.range n) (fun i => g (i + 1))) + g (n + 1) := by
          rw [ih]; simp [sumOver]
      _ = g 0 + (sumOver (List.range n) (fun i => g (i + 1)) + g (n + 1)) := by omega
      _ = g 0 + sumOver (List.range (n + 1)) (fun i => g (i + 1)) := by
          rw [h2, sumOver_append_lem]; simp [sumOver]

theorem plan0_sumOver_range_succ_shift (g : Nat → Int) (n : Nat) :
    sumOver (List.range (n + 1)) g
      = g 0 + sumOver (List.range n) (fun i => g (i + 1)) := by
  exact my_shift_test g n

theorem aux_bank_test2 : True := trivial

theorem aux_indexOf_range2 (l : List AccountId) (g : Nat → Nat) (hl : l.Nodup) :
    sumOver l (fun a => ((match indexOf? l a with | some i => g i | none => 0 : Nat) : Int))
      = sumOver (List.range l.length) (fun i => ((g i : Nat) : Int)) := by
  induction l generalizing g with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotmem, hnodup⟩ := hl
    have hterm0 : (match indexOf? (x :: xs) x with | some i => g i | none => 0) = g 0 := by
      simp [indexOf?]
    have hcongr : ∀ a ∈ xs,
        ((((match indexOf? (x :: xs) a with | some i => g i | none => 0 : Nat)) : Int)
        = ((((match indexOf? xs a with | some i => g (i + 1) | none => 0 : Nat))) : Int)) := by
      intro a ha
      have hne : ¬ (x = a) := fun heq => hnotmem (heq ▸ ha)
      have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
        simp [indexOf?, hne]
      rw [hidx]
      cases h : indexOf? xs a with
      | none => simp
      | some i => simp
    have hleft : sumOver (x :: xs) (fun a => ((match indexOf? (x :: xs) a with | some i => g i | none => 0 : Nat) : Int))
        = ((g 0 : Nat) : Int) + sumOver xs (fun a => ((match indexOf? xs a with | some i => g (i + 1) | none => 0 : Nat) : Int)) := by
      simp only [sumOver_cons]
      rw [hterm0]
      congr 1
      exact sumOver_congr xs _ _ hcongr
    rw [hleft]
    have hright : sumOver (List.range (List.length (x :: xs))) (fun i => ((g i : Nat) : Int))
        = ((g 0 : Nat) : Int) + sumOver (List.range xs.length) (fun i => ((g (i + 1) : Nat) : Int)) := by
      simp only [List.length]
      exact plan0_sumOver_range_succ_shift (fun i => ((g i : Nat) : Int)) xs.length
    rw [hright]
    congr 1
    exact ih (fun i => g (i + 1)) hnodup

theorem aux_psfp_const_sum2 (c : Int) (k : Nat) :
    sumOver (List.range k) (fun _ => c) = ((k : Nat) : Int) * c := by
  induction k with
  | zero => simp [sumOver]
  | succ k ih =>
    have h : List.range (k + 1) = List.range k ++ [k] := by rw [List.range_succ]
    rw [h, sumOver_append_lem]
    simp only [sumOver_nil, sumOver_cons]
    rw [ih]
    have hcast : ((((k + 1 : Nat))) : Int) = ((k : Nat) : Int) + 1 := by simp
    rw [hcast, Int.add_mul, Int.one_mul]
    omega

theorem aux_psfp_ind_sum2 (rem k : Nat) :
    sumOver (List.range k) (fun i => (if i < rem then (1 : Int) else 0))
      = (((min k rem : Nat)) : Int) := by
  induction k with
  | zero => simp [sumOver]
  | succ k ih =>
    have h : List.range (k + 1) = List.range k ++ [k] := by rw [List.range_succ]
    rw [h, sumOver_append_lem]
    simp only [sumOver_nil, sumOver_cons]
    rw [ih]
    by_cases hlt : k < rem
    · have h1 : min k rem = k := Nat.min_eq_left (Nat.le_of_lt hlt)
      have h2 : min (k + 1) rem = k + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hlt)
      rw [h1, h2]
      simp [hlt]
    · have hle : rem ≤ k := Nat.le_of_not_gt hlt
      have h1 : min k rem = rem := Nat.min_eq_right hle
      have h2 : min (k + 1) rem = rem := Nat.min_eq_right (Nat.le_succ_of_le hle)
      rw [h1, h2]
      simp [hlt]

theorem plan0_sum_range_fairShare_prefix (amount n k : Nat) :
    sumOver (List.range k) (fun i => ((fairShare amount n i : Nat) : Int))
      = ((k : Nat) : Int) * (((amount / n : Nat)) : Int)
        + (((min k (amount % n) : Nat)) : Int) := by
  have hterm : ∀ i : Nat, ((fairShare amount n i : Nat) : Int)
      = (((amount / n : Nat)) : Int) + (if i < amount % n then (1 : Int) else 0) := by
    intro i
    unfold fairShare
    by_cases h : i < amount % n
    · simp [h]
    · simp [h]
  have hcongr : sumOver (List.range k) (fun i => ((fairShare amount n i : Nat) : Int))
      = sumOver (List.range k) (fun i => (((amount / n : Nat)) : Int) + (if i < amount % n then (1 : Int) else 0)) := by
    apply sumOver_congr
    intro a _
    exact hterm a
  rw [hcongr, sumOver_add]
  rw [aux_psfp_const_sum2, aux_psfp_ind_sum2]

theorem probe3 : True := trivial
#check @Nat.cast
#check (inferInstance : NatCast Int)

theorem probe_cast_simp (a b : Nat) : (((a + b : Nat)) : Int) = ((a : Nat) : Int) + ((b : Nat) : Int) := by simp

theorem probe_cast_simp2 (a b : Nat) : (((a * b : Nat)) : Int) = ((a : Nat) : Int) * ((b : Nat) : Int) := by simp

theorem probe_cast_simp3 (amount n : Nat) (hdm : amount % n + n * (amount / n) = amount) :
    (((amount % n : Nat)) : Int) + ((((n * (amount / n) : Nat))) : Int) = ((amount : Nat) : Int) := by
  have h : ((((amount % n + n * (amount / n) : Nat))) : Int) = ((amount : Int)) := by rw [hdm]
  simp at h
  exact h

theorem plan0_sumOver_recipients_fairShare (amount : Nat) (l : List AccountId)
    (hl : l.Nodup) (hne : l ≠ []) :
    sumOver l (fun a => (((match indexOf? l a with
      | some i => fairShare amount l.length i
      | none => 0) : Nat) : Int)) = (amount : Int) := by
  have htrans : sumOver l (fun a => (((match indexOf? l a with
      | some i => fairShare amount l.length i
      | none => 0) : Nat) : Int))
      = sumOver (List.range l.length) (fun i => ((fairShare amount l.length i : Nat) : Int)) :=
    plan0_sumOver_indexOf?_range l (fun i => fairShare amount l.length i) hl
  rw [htrans]
  have hpre := plan0_sum_range_fairShare_prefix amount l.length l.length
  rw [hpre]
  have hlen_pos : 0 < l.length := by
    cases l with
    | nil => simp at hne
    | cons _ _ => simp
  have hmod_lt : amount % l.length < l.length := Nat.mod_lt _ hlen_pos
  have hmin : min l.length (amount % l.length) = amount % l.length :=
    Nat.min_eq_right (Nat.le_of_lt hmod_lt)
  rw [hmin]
  have hdm : amount % l.length + l.length * (amount / l.length) = amount :=
    Nat.mod_add_div amount l.length
  have hcast : ((((amount % l.length + l.length * (amount / l.length) : Nat))) : Int) = ((amount : Nat) : Int) := by
    rw [hdm]
  simp at hcast
  omega

theorem tmp_erase_lem2 (l : List AccountId) (f : AccountId → Int) (a : AccountId)
    (hl : l.Nodup) (ha : a ∈ l) :
    f a + sumOver (l.erase a) f = sumOver l f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotmem, hnodup⟩ := hl
    have hmem : a = x ∨ a ∈ xs := by simpa using ha
    rw [List.erase_cons]
    have hbeq : ((x == a) = true) ↔ x = a := beq_iff_eq
    by_cases hxa : x = a
    · have htrue : (x == a) = true := hbeq.mpr hxa
      rw [if_pos htrue]
      subst hxa
      simp only [sumOver_cons]
    · have hfalse : ¬ ((x == a) = true) := fun ht => hxa (hbeq.mp ht)
      rw [if_neg hfalse]
      have ha_xs : a ∈ xs := by
        cases hmem with
        | inl h => exact absurd h.symm hxa
        | inr h => exact h
      have hih := ih hnodup ha_xs
      simp only [sumOver_cons] at *
      omega







theorem plan1_nodup_erase (l : List AccountId) (a : AccountId)
    (hl : l.Nodup) :
    (l.erase a).Nodup :=
  List.Nodup.erase a hl




theorem plan1_sumOver_eq_zero_of_forall_zero (l : List AccountId) (f : AccountId → Int)
    (h : ∀ a ∈ l, f a = 0) :
    sumOver l f = 0 := by
  induction l with
  | nil => simp [sumOver]
  | cons x xs ih =>
    simp only [sumOver_cons]
    have hx : f x = 0 := h x (by simp)
    have hxs : ∀ a ∈ xs, f a = 0 := fun a ha => h a (by simp [ha])
    rw [hx, ih hxs, Int.add_zero]

theorem plan1_sumOver_erase_add (l : List AccountId) (f : AccountId → Int) (a : AccountId)
    (hl : l.Nodup) (ha : a ∈ l) :
    f a + sumOver (l.erase a) f = sumOver l f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotmem, hnodup⟩ := hl
    have hmem : a = x ∨ a ∈ xs := by simpa using ha
    rw [List.erase_cons]
    have hbeq : ((x == a) = true) ↔ x = a := beq_iff_eq
    by_cases hxa : x = a
    · have htrue : (x == a) = true := hbeq.mpr hxa
      rw [if_pos htrue]
      subst hxa
      simp only [sumOver_cons]
    · have hfalse : ¬ ((x == a) = true) := fun ht => hxa (hbeq.mp ht)
      rw [if_neg hfalse]
      have ha_xs : a ∈ xs := by
        cases hmem with
        | inl h => exact absurd h.symm hxa
        | inr h => exact h
      have hih := ih hnodup ha_xs
      simp only [sumOver_cons] at *
      omega

theorem plan1_mem_erase_iff_of_nodup {l : List AccountId} {x a : AccountId}
    (hl : l.Nodup) :
    x ∈ l.erase a ↔ x ≠ a ∧ x ∈ l := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotmem, hnodup⟩ := hl
    have ih' : x ∈ ys.erase a ↔ x ≠ a ∧ x ∈ ys := ih hnodup
    rw [List.erase_cons]
    have hbeq : ∀ u v : AccountId, ((u == v) = true) ↔ u = v := fun u v => beq_iff_eq
    by_cases hya : y = a
    · have htrue : (y == a) = true := (hbeq y a).mpr hya
      rw [if_pos htrue]
      constructor
      · intro hxmem
        have hxa : x ≠ a := by
          intro hcontra
          have hyx : y = x := hya.trans hcontra.symm
          have hyys : y ∈ ys := hyx.symm ▸ hxmem
          exact hnotmem hyys
        constructor
        · exact hxa
        · simp [hxmem]
      · intro ⟨hne, hmem⟩
        have hmem2 : x = y ∨ x ∈ ys := by simpa using hmem
        cases hmem2 with
        | inl h =>
          have hxa : x = a := h.trans hya
          exact absurd hxa hne
        | inr h => exact h
    · have hfalse : ¬ ((y == a) = true) := fun ht => hya ((hbeq y a).mp ht)
      rw [if_neg hfalse]
      simp only [List.mem_cons]
      constructor
      · intro hmem
        cases hmem with
        | inl h =>
          subst h
          exact ⟨hya, Or.inl rfl⟩
        | inr h =>
          obtain ⟨hne, hmem2⟩ := ih'.mp h
          exact ⟨hne, Or.inr hmem2⟩
      · intro ⟨hne, hmem⟩
        cases hmem with
        | inl h =>
          exact Or.inl h
        | inr h =>
          exact Or.inr (ih'.mpr ⟨hne, h⟩)

theorem plan1_nodup_erase_try (l : List AccountId) (a : AccountId)
    (hl : l.Nodup) :
    (l.erase a).Nodup := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotmem, hnodup⟩ := hl
    have ih' := ih hnodup
    rw [List.erase_cons]
    have hbeq : ((y == a) = true) ↔ y = a := beq_iff_eq
    by_cases hya : y = a
    · have htrue : (y == a) = true := hbeq.mpr hya
      rw [if_pos htrue]
      exact hnodup
    · have hfalse : ¬ ((y == a) = true) := fun ht => hya (hbeq.mp ht)
      rw [if_neg hfalse]
      rw [List.nodup_cons]
      constructor
      · intro hmem
        have hmem2 := (plan1_mem_erase_iff_of_nodup hnodup).mp hmem
        exact hnotmem hmem2.2
      · exact ih'

theorem plan1_support_fixed (big small : List AccountId)
    (f : AccountId → Int) (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hsupport : ∀ x ∈ big, x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by
  induction big generalizing small with
  | nil =>
    have hempty : small = [] := by
      cases small with
      | nil => rfl
      | cons y ys =>
        have hy : y ∈ (y :: ys) := by simp
        have hybig : y ∈ ([] : List AccountId) := hsub y hy
        simp at hybig
    subst hempty
    rfl
  | cons x xs ih =>
    rw [List.nodup_cons] at hbig
    obtain ⟨hnotmem_xs, hnodup_xs⟩ := hbig
    by_cases hxmem : x ∈ small
    · have hsmallEraseNodup : (small.erase x).Nodup :=
        plan1_nodup_erase_try small x hsmall
      have herase_eq : f x + sumOver (small.erase x) f = sumOver small f :=
        plan1_sumOver_erase_add small f x hsmall hxmem
      have hsub' : ∀ y ∈ small.erase x, y ∈ xs := by
        intro y hy
        have hmem := (plan1_mem_erase_iff_of_nodup hsmall).mp hy
        obtain ⟨hne, hmem_small⟩ := hmem
        have hmem_big : y ∈ x :: xs := hsub y hmem_small
        simp only [List.mem_cons] at hmem_big
        cases hmem_big with
        | inl h => exact absurd h hne
        | inr h => exact h
      have hsup' : ∀ y ∈ xs, y ∉ small.erase x → f y = 0 := by
        intro y hy_mem hnot_erase
        have hy_big : y ∈ x :: xs := by simp [hy_mem]
        have hy_not_small : y ∉ small := by
          intro hy_small
          have hy_ne : y ≠ x := by
            intro heq
            rw [heq] at hy_mem
            exact hnotmem_xs hy_mem
          have hy_erase : y ∈ small.erase x :=
            (plan1_mem_erase_iff_of_nodup hsmall).mpr ⟨hy_ne, hy_small⟩
          exact hnot_erase hy_erase
        exact hsupport y hy_big hy_not_small
      have ih' := ih (small.erase x) hnodup_xs hsmallEraseNodup hsub' hsup'
      simp only [sumOver_cons] at *
      omega
    · have hfx : f x = 0 := hsupport x (by simp) hxmem
      have hsub' : ∀ y ∈ small, y ∈ xs := by
        intro y hy
        have hmem_big : y ∈ x :: xs := hsub y hy
        simp only [List.mem_cons] at hmem_big
        cases hmem_big with
        | inl h =>
          rw [h] at hy
          exact absurd hy hxmem
        | inr h => exact h
      have hsup' : ∀ y ∈ xs, y ∉ small → f y = 0 := by
        intro y hy_mem hnot_small
        have hy_big : y ∈ x :: xs := by simp [hy_mem]
        exact hsupport y hy_big hnot_small
      have ih' := ih small hnodup_xs hsmall hsub' hsup'
      simp only [sumOver_cons] at *
      omega

theorem req_conservation_newproof : Conserves step := by
  intro s r hOk
  by_cases hv : ValidPayout s r
  · have hvC := hv
    obtain ⟨hNodupAcc, hpos, hne, hNodupR, hsrcNotIn, hsrcMem, hmemR, hauth, hle, htx⟩ := hvC
    have hAcc : (step s r).2.accounts = s.accounts := by simp [step, hv]
    have hBal : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
      intro a; simp [step, hv]
    have hTotEq : total (step s r).2 = sumOver s.accounts (fun a => expectedBalance s r a) := by
      unfold total
      rw [hAcc]
      exact sumOver_congr s.accounts _ _ (fun a _ => hBal a)
    rw [hTotEq]
    have hSumDecomp : sumOver s.accounts (fun a => expectedBalance s r a)
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
          + sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by
      rw [← sumOver_add]
      apply sumOver_congr
      intro a _
      unfold expectedBalance
      rfl
    have hSub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) := by
      exact sumOver_sub s.accounts _ _
    have hIte : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0))
        = (r.amount : Int) := by
      have h := sumOver_ite_eq hNodupAcc r.source (r.amount : Int)
      rw [h]
      simp [hsrcMem]
    have hShareSmall : sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int)) = (r.amount : Int) := by
      have hBase := plan0_sumOver_recipients_fairShare r.amount r.recipients hNodupR hne
      have hcongr : sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int))
          = sumOver r.recipients (fun a => (((match indexOf? r.recipients a with
              | some i => fairShare r.amount r.recipients.length i
              | none => 0) : Nat) : Int)) := by
        apply sumOver_congr
        intro a _
        unfold shareOf
        rfl
      rw [hcongr, hBase]
    have hShare : sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) = (r.amount : Int) := by
      have hsup : ∀ x ∈ s.accounts, x ∉ r.recipients → (fun a => ((shareOf r a : Nat) : Int)) x = 0 := by
        intro x _ hxNot
        simp only
        have hidx : indexOf? r.recipients x = none := indexOf?_eq_none hxNot
        unfold shareOf
        rw [hidx]
        simp
      have hsymm := plan1_support_fixed s.accounts r.recipients
        (fun a => ((shareOf r a : Nat) : Int)) hNodupAcc hNodupR (fun x hx => hmemR x hx) (fun x hx hxNot => hsup x hx hxNot)
      rw [hsymm, hShareSmall]
    rw [hSumDecomp, hSub, hIte, hShare]
    unfold total
    omega
  · unfold step at hOk
    simp [hv] at hOk









theorem plan0_erase_add_for_support (l : List AccountId) (f : AccountId → Int)
    (a : AccountId) (hl : l.Nodup) (ha : a ∈ l) :
    f a + sumOver (l.erase a) f = sumOver l f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotmem, hnodup⟩ := hl
    have hmem : a = x ∨ a ∈ xs := by simpa using ha
    rw [List.erase_cons]
    have hbeq : ((x == a) = true) ↔ x = a := beq_iff_eq
    by_cases hxa : x = a
    · have htrue : (x == a) = true := hbeq.mpr hxa
      rw [if_pos htrue]
      subst hxa
      simp only [sumOver_cons]
    · have hfalse : ¬ ((x == a) = true) := fun ht => hxa (hbeq.mp ht)
      rw [if_neg hfalse]
      have ha_xs : a ∈ xs := by
        cases hmem with
        | inl h => exact absurd h.symm hxa
        | inr h => exact h
      have hih := ih hnodup ha_xs
      simp only [sumOver_cons] at *
      omega

theorem plan0_mem_erase_for_support_aux {l : List AccountId} {x a : AccountId} (hl : l.Nodup) : x ∈ l.erase a ↔ x ≠ a ∧ x ∈ l := plan1_mem_erase_iff_of_nodup hl

theorem plan0_mem_erase_for_support {l : List AccountId} {x a : AccountId} (hl : l.Nodup) : x ∈ l.erase a ↔ x ≠ a ∧ x ∈ l := plan1_mem_erase_iff_of_nodup hl

theorem plan0_nodup_erase_for_support_proof : ∀ (l : List AccountId) (a : AccountId),
    l.Nodup → (l.erase a).Nodup := fun l a hl => plan1_nodup_erase_try l a hl

theorem plan0_nodup_erase_for_support (l : List AccountId) (a : AccountId)
    (hl : l.Nodup) :
    (l.erase a).Nodup := plan1_nodup_erase_try l a hl

theorem plan0_sumOver_support_subset_with_nodup (big small : List AccountId)
    (f : AccountId → Int) (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hsupport : ∀ x ∈ big, x ∉ small → f x = 0) :
    sumOver big f = sumOver small f :=
  plan1_support_fixed big small f hbig hsmall hsub hsupport

theorem tmp_check_erase_api2 (l : List Nat) (a : Nat) (hl : l.Nodup) : (l.erase a).Nodup :=
  List.Nodup.erase a hl

theorem plan1_nodup_erase2 (l : List AccountId) (a : AccountId) (hl : l.Nodup) : (l.erase a).Nodup :=
  List.Nodup.erase a hl

theorem plan1_support_selfcontained (big small : List AccountId)
    (f : AccountId → Int) (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hsupport : ∀ x ∈ big, x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by
  have erase_add : ∀ (l : List AccountId) (g : AccountId → Int) (a : AccountId),
      l.Nodup → a ∈ l → g a + sumOver (l.erase a) g = sumOver l g := by
    intro l g a hl ha
    induction l with
    | nil => simp at ha
    | cons x xs ih =>
      rw [List.nodup_cons] at hl
      obtain ⟨hnotmem, hnodup⟩ := hl
      have hmem : a = x ∨ a ∈ xs := by simpa using ha
      rw [List.erase_cons]
      have hbeq : ((x == a) = true) ↔ x = a := beq_iff_eq
      by_cases hxa : x = a
      · have htrue : (x == a) = true := hbeq.mpr hxa
        rw [if_pos htrue]
        subst hxa
        simp only [sumOver_cons]
      · have hfalse : ¬ ((x == a) = true) := fun ht => hxa (hbeq.mp ht)
        rw [if_neg hfalse]
        have ha_xs : a ∈ xs := by
          cases hmem with
          | inl h => exact absurd h.symm hxa
          | inr h => exact h
        have hih := ih hnodup ha_xs
        simp only [sumOver_cons] at *
        omega
  have mem_erase : ∀ (l : List AccountId) (x a : AccountId),
      l.Nodup → (x ∈ l.erase a ↔ x ≠ a ∧ x ∈ l) := by
    intro l x a hl
    induction l with
    | nil => simp
    | cons y ys ih =>
      rw [List.nodup_cons] at hl
      obtain ⟨hnotmem, hnodup⟩ := hl
      have ih' : x ∈ ys.erase a ↔ x ≠ a ∧ x ∈ ys := ih hnodup
      rw [List.erase_cons]
      have hbeq : ∀ u v : AccountId, ((u == v) = true) ↔ u = v := fun u v => beq_iff_eq
      by_cases hya : y = a
      · have htrue : (y == a) = true := (hbeq y a).mpr hya
        rw [if_pos htrue]
        constructor
        · intro hxmem
          have hxa : x ≠ a := by
            intro hcontra
            have hyx : y = x := hya.trans hcontra.symm
            have hyys : y ∈ ys := hyx.symm ▸ hxmem
            exact hnotmem hyys
          constructor
          · exact hxa
          · simp [hxmem]
        · intro ⟨hne, hmem⟩
          have hmem2 : x = y ∨ x ∈ ys := by simpa using hmem
          cases hmem2 with
          | inl h =>
            have hxa : x = a := h.trans hya
            exact absurd hxa hne
          | inr h => exact h
      · have hfalse : ¬ ((y == a) = true) := fun ht => hya ((hbeq y a).mp ht)
        rw [if_neg hfalse]
        simp only [List.mem_cons]
        constructor
        · intro hmem
          cases hmem with
          | inl h =>
            subst h
            exact ⟨hya, Or.inl rfl⟩
          | inr h =>
            obtain ⟨hne, hmem2⟩ := ih'.mp h
            exact ⟨hne, Or.inr hmem2⟩
        · intro ⟨hne, hmem⟩
          cases hmem with
          | inl h =>
            exact Or.inl h
          | inr h =>
            exact Or.inr (ih'.mpr ⟨hne, h⟩)
  induction big generalizing small with
  | nil =>
    have hempty : small = [] := by
      cases small with
      | nil => rfl
      | cons y ys =>
        have hy : y ∈ (y :: ys) := by simp
        have hybig : y ∈ ([] : List AccountId) := hsub y hy
        simp at hybig
    subst hempty
    rfl
  | cons x xs ih =>
    rw [List.nodup_cons] at hbig
    obtain ⟨hnotmem_xs, hnodup_xs⟩ := hbig
    by_cases hxmem : x ∈ small
    · have hsmallEraseNodup : (small.erase x).Nodup :=
        List.Nodup.erase x hsmall
      have herase_eq : f x + sumOver (small.erase x) f = sumOver small f :=
        erase_add small f x hsmall hxmem
      have hsub' : ∀ y ∈ small.erase x, y ∈ xs := by
        intro y hy
        have hmem := (mem_erase small y x hsmall).mp hy
        obtain ⟨hne, hmem_small⟩ := hmem
        have hmem_big : y ∈ x :: xs := hsub y hmem_small
        simp only [List.mem_cons] at hmem_big
        cases hmem_big with
        | inl h => exact absurd h hne
        | inr h => exact h
      have hsup' : ∀ y ∈ xs, y ∉ small.erase x → f y = 0 := by
        intro y hy_mem hnot_erase
        have hy_big : y ∈ x :: xs := by simp [hy_mem]
        have hy_not_small : y ∉ small := by
          intro hy_small
          have hy_ne : y ≠ x := by
            intro heq
            rw [heq] at hy_mem
            exact hnotmem_xs hy_mem
          have hy_erase : y ∈ small.erase x :=
            (mem_erase small y x hsmall).mpr ⟨hy_ne, hy_small⟩
          exact hnot_erase hy_erase
        exact hsupport y hy_big hy_not_small
      have ih' := ih (small.erase x) hnodup_xs hsmallEraseNodup hsub' hsup'
      simp only [sumOver_cons] at *
      omega
    · have hfx : f x = 0 := hsupport x (by simp) hxmem
      have hsub' : ∀ y ∈ small, y ∈ xs := by
        intro y hy
        have hmem_big : y ∈ x :: xs := hsub y hy
        simp only [List.mem_cons] at hmem_big
        cases hmem_big with
        | inl h =>
          rw [h] at hy
          exact absurd hy hxmem
        | inr h => exact h
      have hsup' : ∀ y ∈ xs, y ∉ small → f y = 0 := by
        intro y hy_mem hnot_small
        have hy_big : y ∈ x :: xs := by simp [hy_mem]
        exact hsupport y hy_big hnot_small
      have ih' := ih small hnodup_xs hsmall hsub' hsup'
      simp only [sumOver_cons] at *
      omega

theorem plan0_fixed_check (big small : List AccountId)
    (f : AccountId → Int) (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hsupport : ∀ x ∈ big, x ∉ small → f x = 0) :
    sumOver big f = sumOver small f :=
  plan1_support_selfcontained big small f hbig hsmall hsub hsupport

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_fair_shares : FairShares step := by
  intro s r hOk i hi
  by_cases hv : ValidPayout s r
  · have hvC := hv
    obtain ⟨hNodupAcc, hpos, hne, hNodupR, hsrcNotIn, hsrcMem, hmem, hauth, hle, htx⟩ := hvC
    have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
      simp [step, hv]
    rw [hbal]
    unfold expectedBalance shareOf
    have hIdx : indexOf? r.recipients r.recipients[i] = some i :=
      indexOf?_getElem hNodupR i hi
    rw [hIdx]
    have hNe : r.recipients[i] ≠ r.source := by
      intro hEq
      apply hsrcNotIn
      rw [← hEq]
      exact List.getElem_mem hi
    have hIf2 : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by
      simp [hNe]
    rw [hIf2]
    simp
    omega
  · unfold step at hOk
    simp [hv] at hOk

theorem req_effects : Effects step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · simp [step, hv]
  · unfold step at h
    simp [hv] at h

theorem req_conservation : Conserves step := by
  intro s r hOk
  by_cases hv : ValidPayout s r
  · have hvC := hv
    obtain ⟨hNodupAcc, hpos, hne, hNodupR, hsrcNotIn, hsrcMem, hmemR, hauth, hle, htx⟩ := hvC
    have hAcc : (step s r).2.accounts = s.accounts := by simp [step, hv]
    have hBal : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
      intro a; simp [step, hv]
    have hTotEq : total (step s r).2 = sumOver s.accounts (fun a => expectedBalance s r a) := by
      unfold total
      rw [hAcc]
      exact sumOver_congr s.accounts _ _ (fun a _ => hBal a)
    rw [hTotEq]
    have hSumDecomp : sumOver s.accounts (fun a => expectedBalance s r a)
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
          + sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by
      rw [← sumOver_add]
      apply sumOver_congr
      intro a _
      unfold expectedBalance
      rfl
    have hSub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) := by
      exact sumOver_sub s.accounts _ _
    have hIte : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0))
        = (r.amount : Int) := by
      have h := sumOver_ite_eq hNodupAcc r.source (r.amount : Int)
      rw [h]
      simp [hsrcMem]
    have hShareSmall : sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int)) = (r.amount : Int) := by
      have hBase := plan0_sumOver_recipients_fairShare r.amount r.recipients hNodupR hne
      have hcongr : sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int))
          = sumOver r.recipients (fun a => (((match indexOf? r.recipients a with
              | some i => fairShare r.amount r.recipients.length i
              | none => 0) : Nat) : Int)) := by
        apply sumOver_congr
        intro a _
        unfold shareOf
        rfl
      rw [hcongr, hBase]
    have hShare : sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) = (r.amount : Int) := by
      have hsup : ∀ x ∈ s.accounts, x ∉ r.recipients → (fun a => ((shareOf r a : Nat) : Int)) x = 0 := by
        intro x _ hxNot
        simp only
        have hidx : indexOf? r.recipients x = none := indexOf?_eq_none hxNot
        unfold shareOf
        rw [hidx]
        simp
      have hsymm := plan1_support_fixed s.accounts r.recipients
        (fun a => ((shareOf r a : Nat) : Int)) hNodupAcc hNodupR (fun x hx => hmemR x hx) (fun x hx hxNot => hsup x hx hxNot)
      rw [hsymm, hShareSmall]
    rw [hSumDecomp, hSub, hIte, hShare]
    unfold total
    omega
  · unfold step at hOk
    simp [hv] at hOk

theorem req_nonnegative : NonNegative step := by
  intro s r hpos a ha
  by_cases hv : ValidPayout s r
  · have hvCopy := hv
    obtain ⟨_, _, _, _, hsrcNotIn, hsrcMem, _, _, hle, _⟩ := hvCopy
    have ha' : a ∈ s.accounts := by
      have hEqAcc : (step s r).2.accounts = s.accounts := by simp [step, hv]
      rw [hEqAcc] at ha
      exact ha
    have hGoal : (step s r).2.balance a = expectedBalance s r a := by simp [step, hv]
    rw [hGoal]
    unfold expectedBalance
    by_cases hs : a = r.source
    · subst hs
      have hshare : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hsrcNotIn]
      simp [hshare]
      have hbal : 0 ≤ s.balance r.source := hpos _ hsrcMem
      omega
    · simp [hs]
      have hbal : 0 ≤ s.balance a := hpos a ha'
      have hshareNN : (0 : Int) ≤ (((shareOf r a : Nat) : Int)) := Int.natCast_nonneg _
      omega
  · have hEq : (step s r).2 = s := by simp [step, hv]
    have ha' : a ∈ s.accounts := by
      have hAcc : (step s r).2.accounts = s.accounts := by rw [hEq]
      rw [hAcc] at ha
      exact ha
    have hBal : (step s r).2.balance a = s.balance a := by rw [hEq]
    rw [hBal]
    exact hpos a ha'

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · unfold step at h
    simp [hv] at h

theorem req_idempotency : Idempotent step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step; simp [hv]
    have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := congrArg Prod.snd hstep
    constructor
    · intro x
      rw [h2]
      simp
    · have hNotValid : ¬ ValidPayout ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r := by
        intro hV
        obtain ⟨_, _, _, _, _, _, _, _, _, hNotMem⟩ := hV
        simp at hNotMem
      have hNotValid2 : ¬ ValidPayout (step s r).2 r := by rw [h2]; exact hNotValid
      exact req_invalid_noop _ _ hNotValid2
  · unfold step at h
    simp [hv] at h

end Payout
