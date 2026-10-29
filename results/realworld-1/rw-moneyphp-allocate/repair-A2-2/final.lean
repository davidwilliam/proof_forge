import Allocation.Spec
/-!
Fixed allocation: Hamilton / largest-remainder method with sign handling.
-/
namespace Allocation

def baseAt (amount : Int) (S : Nat) (r : Nat) : Int :=
  if 0 ≤ amount then amount * (r : Int) / (S : Int)
  else - ((-amount * (r : Int)) / (S : Int))

def keyAt (amount : Int) (S : Nat) (r : Nat) : Int :=
  let b := baseAt amount S r
  if 0 ≤ amount then amount * (r : Int) - b * (S : Int)
  else b * (S : Int) - amount * (r : Int)

def prefers (keys : List Int) (j i : Nat) : Bool :=
  if keys.getD j 0 > keys.getD i 0 then true
  else if keys.getD j 0 < keys.getD i 0 then false
  else decide (j < i)

def rankOf (keys : List Int) (n i : Nat) : Nat :=
  ((List.range n).filter (fun j => prefers keys j i)).length

def allocate : Impl := fun amount ratios =>
  match ratios with
  | [] => none
  | _ :: _ =>
    if ratios.sum = 0 then none
    else
      let S := ratios.sum
      let n := ratios.length
      let bases : List Int := ratios.map (baseAt amount S)
      let keys : List Int := ratios.map (keyAt amount S)
      let L : Nat := if 0 ≤ amount then (amount - bases.sum).toNat else (bases.sum - amount).toNat
      some ((List.range n).map fun i =>
        let b := bases.getD i 0
        if rankOf keys n i < L then (if 0 ≤ amount then b + 1 else b - 1) else b)

def fooTest : Nat := 1

theorem fooTest2 : 1 = 1 := rfl

theorem thm_probe1 : True := trivial

theorem baseAt_zero_thm (amount : Int) (S : Nat) : baseAt amount S 0 = 0 := by
  unfold baseAt
  by_cases h : 0 ≤ amount
  · simp [h]
  · simp [h]

theorem lemmas_probe : True := trivial
#check Allocation.excess

theorem probe_lemmas : True := trivial

theorem t_omega (a : Nat) (h : 0 < a) : 0 ≤ (a : Int) := by omega

theorem t_simp (a : Nat) : (a : Int) = (a : Int) := by rfl
#check Int.ediv_nonneg

theorem t_mem_map_ex (f : Nat → Int) (n : Nat) (x : Int) (h : x ∈ (List.range n).map f) : ∃ i, i < n ∧ f i = x := by
  rw [List.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  rw [List.mem_range] at ha
  exact ⟨a, ha, rfl⟩

theorem t1 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  exact Int.mul_nonneg ha hb
#check Int.mul_nonneg

theorem aux_subset_len_test (l1 : List Nat) : l1.length = l1.length := rfl
#check List.range
#check List.filter
#check List.Nodup
#check List.nodup_range
#check List.mem_range
#check List.mem_filter
#check List.getD

theorem filter_mono_len (l : List Nat) (p q : Nat → Bool) (h : ∀ x ∈ l, p x = true → q x = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter] at *
    by_cases hp : p hd = true
    · have hq : q hd = true := h hd (by simp) hp
      simp [hp, hq]
      have ih2 := ih (fun x hx => h x (by simp [hx]))
      omega
    · simp [hp]
      by_cases hq : q hd = true
      · simp [hq]
        have ih2 := ih (fun x hx => h x (by simp [hx]))
        omega
      · simp [hq]
        exact ih (fun x hx => h x (by simp [hx]))



theorem plan0_bases_diff_bounds (amount : Int) (ratios : List Nat) (hS : 0 < ratios.sum) :
    (0 ≤ amount →
      ((amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat : Int) =
        amount - (ratios.map (baseAt amount ratios.sum)).sum ∧
      (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat ≤ ratios.length) ∧
    (amount ≤ 0 →
      (((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat : Int) =
        (ratios.map (baseAt amount ratios.sum)).sum - amount ∧
      ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat ≤ ratios.length) := by sorry









theorem probe4 : True := trivial
#check @Int.emod_nonneg
#check @Int.emod_lt_of_pos
#check @Int.ediv_nonneg
#check @Int.mul_ediv_add_emod
#check @Int.ediv_zero
#check @Int.zero_ediv
#check @Int.mul_nonneg
#check @Int.neg_mul
#check @Int.mul_comm

theorem tmp_ne (S : Nat) (hS : 0 < S) : (S : Int) ≠ 0 := by omega

theorem probe5 : True := trivial
#check @Int.mul_comm
#check @Int.mul_assoc
#check @Int.neg_mul
#check @Int.mul_neg
#check @Int.neg_neg
#check @Int.sub_eq_add_neg

theorem probe6 : True := trivial
#check @Int.neg_mul
#check @Int.mul_neg
#check @Int.mul_comm
#check @Int.mul_ediv_add_emod
#check @Int.emod_nonneg
#check @Int.emod_lt_of_pos
#check @Int.neg_pos

theorem tmp_swap (a : Int) (S : Nat) : (a / (S : Int)) * (S : Int) = (S : Int) * (a / (S : Int)) :=
  Int.mul_comm _ _













theorem tmp_check_sig : True := by
  trivial
#check @Int.emod_nonneg
#check @Int.emod_lt_of_pos

theorem plan1_emod_bounds_aux_unique : True := trivial

theorem plan1_emod_bounds (t : Int) (S : Nat) (ht : 0 ≤ t) (hS : 0 < S) :
    0 ≤ t % (S : Int) ∧ t % (S : Int) < (S : Int) := by
  have hSpos : (0 : Int) < (S : Int) := by omega
  have hSne : (S : Int) ≠ 0 := by omega
  have _ht' : 0 ≤ t := ht
  exact ⟨Int.emod_nonneg t hSne, Int.emod_lt_of_pos t hSpos⟩

theorem plan1_residual_eq_emod (t : Int) (S : Nat) :
    t - (t / (S : Int)) * (S : Int) = t % (S : Int) := by
  rw [Int.emod_def]
  rw [Int.mul_comm]

theorem plan1_ediv_residual_bounds_proof : True := trivial
#check @plan1_residual_eq_emod
#check @plan1_emod_bounds

theorem plan1_ediv_residual_bounds (t : Int) (S : Nat) (ht : 0 ≤ t) (hS : 0 < S) :
    0 ≤ t - (t / (S : Int)) * (S : Int) ∧
    t - (t / (S : Int)) * (S : Int) < (S : Int) := by
  have h := plan1_emod_bounds t S ht hS
  have heq := plan1_residual_eq_emod t S
  omega

theorem plan1_ediv_residual_neg_bounds (t : Int) (S : Nat) (ht : 0 ≤ t) (hS : 0 < S) :
    -(S : Int) < -(t - (t / (S : Int)) * (S : Int)) ∧
    -(t - (t / (S : Int)) * (S : Int)) ≤ 0 := by
  have h := plan1_ediv_residual_bounds t S ht hS
  omega

theorem plan1_test_aux2 (amount : Int) (S r : Nat) (hS : 0 < S)
    (ha : 0 ≤ amount) :
    -(S : Int) < amount * (r : Int) - baseAt amount S r * (S : Int) ∧
    amount * (r : Int) - baseAt amount S r * (S : Int) < (S : Int) ∧
    (0 ≤ amount → 0 ≤ amount * (r : Int) - baseAt amount S r * (S : Int)) ∧
    (amount ≤ 0 → amount * (r : Int) - baseAt amount S r * (S : Int) ≤ 0) := by
  have hSpos : (0 : Int) < (S : Int) := by omega
  have ht_nonneg : 0 ≤ amount * (r : Int) := Int.mul_nonneg ha (by omega)
  have hbase : baseAt amount S r = (amount * (r : Int)) / (S : Int) := by
    unfold baseAt
    rw [if_pos ha]
  have hres := plan1_ediv_residual_bounds (amount * (r : Int)) S ht_nonneg hS
  rw [hbase]
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro _
    omega
  · intro hle
    have ham0 : amount = 0 := by omega
    subst ham0
    simp

theorem plan1_baseAt_bounds_of_nonneg (amount : Int) (S r : Nat) (hS : 0 < S)
    (ha : 0 ≤ amount) :
    -(S : Int) < amount * (r : Int) - baseAt amount S r * (S : Int) ∧
    amount * (r : Int) - baseAt amount S r * (S : Int) < (S : Int) ∧
    (0 ≤ amount → 0 ≤ amount * (r : Int) - baseAt amount S r * (S : Int)) ∧
    (amount ≤ 0 → amount * (r : Int) - baseAt amount S r * (S : Int) ≤ 0) := by
  have hSpos : (0 : Int) < (S : Int) := by omega
  have ht_nonneg : 0 ≤ amount * (r : Int) := Int.mul_nonneg ha (by omega)
  have hbase : baseAt amount S r = (amount * (r : Int)) / (S : Int) := by
    unfold baseAt
    rw [if_pos ha]
  have hres := plan1_ediv_residual_bounds (amount * (r : Int)) S ht_nonneg hS
  rw [hbase]
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro _
    omega
  · intro hle
    have ham0 : amount = 0 := by omega
    subst ham0
    simp

theorem probe_neg_mul (a b : Int) : (-a) * b = -(a * b) := by
  exact Int.neg_mul a b
#check @Int.neg_mul
#check @Int.mul_neg

theorem probe_int_lemmas2 (a b : Int) : (-a) * b = -(a * b) ∧ (-a) * b = -(a*b) ∧ -(-a) = a ∧ (-a)*b = -(a*b) := by
  exact ⟨Int.neg_mul a b, Int.neg_mul a b, Int.neg_neg a, Int.neg_mul a b⟩
#check @Int.neg_neg
#check @Int.neg_mul
#check @Int.mul_neg
#check @Int.sub_eq_add_neg

theorem plan1_heq_via_omega (amount : Int) (S : Nat) (r : Nat) :
    amount * (r : Int) - -(-amount * (r : Int) / (S : Int)) * (S : Int) =
      -(-amount * (r : Int) - (-amount * (r : Int) / (S : Int)) * (S : Int)) := by
  have hU : -amount * (r : Int) = -(amount * (r : Int)) := Int.neg_mul amount (r : Int)
  have hV : -(-amount * (r : Int) / (S : Int)) * (S : Int) =
      -(((-amount * (r : Int) / (S : Int)) * (S : Int))) := Int.neg_mul _ _
  omega

theorem plan1_baseAt_neg_unfold (amount : Int) (S r : Nat) (ha : ¬ 0 ≤ amount) :
    baseAt amount S r = - ((-amount * (r : Int)) / (S : Int)) := by
  unfold baseAt
  simp [ha]

theorem plan1_baseAt_bounds_of_neg (amount : Int) (S r : Nat) (hS : 0 < S)
    (ha : ¬ 0 ≤ amount) :
    -(S : Int) < amount * (r : Int) - baseAt amount S r * (S : Int) ∧
    amount * (r : Int) - baseAt amount S r * (S : Int) < (S : Int) ∧
    (0 ≤ amount → 0 ≤ amount * (r : Int) - baseAt amount S r * (S : Int)) ∧
    (amount ≤ 0 → amount * (r : Int) - baseAt amount S r * (S : Int) ≤ 0) := by
  have ham_neg : amount < 0 := by omega
  have h_nneg : (0 : Int) ≤ -amount := by omega
  have h_rnonneg : (0 : Int) ≤ (r : Int) := by omega
  have ht_nonneg : (0 : Int) ≤ -amount * (r : Int) := Int.mul_nonneg h_nneg h_rnonneg
  have hbase : baseAt amount S r = - ((-amount * (r : Int)) / (S : Int)) :=
    plan1_baseAt_neg_unfold amount S r ha
  have hres := plan1_ediv_residual_bounds (-amount * (r : Int)) S ht_nonneg hS
  have heq : amount * (r : Int) - baseAt amount S r * (S : Int) =
      -(-amount * (r : Int) - (-amount * (r : Int) / (S : Int)) * (S : Int)) := by
    rw [hbase]
    exact plan1_heq_via_omega amount S r
  rw [heq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro hle
    omega
  · intro _
    omega

theorem plan0_baseAt_bounds (amount : Int) (S r : Nat) (hS : 0 < S) :
    -(S : Int) < amount * (r : Int) - baseAt amount S r * (S : Int) ∧
    amount * (r : Int) - baseAt amount S r * (S : Int) < (S : Int) ∧
    (0 ≤ amount → 0 ≤ amount * (r : Int) - baseAt amount S r * (S : Int)) ∧
    (amount ≤ 0 → amount * (r : Int) - baseAt amount S r * (S : Int) ≤ 0) := by
  by_cases ha : 0 ≤ amount
  · exact plan1_baseAt_bounds_of_nonneg amount S r hS ha
  · exact plan1_baseAt_bounds_of_neg amount S r hS ha

theorem probe_mul_le : True := by trivial
#check @Int.mul_le_mul_right
#check @Int.mul_lt_mul_right
#check @Int.mul_nonneg
#check @Int.mul_pos
#check @Int.ediv_mul_cancel
#check @Int.le_of_mul_le_mul_right
#check @Int.lt_of_mul_lt_mul_right

theorem probe_div_lemmas2 : True := by trivial
#check @Int.mul_le_mul_left
#check @Int.mul_le_mul_right
#check @Int.mul_lt_mul_left
#check @Int.mul_lt_mul_right

theorem probe_cancel_sig : True := by trivial
#check @Int.le_of_mul_le_mul_right
#check @Int.lt_of_mul_lt_mul_right
#check @Int.le_of_mul_le_mul_left

theorem probe_mul_neg_names : True := by trivial
#check @Int.mul_pos
#check @Int.mul_nonneg
#check @Int.mul_neg_of_neg_of_pos
#check @Int.mul_neg_of_pos_of_neg
#check @Int.mul_nonpos_of_nonpos_of_nonneg

theorem probe_toNat_lemmas : True := trivial
#check @Int.toNat_of_nonneg
#check @Int.toNat_sub_of_le
#check @Int.ofNat_toNat

theorem probe_sum_api4 : True := trivial

theorem probe_dummy2 : True := trivial

theorem probe_q1 : True := trivial

theorem probe_ok : True := trivial
#check @Int.mul_le_mul_left
#check @Int.mul_le_mul_right
#check @Int.mul_lt_mul_left
#check @Int.mul_lt_mul_right
#check @Int.ediv_mul_cancel

theorem toNat_test (x : Int) (h : 0 ≤ x) : ((x.toNat : Nat) : Int) = x := by
  omega

theorem toNat_le_test (x : Int) (n : Nat) (h1 : 0 ≤ x) (h2 : x ≤ (n : Int)) : x.toNat ≤ n := by
  omega

theorem prefers_self_false (keys : List Int) (i : Nat) : prefers keys i i = false := by
  unfold prefers
  simp
#check @List.length_filter_le
#check @List.length_range
#check @List.range_succ
#check List.filter_append

theorem probe_range_succ_test (n : Nat) : List.range (n+1) = List.range n ++ [n] := by
  exact List.range_succ
#check @List.range_succ
#check @List.filter_append
#check @List.length_append
#check @List.length_filter_le

theorem test_sig_order (keys : List Int) (n i : Nat) :
    ((List.range n).filter (fun j => prefers keys j i)).length ≤ n := by
  have h := List.length_filter_le (fun j => prefers keys j i) (List.range n)
  simp [List.length_range] at h
  exact h

theorem probe_filter_cons_form : True := trivial
#check @List.filter_cons
#check List.length_filter_le

theorem probe_filter_cons2 (p : Nat → Bool) (hd : Nat) (tl : List Nat) :
    (hd :: tl).filter p = if p hd then hd :: tl.filter p else tl.filter p := by
  by_cases h : p hd <;> simp [h]
#check @List.filter_cons



theorem plan2_prefers_self_false (keys : List Int) (i : Nat) :
    prefers keys i i = false := by
  unfold prefers
  simp




theorem plan2_rankOf_lt_range_length (keys : List Int) (n i : Nat) (hi : i < n) :
    rankOf keys n i < (List.range n).length := by
  unfold rankOf
  have hself : (fun j => prefers keys j i) i = false := by
    show prefers keys i i = false
    unfold prefers
    simp
  have hmem : i ∈ List.range n := by simp [List.mem_range, hi]
  have aux : ∀ (l : List Nat) (p : Nat → Bool), i ∈ l → p i = false → (l.filter p).length < l.length := by
    intro l p hm hp
    induction l with
    | nil => simp at hm
    | cons hd tl ih =>
      simp only [List.mem_cons] at hm
      by_cases hphd : p hd = true
      · have hfilt : ((hd :: tl).filter p).length = (tl.filter p).length + 1 := by simp [hphd]
        have hlen : (hd :: tl).length = tl.length + 1 := by simp
        rw [hfilt, hlen]
        cases hm with
        | inl heq => subst heq; simp [hphd] at hp
        | inr hmem => have ihh := ih hmem; omega
      · have hphdF : p hd = false := by cases h : p hd <;> simp_all
        have hfilt : ((hd :: tl).filter p).length = (tl.filter p).length := by simp [hphdF]
        have hlen : (hd :: tl).length = tl.length + 1 := by simp
        rw [hfilt, hlen]
        have hle : (tl.filter p).length ≤ tl.length := List.length_filter_le p tl
        omega
  exact aux (List.range n) (fun j => prefers keys j i) hmem hself


theorem my_filter_aux2 (l : List Nat) (p : Nat → Bool)
    (x : Nat) (hx : x ∈ l) (hpx : p x = false) :
    (l.filter p).length < l.length := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    have hlen : (hd :: tl).length = tl.length + 1 := by simp
    simp only [List.mem_cons] at hx
    by_cases hphd : p hd = true
    · have hfilt : ((hd :: tl).filter p).length = (tl.filter p).length + 1 := by
        simp [hphd]
      rw [hfilt, hlen]
      cases hx with
      | inl heq =>
        subst heq
        simp [hphd] at hpx
      | inr hmem =>
        have ihh := ih hmem
        omega
    · have hphdF : p hd = false := by cases h : p hd <;> simp_all
      have hfilt : ((hd :: tl).filter p).length = (tl.filter p).length := by
        simp [hphdF]
      rw [hfilt, hlen]
      have hle : (tl.filter p).length ≤ tl.length := List.length_filter_le p tl
      omega

theorem plan2_filter_length_lt_of_mem_false (l : List Nat) (p : Nat → Bool)
    (x : Nat) (hx : x ∈ l) (hpx : p x = false) :
    (l.filter p).length < l.length :=
  my_filter_aux2 l p x hx hpx

theorem plan2_prefers_self_false_v2 (keys : List Int) (i : Nat) :
    prefers keys i i = false := by
  unfold prefers
  simp

theorem plan2_prefers_self_false2 (keys : List Int) (i : Nat) :
    prefers keys i i = false := by
  unfold prefers
  simp

theorem plan2_mem_range_of_lt (n i : Nat) (hi : i < n) :
    i ∈ List.range n := by
  simp [List.mem_range] at hi ⊢
  exact hi

theorem plan2_rankOf_lt_range_length_proof (keys : List Int) (n i : Nat) (hi : i < n) :
    rankOf keys n i < (List.range n).length := by
  unfold rankOf
  have hself : (fun j => prefers keys j i) i = false := by
    show prefers keys i i = false
    unfold prefers
    simp
  have hmem : i ∈ List.range n := by
    simp [List.mem_range, hi]
  have aux : ∀ (l : List Nat) (p : Nat → Bool), i ∈ l → p i = false → (l.filter p).length < l.length := by
    intro l p hm hp
    induction l with
    | nil => simp at hm
    | cons hd tl ih =>
      simp only [List.mem_cons] at hm
      by_cases hphd : p hd = true
      · have hfilt : ((hd :: tl).filter p).length = (tl.filter p).length + 1 := by simp [hphd]
        have hlen : (hd :: tl).length = tl.length + 1 := by simp
        rw [hfilt, hlen]
        cases hm with
        | inl heq =>
          subst heq
          simp [hphd] at hp
        | inr hmem =>
          have ihh := ih hmem
          omega
      · have hphdF : p hd = false := by cases h : p hd <;> simp_all
        have hfilt : ((hd :: tl).filter p).length = (tl.filter p).length := by simp [hphdF]
        have hlen : (hd :: tl).length = tl.length + 1 := by simp
        rw [hfilt, hlen]
        have hle : (tl.filter p).length ≤ tl.length := List.length_filter_le p tl
        omega
  exact aux (List.range n) (fun j => prefers keys j i) hmem hself


theorem plan2_rankOf_lt_range_length_aux_unique (keys : List Int) (n i : Nat) (hi : i < n) :
    rankOf keys n i < (List.range n).length :=
  plan2_rankOf_lt_range_length_proof keys n i hi

theorem plan2_rankOf_self_contained_test (keys : List Int) (n i : Nat) (hi : i < n) :
    rankOf keys n i < (List.range n).length := by
  unfold rankOf
  have hself : (fun j => prefers keys j i) i = false := by
    show prefers keys i i = false
    unfold prefers
    simp
  have hmem : i ∈ List.range n := by
    simp [List.mem_range, hi]
  have aux : ∀ (l : List Nat) (p : Nat → Bool), i ∈ l → p i = false → (l.filter p).length < l.length := by
    intro l p hm hp
    induction l with
    | nil => simp at hm
    | cons hd tl ih =>
      simp only [List.mem_cons] at hm
      by_cases hphd : p hd = true
      · have hfilt : ((hd :: tl).filter p).length = (tl.filter p).length + 1 := by simp [hphd]
        have hlen : (hd :: tl).length = tl.length + 1 := by simp
        rw [hfilt, hlen]
        cases hm with
        | inl heq =>
          subst heq
          simp [hphd] at hp
        | inr hmem =>
          have ihh := ih hmem
          omega
      · have hphdF : p hd = false := by cases h : p hd <;> simp_all
        have hfilt : ((hd :: tl).filter p).length = (tl.filter p).length := by simp [hphdF]
        have hlen : (hd :: tl).length = tl.length + 1 := by simp
        rw [hfilt, hlen]
        have hle : (tl.filter p).length ≤ tl.length := List.length_filter_le p tl
        omega
  exact aux (List.range n) (fun j => prefers keys j i) hmem hself
theorem plan2_rankOf_self_contained_test_dup : True := trivial

theorem plan0_rankOf_lt (keys : List Int) (n i : Nat) (hi : i < n) :
    rankOf keys n i < n := by
  have h := plan2_rankOf_self_contained_test keys n i hi
  simp [List.length_range] at h
  exact h

theorem prefers_trans_aux (keys : List Int) (a b c : Nat)
    (hab : prefers keys a b = true) (hbc : prefers keys b c = true) :
    prefers keys a c = true := by
  unfold prefers at *
  by_cases h1 : keys.getD a 0 > keys.getD b 0
  · rw [if_pos h1] at hab
    by_cases h2 : keys.getD b 0 > keys.getD c 0
    · have hgt : keys.getD a 0 > keys.getD c 0 := by omega
      rw [if_pos hgt]
    · have h2f : ¬ keys.getD b 0 > keys.getD c 0 := h2
      rw [if_neg h2f] at hbc
      by_cases h2l : keys.getD b 0 < keys.getD c 0
      · rw [if_pos h2l] at hbc
        contradiction
      · rw [if_neg h2l] at hbc
        have hbc' : b < c := of_decide_eq_true hbc
        have hgt : keys.getD a 0 > keys.getD c 0 := by omega
        rw [if_pos hgt]
  · have h1f : ¬ keys.getD a 0 > keys.getD b 0 := h1
    rw [if_neg h1f] at hab
    by_cases h1l : keys.getD a 0 < keys.getD b 0
    · rw [if_pos h1l] at hab
      contradiction
    · rw [if_neg h1l] at hab
      have hab' : a < b := of_decide_eq_true hab
      have heq1 : keys.getD a 0 = keys.getD b 0 := by omega
      by_cases h2 : keys.getD b 0 > keys.getD c 0
      · have hgt : keys.getD a 0 > keys.getD c 0 := by omega
        rw [if_pos hgt]
      · have h2f : ¬ keys.getD b 0 > keys.getD c 0 := h2
        rw [if_neg h2f] at hbc
        by_cases h2l : keys.getD b 0 < keys.getD c 0
        · rw [if_pos h2l] at hbc
          contradiction
        · rw [if_neg h2l] at hbc
          have hbc' : b < c := of_decide_eq_true hbc
          have heq2 : keys.getD b 0 = keys.getD c 0 := by omega
          have heq : keys.getD a 0 = keys.getD c 0 := by omega
          have hlt : a < c := by omega
          have hgtf : ¬ keys.getD a 0 > keys.getD c 0 := by omega
          have hltf : ¬ keys.getD a 0 < keys.getD c 0 := by omega
          rw [if_neg hgtf, if_neg hltf]
          exact decide_eq_true hlt

theorem prefers_total_aux (keys : List Int) (i j : Nat) (hne : i ≠ j) :
    prefers keys i j = true ∨ prefers keys j i = true := by
  unfold prefers
  by_cases h1 : keys.getD i 0 > keys.getD j 0
  · rw [if_pos h1]; exact Or.inl rfl
  · rw [if_neg h1]
    by_cases h1l : keys.getD i 0 < keys.getD j 0
    · rw [if_pos h1l]
      have hgt : keys.getD j 0 > keys.getD i 0 := by omega
      have : (if keys.getD j 0 > keys.getD i 0 then (true : Bool) else if keys.getD j 0 < keys.getD i 0 then false else decide (j < i)) = true := by
        rw [if_pos hgt]
      rw [this]; exact Or.inr rfl
    · rw [if_neg h1l]
      have heq : keys.getD i 0 = keys.getD j 0 := by omega
      have heqs : keys.getD j 0 = keys.getD i 0 := by omega
      by_cases hij : i < j
      · rw [decide_eq_true hij]
        exact Or.inl rfl
      · have hji : j < i := by omega
        have h1b : (decide (i < j) : Bool) = false := decide_eq_false (by omega)
        rw [h1b]
        have h2 : (if keys.getD j 0 > keys.getD i 0 then (true : Bool) else if keys.getD j 0 < keys.getD i 0 then false else decide (j < i)) = true := by
          have hgtf : ¬ keys.getD j 0 > keys.getD i 0 := by omega
          have hltf : ¬ keys.getD j 0 < keys.getD i 0 := by omega
          rw [if_neg hgtf, if_neg hltf, decide_eq_true hji]
        rw [h2]; exact Or.inr rfl

theorem prefers_self_false_aux2 (keys : List Int) (i : Nat) : prefers keys i i = false := by
  unfold prefers
  by_cases h : keys.getD i 0 > keys.getD i 0
  · omega
  · have h1 : (if keys.getD i 0 > keys.getD i 0 then (true : Bool) else if keys.getD i 0 < keys.getD i 0 then false else decide (i < i)) = (if keys.getD i 0 < keys.getD i 0 then (false : Bool) else decide (i < i)) := by
      rw [if_neg h]
    rw [h1]
    by_cases h2 : keys.getD i (0 : Int) < keys.getD i 0
    · omega
    · have h2b : (if keys.getD i 0 < keys.getD i 0 then (false : Bool) else decide (i < i)) = decide (i < i) := by
        rw [if_neg h2]
      rw [h2b]
      exact decide_eq_false (by omega)

theorem filter_strict_mono_gen : ∀ (l : List Nat) (p q : Nat → Bool) (w : Nat),
    (∀ x ∈ l, p x = true → q x = true) → w ∈ l → q w = true → p w = false →
    (l.filter p).length < (l.filter q).length := by
  intro l
  induction l with
  | nil =>
    intro p q w hsub hwmem hwq hwp
    simp at hwmem
  | cons hd tl ih =>
    intro p q w hsub hwmem hwq hwp
    simp only [List.mem_cons] at hwmem
    by_cases hphd : p hd = true
    · have hqhd : q hd = true := hsub hd (by simp) hphd
      have e1 : ((hd :: tl).filter p).length = (tl.filter p).length + 1 := by simp [hphd]
      have e2 : ((hd :: tl).filter q).length = (tl.filter q).length + 1 := by simp [hqhd]
      rw [e1, e2]
      cases hwmem with
      | inl heq =>
        subst heq
        simp [hphd] at hwp
      | inr hmem =>
        have hsub' : ∀ x ∈ tl, p x = true → q x = true :=
          fun x hx hpx => hsub x (by simp [hx]) hpx
        have hlt := ih p q w hsub' hmem hwq hwp
        omega
    · have hphdF : p hd = false := by cases h : p hd <;> simp_all
      have e1 : ((hd :: tl).filter p).length = (tl.filter p).length := by simp [hphdF]
      rw [e1]
      by_cases hqhd : q hd = true
      · have e2 : ((hd :: tl).filter q).length = (tl.filter q).length + 1 := by simp [hqhd]
        rw [e2]
        have hsub' : ∀ x ∈ tl, p x = true → q x = true :=
          fun x hx hpx => hsub x (by simp [hx]) hpx
        have hle := filter_mono_len tl p q hsub'
        omega
      · have hqhdF : q hd = false := by cases h : q hd <;> simp_all
        have e2 : ((hd :: tl).filter q).length = (tl.filter q).length := by simp [hqhdF]
        rw [e2]
        cases hwmem with
        | inl heq =>
          subst heq
          simp [hqhdF] at hwq
        | inr hmem =>
          have hsub' : ∀ x ∈ tl, p x = true → q x = true :=
            fun x hx hpx => hsub x (by simp [hx]) hpx
          exact ih p q w hsub' hmem hwq hwp

theorem plan0_rankOf_inj_check (keys : List Int) (n i j : Nat) (hi : i < n) (hj : j < n)
    (h : rankOf keys n i = rankOf keys n j) : i = j := by
  by_cases heq : i = j
  · exact heq
  · have hne : i ≠ j := heq
    have hdisj := prefers_total_aux keys i j hne
    cases hdisj with
    | inl hij =>
      have hmem : i ∈ List.range n := by simp [List.mem_range, hi]
      have hself : prefers keys i i = false := prefers_self_false_aux2 keys i
      have hsub : ∀ x ∈ List.range n, (fun k => prefers keys k i) x = true → (fun k => prefers keys k j) x = true := by
        intro x _ hx
        simp only at hx ⊢
        exact prefers_trans_aux keys x i j hx hij
      have hlt := filter_strict_mono_gen (List.range n) (fun k => prefers keys k i) (fun k => prefers keys k j) i hsub hmem hij hself
      unfold rankOf at h
      omega
    | inr hji =>
      have hmem : j ∈ List.range n := by simp [List.mem_range, hj]
      have hself : prefers keys j j = false := prefers_self_false_aux2 keys j
      have hsub : ∀ x ∈ List.range n, (fun k => prefers keys k j) x = true → (fun k => prefers keys k i) x = true := by
        intro x _ hx
        simp only at hx ⊢
        exact prefers_trans_aux keys x j i hx hji
      have hlt := filter_strict_mono_gen (List.range n) (fun k => prefers keys k j) (fun k => prefers keys k i) j hsub hmem hji hself
      unfold rankOf at h
      omega













theorem plan3_prefers_self_false_test (keys : List Int) (i : Nat) : prefers keys i i = false := by unfold prefers; simp

theorem plan3_prefers_self_false (keys : List Int) (i : Nat) : prefers keys i i = false := by unfold prefers; simp

theorem plan3_prefers_trans (keys : List Int) (a b c : Nat)
    (hab : prefers keys a b = true) (hbc : prefers keys b c = true) :
    prefers keys a c = true := by
  unfold prefers at *
  by_cases h1 : keys.getD a 0 > keys.getD b 0
  · rw [if_pos h1] at hab
    by_cases h2 : keys.getD b 0 > keys.getD c 0
    · have hgt : keys.getD a 0 > keys.getD c 0 := by omega
      rw [if_pos hgt]
    · have h2f : ¬ keys.getD b 0 > keys.getD c 0 := h2
      rw [if_neg h2f] at hbc
      by_cases h2l : keys.getD b 0 < keys.getD c 0
      · rw [if_pos h2l] at hbc
        contradiction
      · rw [if_neg h2l] at hbc
        have hbc' : b < c := of_decide_eq_true hbc
        have hgt : keys.getD a 0 > keys.getD c 0 := by omega
        rw [if_pos hgt]
  · have h1f : ¬ keys.getD a 0 > keys.getD b 0 := h1
    rw [if_neg h1f] at hab
    by_cases h1l : keys.getD a 0 < keys.getD b 0
    · rw [if_pos h1l] at hab
      contradiction
    · rw [if_neg h1l] at hab
      have hab' : a < b := of_decide_eq_true hab
      have heq1 : keys.getD a 0 = keys.getD b 0 := by omega
      by_cases h2 : keys.getD b 0 > keys.getD c 0
      · have hgt : keys.getD a 0 > keys.getD c 0 := by omega
        rw [if_pos hgt]
      · have h2f : ¬ keys.getD b 0 > keys.getD c 0 := h2
        rw [if_neg h2f] at hbc
        by_cases h2l : keys.getD b 0 < keys.getD c 0
        · rw [if_pos h2l] at hbc
          contradiction
        · rw [if_neg h2l] at hbc
          have hbc' : b < c := of_decide_eq_true hbc
          have heq2 : keys.getD b 0 = keys.getD c 0 := by omega
          have heq : keys.getD a 0 = keys.getD c 0 := by omega
          have hlt : a < c := by omega
          have hgtf : ¬ keys.getD a 0 > keys.getD c 0 := by omega
          have hltf : ¬ keys.getD a 0 < keys.getD c 0 := by omega
          rw [if_neg hgtf, if_neg hltf]
          exact decide_eq_true hlt

theorem plan3_prefers_total (keys : List Int) (i j : Nat) (hne : i ≠ j) :
    prefers keys i j = true ∨ prefers keys j i = true :=
  prefers_total_aux keys i j hne

theorem plan3_filter_length_le_check (l : List Nat) (p q : Nat → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length :=
  filter_mono_len l p q h

theorem plan3_filter_length_le (l : List Nat) (p q : Nat → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length :=
  filter_mono_len l p q h

theorem plan3_filter_length_lt (l : List Nat) (p q : Nat → Bool) (w : Nat)
    (h : ∀ x ∈ l, p x = true → q x = true)
    (hw : w ∈ l) (hqw : q w = true) (hpw : p w = false) :
    (l.filter p).length < (l.filter q).length :=
  filter_strict_mono_gen l p q w h hw hqw hpw

theorem plan3_rankOf_lt_of_prefers_aux (keys : List Int) (n i j : Nat)
    (hi : i < n) (hpref : prefers keys i j = true) :
    rankOf keys n i < rankOf keys n j := by
  unfold rankOf
  have hsub : ∀ x ∈ List.range n, (fun k => prefers keys k i) x = true → (fun k => prefers keys k j) x = true := by
    intro x _ hx
    exact plan3_prefers_trans keys x i j hx hpref
  have hmem : i ∈ List.range n := by
    rw [List.mem_range]
    exact hi
  have hq : (fun k => prefers keys k j) i = true := hpref
  have hp : (fun k => prefers keys k i) i = false := plan3_prefers_self_false keys i
  exact filter_strict_mono_gen (List.range n) (fun k => prefers keys k i) (fun k => prefers keys k j) i hsub hmem hq hp

theorem plan3_rankOf_lt_of_prefers (keys : List Int) (n i j : Nat)
    (hi : i < n) (hpref : prefers keys i j = true) :
    rankOf keys n i < rankOf keys n j := by
  unfold rankOf
  have hsub : ∀ x ∈ List.range n, (fun k => prefers keys k i) x = true → (fun k => prefers keys k j) x = true := by
    intro x _ hx
    exact plan3_prefers_trans keys x i j hx hpref
  have hmem : i ∈ List.range n := by
    rw [List.mem_range]
    exact hi
  have hq : (fun k => prefers keys k j) i = true := hpref
  have hp : (fun k => prefers keys k i) i = false := plan3_prefers_self_false keys i
  exact filter_strict_mono_gen (List.range n) (fun k => prefers keys k i) (fun k => prefers keys k j) i hsub hmem hq hp

theorem plan0_rankOf_inj_newproof (keys : List Int) (n i j : Nat) (hi : i < n) (hj : j < n)
    (h : rankOf keys n i = rankOf keys n j) : i = j :=
  plan0_rankOf_inj_check keys n i j hi hj h

theorem plan0_rankOf_inj_selfcontained (keys : List Int) (n i j : Nat) (hi : i < n) (hj : j < n)
    (h : rankOf keys n i = rankOf keys n j) : i = j := by
  have hself : ∀ k : Nat, prefers keys k k = false := fun k => by unfold prefers; simp
  have htrans : ∀ a b c : Nat, prefers keys a b = true → prefers keys b c = true → prefers keys a c = true := by
    intro a b c hab hbc
    unfold prefers at *
    by_cases h1 : keys.getD a 0 > keys.getD b 0
    · rw [if_pos h1] at hab
      by_cases h2 : keys.getD b 0 > keys.getD c 0
      · have hgt : keys.getD a 0 > keys.getD c 0 := by omega
        rw [if_pos hgt]
      · have h2f : ¬ keys.getD b 0 > keys.getD c 0 := h2
        rw [if_neg h2f] at hbc
        by_cases h2l : keys.getD b 0 < keys.getD c 0
        · rw [if_pos h2l] at hbc; contradiction
        · rw [if_neg h2l] at hbc
          have hgt : keys.getD a 0 > keys.getD c 0 := by omega
          rw [if_pos hgt]
    · have h1f : ¬ keys.getD a 0 > keys.getD b 0 := h1
      rw [if_neg h1f] at hab
      by_cases h1l : keys.getD a 0 < keys.getD b 0
      · rw [if_pos h1l] at hab; contradiction
      · rw [if_neg h1l] at hab
        have hab' : a < b := of_decide_eq_true hab
        by_cases h2 : keys.getD b 0 > keys.getD c 0
        · have hgt : keys.getD a 0 > keys.getD c 0 := by omega
          rw [if_pos hgt]
        · have h2f : ¬ keys.getD b 0 > keys.getD c 0 := h2
          rw [if_neg h2f] at hbc
          by_cases h2l : keys.getD b 0 < keys.getD c 0
          · rw [if_pos h2l] at hbc; contradiction
          · rw [if_neg h2l] at hbc
            have hbc' : b < c := of_decide_eq_true hbc
            have hlt : a < c := by omega
            have hgtf : ¬ keys.getD a 0 > keys.getD c 0 := by omega
            have hltf : ¬ keys.getD a 0 < keys.getD c 0 := by omega
            rw [if_neg hgtf, if_neg hltf]
            exact decide_eq_true hlt
  have htotal : ∀ x y : Nat, x ≠ y → prefers keys x y = true ∨ prefers keys y x = true := by
    intro x y hne
    unfold prefers
    by_cases h1 : keys.getD x 0 > keys.getD y 0
    · rw [if_pos h1]; exact Or.inl rfl
    · rw [if_neg h1]
      by_cases h1l : keys.getD x 0 < keys.getD y 0
      · rw [if_pos h1l]
        have hgt : keys.getD y 0 > keys.getD x 0 := by omega
        have hpos : (if keys.getD y 0 > keys.getD x 0 then (true : Bool) else if keys.getD y 0 < keys.getD x 0 then false else decide (y < x)) = true := by rw [if_pos hgt]
        rw [hpos]; exact Or.inr rfl
      · rw [if_neg h1l]
        by_cases hxy : x < y
        · rw [decide_eq_true hxy]; exact Or.inl rfl
        · have hyx : y < x := by omega
          have h1b : (decide (x < y) : Bool) = false := decide_eq_false (by omega)
          rw [h1b]
          have h2 : (if keys.getD y 0 > keys.getD x 0 then (true : Bool) else if keys.getD y 0 < keys.getD x 0 then false else decide (y < x)) = true := by
            have hgtf : ¬ keys.getD y 0 > keys.getD x 0 := by omega
            have hltf : ¬ keys.getD y 0 < keys.getD x 0 := by omega
            rw [if_neg hgtf, if_neg hltf, decide_eq_true hyx]
          rw [h2]; exact Or.inr rfl
  have hstrict : ∀ (l : List Nat) (p q : Nat → Bool) (w : Nat),
      (∀ x ∈ l, p x = true → q x = true) → w ∈ l → q w = true → p w = false →
      (l.filter p).length < (l.filter q).length := by
    intro l
    induction l with
    | nil => intro p q w hsub hwmem hwq hwp; simp at hwmem
    | cons hd tl ih =>
      intro p q w hsub hwmem hwq hwp
      simp only [List.mem_cons] at hwmem
      by_cases hphd : p hd = true
      · have hqhd : q hd = true := hsub hd (by simp) hphd
        have e1 : ((hd :: tl).filter p).length = (tl.filter p).length + 1 := by simp [hphd]
        have e2 : ((hd :: tl).filter q).length = (tl.filter q).length + 1 := by simp [hqhd]
        rw [e1, e2]
        cases hwmem with
        | inl heq => subst heq; simp [hphd] at hwp
        | inr hmem =>
          have hsub' : ∀ x ∈ tl, p x = true → q x = true := fun x hx hpx => hsub x (by simp [hx]) hpx
          have hlt := ih p q w hsub' hmem hwq hwp
          omega
      · have hphdF : p hd = false := by cases h : p hd <;> simp_all
        have e1 : ((hd :: tl).filter p).length = (tl.filter p).length := by simp [hphdF]
        rw [e1]
        by_cases hqhd : q hd = true
        · have e2 : ((hd :: tl).filter q).length = (tl.filter q).length + 1 := by simp [hqhd]
          rw [e2]
          have hsub' : ∀ x ∈ tl, p x = true → q x = true := fun x hx hpx => hsub x (by simp [hx]) hpx
          have hle := filter_mono_len tl p q hsub'
          omega
        · have hqhdF : q hd = false := by cases h : q hd <;> simp_all
          have e2 : ((hd :: tl).filter q).length = (tl.filter q).length := by simp [hqhdF]
          rw [e2]
          cases hwmem with
          | inl heq => subst heq; simp [hqhdF] at hwq
          | inr hmem =>
            have hsub' : ∀ x ∈ tl, p x = true → q x = true := fun x hx hpx => hsub x (by simp [hx]) hpx
            exact ih p q w hsub' hmem hwq hwp
  by_cases heq : i = j
  · exact heq
  · have hne : i ≠ j := heq
    have hdisj := htotal i j hne
    cases hdisj with
    | inl hij =>
      have hmem : i ∈ List.range n := by simp [List.mem_range, hi]
      have hs := hself i
      have hsub : ∀ x ∈ List.range n, (fun k => prefers keys k i) x = true → (fun k => prefers keys k j) x = true := by
        intro x _ hx; simp only at hx ⊢; exact htrans x i j hx hij
      have hlt := hstrict (List.range n) (fun k => prefers keys k i) (fun k => prefers keys k j) i hsub hmem hij hs
      unfold rankOf at h; omega
    | inr hji =>
      have hmem : j ∈ List.range n := by simp [List.mem_range, hj]
      have hs := hself j
      have hsub : ∀ x ∈ List.range n, (fun k => prefers keys k j) x = true → (fun k => prefers keys k i) x = true := by
        intro x _ hx; simp only at hx ⊢; exact htrans x j i hx hji
      have hlt := hstrict (List.range n) (fun k => prefers keys k j) (fun k => prefers keys k i) j hsub hmem hji hs
      unfold rankOf at h; omega

theorem plan0_rankOf_inj_dup2 (keys : List Int) (n i j : Nat) (hi : i < n) (hj : j < n)
    (h : rankOf keys n i = rankOf keys n j) : i = j := by
  have hself : ∀ k : Nat, prefers keys k k = false := fun k => by unfold prefers; simp
  have htrans : ∀ a b c : Nat, prefers keys a b = true → prefers keys b c = true → prefers keys a c = true := by
    intro a b c hab hbc
    unfold prefers at *
    by_cases h1 : keys.getD a 0 > keys.getD b 0
    · rw [if_pos h1] at hab
      by_cases h2 : keys.getD b 0 > keys.getD c 0
      · have hgt : keys.getD a 0 > keys.getD c 0 := by omega
        rw [if_pos hgt]
      · have h2f : ¬ keys.getD b 0 > keys.getD c 0 := h2
        rw [if_neg h2f] at hbc
        by_cases h2l : keys.getD b 0 < keys.getD c 0
        · rw [if_pos h2l] at hbc; contradiction
        · rw [if_neg h2l] at hbc
          have hgt : keys.getD a 0 > keys.getD c 0 := by omega
          rw [if_pos hgt]
    · have h1f : ¬ keys.getD a 0 > keys.getD b 0 := h1
      rw [if_neg h1f] at hab
      by_cases h1l : keys.getD a 0 < keys.getD b 0
      · rw [if_pos h1l] at hab; contradiction
      · rw [if_neg h1l] at hab
        have hab' : a < b := of_decide_eq_true hab
        by_cases h2 : keys.getD b 0 > keys.getD c 0
        · have hgt : keys.getD a 0 > keys.getD c 0 := by omega
          rw [if_pos hgt]
        · have h2f : ¬ keys.getD b 0 > keys.getD c 0 := h2
          rw [if_neg h2f] at hbc
          by_cases h2l : keys.getD b 0 < keys.getD c 0
          · rw [if_pos h2l] at hbc; contradiction
          · rw [if_neg h2l] at hbc
            have hbc' : b < c := of_decide_eq_true hbc
            have hlt : a < c := by omega
            have hgtf : ¬ keys.getD a 0 > keys.getD c 0 := by omega
            have hltf : ¬ keys.getD a 0 < keys.getD c 0 := by omega
            rw [if_neg hgtf, if_neg hltf]
            exact decide_eq_true hlt
  exact plan0_rankOf_inj_selfcontained keys n i j hi hj h

theorem plan0_rankOf_inj (keys : List Int) (n i j : Nat) (hi : i < n) (hj : j < n)
    (h : rankOf keys n i = rankOf keys n j) : i = j :=
  plan0_rankOf_inj_selfcontained keys n i j hi hj h

theorem probe_nodup2 : True := by trivial
#check @List.nodup_range
#check @List.Nodup
open List in
example (n : Nat) : (List.range n).Nodup := by
  exact List.nodup_range

theorem probe_perm_api : True := by trivial
#check @List.Perm
#check @List.isPerm
#check @List.Nodup
#check @List.nodup_range
#check @List.length_range
#check @List.mem_range

theorem plan4_rankOf_lt_n (keys : List Int) (n i : Nat) (hi : i < n) :
    rankOf keys n i < n :=
  plan0_rankOf_lt keys n i hi


theorem plan4_rankOf_injective (keys : List Int) (n i j : Nat)
    (hi : i < n) (hj : j < n)
    (h : rankOf keys n i = rankOf keys n j) : i = j :=
  plan0_rankOf_inj keys n i j hi hj h








theorem plan4_rankOf_lt_n_aux_unique : rankOf ([] : List Int) 0 0 = 0 := by rfl

theorem plan4_rankOf_lt_n_pf : ∀ (keys : List Int) (n i : Nat), i < n → rankOf keys n i < n := fun keys n i hi => plan0_rankOf_lt keys n i hi

theorem plan4_rankOf_injective_proof (keys : List Int) (n i j : Nat)
    (hi : i < n) (hj : j < n)
    (h : rankOf keys n i = rankOf keys n j) : i = j :=
  plan0_rankOf_inj keys n i j hi hj h

theorem plan4_rankOf_injective_dup_test (keys : List Int) (n i j : Nat)
    (hi : i < n) (hj : j < n)
    (h : rankOf keys n i = rankOf keys n j) : i = j :=
  plan0_rankOf_inj keys n i j hi hj h

theorem pigeonhole_surj_aux : ∀ (n : Nat) (f : Nat → Nat),
    (∀ i, i < n → f i < n) → (∀ i j, i < n → j < n → f i = f j → i = j) →
    ∀ k, k < n → ∃ i, i < n ∧ f i = k := by
  intro n
  induction n with
  | zero =>
    intro f _ _ k hk
    omega
  | succ n ih =>
    intro f hbound hinj k hk
    by_cases hex : ∃ i0, i0 < n ∧ f i0 = n
    · obtain ⟨i0, hi0lt, hi0eq⟩ := hex
      have hfn_ne_n : f n ≠ n := by
        intro hcon
        have hmem1 : i0 < n + 1 := by omega
        have hmem2 : n < n + 1 := by omega
        have heq : f n = f i0 := hcon.trans hi0eq.symm
        have := hinj i0 n hmem1 hmem2 heq.symm
        omega
      by_cases hk_eq : k = n
      · rw [hk_eq]
        exact ⟨i0, by omega, hi0eq⟩
      · have hk_lt_n : k < n := by omega
        have hg_bound : ∀ i, i < n → (if i = i0 then f n else if i = n then n else f i) < n := by
          intro i hi
          by_cases hi_eq : i = i0
          · rw [if_pos hi_eq]
            have := hbound n (by omega)
            omega
          · rw [if_neg hi_eq]
            by_cases hi_eqn : i = n
            · omega
            · rw [if_neg hi_eqn]
              have hfi : f i < n + 1 := hbound i (by omega)
              have hfi_ne : f i ≠ n := by
                intro hcon
                have h1 : i < n + 1 := by omega
                have h2 : i0 < n + 1 := by omega
                have heq : f i = f i0 := hcon.trans hi0eq.symm
                have := hinj i i0 h1 h2 heq
                exact hi_eq this
              omega
        have hg_inj : ∀ i j, i < n → j < n →
            (if i = i0 then f n else if i = n then n else f i) =
            (if j = i0 then f n else if j = n then n else f j) → i = j := by
          intro i j hi hj heq
          by_cases hi_eq : i = i0
          · by_cases hj_eq : j = i0
            · rw [hi_eq, hj_eq]
            · rw [if_pos hi_eq] at heq
              rw [if_neg hj_eq] at heq
              by_cases hj_eqn : j = n
              · omega
              · rw [if_neg hj_eqn] at heq
                have hcontra : f n = f j := heq
                have := hinj n j (by omega) (by omega) hcontra
                omega
          · by_cases hj_eq : j = i0
            · rw [if_neg hi_eq] at heq
              rw [if_pos hj_eq] at heq
              by_cases hi_eqn : i = n
              · omega
              · rw [if_neg hi_eqn] at heq
                have hcontra : f i = f n := heq
                have := hinj i n (by omega) (by omega) hcontra
                omega
            · rw [if_neg hi_eq] at heq
              rw [if_neg hj_eq] at heq
              by_cases hi_eqn : i = n
              · omega
              · by_cases hj_eqn : j = n
                · omega
                · rw [if_neg hi_eqn] at heq
                  rw [if_neg hj_eqn] at heq
                  exact hinj i j (by omega) (by omega) heq
        obtain ⟨i, hi_lt, hi_eq⟩ := ih _ hg_bound hg_inj k hk_lt_n
        by_cases hi_eq_i0 : i = i0
        · subst hi_eq_i0
          rw [if_pos rfl] at hi_eq
          exact ⟨n, by omega, hi_eq⟩
        · have hi_ne_n : i ≠ n := by omega
          rw [if_neg hi_eq_i0, if_neg hi_ne_n] at hi_eq
          exact ⟨i, by omega, hi_eq⟩
    · have hex2 : ∀ i0, i0 < n → f i0 ≠ n := by
        intro i0 hi0 hcon
        exact hex ⟨i0, hi0, hcon⟩
      have hf_bound_n : ∀ i, i < n → f i < n := by
        intro i hi
        have hfi := hbound i (by omega)
        have hne : f i ≠ n := hex2 i hi
        omega
      have hf_inj_n : ∀ i j, i < n → j < n → f i = f j → i = j := by
        intro i j hi hj heq
        exact hinj i j (by omega) (by omega) heq
      by_cases hk_eq : k = n
      · have hfn_eq : f n = n := by
          by_cases hfn_eq : f n = n
          · exact hfn_eq
          · have hfn_lt : f n < n := by
              have hfb := hbound n (by omega)
              omega
            obtain ⟨i, hi_lt, hi_eq⟩ := ih f hf_bound_n hf_inj_n (f n) hfn_lt
            have h1 : i < n + 1 := by omega
            have h2 : n < n + 1 := by omega
            have := hinj i n h1 h2 hi_eq
            omega
        rw [hk_eq]
        exact ⟨n, by omega, hfn_eq⟩
      · have hk_lt_n : k < n := by omega
        obtain ⟨i, hi_lt, hi_eq⟩ := ih f hf_bound_n hf_inj_n k hk_lt_n
        exact ⟨i, by omega, hi_eq⟩

theorem plan4_exists_rankOf_eq (keys : List Int) (n k : Nat) (hk : k < n) :
    ∃ i, i < n ∧ rankOf keys n i = k := by
  exact pigeonhole_surj_aux n (rankOf keys n) (fun i hi => plan0_rankOf_lt keys n i hi)
    (fun i j hi hj h => plan0_rankOf_inj keys n i j hi hj h) k hk

theorem aux_noL_eq5 (f : Nat → Nat) (n L : Nat)
    (hno : ∀ i, i < n → f i ≠ L) :
    ((List.range n).filter (fun i => decide (f i < L + 1))).length =
      ((List.range n).filter (fun i => decide (f i < L))).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hno' : ∀ i, i < n → f i ≠ L := fun i hi hcon => hno i (by omega) hcon
    have ih' := ih hno'
    have hfn : f n ≠ L := hno n (by omega)
    have heq : decide (f n < L + 1) = decide (f n < L) := by
      by_cases h1 : f n < L
      · rw [decide_eq_true h1, decide_eq_true (by omega)]
      · have h2 : ¬ f n < L + 1 := by omega
        rw [decide_eq_false h1, decide_eq_false h2]
    have hr : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [hr, List.filter_append, List.filter_append, List.length_append, List.length_append, ih']
    have hsing : (([n].filter (fun i => decide (f i < L + 1)))).length =
      (([n].filter (fun i => decide (f i < L)))).length := by
      simp only [List.filter_cons, List.filter_nil]
      rw [heq]
    rw [hsing]

theorem plan4_filter_count_succ (f : Nat → Nat) (n L i0 : Nat)
    (hi0 : i0 < n) (hf0 : f i0 = L)
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j) :
    ((List.range n).filter (fun i => decide (f i < L + 1))).length =
      ((List.range n).filter (fun i => decide (f i < L))).length + 1 := by
  induction n generalizing L i0 with
  | zero => omega
  | succ m ih =>
    by_cases hi0m : i0 = m
    · have hno : ∀ i, i < m → f i ≠ L := by
        intro i hi hcon
        have h1 : i < m + 1 := by omega
        have h2 : i0 < m + 1 := hi0
        have heq := hinj i i0 h1 h2 (hcon.trans hf0.symm)
        omega
      have heqN := aux_noL_eq5 f m L hno
      have hfL : f m = L := hi0m ▸ hf0
      have hr : List.range (m + 1) = List.range m ++ [m] := List.range_succ
      have hA : decide (f m < L) = false := decide_eq_false (by omega)
      have hB : decide (f m < L + 1) = true := decide_eq_true (by omega)
      have hfltA : ((List.range (m+1)).filter (fun i => decide (f i < L))).length =
        (((List.range m).filter (fun i => decide (f i < L)))).length := by
        rw [hr, List.filter_append]
        simp [hA]
      have hfltB : ((List.range (m+1)).filter (fun i => decide (f i < L + 1))).length =
        (((List.range m).filter (fun i => decide (f i < L + 1)))).length + 1 := by
        rw [hr, List.filter_append]
        simp [hB]
      rw [hfltA, hfltB, heqN]
    · have hi0lt : i0 < m := by omega
      have hinj' : ∀ i j, i < m → j < m → f i = f j → i = j := by
        intro i j hi hj hcon
        exact hinj i j (by omega) (by omega) hcon
      have ih' := ih (L := L) (i0 := i0) hi0lt hf0 hinj'
      have hfn_ne : f m ≠ L := by
        intro hcon
        have heq := hinj i0 m hi0 (by omega) (hf0.trans hcon.symm)
        exact hi0m heq
      have heq : decide (f m < L + 1) = decide (f m < L) := by
        by_cases h1 : f m < L
        · rw [decide_eq_true h1, decide_eq_true (by omega)]
        · have h2 : ¬ f m < L + 1 := by omega
          rw [decide_eq_false h1, decide_eq_false h2]
      have hr : List.range (m + 1) = List.range m ++ [m] := List.range_succ
      have hfltA : ((List.range (m+1)).filter (fun i => decide (f i < L))).length =
        (((List.range m).filter (fun i => decide (f i < L)))).length +
          (([m].filter (fun i => decide (f i < L)))).length := by
        rw [hr, List.filter_append, List.length_append]
      have hfltB : ((List.range (m+1)).filter (fun i => decide (f i < L + 1))).length =
        (((List.range m).filter (fun i => decide (f i < L + 1)))).length +
          (([m].filter (fun i => decide (f i < L + 1)))).length := by
        rw [hr, List.filter_append, List.length_append]
      have hsing : (([m].filter (fun i => decide (f i < L + 1)))).length =
        (([m].filter (fun i => decide (f i < L)))).length := by
        simp only [List.filter_cons, List.filter_nil]
        rw [heq]
      rw [hfltA, hfltB, hsing, ih']
      omega

theorem plan4_count_filter_lt_eq_of_exists (f : Nat → Nat) (n L : Nat)
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j)
    (hex : ∀ k, k < n → ∃ i, i < n ∧ f i = k)
    (hL : L ≤ n) :
    ((List.range n).filter (fun i => decide (f i < L))).length = L := by
  induction L generalizing n with
  | zero =>
    have h0 : ∀ m : Nat, ((List.range m).filter (fun i => decide (f i < 0))).length = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ k ihk =>
        have hr : List.range (k + 1) = List.range k ++ [k] := List.range_succ
        rw [hr, List.filter_append, List.length_append, ihk]
        simp
    exact h0 n
  | succ L ih =>
    by_cases hLn : L < n
    · obtain ⟨i0, hi0lt, hi0eq⟩ := hex L hLn
      have hstep := plan4_filter_count_succ f n L i0 hi0lt hi0eq hinj
      have hprev := ih n hinj hex (by omega)
      omega
    · omega

theorem plan0_count_rankOf_lt (keys : List Int) (n L : Nat) (hL : L ≤ n) :
    ((List.range n).filter (fun i => decide (rankOf keys n i < L))).length = L := by
  exact plan4_count_filter_lt_eq_of_exists (rankOf keys n) n L
    (fun i j hi hj h => plan0_rankOf_inj keys n i j hi hj h)
    (fun k hk => plan4_exists_rankOf_eq keys n k hk) hL

theorem probe_sum_bump_types : True := trivial
#check @List.sum_cons
#check @List.sum_append
#check @List.range_succ
#check @List.range_succ_eq_map
#check @List.map_append
#check @List.filter_append
#check @List.length_append
#check @List.getD
#check List.sum

theorem bump_unfold_probe (a : Int) (l : List Int) : (a :: l).sum = a + l.sum := by
  rfl
#check List.sum

theorem probe_list_sum2 : True := trivial
#check List.sum_cons

theorem cast_probe1 (m : Nat) : (((m + 1 : Nat) : Int)) = (((m : Nat) : Int)) + 1 := by
  simp



theorem plan5_sum_range_getD (bs : List Int) :
    ((List.range bs.length).map (fun i => bs.getD i 0)).sum = bs.sum := by
  induction bs with
  | nil => rfl
  | cons a tl ih =>
    have h1 : List.range (tl.length + 1) = 0 :: (List.range tl.length).map Nat.succ := List.range_succ_eq_map
    have hlen : (a :: tl).length = tl.length + 1 := rfl
    rw [hlen, h1]
    simp only [List.map_cons]
    rw [List.sum_cons, List.sum_cons]
    have hget0 : (a :: tl).getD 0 0 = a := rfl
    rw [hget0]
    have hcomp : (fun i => (a :: tl).getD i 0) ∘ Nat.succ = (fun i => tl.getD i 0) := by
      funext i
      rfl
    have hmap : (((List.range tl.length).map Nat.succ).map (fun i => (a :: tl).getD i 0))
        = (List.range tl.length).map (fun i => tl.getD i 0) := by
      rw [List.map_map]
      rw [hcomp]
    rw [hmap, ih]






theorem plan5_getD_cons_succ (a : Int) (tl : List Int) (i : Nat) :
    (a :: tl).getD (i + 1) 0 = tl.getD i 0 := by simp [List.getD]

theorem plan5_sum_range_getD_check2 : True := trivial
#check @List.range_succ
#check @List.get_eq_getElem
#check @List.getElem_cons_succ

theorem plan5_range_eq_map_check : List.range 3 = [0,1,2] := by rfl
#check @List.range_succ_eq_map
#check @List.sum_append
#check @List.map_append

theorem srg_probe_a : True := trivial
#check @List.sum_append
#check @List.range_succ
#check @List.map_append

theorem srg_probe_e : True := trivial
#check List.range_succ_eq_map
#check List.range_succ

theorem srg_getd_zero (a : Int) (tl : List Int) : (a :: tl).getD 0 0 = a := by simp

theorem srg_getd_succ (a : Int) (tl : List Int) (i : Nat) : (a :: tl).getD (i+1) 0 = tl.getD i 0 := by simp

theorem srg_map_head (n : Nat) (f : Nat → Int) :
    ((0 :: (List.range n).map Nat.succ).map f).sum = f 0 + (((List.range n).map Nat.succ).map f).sum := by
  simp

theorem plan5_sum_map_add_range (n : Nat) (f g : Nat → Int) :
    ((List.range n).map (fun i => f i + g i)).sum =
      ((List.range n).map f).sum + ((List.range n).map g).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hr : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [hr, List.map_append, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp
    omega

theorem plan5_sum_range_ite_eq_mul_filter_length (n : Nat) (p : Nat → Bool) (e : Int) :
    ((List.range n).map (fun i => if p i then e else 0)).sum =
      e * (((List.range n).filter p).length : Int) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [hr, List.map_append, List.filter_append, List.sum_append, List.length_append, ih]
    by_cases hp : p n = true
    · have hmap : (([n].map (fun i => if p i then e else (0 : Int))).sum) = e := by simp [hp]
      have hfilt : (([n].filter p).length) = 1 := by simp [hp]
      rw [hmap, hfilt]
      simp
      rw [Int.mul_add, Int.mul_one]
    · have hpf : p n = false := by cases h : p n <;> simp_all
      have hmap : (([n].map (fun i => if p i then e else (0 : Int))).sum) = 0 := by simp [hpf]
      have hfilt : (([n].filter p).length) = 0 := by simp [hpf]
      rw [hmap, hfilt]
      simp

theorem plan0_sum_range_bump_aux_banked (bs : List Int) (p : Nat → Bool) (e : Int)
    (_he : e = 1 ∨ e = -1) :
    ((List.range bs.length).map (fun i => bs.getD i 0 + if p i then e else 0)).sum =
      bs.sum + e * (((List.range bs.length).filter p).length : Int) := by
  have hAdd := plan5_sum_map_add_range bs.length (fun i => bs.getD i 0) (fun i => if p i then e else (0 : Int))
  have hGet := plan5_sum_range_getD bs
  have hIte := plan5_sum_range_ite_eq_mul_filter_length bs.length p e
  calc ((List.range bs.length).map (fun i => bs.getD i 0 + if p i then e else 0)).sum
      = ((List.range bs.length).map (fun i => bs.getD i 0)).sum + ((List.range bs.length).map (fun i => if p i then e else 0)).sum := hAdd
    _ = bs.sum + e * (((List.range bs.length).filter p).length : Int) := by rw [hGet, hIte]

theorem plan0_sum_range_bump_checker (bs : List Int) (p : Nat → Bool) (e : Int)
    (he : e = 1 ∨ e = -1) :
    ((List.range bs.length).map (fun i => bs.getD i 0 + if p i then e else 0)).sum =
      bs.sum + e * (((List.range bs.length).filter p).length : Int) :=
  plan0_sum_range_bump_aux_banked bs p e he

theorem plan0_sum_range_bump_newname123 (bs : List Int) (p : Nat → Bool) (e : Int)
    (_he : e = 1 ∨ e = -1) :
    ((List.range bs.length).map (fun i => bs.getD i 0 + if p i then e else 0)).sum =
      bs.sum + e * (((List.range bs.length).filter p).length : Int) := by
  have hAdd := plan5_sum_map_add_range bs.length (fun i => bs.getD i 0) (fun i => if p i then e else (0 : Int))
  have hGet := plan5_sum_range_getD bs
  have hIte := plan5_sum_range_ite_eq_mul_filter_length bs.length p e
  calc ((List.range bs.length).map (fun i => bs.getD i 0 + if p i then e else 0)).sum
      = ((List.range bs.length).map (fun i => bs.getD i 0)).sum + ((List.range bs.length).map (fun i => if p i then e else 0)).sum := hAdd
    _ = bs.sum + e * (((List.range bs.length).filter p).length : Int) := by rw [hGet, hIte]

theorem plan0_sum_range_bump (bs : List Int) (p : Nat → Bool) (e : Int)
    (he : e = 1 ∨ e = -1) :
    ((List.range bs.length).map (fun i => bs.getD i 0 + if p i then e else 0)).sum =
      bs.sum + e * (((List.range bs.length).filter p).length : Int) := by
  have _hhe := he
  have hAdd := plan5_sum_map_add_range bs.length (fun i => bs.getD i 0) (fun i => if p i then e else (0 : Int))
  have hGet := plan5_sum_range_getD bs
  have hIte := plan5_sum_range_ite_eq_mul_filter_length bs.length p e
  calc ((List.range bs.length).map (fun i => bs.getD i 0 + if p i then e else 0)).sum
      = ((List.range bs.length).map (fun i => bs.getD i 0)).sum + ((List.range bs.length).map (fun i => if p i then e else 0)).sum := hAdd
    _ = bs.sum + e * (((List.range bs.length).filter p).length : Int) := by rw [hGet, hIte]

theorem probe_range_eq_map_sig : True := by trivial
#check @List.range_succ_eq_map
#check @List.range_succ

theorem probe_sig3 : True := trivial
#check List.range_succ_eq_map
#check List.range_succ
#check List.getD

theorem my_range_rw (n : Nat) : List.range (n + 1) = 0 :: (List.range n).map Nat.succ := by
  exact List.range_succ_eq_map

theorem my_srg3 (bs : List Int) :
    ((List.range bs.length).map (fun i => bs.getD i 0)).sum = bs.sum := by
  induction bs with
  | nil => rfl
  | cons a tl ih =>
    have h1 : List.range (tl.length + 1) = 0 :: (List.range tl.length).map Nat.succ := List.range_succ_eq_map
    have hlen : (a :: tl).length = tl.length + 1 := rfl
    rw [hlen, h1]
    simp only [List.map_cons]
    rw [List.sum_cons, List.sum_cons]
    have hget0 : (a :: tl).getD 0 0 = a := rfl
    rw [hget0]
    have hcomp : (fun i => (a :: tl).getD i 0) ∘ Nat.succ = (fun i => tl.getD i 0) := by
      funext i
      rfl
    have hmap : (((List.range tl.length).map Nat.succ).map (fun i => (a :: tl).getD i 0))
        = (List.range tl.length).map (fun i => tl.getD i 0) := by
      rw [List.map_map]
      rw [hcomp]
    rw [hmap, ih]

theorem plan5_sum_range_getD_inline_test (bs : List Int) :
    ((List.range bs.length).map (fun i => bs.getD i 0)).sum = bs.sum := by
  induction bs with
  | nil => rfl
  | cons a tl ih =>
    have h1 : List.range (tl.length + 1) = 0 :: (List.range tl.length).map Nat.succ := List.range_succ_eq_map
    have hlen : (a :: tl).length = tl.length + 1 := rfl
    rw [hlen, h1]
    simp only [List.map_cons]
    rw [List.sum_cons, List.sum_cons]
    have hget0 : (a :: tl).getD 0 0 = a := rfl
    rw [hget0]
    have hcomp : (fun i => (a :: tl).getD i 0) ∘ Nat.succ = (fun i => tl.getD i 0) := by
      funext i
      rfl
    have hmap : (((List.range tl.length).map Nat.succ).map (fun i => (a :: tl).getD i 0))
        = (List.range tl.length).map (fun i => tl.getD i 0) := by
      rw [List.map_map]
      rw [hcomp]
    rw [hmap, ih]

theorem probe_cons_goal : True := trivial
#check @plan0_bases_diff_bounds
#check @plan0_sum_range_bump
#check @plan0_count_rankOf_lt
#check @plan5_sum_range_getD

theorem inj_probe (a b : List Int) (h : (some a : Option (List Int)) = some b) : a = b := by
  simpa using h
#check Option.some_inj

theorem show_unfold_shape (amount : Int) (r : Nat) (rs : List Nat) :
    allocate amount (r :: rs) =
    (match (r :: rs) with
    | [] => (none : Option (List Int))
    | _ :: _ =>
      if (r :: rs).sum = 0 then none
      else
        let S := (r :: rs).sum
        let n := (r :: rs).length
        let bases : List Int := (r :: rs).map (baseAt amount S)
        let keys : List Int := (r :: rs).map (keyAt amount S)
        let L : Nat := if 0 ≤ amount then (amount - bases.sum).toNat else (bases.sum - amount).toNat
        some ((List.range n).map fun i =>
          let b := bases.getD i 0
          if rankOf keys n i < L then (if 0 ≤ amount then b + 1 else b - 1) else b)) := by
  rfl

theorem wiu_map_getD_aux2 (f : Nat → Int) (l : List Nat) (i : Nat) (hi : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    match i with
    | 0 => simp
    | n+1 =>
      have h1 : ((hd :: tl).map f).getD (n+1) 0 = (tl.map f).getD n 0 := by simp
      have h2 : (hd :: tl).getD (n+1) 0 = tl.getD n 0 := by simp
      rw [h1, h2]
      have htl : n < tl.length := by simpa using hi
      exact ih n htl

theorem wiu_bases_len (amount : Int) (ratios : List Nat) :
    (ratios.map (baseAt amount ratios.sum)).length = ratios.length := by simp

theorem wiu_keys_len (amount : Int) (ratios : List Nat) :
    (ratios.map (keyAt amount ratios.sum)).length = ratios.length := by simp

theorem wiu_base_getD (amount : Int) (ratios : List Nat) (i : Nat) (hi : i < ratios.length) :
    (ratios.map (baseAt amount ratios.sum)).getD i 0 = baseAt amount ratios.sum (ratios.getD i 0) :=
  wiu_map_getD_aux2 (baseAt amount ratios.sum) ratios i hi

theorem wiu_key_getD (amount : Int) (ratios : List Nat) (i : Nat) (hi : i < ratios.length) :
    (ratios.map (keyAt amount ratios.sum)).getD i 0 = keyAt amount ratios.sum (ratios.getD i 0) :=
  wiu_map_getD_aux2 (keyAt amount ratios.sum) ratios i hi

theorem wiu_key_range2 (amount : Int) (S r : Nat) (hS : 0 < S) :
    0 ≤ keyAt amount S r ∧ keyAt amount S r < (S : Int) := by
  have hb := plan0_baseAt_bounds amount S r hS
  obtain ⟨hlo, hhi, hnn, hnp⟩ := hb
  unfold keyAt
  simp only
  by_cases ha : 0 ≤ amount
  · simp [ha]
    constructor
    · have := hnn ha; omega
    · omega
  · simp [ha]
    have ham : amount < 0 := by omega
    have hle : amount ≤ 0 := by omega
    have := hnp hle
    constructor <;> omega



theorem plan6_sum_keys_general (amount : Int) (S : Nat) (ratios : List Nat) :
    (ratios.map (keyAt amount S)).sum =
      if 0 ≤ amount then
        amount * (ratios.sum : Int) - (S : Int) * (ratios.map (baseAt amount S)).sum
      else
        (S : Int) * (ratios.map (baseAt amount S)).sum - amount * (ratios.sum : Int) := by
  have hkey : ∀ r : Nat, keyAt amount S r =
      if 0 ≤ amount then amount * (r : Int) - baseAt amount S r * (S : Int)
      else baseAt amount S r * (S : Int) - amount * (r : Int) := by
    intro r
    unfold keyAt
    by_cases ha : 0 ≤ amount <;> simp [ha]
  by_cases ha : 0 ≤ amount
  · rw [if_pos ha]
    induction ratios with
    | nil => simp
    | cons hd tl ih =>
      have h1 : ((hd :: tl).map (keyAt amount S)).sum =
        keyAt amount S hd + (tl.map (keyAt amount S)).sum := by simp
      have h2 : ((hd :: tl).map (baseAt amount S)).sum =
        baseAt amount S hd + (tl.map (baseAt amount S)).sum := by simp
      have h3 : ((hd :: tl).sum : Int) = (hd : Int) + ((tl.sum : Nat) : Int) := by simp
      rw [h1, hkey hd, if_pos ha, ih, h2, h3]
      have hmul : amount * ((hd : Int) + ((tl.sum : Nat) : Int)) = amount * (hd : Int) + amount * ((tl.sum : Nat) : Int) := Int.mul_add _ _ _
      have hmulS : (S : Int) * (baseAt amount S hd + (tl.map (baseAt amount S)).sum) =
        (S : Int) * baseAt amount S hd + (S : Int) * (tl.map (baseAt amount S)).sum := Int.mul_add _ _ _
      have hcomm : (S : Int) * baseAt amount S hd = baseAt amount S hd * (S : Int) := Int.mul_comm _ _
      rw [hmul, hmulS, hcomm]
      omega
  · rw [if_neg ha]
    induction ratios with
    | nil => simp
    | cons hd tl ih =>
      have h1 : ((hd :: tl).map (keyAt amount S)).sum =
        keyAt amount S hd + (tl.map (keyAt amount S)).sum := by simp
      have h2 : ((hd :: tl).map (baseAt amount S)).sum =
        baseAt amount S hd + (tl.map (baseAt amount S)).sum := by simp
      have h3 : ((hd :: tl).sum : Int) = (hd : Int) + ((tl.sum : Nat) : Int) := by simp
      rw [h1, hkey hd, if_neg ha, ih, h2, h3]
      have hmul : amount * ((hd : Int) + ((tl.sum : Nat) : Int)) = amount * (hd : Int) + amount * ((tl.sum : Nat) : Int) := Int.mul_add _ _ _
      have hmulS : (S : Int) * (baseAt amount S hd + (tl.map (baseAt amount S)).sum) =
        (S : Int) * baseAt amount S hd + (S : Int) * (tl.map (baseAt amount S)).sum := Int.mul_add _ _ _
      have hcomm : baseAt amount S hd * (S : Int) = (S : Int) * baseAt amount S hd := Int.mul_comm _ _
      rw [hmul, hmulS, hcomm]
      omega






theorem plan6_key_pos_of_rank_lt_L (amount : Int) (ratios : List Nat) (i : Nat)
    (hS : 0 < ratios.sum) (hi : i < ratios.length)
    (hrank : rankOf (ratios.map (keyAt amount ratios.sum)) ratios.length i <
      (if 0 ≤ amount then
        (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat
       else
        ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat)) :
    0 < (ratios.map (keyAt amount ratios.sum)).getD i 0 := by sorry

theorem plan6_excess_share_of_allocate (amount : Int) (ratios : List Nat)
    (shares : List Int) (hS : 0 < ratios.sum) (hne : ratios ≠ [])
    (halloc : allocate amount ratios = some shares)
    (i : Nat) (hx : i < shares.length) (hr : i < ratios.length) :
    -(ratios.sum : Int) < excess amount ratios.sum shares[i] ratios[i] ∧
    excess amount ratios.sum shares[i] ratios[i] < (ratios.sum : Int) := by sorry

theorem plan6_key_excess_base (amount : Int) (S : Nat) (r : Nat) (hS : 0 < S) :
    0 ≤ keyAt amount S r ∧ keyAt amount S r < (S : Int) ∧
    excess amount S (baseAt amount S r) r =
      if 0 ≤ amount then - keyAt amount S r else keyAt amount S r := by
  have hkeys := wiu_key_range2 amount S r hS
  refine ⟨hkeys.1, hkeys.2, ?_⟩
  unfold keyAt excess
  by_cases ha : 0 ≤ amount
  · simp only [ha, ↓reduceIte]
    omega
  · simp only [ha, ↓reduceIte]

theorem probe_b : True := trivial
#check @Int.mul_add
#check @Int.add_mul
#check @Int.mul_comm
#check @Int.mul_assoc
#check @Int.sub_add_cancel
#check @Int.add_comm
#check @Int.add_assoc

theorem lin_test (a b c d : Int) : a - b + (c - d) = a + c - (b + d) := by omega

theorem dist_test (amount : Int) (a b : Int) : amount * a + amount * b = amount * (a + b) := by
  rw [Int.mul_add]

theorem dist_test2 (a b : Int) (S : Int) : a * S + b * S = (a + b) * S := by
  rw [Int.add_mul]

theorem cast_add_test (hd tl : Nat) : (((hd + tl : Nat) : Int)) = (hd : Int) + ((tl : Nat) : Int) := by
  simp

theorem keyAt_eq_aux2 (amount : Int) (S r : Nat) :
    keyAt amount S r =
      if 0 ≤ amount then amount * (r : Int) - baseAt amount S r * (S : Int)
      else baseAt amount S r * (S : Int) - amount * (r : Int) := by
  unfold keyAt
  by_cases ha : 0 ≤ amount <;> simp [ha]

theorem sum_map_sub_aux2 (l : List Nat) (f g : Nat → Int) :
    (l.map (fun r => f r - g r)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    omega

theorem sum_map_amount_mul2 (amount : Int) (l : List Nat) :
    (l.map (fun r : Nat => amount * (r : Int))).sum = amount * ((l.sum : Nat) : Int) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.sum_cons] at ih ⊢
    rw [ih]
    have hcast : ((((hd + tl.sum : Nat)) : Int)) = (hd : Int) + ((tl.sum : Nat) : Int) := by simp
    rw [hcast, Int.mul_add]

theorem sum_map_base_mul2 (S : Nat) (amount : Int) (l : List Nat) :
    (l.map (fun r : Nat => baseAt amount S r * (S : Int))).sum =
      ((l.map (baseAt amount S)).sum) * (S : Int) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Int.add_mul]

theorem map_congr_probe (l : List Nat) (f g : Nat → Int) (h : ∀ r, f r = g r) :
    l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [h hd, ih]

theorem muladd_sig (a b c : Int) : a * (b + c) = a * b + a * c := Int.mul_add a b c

theorem addmul_sig (a b c : Int) : (a + b) * c = a * c + b * c := Int.add_mul a b c







theorem plan7_sum_map_base_mul (amount : Int) (S : Nat) (l : List Nat) :
    (l.map (fun r : Nat => baseAt amount S r * (S : Int))).sum =
      (l.map (baseAt amount S)).sum * (S : Int) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Int.add_mul]






theorem plan7_keyAt_eq2 (amount : Int) (S : Nat) (r : Nat) :
    keyAt amount S r =
      if 0 ≤ amount then amount * (r : Int) - baseAt amount S r * (S : Int)
      else baseAt amount S r * (S : Int) - amount * (r : Int) :=
  keyAt_eq_aux2 amount S r

theorem plan7_keyAt_eq (amount : Int) (S : Nat) (r : Nat) :
    keyAt amount S r =
      if 0 ≤ amount then amount * (r : Int) - baseAt amount S r * (S : Int)
      else baseAt amount S r * (S : Int) - amount * (r : Int) := by
  exact keyAt_eq_aux2 amount S r

theorem plan7_sum_map_sub (l : List Nat) (f g : Nat → Int) :
    (l.map (fun r => f r - g r)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem plan7_sum_map_amount_mul (amount : Int) (l : List Nat) :
    (l.map (fun r : Nat => amount * (r : Int))).sum = amount * (l.sum : Int) := by
  exact sum_map_amount_mul2 amount l

theorem plan7_sum_map_base_mul_pf (amount : Int) (S : Nat) (l : List Nat) :
    (l.map (fun r : Nat => baseAt amount S r * (S : Int))).sum =
      (l.map (baseAt amount S)).sum * (S : Int) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Int.add_mul]

theorem plan7_sum_keys_of_nonneg (amount : Int) (S : Nat) (ratios : List Nat)
    (ha : 0 ≤ amount) :
    (ratios.map (keyAt amount S)).sum =
      amount * (ratios.sum : Int) - (S : Int) * (ratios.map (baseAt amount S)).sum := by
  have hfun : ∀ r : Nat, keyAt amount S r = amount * (r : Int) - baseAt amount S r * (S : Int) := by
    intro r
    rw [plan7_keyAt_eq amount S r, if_pos ha]
  have hmap : ratios.map (keyAt amount S) = ratios.map (fun r : Nat => amount * (r : Int) - baseAt amount S r * (S : Int)) :=
    map_congr_probe ratios (keyAt amount S) (fun r : Nat => amount * (r : Int) - baseAt amount S r * (S : Int)) hfun
  rw [hmap, plan7_sum_map_sub ratios (fun r : Nat => amount * (r : Int)) (fun r : Nat => baseAt amount S r * (S : Int))]
  rw [plan7_sum_map_amount_mul amount ratios]
  rw [plan7_sum_map_base_mul_pf amount S ratios]
  rw [Int.mul_comm ((ratios.map (baseAt amount S)).sum) (S : Int)]

theorem plan7_sum_keys_of_neg : ∀ (amount : Int) (S : Nat) (ratios : List Nat),
    (¬ 0 ≤ amount) →
    (ratios.map (keyAt amount S)).sum =
      (S : Int) * (ratios.map (baseAt amount S)).sum - amount * (ratios.sum : Int) := by
  intro amount S ratios ha
  have hfun : ∀ r : Nat, keyAt amount S r = baseAt amount S r * (S : Int) - amount * (r : Int) := by
    intro r
    rw [plan7_keyAt_eq amount S r, if_neg ha]
  have hmap : ratios.map (keyAt amount S) = ratios.map (fun r : Nat => baseAt amount S r * (S : Int) - amount * (r : Int)) :=
    map_congr_probe ratios (keyAt amount S) (fun r : Nat => baseAt amount S r * (S : Int) - amount * (r : Int)) hfun
  rw [hmap, plan7_sum_map_sub ratios (fun r : Nat => baseAt amount S r * (S : Int)) (fun r : Nat => amount * (r : Int))]
  rw [plan7_sum_map_base_mul_pf amount S ratios]
  rw [plan7_sum_map_amount_mul amount ratios]
  rw [Int.mul_comm ((ratios.map (baseAt amount S)).sum) (S : Int)]

theorem plan6_sum_keys_general_aux_tmp (amount : Int) (S : Nat) (ratios : List Nat) :
    (ratios.map (keyAt amount S)).sum =
      if 0 ≤ amount then
        amount * (ratios.sum : Int) - (S : Int) * (ratios.map (baseAt amount S)).sum
      else
        (S : Int) * (ratios.map (baseAt amount S)).sum - amount * (ratios.sum : Int) := by
  by_cases ha : 0 ≤ amount
  · rw [if_pos ha]; exact plan7_sum_keys_of_nonneg amount S ratios ha
  · rw [if_neg ha]; exact plan7_sum_keys_of_neg amount S ratios ha

theorem plan6_sum_keys_general_dup (amount : Int) (S : Nat) (ratios : List Nat) :
    (ratios.map (keyAt amount S)).sum =
      if 0 ≤ amount then
        amount * (ratios.sum : Int) - (S : Int) * (ratios.map (baseAt amount S)).sum
      else
        (S : Int) * (ratios.map (baseAt amount S)).sum - amount * (ratios.sum : Int) := by
  by_cases ha : 0 ≤ amount
  · rw [if_pos ha]; exact plan7_sum_keys_of_nonneg amount S ratios ha
  · rw [if_neg ha]; exact plan7_sum_keys_of_neg amount S ratios ha

theorem plan6_selfcontained_test4 (amount : Int) (S : Nat) (ratios : List Nat) :
    (ratios.map (keyAt amount S)).sum =
      if 0 ≤ amount then
        amount * (ratios.sum : Int) - (S : Int) * (ratios.map (baseAt amount S)).sum
      else
        (S : Int) * (ratios.map (baseAt amount S)).sum - amount * (ratios.sum : Int) := by
  have hkey : ∀ r : Nat, keyAt amount S r =
      if 0 ≤ amount then amount * (r : Int) - baseAt amount S r * (S : Int)
      else baseAt amount S r * (S : Int) - amount * (r : Int) := by
    intro r
    unfold keyAt
    by_cases ha : 0 ≤ amount <;> simp [ha]
  by_cases ha : 0 ≤ amount
  · rw [if_pos ha]
    induction ratios with
    | nil => simp
    | cons hd tl ih =>
      have h1 : ((hd :: tl).map (keyAt amount S)).sum =
        keyAt amount S hd + (tl.map (keyAt amount S)).sum := by simp
      have h2 : ((hd :: tl).map (baseAt amount S)).sum =
        baseAt amount S hd + (tl.map (baseAt amount S)).sum := by simp
      have h3 : ((hd :: tl).sum : Int) = (hd : Int) + ((tl.sum : Nat) : Int) := by simp
      rw [h1, hkey hd, if_pos ha, ih, h2, h3]
      have hmul : amount * ((hd : Int) + ((tl.sum : Nat) : Int)) = amount * (hd : Int) + amount * ((tl.sum : Nat) : Int) := Int.mul_add _ _ _
      have hmulS : (S : Int) * (baseAt amount S hd + (tl.map (baseAt amount S)).sum) =
        (S : Int) * baseAt amount S hd + (S : Int) * (tl.map (baseAt amount S)).sum := Int.mul_add _ _ _
      have hcomm : (S : Int) * baseAt amount S hd = baseAt amount S hd * (S : Int) := Int.mul_comm _ _
      rw [hmul, hmulS, hcomm]
      omega
  · rw [if_neg ha]
    induction ratios with
    | nil => simp
    | cons hd tl ih =>
      have h1 : ((hd :: tl).map (keyAt amount S)).sum =
        keyAt amount S hd + (tl.map (keyAt amount S)).sum := by simp
      have h2 : ((hd :: tl).map (baseAt amount S)).sum =
        baseAt amount S hd + (tl.map (baseAt amount S)).sum := by simp
      have h3 : ((hd :: tl).sum : Int) = (hd : Int) + ((tl.sum : Nat) : Int) := by simp
      rw [h1, hkey hd, if_neg ha, ih, h2, h3]
      have hmul : amount * ((hd : Int) + ((tl.sum : Nat) : Int)) = amount * (hd : Int) + amount * ((tl.sum : Nat) : Int) := Int.mul_add _ _ _
      have hmulS : (S : Int) * (baseAt amount S hd + (tl.map (baseAt amount S)).sum) =
        (S : Int) * baseAt amount S hd + (S : Int) * (tl.map (baseAt amount S)).sum := Int.mul_add _ _ _
      have hcomm : baseAt amount S hd * (S : Int) = (S : Int) * baseAt amount S hd := Int.mul_comm _ _
      rw [hmul, hmulS, hcomm]
      omega

theorem plan6_count_pos_le_rankOf (keys : List Int) (n i : Nat)
    (hkey : keys.getD i 0 = 0) :
    ((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length ≤
      rankOf keys n i := by
  unfold rankOf
  apply filter_mono_len
  intro x _ hx
  have hpos : 0 < keys.getD x 0 := of_decide_eq_true hx
  have hgt : keys.getD x 0 > keys.getD i 0 := by omega
  unfold prefers
  rw [if_pos hgt]

theorem sing_true_test (keys : List Int) (n : Nat)
    (hdec : decide (0 < keys.getD n 0) = true) :
    ([n].filter (fun j => decide (0 < keys.getD j 0))).length = 1 := by
  simp only [List.filter_cons, List.filter_nil, hdec]
  rfl

theorem sing_false_test (keys : List Int) (n : Nat)
    (hdec : decide (0 < keys.getD n 0) = false) :
    ([n].filter (fun j => decide (0 < keys.getD j 0))).length = 0 := by
  simp only [List.filter_cons, List.filter_nil, hdec]
  rfl





theorem plan8_sum_indicator_eq_mul_filter (keys : List Int) (n : Nat) (e : Int) :
    ((List.range n).map (fun j => if 0 < keys.getD j 0 then e else 0)).sum =
      e * (((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length : Int) := by sorry



theorem plan8_pointwise_le_indicator_dup (S x : Int) (h0 : 0 ≤ x) (hS : x < S) :
    x ≤ (if 0 < x then S - 1 else 0) := by
  by_cases h : 0 < x <;> simp [h] <;> omega

theorem plan8_pointwise_le_indicator (S x : Int) (h0 : 0 ≤ x) (hS : x < S) :
    x ≤ (if 0 < x then S - 1 else 0) := by
  by_cases h : 0 < x <;> simp [h] <;> omega

theorem plan8_sum_le_of_pointwise (n : Nat) (f g : Nat → Int)
    (h : ∀ i, i < n → f i ≤ g i) :
    ((List.range n).map f).sum ≤ ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [hr, List.map_append, List.map_append, List.sum_append, List.sum_append]
    have h1 : ((List.range n).map f).sum ≤ ((List.range n).map g).sum :=
      ih (fun i hi => h i (by omega))
    have h2 : f n ≤ g n := h n (by omega)
    have e1 : (([n].map f).sum) = f n := by simp
    have e2 : (([n].map g).sum) = g n := by simp
    omega

theorem plan8_sum_indicator_eq_mul_filter_aux_tmp2 (keys : List Int) (n : Nat) (e : Int) :
    (([n].map (fun j => if 0 < keys.getD j 0 then e else (0 : Int))).sum) = (if 0 < keys.getD n 0 then e else 0) := by
  simp

theorem plan8_sum_le_indicator_sum (keys : List Int) (n : Nat) (S : Int)
    (hkeys : ∀ j, j < n → 0 ≤ keys.getD j 0 ∧ keys.getD j 0 < S) :
    ((List.range n).map (fun j => keys.getD j 0)).sum ≤
      ((List.range n).map (fun j => if 0 < keys.getD j 0 then S - 1 else 0)).sum := by
  apply plan8_sum_le_of_pointwise
  intro i hi
  exact plan8_pointwise_le_indicator S (keys.getD i 0) (hkeys i hi).1 (hkeys i hi).2

theorem cast_probe2 (a b : Nat) : (((a + b : Nat)) : Int) = ((a : Int)) + ((b : Int)) := by
  simp

theorem sing_probe2 (p : Nat → Bool) (n : Nat) (h : p n = true) :
    (([n].filter p).length) = 1 := by
  simp [h]

theorem sing_probe3 (p : Nat → Bool) (n : Nat) (h : p n = false) :
    (([n].filter p).length) = 0 := by
  simp [h]

theorem mul_probe2 (S d e : Int) : (S - 1) * (d + e) = (S - 1) * d + (S - 1) * e := by
  exact Int.mul_add _ _ _

theorem cast_self_test (k : Nat) : (((k + 1 : Nat)) : Int) = (((k : Nat)) : Int) + 1 := by
  simp

theorem sing_self_test (p : Nat → Bool) (n : Nat) (h : p n = true) : (([n].filter p).length) = 1 := by
  simp [h]

theorem plan6_bound_self_final (keys : List Int) (n : Nat) (S : Int)
    (hS : 0 < S)
    (hkeys : ∀ j, j < n → 0 ≤ keys.getD j 0 ∧ keys.getD j 0 < S) :
    ((List.range n).map (fun j => keys.getD j 0)).sum ≤
      (S - 1) * (((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length : Int) := by
  have hSpos : (0 : Int) < S := hS
  induction n with
  | zero => simp
  | succ n ih =>
    have hkeys_n : ∀ j, j < n → 0 ≤ keys.getD j 0 ∧ keys.getD j 0 < S := fun j hj => hkeys j (by omega)
    have IH := ih hkeys_n
    have hkn := hkeys n (by omega)
    have hr : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    have hmap : ((List.range (n+1)).map (fun j => keys.getD j 0)).sum =
      ((List.range n).map (fun j => keys.getD j 0)).sum + keys.getD n 0 := by
      rw [hr, List.map_append, List.sum_append]
      simp
    have hflt : ((List.range (n+1)).filter (fun j => decide (0 < keys.getD j 0))).length =
      ((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length +
        (([n].filter (fun j => decide (0 < keys.getD j 0))).length) := by
      rw [hr, List.filter_append, List.length_append]
    by_cases h : 0 < keys.getD n 0
    · have hd : decide (0 < keys.getD n 0) = true := decide_eq_true h
      have hsing : (([n].filter (fun j => decide (0 < keys.getD j 0))).length) = 1 := by
        exact sing_probe2 _ n hd
      rw [hflt, hsing]
      rw [hmap]
      have hcast : ((((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length + 1 : Nat) : Int) =
        (((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length : Int) + 1 := by
        exact cast_probe2 _ _
      rw [hcast]
      have hdist : (S - 1) * ((((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length : Int) + 1) =
        (S - 1) * (((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length : Int) + (S - 1) := by
        have hmul := Int.mul_add (S - 1) (((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length : Int) 1
        rw [Int.mul_one] at hmul
        exact hmul
      rw [hdist]
      omega
    · have hn : ¬ 0 < keys.getD n 0 := h
      have hd : decide (0 < keys.getD n 0) = false := decide_eq_false hn
      have hsing : (([n].filter (fun j => decide (0 < keys.getD j 0))).length) = 0 := by
        exact sing_probe3 _ n hd
      rw [hflt, hsing]
      simp only [Nat.add_zero]
      rw [hmap]
      omega

theorem plan6_sum_range_le_count_pos (keys : List Int) (n : Nat) (S : Int)
    (hS : 0 < S)
    (hkeys : ∀ j, j < n → 0 ≤ keys.getD j 0 ∧ keys.getD j 0 < S) :
    ((List.range n).map (fun j => keys.getD j 0)).sum ≤
      (S - 1) * (((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length : Int) :=
  plan6_bound_self_final keys n S hS hkeys

theorem probe_mulmono : True := by trivial
#check @Nat.mul_le_mul_left
#check @Nat.mul_le_mul_right
#check @Int.mul_le_mul_of_nonneg_left
#check @Int.mul_le_mul_of_nonneg_right
#check @Int.ofNat_le
#check @Int.toNat_of_nonneg

theorem probe_check_sigs : True := by trivial
#check @plan6_count_pos_le_rankOf
#check @plan6_sum_range_le_count_pos
#check @plan5_sum_range_getD
#check @plan6_sum_keys_general_dup
#check @plan0_bases_diff_bounds
#check @wiu_key_getD
#check @wiu_key_range2
#check @wiu_keys_len
#check @Int.mul_le_mul_of_nonneg_left
#check @Int.ofNat_le

theorem probe_mulmono3 : True := by trivial
#check @Int.mul_le_mul_of_nonneg_left
#check @Int.mul_le_mul_of_nonneg_right

theorem probe_distrib_names : True := by trivial
#check @Int.mul_le_mul_of_nonneg_left
#check @Int.mul_le_mul_of_nonneg_right
#check @Int.sub_mul
#check @Int.mul_sub
#check @Int.add_mul
#check @Int.mul_add
#check @Int.one_mul
#check @Int.mul_one

theorem probe_sig_check : True := by trivial
#check @Int.mul_le_mul_of_nonneg_left
#check @Int.mul_le_mul_of_nonneg_right
#check @Int.mul_lt_mul_of_pos_left

theorem arith_core_test (S L C : Int) (hS : 0 < S) (hC0 : 0 ≤ C) (hCL : C < L)
    (h : S * L ≤ (S - 1) * C) : False := by
  have hD : 0 < L - C := by omega
  have hSD : 0 < S * (L - C) := Int.mul_pos hS hD
  have hexpand1 : S * L = S * C + S * (L - C) := by
    have h1 : L = C + (L - C) := by omega
    calc S * L = S * (C + (L - C)) := by rw [← h1]
      _ = S * C + S * (L - C) := Int.mul_add S C (L - C)
  have hexpand2 : (S - 1) * C = S * C - C := by
    calc (S - 1) * C = S * C - 1 * C := by rw [Int.sub_mul]
      _ = S * C - C := by rw [Int.one_mul]
  omega

theorem tactic_probe1 (p : Prop) (h : ¬ ¬ p) : p := by
  exact Classical.byContradiction h













theorem plan9_key_bounds_getD (amount : Int) (ratios : List Nat) (i : Nat)
    (hS : 0 < ratios.sum) (hi : i < ratios.length) :
    0 ≤ (ratios.map (keyAt amount ratios.sum)).getD i 0 ∧
    (ratios.map (keyAt amount ratios.sum)).getD i 0 < (ratios.sum : Int) := by
  have hget := wiu_key_getD amount ratios i hi
  have hrange := wiu_key_range2 amount ratios.sum (ratios.getD i 0) hS
  rw [hget]
  exact hrange

theorem plan9_count_pos_lt_of_key_zero (keys : List Int) (n i L : Nat)
    (h0 : keys.getD i 0 = 0) (hr : rankOf keys n i < L) :
    ((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length < L := by
  have hle := plan6_count_pos_le_rankOf keys n i h0
  omega

theorem plan9_keys_sum_le_count_pos_aux_unique_test123 : True := trivial

theorem plan9_keys_sum_le_count_pos_proof_helper (amount : Int) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    (ratios.map (keyAt amount ratios.sum)).sum ≤
      ((ratios.sum : Int) - 1) *
        (((List.range ratios.length).filter
          (fun j => decide (0 < (ratios.map (keyAt amount ratios.sum)).getD j 0))).length : Int) := by
  have hSpos : (0 : Int) < ((ratios.sum : Nat) : Int) := by
    exact_mod_cast hS
  have hkeys : ∀ j, j < ratios.length →
      0 ≤ (ratios.map (keyAt amount ratios.sum)).getD j 0 ∧
      (ratios.map (keyAt amount ratios.sum)).getD j 0 < ((ratios.sum : Nat) : Int) := by
    intro j hj
    exact plan9_key_bounds_getD amount ratios j hS hj
  have hbound := plan6_sum_range_le_count_pos (ratios.map (keyAt amount ratios.sum)) ratios.length ((ratios.sum : Int)) hSpos hkeys
  have hlen : ((ratios.map (keyAt amount ratios.sum)).length) = ratios.length := by simp
  have heq := plan5_sum_range_getD (ratios.map (keyAt amount ratios.sum))
  rw [hlen] at heq
  rw [← heq]
  exact hbound

theorem plan9_keys_sum_le_count_pos_dup_tmp (amount : Int) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    (ratios.map (keyAt amount ratios.sum)).sum ≤
      ((ratios.sum : Int) - 1) *
        (((List.range ratios.length).filter
          (fun j => decide (0 < (ratios.map (keyAt amount ratios.sum)).getD j 0))).length : Int) :=
  plan9_keys_sum_le_count_pos_proof_helper amount ratios hS

theorem plan9_keys_sum_le_count_pos (amount : Int) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    (ratios.map (keyAt amount ratios.sum)).sum ≤
      ((ratios.sum : Int) - 1) *
        (((List.range ratios.length).filter
          (fun j => decide (0 < (ratios.map (keyAt amount ratios.sum)).getD j 0))).length : Int) :=
  plan9_keys_sum_le_count_pos_proof_helper amount ratios hS

theorem plan9_mul_sub_factor (S x y : Int) :
    S * (x - y) = x * S - S * y := by
  have h1 : S * (x - y) = S * x - S * y := Int.mul_sub S x y
  have h2 : S * x = x * S := Int.mul_comm S x
  omega

theorem probe_mulneg_sig : True := trivial
#check @Int.mul_neg
#check @Int.neg_mul
#check @Int.mul_pos
#check @Int.mul_nonneg
#check @Int.toNat_of_nonneg
#check @Int.mul_add
#check @Int.mul_sub
#check @Int.mul_comm

theorem sum_keys_nonneg_aux (amount : Int) (S : Nat) (l : List Nat)
    (h : ∀ r ∈ l, 0 ≤ keyAt amount S r) :
    0 ≤ (l.map (keyAt amount S)).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    have hhd : 0 ≤ keyAt amount S hd := h hd (by simp)
    have htl : ∀ r ∈ tl, 0 ≤ keyAt amount S r := fun r hr => h r (by simp [hr])
    have ihtl := ih htl
    omega

theorem check_mul_lemmas_exist : True := trivial
#check @Int.mul_neg_of_pos_of_neg
#check @Int.mul_pos
#check @Int.mul_nonneg
#check @Int.le_of_mul_le_mul_right
#check @Int.toNat_of_nonneg

theorem aux_neg_prod_test (S D : Int) (hS : 0 < S) (hD : D < 0) : S * D < 0 := by
  exact Int.mul_neg_of_pos_of_neg hS hD

theorem plan9_Lnat_cast (amount : Int) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    (((if 0 ≤ amount then
        (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat
       else
        ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat) : Nat) : Int) =
      (if 0 ≤ amount then
        amount - (ratios.map (baseAt amount ratios.sum)).sum
       else
        (ratios.map (baseAt amount ratios.sum)).sum - amount) := by
  by_cases ha : 0 ≤ amount
  · have heqN : (if 0 ≤ amount then (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat else ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat) = (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat := by simp [ha]
    have heqI : (if 0 ≤ amount then amount - (ratios.map (baseAt amount ratios.sum)).sum else (ratios.map (baseAt amount ratios.sum)).sum - amount) = amount - (ratios.map (baseAt amount ratios.sum)).sum := by simp [ha]
    rw [heqN, heqI]
    have hSpos : (0 : Int) < ((ratios.sum : Nat) : Int) := by exact_mod_cast hS
    have hsumEq := plan7_sum_keys_of_nonneg amount ratios.sum ratios ha
    have hnonneg : 0 ≤ (ratios.map (keyAt amount ratios.sum)).sum := by
      apply sum_keys_nonneg_aux
      intro r hr
      exact (wiu_key_range2 amount ratios.sum r hS).1
    rw [hsumEq] at hnonneg
    have hexpand : amount * ((ratios.sum : Nat) : Int) - ((ratios.sum : Nat) : Int) * (ratios.map (baseAt amount ratios.sum)).sum = ((ratios.sum : Nat) : Int) * (amount - (ratios.map (baseAt amount ratios.sum)).sum) := by
      rw [Int.mul_sub, Int.mul_comm amount _]
    by_cases hD : 0 ≤ amount - (ratios.map (baseAt amount ratios.sum)).sum
    · omega
    · have hDneg : amount - (ratios.map (baseAt amount ratios.sum)).sum < 0 := by omega
      have hmulneg : ((ratios.sum : Nat) : Int) * (amount - (ratios.map (baseAt amount ratios.sum)).sum) < 0 :=
        Int.mul_neg_of_pos_of_neg hSpos hDneg
      omega
  · have haN : ¬ 0 ≤ amount := ha
    have heqN : (if 0 ≤ amount then (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat else ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat) = ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat := by simp [ha]
    have heqI : (if 0 ≤ amount then amount - (ratios.map (baseAt amount ratios.sum)).sum else (ratios.map (baseAt amount ratios.sum)).sum - amount) = (ratios.map (baseAt amount ratios.sum)).sum - amount := by simp [ha]
    rw [heqN, heqI]
    have hSpos : (0 : Int) < ((ratios.sum : Nat) : Int) := by exact_mod_cast hS
    have hsumEq := plan7_sum_keys_of_neg amount ratios.sum ratios haN
    have hnonneg : 0 ≤ (ratios.map (keyAt amount ratios.sum)).sum := by
      apply sum_keys_nonneg_aux
      intro r hr
      exact (wiu_key_range2 amount ratios.sum r hS).1
    rw [hsumEq] at hnonneg
    have hexpand : ((ratios.sum : Nat) : Int) * (ratios.map (baseAt amount ratios.sum)).sum - amount * ((ratios.sum : Nat) : Int) = ((ratios.sum : Nat) : Int) * ((ratios.map (baseAt amount ratios.sum)).sum - amount) := by
      rw [Int.mul_sub, Int.mul_comm amount _]
    by_cases hD : 0 ≤ (ratios.map (baseAt amount ratios.sum)).sum - amount
    · omega
    · have hDneg : (ratios.map (baseAt amount ratios.sum)).sum - amount < 0 := by omega
      have hmulneg : ((ratios.sum : Nat) : Int) * ((ratios.map (baseAt amount ratios.sum)).sum - amount) < 0 :=
        Int.mul_neg_of_pos_of_neg hSpos hDneg
      omega

theorem plan9_keys_sum_eq_mul_Lnat (amount : Int) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    (ratios.map (keyAt amount ratios.sum)).sum =
      (ratios.sum : Int) *
        (((if 0 ≤ amount then
            (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat
           else
            ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat) : Nat) : Int) := by
  have hGen := plan6_sum_keys_general_dup amount ratios.sum ratios
  have hCast := plan9_Lnat_cast amount ratios hS
  by_cases ha : 0 ≤ amount
  · simp only [ha, ↓reduceIte] at hCast ⊢
    have hGenA : (ratios.map (keyAt amount ratios.sum)).sum =
        amount * (ratios.sum : Int) - (ratios.sum : Int) * (ratios.map (baseAt amount ratios.sum)).sum := by
      rw [hGen, if_pos ha]
    rw [hCast, hGenA, Int.mul_sub, Int.mul_comm amount _]
  · have haN : ¬ 0 ≤ amount := ha
    simp only [ha, ↓reduceIte] at hCast ⊢
    have hGenB : (ratios.map (keyAt amount ratios.sum)).sum =
        (ratios.sum : Int) * (ratios.map (baseAt amount ratios.sum)).sum - amount * (ratios.sum : Int) := by
      rw [hGen, if_neg haN]
    rw [hCast, hGenB, Int.mul_sub, Int.mul_comm amount _]

theorem plan6_key_pos_of_rank_lt_L_proof2 (amount : Int) (ratios : List Nat) (i : Nat)
    (hS : 0 < ratios.sum) (hi : i < ratios.length)
    (hrank : rankOf (ratios.map (keyAt amount ratios.sum)) ratios.length i <
      (if 0 ≤ amount then
        (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat
       else
        ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat)) :
    0 < (ratios.map (keyAt amount ratios.sum)).getD i 0 := by
  by_cases hpos : 0 < (ratios.map (keyAt amount ratios.sum)).getD i 0
  · exact hpos
  · exfalso
    have hbounds := plan9_key_bounds_getD amount ratios i hS hi
    have h0le : 0 ≤ (ratios.map (keyAt amount ratios.sum)).getD i 0 := hbounds.1
    have heq0 : (ratios.map (keyAt amount ratios.sum)).getD i 0 = 0 := by omega
    have hC_lt : ((List.range ratios.length).filter
        (fun j => decide (0 < (ratios.map (keyAt amount ratios.sum)).getD j 0))).length <
        (if 0 ≤ amount then
          (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat
         else
          ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat) :=
      plan9_count_pos_lt_of_key_zero (ratios.map (keyAt amount ratios.sum)) ratios.length i _ heq0 hrank
    have hsum_le := plan9_keys_sum_le_count_pos amount ratios hS
    have hsum_eq := plan9_keys_sum_eq_mul_Lnat amount ratios hS
    have hSpos : (0 : Int) < ((ratios.sum : Nat) : Int) := by exact_mod_cast hS
    have hC0 : (0 : Int) ≤ ((((List.range ratios.length).filter
        (fun j => decide (0 < (ratios.map (keyAt amount ratios.sum)).getD j 0))).length : Nat) : Int) := by omega
    have hCL_int : ((((List.range ratios.length).filter
        (fun j => decide (0 < (ratios.map (keyAt amount ratios.sum)).getD j 0))).length : Nat) : Int) <
        (((if 0 ≤ amount then
          (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat
         else
          ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat : Nat)) : Int) := by
      exact_mod_cast hC_lt
    have hcontra : ((ratios.sum : Nat) : Int) *
        ((((if 0 ≤ amount then (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat else ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat : Nat))) : Int) ≤
        (((ratios.sum : Nat) : Int) - 1) *
        (((((List.range ratios.length).filter
          (fun j => decide (0 < (ratios.map (keyAt amount ratios.sum)).getD j 0))).length : Nat)) : Int) := by
      omega
    exact arith_core_test ((ratios.sum : Nat) : Int)
      (((if 0 ≤ amount then (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat else ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat : Nat)) : Int)
      (((((List.range ratios.length).filter
          (fun j => decide (0 < (ratios.map (keyAt amount ratios.sum)).getD j 0))).length : Nat)) : Int)
      hSpos hC0 hCL_int hcontra

theorem req_valid_succeeds : ValidSucceeds allocate := by
  unfold ValidSucceeds Valid allocate
  intro amount ratios h
  obtain ⟨hne, hpos⟩ := h
  cases ratios with
  | nil => simp at hne
  | cons r rs =>
    simp only
    split
    · omega
    · trivial

theorem req_invalid_fails : InvalidFails allocate := by
  unfold InvalidFails Valid allocate
  intro amount ratios h
  cases ratios with
  | nil => rfl
  | cons r rs =>
    simp only
    by_cases hsum : (r :: rs).sum = 0
    · simp [hsum]
    · exfalso; apply h
      constructor
      · simp
      · omega

theorem req_one_share_each : OneShareEach allocate := by
  unfold OneShareEach OneShareEachOn
  intro amount ratios shares h
  cases hr : ratios with
  | nil =>
    simp [allocate, hr] at h
  | cons r rs =>
    subst hr
    simp only [allocate] at h
    split at h
    · simp at h
    · simp at h
      rw [← h]
      simp

theorem req_conservation      : Conserves allocate := sorry

theorem req_within_one_unit   : WithinOneUnit allocate := sorry

theorem req_zero_ratio        : ZeroRatio allocate := sorry

theorem req_sign              : Sign allocate := sorry

theorem req_largest_remainder : LargestRemainder allocate := sorry

end Allocation
