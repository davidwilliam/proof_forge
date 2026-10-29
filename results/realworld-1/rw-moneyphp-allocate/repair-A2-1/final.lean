import Allocation.Spec
namespace Allocation

def allocate : Impl := fun amount ratios =>
  if ratios = [] ∨ ratios.sum = 0 then none
  else
    let S := ratios.sum
    let A := amount.natAbs
    let floors := ratios.map fun r => (A * r) / S
    let rems := ratios.map fun r => (A * r) % S
    let k := A - floors.sum
    let n := ratios.length
    let sharesNat : List Nat :=
      (List.range n).map fun i =>
        let f := floors.getD i 0
        let ri := rems.getD i 0
        let rank := ((List.range n).filter fun j => rems.getD j 0 > ri ∨ (rems.getD j 0 = ri ∧ j < i)).length
        f + if rank < k then 1 else 0
    let shares : List Int :=
      if amount < 0 then sharesNat.map fun x => - ((x : Nat) : Int)
      else sharesNat.map fun x => ((x : Nat) : Int)
    some shares

theorem req_one_share_each_test : True := by
  have h : (let S := (5 : Nat); S + 1) = 6 := rfl
  trivial

theorem probe_option_lemmas : True := by
  trivial
#check Option.some_inj

theorem helper_one_share_each_aux : OneShareEach allocate := by
  intro amount ratios shares h
  unfold allocate at h
  by_cases hc : ratios = [] ∨ ratios.sum = 0
  · rw [if_pos hc] at h; contradiction
  · rw [if_neg hc] at h
    simp only at h
    have hEq := Option.some_inj.mp h
    subst hEq
    unfold OneShareEachOn
    split
    · simp
    · simp

theorem tmp_check_list : (List.range 3).length = 3 := by simp
#check List.sum
#check List.getD
#check List.range
#check List.filter
#check Nat.div_add_mod

theorem tmp_env_probe : True := trivial
#check List.sum
#check List.getD

theorem tmp_probe2 : True := trivial
#check List.length_range
#check List.mem_range
#check List.nodup_range
#check List.getElem_cons
#check Nat.div_add_mod
#check Nat.mod_lt
#check Nat.div_le_self
#check Int.natAbs
#check List.sum_cons

theorem probe_list2 : True := trivial
#check @List.getD
#check @List.length_map
#check @List.length_range
#check @List.getElem_map
#check @List.getElem_range
#check @Nat.div_add_mod
#check @Nat.mod_lt

theorem probe_getelem_syntax : True := trivial
#check fun (l : List Int) (i : Nat) (h : i < l.length) => l[i]
#check @GetElem.getElem

theorem probe_lemmas_file : True := by trivial
#check Allocation.Valid
#check Allocation.excess
#check Allocation.OneShareEachOn

theorem probe_sum_lemmas : True := by trivial
#check @List.sum_cons
#check @List.sum_nil
#check @List.sum_append
#check @List.length_map
#check @List.map_cons

theorem probe_print_getD : True := trivial
#print List.getD

theorem probe_a1 : True := by trivial
#check @List.getElem_map

theorem helper_sign_nonneg_mem (sh : List Nat) (x : Int) (hx : x ∈ sh.map fun x => ((x : Nat) : Int)) : 0 ≤ x := by
  rw [List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact Int.natCast_nonneg y

theorem helper_sign_nonpos_mem (sh : List Nat) (x : Int) (hx : x ∈ sh.map fun x => - ((x : Nat) : Int)) : x ≤ 0 := by
  rw [List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  simp

theorem probe_lemmas_avail : True := trivial
#check Allocation.Valid

theorem helper_natabs_zero_test : (0 : Int).natAbs = 0 := by simp
#check Int.natAbs_zero
#check Int.natAbs_eq_zero
#check List.getD
#check List.getElem_map

theorem probe_getDp : True := trivial
#print List.getD

theorem helper_getD_nil (i : Nat) (d : α) : List.getD ([] : List α) i d = d := by
  unfold List.getD
  simp

theorem helper_map_zero_floors :
    (List.map (fun r => (0 : Nat) * r / S) ratios) = List.map (fun _ => 0) ratios := by
  apply List.map_congr_left
  intro r _
  simp

theorem probe_unfold_alloc : True := trivial
#check (List.range 3).getD
#check List.getD
#check List.range_eq_range'

theorem probe_print_alloc : True := trivial
#print allocate

theorem probe_nat_api : True := trivial
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @Nat.div_le_self
#check @Nat.add_sub_cancel
#check @Int.natAbs
#check @Int.ofNat_sub

theorem probe_simple_ok : True := trivial

theorem helper_test_one : OneShareEach allocate := by
  intro amount ratios shares h
  unfold allocate at h
  by_cases hc : ratios = [] ∨ ratios.sum = 0
  · rw [if_pos hc] at h; contradiction
  · rw [if_neg hc] at h
    simp only at h
    have hEq := Option.some_inj.mp h
    subst hEq
    unfold OneShareEachOn
    split
    · simp
    · simp

theorem probe_list_api : True := trivial
#check List.sum
#check List.length
#check List.map
#check List.filter
#check List.range
#check List.getD
open List in
#check @List.sum_cons
#check @List.sum_nil
#check @List.length_cons

theorem probe_lemmas_import : True := trivial
#check Allocation.Valid

theorem probe_sum_induct : True := trivial
#check @List.sum_nil
#check @List.sum_cons
example : ([1,2,3] : List Nat).sum = 6 := rfl
example : ([1,2] : List Int).sum = 3 := rfl



theorem plan0_sum_map_neg_natCast (l : List Nat) :
    (l.map (fun x : Nat => - (x : Int))).sum = - (l.sum : Int) := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp only [List.map_cons, List.sum_cons, List.sum_cons, ih]; omega


theorem plan0_div_mod_sum (A S : Nat) (ratios : List Nat) (hS : ratios.sum = S) :
    (ratios.map (fun r => (A * r) / S)).sum * S +
      (ratios.map (fun r => (A * r) % S)).sum = A * S := by
  have hgen : ∀ l : List Nat,
    (l.map (fun r => (A * r) / S)).sum * S +
      (l.map (fun r => (A * r) % S)).sum = A * l.sum := by
    intro l
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      have hdm := Nat.div_add_mod (A * hd) S
      have h1 : ((A * hd) / S + (tl.map fun r => (A * r) / S).sum) * S
        = (A * hd) / S * S + (tl.map fun r => (A * r) / S).sum * S := Nat.add_mul _ _ _
      have h2 : (A * hd) / S * S = S * ((A * hd) / S) := Nat.mul_comm _ _
      have h3 : A * (hd + tl.sum) = A * hd + A * tl.sum := Nat.mul_add _ _ _
      omega
  have h := hgen ratios
  rw [hS] at h
  exact h




theorem plan0_sum_range_getD (l : List Nat) :
    ((List.range l.length).map (fun i => l.getD i 0)).sum = l.sum := by sorry

theorem plan0_rank_bonus_count (rems : List Nat) (k : Nat) (hk : k ≤ rems.length) :
    ((List.range rems.length).map (fun i =>
      if ((List.range rems.length).filter (fun j =>
            rems.getD j 0 > rems.getD i 0 ∨
            (rems.getD j 0 = rems.getD i 0 ∧ j < i))).length < k
        then (1 : Nat) else 0)).sum = k := by sorry

theorem plan0_sum_map_natCast2 (l : List Nat) :
    (l.map (fun x : Nat => (x : Int))).sum = (l.sum : Int) := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp [ih]

theorem plan0_sum_map_natCast_dup (l : List Nat) :
    (l.map (fun x : Nat => (x : Int))).sum = (l.sum : Int) := plan0_sum_map_natCast2 l

theorem plan0_sum_map_natCast (l : List Nat) :
    (l.map (fun x : Nat => (x : Int))).sum = (l.sum : Int) := plan0_sum_map_natCast2 l

theorem plan0_sum_map_neg_natCast_fix2 (l : List Nat) :
    (l.map (fun x : Nat => - (x : Int))).sum = - (l.sum : Int) := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp only [List.map_cons, List.sum_cons, List.sum_cons, ih]; omega

theorem plan0_div_mod_sum_aux_general (A S : Nat) (l : List Nat) :
    (l.map (fun r => (A * r) / S)).sum * S +
      (l.map (fun r => (A * r) % S)).sum = A * l.sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    have hdm := Nat.div_add_mod (A * hd) S
    have h1 : ((A * hd) / S + (tl.map fun r => (A * r) / S).sum) * S
      = (A * hd) / S * S + (tl.map fun r => (A * r) / S).sum * S := Nat.add_mul _ _ _
    have h2 : (A * hd) / S * S = S * ((A * hd) / S) := Nat.mul_comm _ _
    have h3 : A * (hd + tl.sum) = A * hd + A * tl.sum := Nat.mul_add _ _ _
    omega

theorem plan0_div_mod_sum_proof : True := trivial

theorem plan0_leftover_le_length (A S : Nat) (ratios : List Nat)
    (hS : 0 < S) (hSeq : S = ratios.sum) :
    A - (ratios.map (fun r => (A * r) / S)).sum ≤ ratios.length := by
  have hDM := plan0_div_mod_sum_aux_general A S ratios
  have hbound : ∀ l : List Nat,
      (l.map (fun r => (A * r) % S)).sum ≤ l.length * S := by
    intro l
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hlt : (A * hd) % S < S := Nat.mod_lt _ hS
      have hmul : (tl.length + 1) * S = tl.length * S + S := by
        have e1 : (tl.length + 1) * S = tl.length * S + 1 * S := Nat.add_mul _ _ _
        have e2 : (1 : Nat) * S = S := Nat.one_mul _
        omega
      omega
  have h1 : (ratios.map (fun r => (A * r) / S)).sum * S ≤ A * S := by
    rw [← hSeq] at hDM
    omega
  have hF_le_A : (ratios.map (fun r => (A * r) / S)).sum ≤ A :=
    Nat.le_of_mul_le_mul_right h1 hS
  have hAeq : (ratios.map (fun r => (A * r) / S)).sum +
      (A - (ratios.map (fun r => (A * r) / S)).sum) = A :=
    Nat.add_sub_of_le hF_le_A
  have htmp := Nat.add_mul
      ((ratios.map (fun r => (A * r) / S)).sum)
      (A - (ratios.map (fun r => (A * r) / S)).sum) S
  rw [hAeq] at htmp
  have hDM2 : (ratios.map (fun r => (A * r) / S)).sum * S +
        (ratios.map (fun r => (A * r) % S)).sum = A * S := by
    rw [← hSeq] at hDM
    exact hDM
  have hR_eq : (A - (ratios.map (fun r => (A * r) / S)).sum) * S =
      (ratios.map (fun r => (A * r) % S)).sum := by omega
  have hle2 : (A - (ratios.map (fun r => (A * r) / S)).sum) * S ≤
      ratios.length * S := by
    rw [hR_eq]
    exact hbound ratios
  exact Nat.le_of_mul_le_mul_right hle2 hS

theorem probe_rs : True := trivial
#check List.range_succ
#check List.sum_append
#check List.map_append
#check List.getD_cons_zero

theorem probe_range_succ_stmt : True := by
  have h := List.range_succ (n := 3)
  have h2 : List.range 0 = ([] : List Nat) := List.range_zero
  trivial
#check @List.range_succ
#check @List.range_zero
#check @List.getD_cons_zero
#check @List.getD_cons_succ
#check @List.take_succ_cons
#check @List.sum_cons
#check @List.map_cons

theorem probe_succ_eq_map : True := by
  have h := @List.range_succ_eq_map
  trivial
#check @List.range_succ_eq_map

theorem plan1_getD_cons_zero {α : Type} (a : α) (l : List α) (d : α) :
    (a :: l).getD 0 d = a := by simp


theorem plan1_getD_cons_succ {α : Type} (a : α) (l : List α) (d : α) (i : Nat) :
    (a :: l).getD (i + 1) d = l.getD i d := by simp


theorem plan1_range_succ_eq_zero_cons_map_succ (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map (fun i => i + 1) := by sorry

theorem plan1_map_range_getD_cons {α : Type} (a : α) (l : List α) (d : α) :
    (List.range (a :: l).length).map (fun i => (a :: l).getD i d) =
      a :: (List.range l.length).map (fun i => l.getD i d) := by sorry

theorem plan1_map_range_getD_eq {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by sorry

theorem plan1_sum_range_getD (l : List Nat) :
    ((List.range l.length).map (fun i => l.getD i 0)).sum = l.sum := by sorry

theorem plan1_getD_cons_zero_test {α : Type} (a : α) (l : List α) (d : α) :
    (a :: l).getD 0 d = a := by simp

theorem plan1_getD_cons_succ_proof {α : Type} (a : α) (l : List α) (d : α) (i : Nat) :
    (a :: l).getD (i + 1) d = l.getD i d := by simp

theorem planX_probe : True := by trivial
#check @List.range_succ
#check @List.range_succ_eq_map
#check @List.map_append
#check @List.cons_append

theorem req_valid_succeeds : ValidSucceeds allocate := by
  intro amount ratios h
  unfold allocate
  have h1 : ¬ (ratios = [] ∨ ratios.sum = 0) := by
    intro hc
    have hv : Valid amount ratios := h
    rw [Valid] at hv
    cases hc with
    | inl heq => exact hv.left heq
    | inr heq => rw [heq] at hv; exact absurd hv.right (Nat.lt_irrefl 0)
  rw [if_neg h1]
  simp

theorem req_invalid_fails : InvalidFails allocate := by
  intro amount ratios h
  have hcond : ratios = [] ∨ ratios.sum = 0 := by
    by_cases hempty : ratios = []
    · exact Or.inl hempty
    · have hne : ratios ≠ [] := hempty
      have hnpos : ¬ 0 < ratios.sum := by
        intro hpos
        apply h
        unfold Valid
        exact ⟨hne, hpos⟩
      have hzero : ratios.sum = 0 := by omega
      exact Or.inr hzero
  unfold allocate
  rw [if_pos hcond]

theorem req_one_share_each : OneShareEach allocate := by
  intro amount ratios shares h
  unfold allocate at h
  by_cases hc : ratios = [] ∨ ratios.sum = 0
  · rw [if_pos hc] at h; contradiction
  · rw [if_neg hc] at h
    simp only at h
    have hEq := Option.some_inj.mp h
    subst hEq
    unfold OneShareEachOn
    split
    · simp
    · simp

theorem req_conservation      : Conserves allocate := sorry

theorem req_within_one_unit   : WithinOneUnit allocate := sorry

theorem req_zero_ratio        : ZeroRatio allocate := sorry

theorem req_sign              : Sign allocate := sorry

theorem req_largest_remainder : LargestRemainder allocate := sorry

end Allocation
