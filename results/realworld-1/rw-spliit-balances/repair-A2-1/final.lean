import Allocation.Spec
namespace Allocation

def insertIdx (rems : List Nat) (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: js => if rems.getD j 0 >= rems.getD i 0 then j :: insertIdx rems i js else i :: j :: js

def sortedIdxs (rems : List Nat) (n : Nat) : List Nat :=
  (List.range n).foldl (fun acc i => insertIdx rems i acc) []

def bumped (rems : List Nat) (n R : Nat) : List Nat :=
  (sortedIdxs rems n).take R

def shareAt (An S : Nat) (ratios : List Nat) (bset : List Nat) (i : Nat) : Int :=
  let r := ratios.getD i 0
  let b : Nat := An * r / S
  if bset.contains i then (b : Int) + 1 else (b : Int)

def sharesNonneg (An : Nat) (ratios : List Nat) : List Int :=
  let S := ratios.sum
  let rems := ratios.map (fun r => An * r % S)
  let n := ratios.length
  let R := rems.sum / S
  let bset := bumped rems n R
  (List.range n).map (fun i => shareAt An S ratios bset i)

def allocate : Impl := fun amount ratios =>
  if ratios = [] ∨ ratios.sum = 0 then none
  else if 0 ≤ amount then some (sharesNonneg amount.toNat ratios)
  else some ((sharesNonneg (-amount).toNat ratios).map (fun x => -x))

theorem tmp_test : True := trivial

theorem len_sharesNonneg_aux (An : Nat) (ratios : List Nat) : (sharesNonneg An ratios).length = ratios.length := by
  unfold sharesNonneg
  simp

def dummyB : Nat := 0
#check @Nat.add_mul_div_left
#check @Nat.mul_div_cancel
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @List.sum_cons
#check @List.map_cons
#check @List.length_map
#check @List.getD

def dummyD : Nat := 0
#check @List.range_succ
#check @List.foldl_append
#check @List.length_take
#check @List.Nodup
#check @List.contains_eq_mem

def dummyE : Nat := 0
#check @List.range_succ
#check @List.length_append
#check @List.foldl_append

def dummyF : Nat := 0
#check @List.range_succ
#check @List.getD_cons_zero
#check @List.getD_cons_succ

def dummyH : Nat := 0
#check @List.sum_append
#check @List.map_append
#check @List.range_succ
#check @Nat.div_le_div_right
#check @Nat.mul_div_cancel
#check @Nat.div_add_mod
#check @List.length_append

def dummyJ : Nat := 0
#check @List.range_succ
#check @List.foldl_append
open List in
example (n : Nat) : range (n+1) = range n ++ [n] := by exact range_succ

def _probe1 : Nat := 0
#check Allocation.Valid
#check Lean.versionString

def _probe3 : Nat := 0
#check Allocation.excess
open Allocation in
#check (show Prop from True)

def _pA : Nat := 0
#check @List.length_range

theorem sig_probe_a : (0 : Int) ≤ 0 := by omega

theorem sig_probe_b (a b : Int) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by omega
#check @Nat.zero_mul
#check @Nat.zero_div
#check @List.take_zero

theorem sharesNonneg_mem_nonneg (An : Nat) (ratios : List Nat) (x : Int)
  (hx : x ∈ sharesNonneg An ratios) : 0 ≤ x := by
  unfold sharesNonneg at hx
  simp only at hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  unfold shareAt
  simp only
  split
  · have h2 : (0 : Int) ≤ ((An * ratios.getD i 0 / ratios.sum : Nat) : Int) := Int.ofNat_nonneg _
    omega
  · exact Int.ofNat_nonneg _

theorem rems_sum_An_zero (ratios : List Nat) (S : Nat)
  : (ratios.map (fun r => 0 * r % S)).sum = 0 := by
  induction ratios with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp [Nat.zero_mul]

theorem shareAt_zero_nil (ratios : List Nat) (S i : Nat) : shareAt 0 S ratios [] i = 0 := by
  unfold shareAt
  simp [Nat.zero_mul]

theorem bumped_R_zero (rems : List Nat) (n : Nat) (R : Nat) (hR : R = 0) : bumped rems n R = [] := by
  rw [hR]
  unfold bumped
  simp

theorem probe_lemmas : True := trivial
#check @List.getD
#check @List.contains
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @List.length_range
#check @List.mem_range

theorem probeB : True := trivial
#check @List.sum
#check @Nat.div_add_mod

theorem probeE : True := trivial
#print Allocation.WithinOneUnitOn

def foo : Nat := 0

theorem insertIdx_length (rems : List Nat) (i : Nat) (l : List Nat) :
    (insertIdx rems i l).length = l.length + 1 := by
  unfold insertIdx
  cases l with
  | nil => rfl
  | cons j js =>
    simp only
    split
    · simp [insertIdx_length rems i js]
    · rfl

theorem sortedIdxs_succ (rems : List Nat) (n : Nat) :
    sortedIdxs rems (n+1) = insertIdx rems n (sortedIdxs rems n) := by
  unfold sortedIdxs
  rw [List.range_succ]
  rw [List.foldl_append]
  rfl

theorem sortedIdxs_length (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).length = n := by
  induction n with
  | zero => unfold sortedIdxs; simp
  | succ n ih =>
    rw [sortedIdxs_succ, insertIdx_length, ih]

theorem bumped_length_le (rems : List Nat) (n R : Nat) :
    (bumped rems n R).length = min R n := by
  unfold bumped
  rw [List.length_take, sortedIdxs_length]

theorem plan0_floor_rem_sum (An S : Nat) (l : List Nat) :
    (l.map (fun r => An * r % S)).sum + S * (l.map (fun r => An * r / S)).sum
      = An * l.sum := by
  induction l with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hdiv : S * (An * r / S) + An * r % S = An * r := Nat.div_add_mod _ _
    calc (An * r % S + (rs.map fun r => An * r % S).sum) + S * (An * r / S + (rs.map fun r => An * r / S).sum)
        = (An * r % S + S * (An * r / S)) + ((rs.map fun r => An * r % S).sum + S * (rs.map fun r => An * r / S).sum) := by
          rw [Nat.mul_add]; omega
      _ = An * r + An * rs.sum := by rw [ih]; omega
      _ = An * (r + rs.sum) := by rw [Nat.mul_add]




theorem plan0_sortedIdxs_props (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup ∧ ∀ i : Nat, i ∈ sortedIdxs rems n ↔ i < n := by
  have hmemInsert : ∀ (rs : List Nat) (a x : Nat) (l : List Nat),
      x ∈ insertIdx rs a l ↔ x = a ∨ x ∈ l := by
    intro rs a x l
    induction l with
    | nil =>
      have h0 : insertIdx rs a [] = [a] := rfl
      rw [h0]
      simp
    | cons j js ih =>
      have hdef : insertIdx rs a (j :: js) =
        (if rs.getD j 0 >= rs.getD a 0 then j :: insertIdx rs a js else a :: j :: js) := rfl
      rw [hdef]
      by_cases hc : rs.getD j 0 >= rs.getD a 0
      · rw [if_pos hc]
        simp only [List.mem_cons, ih]
        constructor
        · intro h
          rcases h with rfl | rfl | h
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)
        · intro h
          rcases h with rfl | h
          · exact Or.inr (Or.inl rfl)
          · rcases h with rfl | h
            · exact Or.inl rfl
            · exact Or.inr (Or.inr h)
      · rw [if_neg hc]
        simp only [List.mem_cons]
  have hmem : ∀ (m : Nat) (i : Nat), i ∈ sortedIdxs rems m ↔ i < m := by
    intro m i
    induction m with
    | zero =>
      unfold sortedIdxs
      simp
    | succ m ih =>
      rw [sortedIdxs_succ, hmemInsert, ih]
      omega
  have hins : ∀ (i : Nat) (l : List Nat), l.Nodup → i ∉ l → (insertIdx rems i l).Nodup := by
    intro i l hnd hi
    induction l with
    | nil =>
      have h0 : insertIdx rems i [] = [i] := rfl
      rw [h0]
      simp
    | cons j js ih =>
      have hdef : insertIdx rems i (j :: js) =
        (if rems.getD j 0 >= rems.getD i 0 then j :: insertIdx rems i js else i :: j :: js) := rfl
      rw [hdef]
      have hnd_js : js.Nodup := (List.nodup_cons.mp hnd).2
      have hj_notin : j ∉ js := (List.nodup_cons.mp hnd).1
      have hi_ne_j : i ≠ j := by
        intro heq
        apply hi
        rw [heq]
        exact List.Mem.head _
      have hi_notin_js : i ∉ js := by
        intro hm
        apply hi
        exact List.Mem.tail _ hm
      have ih' : (insertIdx rems i js).Nodup := ih hnd_js hi_notin_js
      by_cases hc : rems.getD j 0 >= rems.getD i 0
      · rw [if_pos hc]
        rw [List.nodup_cons]
        constructor
        · intro hm
          rw [hmemInsert] at hm
          rcases hm with rfl | hm
          · exact hi_ne_j rfl
          · exact hj_notin hm
        · exact ih'
      · rw [if_neg hc]
        rw [List.nodup_cons]
        exact ⟨hi, hnd⟩
  have hnodup : ∀ (m : Nat), (sortedIdxs rems m).Nodup := by
    intro m
    induction m with
    | zero =>
      unfold sortedIdxs
      simp
    | succ m ih =>
      rw [sortedIdxs_succ]
      apply hins _ _ ih
      intro hm
      rw [hmem] at hm
      omega
  exact ⟨hnodup n, fun i => hmem n i⟩


theorem plan0_sum_shareAt (An S : Nat) (ratios : List Nat) (bset : List Nat)
    (hnd : bset.Nodup) (hmem : ∀ i : Nat, i ∈ bset → i < ratios.length) :
    ((List.range ratios.length).map (fun i => shareAt An S ratios bset i)).sum
      = ((ratios.map (fun r => An * r / S)).sum : Int) + (bset.length : Int) := by sorry

theorem plan0_floors_add_quotient (An : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    (ratios.map (fun r => An * r / ratios.sum)).sum
        + (ratios.map (fun r => An * r % ratios.sum)).sum / ratios.sum = An
      ∧ (ratios.map (fun r => An * r % ratios.sum)).sum / ratios.sum
          ≤ ratios.length := by sorry

theorem plan0_sharesNonneg_sum (An : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    (sharesNonneg An ratios).sum = (An : Int) := by sorry

theorem plan0_floor_rem_sum_aux (An S : Nat) (l : List Nat) :
    (l.map (fun r => An * r % S)).sum + S * (l.map (fun r => An * r / S)).sum
      = An * l.sum := by
  induction l with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hdiv : S * (An * r / S) + An * r % S = An * r := Nat.div_add_mod _ _
    calc (An * r % S + (rs.map fun r => An * r % S).sum) + S * (An * r / S + (rs.map fun r => An * r / S).sum)
        = (An * r % S + S * (An * r / S)) + ((rs.map fun r => An * r % S).sum + S * (rs.map fun r => An * r / S).sum) := by
          rw [Nat.mul_add]; omega
      _ = An * r + An * rs.sum := by rw [ih]; omega
      _ = An * (r + rs.sum) := by rw [Nat.mul_add]

theorem plan0_floor_rem_sum_proof : ∀ (An S : Nat) (l : List Nat),
    (l.map (fun r => An * r % S)).sum + S * (l.map (fun r => An * r / S)).sum
      = An * l.sum := fun An S l => plan0_floor_rem_sum_aux An S l

theorem probe_mapmap_sig : True := trivial

theorem range_zero_cons_map_succ_aux (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map (fun x => x + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hr1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := List.range_succ
    have hr2 : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    have hmap : ((List.range (n + 1)).map (fun x => x + 1))
        = ((List.range n).map (fun x => x + 1)) ++ [n + 1] := by
      rw [hr2, List.map_append]
      rfl
    calc List.range (n + 1 + 1)
        = List.range (n + 1) ++ [n + 1] := hr1
      _ = (0 :: (List.range n).map (fun x => x + 1)) ++ [n + 1] := by rw [ih]
      _ = 0 :: (((List.range n).map (fun x => x + 1)) ++ [n + 1]) := rfl
      _ = 0 :: ((List.range (n + 1)).map (fun x => x + 1)) := by rw [hmap]

theorem hcomp_test (f : Nat → Nat) (hd : Nat) (tl : List Nat) :
    (fun i => f ((hd :: tl).getD i 0)) ∘ (fun x => x + 1)
        = (fun i => f (tl.getD i 0)) := by
  funext i
  simp only [Function.comp_apply]
  simp





theorem plan1_range_succ_cons_map_succ (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map (fun x => x + 1) :=
  range_zero_cons_map_succ_aux n




theorem plan1_range_map_getD (f : Nat → Nat) (l : List Nat) :
    (List.range l.length).map (fun i => f (l.getD i 0)) = l.map f := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hlen : (a :: t).length = t.length + 1 := rfl
    rw [hlen, plan1_range_succ_cons_map_succ]
    simp only [List.map_cons]
    have hhead : f ((a :: t).getD 0 0) = f a := by rfl
    rw [hhead]
    congr 1
    have h1 : ((List.range t.length).map (fun x => x + 1)).map (fun i => f ((a :: t).getD i 0))
        = (List.range t.length).map ((fun i => f ((a :: t).getD i 0)) ∘ (fun x => x + 1)) := by
      rw [List.map_map]
    rw [h1, hcomp_test, ih]


theorem plan1_getD_cons_zero (a : Nat) (l : List Nat) (d : Nat) :
    (a :: l).getD 0 d = a := by rfl

theorem plan1_getD_cons_succ_test (a : Nat) (l : List Nat) (i d : Nat) :
    (a :: l).getD (i + 1) d = l.getD i d := by simp

theorem plan1_getD_cons_succ (a : Nat) (l : List Nat) (i d : Nat) :
    (a :: l).getD (i + 1) d = l.getD i d := by simp

theorem plan1_range_succ_cons_map_succ_aux2 (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map (fun x => x + 1) :=
  range_zero_cons_map_succ_aux n

theorem plan1_map_range_getD_cons_succ (f : Nat → Nat) (a : Nat) (l : List Nat) :
    (List.range l.length).map (fun i => f ((a :: l).getD (i + 1) 0))
      = (List.range l.length).map (fun i => f (l.getD i 0)) := by
  have hfun : (fun i => f ((a :: l).getD (i + 1) 0)) = (fun i => f (l.getD i 0)) := by
    funext i
    simp only [plan1_getD_cons_succ]
  rw [hfun]

theorem plan1_range_map_getD_test (f : Nat → Nat) (l : List Nat) :
    (List.range l.length).map (fun i => f (l.getD i 0)) = l.map f := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hlen : (a :: t).length = t.length + 1 := rfl
    rw [hlen, plan1_range_succ_cons_map_succ]
    simp only [List.map_cons, plan1_getD_cons_zero]
    congr 1
    have h1 : ((List.range t.length).map (fun x => x + 1)).map (fun i => f ((a :: t).getD i 0))
        = (List.range t.length).map (fun i => f ((a :: t).getD (i + 1) 0)) := by
      rw [List.map_map]
      rfl
    rw [h1, plan1_map_range_getD_cons_succ, ih]

theorem plan1_range_map_getD_check (f : Nat → Nat) (l : List Nat) :
    (List.range l.length).map (fun i => f (l.getD i 0)) = l.map f := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hlen : (a :: t).length = t.length + 1 := rfl
    rw [hlen, plan1_range_succ_cons_map_succ]
    simp only [List.map_cons]
    have hhead : f ((a :: t).getD 0 0) = f a := by rfl
    rw [hhead]
    congr 1
    have h1 : ((List.range t.length).map (fun x => x + 1)).map (fun i => f ((a :: t).getD i 0))
        = (List.range t.length).map ((fun i => f ((a :: t).getD i 0)) ∘ (fun x => x + 1)) := by
      rw [List.map_map]
    rw [h1, hcomp_test, ih]

theorem plan0_range_map_getD (f : Nat → Nat) (l : List Nat) :
    (List.range l.length).map (fun i => f (l.getD i 0)) = l.map f :=
  plan1_range_map_getD f l

theorem insertIdx_unfold_test (rems : List Nat) (a j : Nat) (js : List Nat) :
    True := by
  have h := (insertIdx rems a (j :: js))
  unfold insertIdx at h
  trivial

theorem probe_insert_eq (rems : List Nat) (a j : Nat) (js : List Nat) :
    insertIdx rems a (j :: js) = (if rems.getD j 0 >= rems.getD a 0 then j :: insertIdx rems a js else a :: j :: js) := by
  rfl

theorem probe_mem2 (x a j : Nat) (js : List Nat) :
    (x ∈ a :: j :: js) = (x = a ∨ x ∈ j :: js) := by
  simp only [List.mem_cons]

theorem insertIdx_mem_hlp4 (rems : List Nat) (a x : Nat) (l : List Nat) :
    x ∈ insertIdx rems a l ↔ x = a ∨ x ∈ l := by
  induction l with
  | nil =>
    have h0 : insertIdx rems a [] = [a] := rfl
    rw [h0]
    simp
  | cons j js ih =>
    have hdef : insertIdx rems a (j :: js) =
      (if rems.getD j 0 >= rems.getD a 0 then j :: insertIdx rems a js else a :: j :: js) := rfl
    rw [hdef]
    by_cases hc : rems.getD j 0 >= rems.getD a 0
    · rw [if_pos hc]
      simp only [List.mem_cons, ih]
      constructor
      · intro h
        rcases h with rfl | rfl | h
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h)
      · intro h
        rcases h with rfl | h
        · exact Or.inr (Or.inl rfl)
        · rcases h with rfl | h
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)
    · rw [if_neg hc]
      simp only [List.mem_cons]

theorem plan2_insertIdx_nodup (rems : List Nat) (i : Nat) (l : List Nat)
    (hnd : l.Nodup) (hi : i ∉ l) : (insertIdx rems i l).Nodup := by
  induction l with
  | nil =>
    have h0 : insertIdx rems i [] = [i] := rfl
    rw [h0]
    simp
  | cons j js ih =>
    have hdef : insertIdx rems i (j :: js) =
      (if rems.getD j 0 >= rems.getD i 0 then j :: insertIdx rems i js else i :: j :: js) := rfl
    rw [hdef]
    have hnd_js : js.Nodup := (List.nodup_cons.mp hnd).2
    have hj_notin : j ∉ js := (List.nodup_cons.mp hnd).1
    have hi_ne_j : i ≠ j := by
      intro heq
      apply hi
      rw [heq]
      exact List.Mem.head _
    have hi_notin_js : i ∉ js := by
      intro hm
      apply hi
      exact List.Mem.tail _ hm
    have ih' : (insertIdx rems i js).Nodup := ih hnd_js hi_notin_js
    by_cases hc : rems.getD j 0 >= rems.getD i 0
    · rw [if_pos hc]
      rw [List.nodup_cons]
      constructor
      · intro hm
        rw [insertIdx_mem_hlp4] at hm
        rcases hm with rfl | hm
        · exact hi_ne_j rfl
        · exact hj_notin hm
      · exact ih'
    · rw [if_neg hc]
      rw [List.nodup_cons]
      exact ⟨hi, hnd⟩




theorem plan2_sortedIdxs_nodup (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup := by
  have hmem : ∀ (m : Nat) (i : Nat), i ∈ sortedIdxs rems m → i < m := by
    intro m
    induction m with
    | zero =>
      intro i hi
      unfold sortedIdxs at hi
      simp at hi
    | succ m ih =>
      intro i hi
      rw [sortedIdxs_succ, insertIdx_mem_hlp4] at hi
      rcases hi with rfl | hi
      · omega
      · have h := ih i hi
        omega
  induction n with
  | zero =>
    unfold sortedIdxs
    simp
  | succ n ih =>
    rw [sortedIdxs_succ]
    apply plan2_insertIdx_nodup _ _ _ ih
    intro hm
    have h := hmem n _ hm
    omega




theorem plan2_insertIdx_nodup_proof (rems : List Nat) (i : Nat) (l : List Nat)
    (hnd : l.Nodup) (hi : i ∉ l) : (insertIdx rems i l).Nodup := by
  induction l with
  | nil =>
    have h0 : insertIdx rems i [] = [i] := rfl
    rw [h0]
    simp
  | cons j js ih =>
    have hdef : insertIdx rems i (j :: js) =
      (if rems.getD j 0 >= rems.getD i 0 then j :: insertIdx rems i js else i :: j :: js) := rfl
    rw [hdef]
    have hnd_js : js.Nodup := (List.nodup_cons.mp hnd).2
    have hj_notin : j ∉ js := (List.nodup_cons.mp hnd).1
    have hi_ne_j : i ≠ j := by
      intro heq
      apply hi
      rw [heq]
      exact List.Mem.head _
    have hi_notin_js : i ∉ js := by
      intro hm
      apply hi
      exact List.Mem.tail _ hm
    have ih' : (insertIdx rems i js).Nodup := ih hnd_js hi_notin_js
    by_cases hc : rems.getD j 0 >= rems.getD i 0
    · rw [if_pos hc]
      rw [List.nodup_cons]
      constructor
      · intro hm
        rw [insertIdx_mem_hlp4] at hm
        rcases hm with rfl | hm
        · exact hi_ne_j rfl
        · exact hj_notin hm
      · exact ih'
    · rw [if_neg hc]
      rw [List.nodup_cons]
      exact ⟨hi, hnd⟩

theorem plan2_sortedIdxs_mem (rems : List Nat) (n i : Nat) :
    i ∈ sortedIdxs rems n ↔ i < n := by
  induction n with
  | zero =>
    unfold sortedIdxs
    simp
  | succ n ih =>
    rw [sortedIdxs_succ, insertIdx_mem_hlp4, ih]
    omega

theorem plan2_sortedIdxs_nodup_aux_unique (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup := by
  induction n with
  | zero =>
    unfold sortedIdxs
    simp
  | succ n ih =>
    rw [sortedIdxs_succ]
    apply plan2_insertIdx_nodup _ _ _ ih
    intro hm
    rw [plan2_sortedIdxs_mem] at hm
    omega

theorem plan2_nodup_selfcontained_test (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup := by
  have hmem : ∀ (m : Nat) (i : Nat), i ∈ sortedIdxs rems m → i < m := by
    intro m
    induction m with
    | zero =>
      intro i hi
      unfold sortedIdxs at hi
      simp at hi
    | succ m ih =>
      intro i hi
      rw [sortedIdxs_succ, insertIdx_mem_hlp4] at hi
      rcases hi with rfl | hi
      · omega
      · have h := ih i hi
        omega
  induction n with
  | zero =>
    unfold sortedIdxs
    simp
  | succ n ih =>
    rw [sortedIdxs_succ]
    apply plan2_insertIdx_nodup _ _ _ ih
    intro hm
    have h := hmem n _ hm
    omega

theorem plan2_sortedIdxs_nodup_fix (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup := by
  have hmem : ∀ (m : Nat) (i : Nat), i ∈ sortedIdxs rems m → i < m := by
    intro m
    induction m with
    | zero =>
      intro i hi
      unfold sortedIdxs at hi
      simp at hi
    | succ m ih =>
      intro i hi
      rw [sortedIdxs_succ, insertIdx_mem_hlp4] at hi
      rcases hi with rfl | hi
      · omega
      · have h := ih i hi
        omega
  induction n with
  | zero =>
    unfold sortedIdxs
    simp
  | succ n ih =>
    rw [sortedIdxs_succ]
    exact plan2_insertIdx_nodup rems n (sortedIdxs rems n) ih (fun hm => by have h := hmem n _ hm; omega)

theorem plan2_sortedIdxs_nodup_inline (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup := by
  have hmem : ∀ (m : Nat) (i : Nat), i ∈ sortedIdxs rems m → i < m := by
    intro m
    induction m with
    | zero =>
      intro i hi
      unfold sortedIdxs at hi
      simp at hi
    | succ m ih =>
      intro i hi
      rw [sortedIdxs_succ, insertIdx_mem_hlp4] at hi
      rcases hi with rfl | hi
      · omega
      · have h := ih i hi
        omega
  induction n with
  | zero =>
    unfold sortedIdxs
    simp
  | succ n ih =>
    rw [sortedIdxs_succ]
    apply plan2_insertIdx_nodup _ _ _ ih
    intro hm
    have h := hmem n _ hm
    omega

theorem plan2_sortedIdxs_props_fix (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup ∧ ∀ i : Nat, i ∈ sortedIdxs rems n ↔ i < n :=
  ⟨plan2_sortedIdxs_nodup_aux_unique rems n, fun i => plan2_sortedIdxs_mem rems n i⟩

theorem plan2_sortedIdxs_props (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup ∧ ∀ i : Nat, i ∈ sortedIdxs rems n ↔ i < n :=
  ⟨plan2_sortedIdxs_nodup_aux_unique rems n, fun i => plan2_sortedIdxs_mem rems n i⟩

theorem plan0_sortedIdxs_props_test (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup ∧ ∀ i : Nat, i ∈ sortedIdxs rems n ↔ i < n :=
  ⟨plan2_sortedIdxs_nodup_aux_unique rems n, fun i => plan2_sortedIdxs_mem rems n i⟩

theorem plan0_self_test2 (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup ∧ ∀ i : Nat, i ∈ sortedIdxs rems n ↔ i < n := by
  have hmem : ∀ (m : Nat) (i : Nat), i ∈ sortedIdxs rems m ↔ i < m := by
    intro m i
    induction m with
    | zero =>
      unfold sortedIdxs
      simp
    | succ m ih =>
      rw [sortedIdxs_succ, insertIdx_mem_hlp4, ih]
      omega
  have hins : ∀ (i : Nat) (l : List Nat), l.Nodup → i ∉ l → (insertIdx rems i l).Nodup := by
    intro i l hnd hi
    induction l with
    | nil =>
      have h0 : insertIdx rems i [] = [i] := rfl
      rw [h0]
      simp
    | cons j js ih =>
      have hdef : insertIdx rems i (j :: js) =
        (if rems.getD j 0 >= rems.getD i 0 then j :: insertIdx rems i js else i :: j :: js) := rfl
      rw [hdef]
      have hnd_js : js.Nodup := (List.nodup_cons.mp hnd).2
      have hj_notin : j ∉ js := (List.nodup_cons.mp hnd).1
      have hi_ne_j : i ≠ j := by
        intro heq
        apply hi
        rw [heq]
        exact List.Mem.head _
      have hi_notin_js : i ∉ js := by
        intro hm
        apply hi
        exact List.Mem.tail _ hm
      have ih' : (insertIdx rems i js).Nodup := ih hnd_js hi_notin_js
      by_cases hc : rems.getD j 0 >= rems.getD i 0
      · rw [if_pos hc]
        rw [List.nodup_cons]
        constructor
        · intro hm
          rw [insertIdx_mem_hlp4] at hm
          rcases hm with rfl | hm
          · exact hi_ne_j rfl
          · exact hj_notin hm
        · exact ih'
      · rw [if_neg hc]
        rw [List.nodup_cons]
        exact ⟨hi, hnd⟩
  have hnodup : ∀ (m : Nat), (sortedIdxs rems m).Nodup := by
    intro m
    induction m with
    | zero =>
      unfold sortedIdxs
      simp
    | succ m ih =>
      rw [sortedIdxs_succ]
      apply hins _ _ ih
      intro hm
      rw [hmem] at hm
      omega
  exact ⟨hnodup n, fun i => hmem n i⟩

theorem plan0_self_test3 (rems0 : List Nat) (n0 : Nat) :
    (sortedIdxs rems0 n0).Nodup ∧ ∀ i : Nat, i ∈ sortedIdxs rems0 n0 ↔ i < n0 := by
  have hmemInsert : ∀ (rs : List Nat) (a x : Nat) (l : List Nat),
      x ∈ insertIdx rs a l ↔ x = a ∨ x ∈ l := by
    intro rs a x l
    induction l with
    | nil =>
      have h0 : insertIdx rs a [] = [a] := rfl
      rw [h0]
      simp
    | cons j js ih =>
      have hdef : insertIdx rs a (j :: js) =
        (if rs.getD j 0 >= rs.getD a 0 then j :: insertIdx rs a js else a :: j :: js) := rfl
      rw [hdef]
      by_cases hc : rs.getD j 0 >= rs.getD a 0
      · rw [if_pos hc]
        simp only [List.mem_cons, ih]
        constructor
        · intro h
          rcases h with rfl | rfl | h
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)
        · intro h
          rcases h with rfl | h
          · exact Or.inr (Or.inl rfl)
          · rcases h with rfl | h
            · exact Or.inl rfl
            · exact Or.inr (Or.inr h)
      · rw [if_neg hc]
        simp only [List.mem_cons]
  have hmem : ∀ (m : Nat) (i : Nat), i ∈ sortedIdxs rems0 m ↔ i < m := by
    intro m i
    induction m with
    | zero =>
      unfold sortedIdxs
      simp
    | succ m ih =>
      rw [sortedIdxs_succ, hmemInsert, ih]
      omega
  have hins : ∀ (i : Nat) (l : List Nat), l.Nodup → i ∉ l → (insertIdx rems0 i l).Nodup := by
    intro i l hnd hi
    induction l with
    | nil =>
      have h0 : insertIdx rems0 i [] = [i] := rfl
      rw [h0]
      simp
    | cons j js ih =>
      have hdef : insertIdx rems0 i (j :: js) =
        (if rems0.getD j 0 >= rems0.getD i 0 then j :: insertIdx rems0 i js else i :: j :: js) := rfl
      rw [hdef]
      have hnd_js : js.Nodup := (List.nodup_cons.mp hnd).2
      have hj_notin : j ∉ js := (List.nodup_cons.mp hnd).1
      have hi_ne_j : i ≠ j := by
        intro heq
        apply hi
        rw [heq]
        exact List.Mem.head _
      have hi_notin_js : i ∉ js := by
        intro hm
        apply hi
        exact List.Mem.tail _ hm
      have ih' : (insertIdx rems0 i js).Nodup := ih hnd_js hi_notin_js
      by_cases hc : rems0.getD j 0 >= rems0.getD i 0
      · rw [if_pos hc]
        rw [List.nodup_cons]
        constructor
        · intro hm
          rw [hmemInsert] at hm
          rcases hm with rfl | hm
          · exact hi_ne_j rfl
          · exact hj_notin hm
        · exact ih'
      · rw [if_neg hc]
        rw [List.nodup_cons]
        exact ⟨hi, hnd⟩
  have hnodup : ∀ (m : Nat), (sortedIdxs rems0 m).Nodup := by
    intro m
    induction m with
    | zero =>
      unfold sortedIdxs
      simp
    | succ m ih =>
      rw [sortedIdxs_succ]
      apply hins _ _ ih
      intro hm
      rw [hmem] at hm
      omega
  exact ⟨hnodup n0, fun i => hmem n0 i⟩

theorem my_shareAt_eq (An S : Nat) (ratios : List Nat) (bset : List Nat) (i : Nat) :
    shareAt An S ratios bset i =
      ((An * ratios.getD i 0 / S : Nat) : Int) + (if bset.contains i then (1 : Int) else 0) := by
  unfold shareAt
  by_cases hc : bset.contains i = true
  · rw [hc]; simp
  · have hc2 : bset.contains i = false := by
      cases hb : bset.contains i with
      | true => rw [hb] at hc; contradiction
      | false => rfl
    rw [hc2]; simp

theorem my_contains_head (a : Nat) (l : List Nat) : (a :: l).contains a = true := by
  simp

theorem req_valid_succeeds : ValidSucceeds allocate := by
  unfold ValidSucceeds Valid allocate
  intro amount ratios h
  obtain ⟨hne, hpos⟩ := h
  have h1 : ¬ (ratios = [] ∨ ratios.sum = 0) := by
    intro hc
    cases hc with
    | inl he => exact hne he
    | inr he => rw [he] at hpos; exact (Nat.lt_irrefl 0 hpos)
  simp [h1]
  by_cases hc : 0 ≤ amount <;> simp [hc]

theorem req_invalid_fails : InvalidFails allocate := by
  unfold InvalidFails Valid allocate
  intro amount ratios h
  have hc : ratios = [] ∨ ratios.sum = 0 := by
    by_cases he : ratios = []
    · exact Or.inl he
    · by_cases hs : ratios.sum = 0
      · exact Or.inr hs
      · exfalso; apply h
        constructor
        · exact he
        · omega
  simp [hc]

theorem req_one_share_each : OneShareEach allocate := by
  unfold OneShareEach OneShareEachOn allocate
  intro amount ratios shares h
  by_cases hc : ratios = [] ∨ ratios.sum = 0
  · simp [hc] at h
  · simp [hc] at h
    by_cases hnn : 0 ≤ amount
    · simp [hnn] at h
      subst h
      rw [len_sharesNonneg_aux]
    · simp [hnn] at h
      subst h
      simp [len_sharesNonneg_aux]

theorem req_conservation      : Conserves allocate := sorry

theorem req_within_one_unit   : WithinOneUnit allocate := sorry

theorem req_zero_ratio        : ZeroRatio allocate := sorry

theorem req_sign              : Sign allocate := sorry

theorem req_largest_remainder : LargestRemainder allocate := sorry

end Allocation
