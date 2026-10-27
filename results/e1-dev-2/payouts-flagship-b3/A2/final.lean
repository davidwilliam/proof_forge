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

theorem myNonneg_proof2 : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      simp [step, hv]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have hbal : (step s r).2.balance a = expectedBalance s r a := by rw [hstep]
    rw [hacc] at ha
    rw [hbal]
    obtain ⟨hnodup, hpos, hne, hnodupR, hnotmem, hsrcMem, hrecMem, hauth, hle, htx⟩ := hv
    unfold expectedBalance
    by_cases hsrc : a = r.source
    · subst hsrc
      have hshare : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hnotmem]
      rw [if_pos rfl, hshare]
      simp
      omega
    · rw [if_neg hsrc]
      have h1 : 0 ≤ s.balance a := hnn a ha
      have h2 : (0 : Int) ≤ ((shareOf r a : Nat) : Int) := by exact_mod_cast Nat.zero_le _
      omega
  · have hstep : step s r = (.rejected, s) := by simp [step, hv]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have hbal : (step s r).2.balance a = s.balance a := by rw [hstep]
    rw [hacc] at ha
    rw [hbal]
    exact hnn a ha

theorem foo_thm : True := trivial

theorem check_range_thm : List.range 3 = [0,1,2] := rfl

theorem probe_append : ∀ (l1 l2 : List Nat) (f : Nat → Int), sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  intro l1 l2 f
  induction l1 with
  | nil => simp
  | cons a t ih => simp [ih]; omega

theorem idx_of_mem_offset : ∀ (l1 : List Nat) (x : Nat), x ∉ l1 → indexOf? l1 x = none → True := by intro _ _ _ _; trivial

theorem probe_range_lemma : ∀ (n : Nat), List.range (n + 1) = List.range n ++ [n] := by
  intro n
  have h := List.range_succ (n := n)
  simpa using h

theorem probe_mem_filter_test : ∀ (l : List Nat) (p : Nat → Bool) (x : Nat), x ∈ l.filter p → x ∈ l := by
  intro l p x h
  exact (List.mem_filter.mp h).1

def sumFairAux (amount n : Nat) : List Nat → Nat → Int
  | [], _ => 0
  | _ :: xs, k => ((fairShare amount n k : Nat) : Int) + sumFairAux amount n xs (k + 1)

def sumRangeFair (amount n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, k => fairShare amount n k + sumRangeFair amount n m (k + 1)

theorem sumRangeFair_zero (amount n k : Nat) : sumRangeFair amount n 0 k = 0 := rfl

theorem sumRangeFair_succ (amount n m k : Nat) :
    sumRangeFair amount n (m + 1) k = fairShare amount n k + sumRangeFair amount n m (k + 1) := rfl

theorem min_succ_eq (m d : Nat) (hd : 1 ≤ d) : min (m + 1) d = 1 + min m (d - 1) := by
  omega

theorem rem_add_eq2 (m k r : Nat) :
    (if k < r then 1 else 0) + (if k + 1 < r then min m (r - (k + 1)) else 0) =
    (if k < r then min (m + 1) (r - k) else 0) := by
  by_cases hk : k < r
  · have hk1 : k + 1 ≤ r := hk
    by_cases hk2 : k + 1 < r
    · have h1 : min (m + 1) (r - k) = 1 + min m (r - (k + 1)) := by omega
      simp only [hk, hk2, if_true]
      omega
    · have hmin1 : min (m + 1) (r - k) = 1 := by omega
      simp only [hk, hk2, if_true, if_false]
      omega
  · have hk2 : ¬ (k + 1 < r) := by omega
    simp [hk, hk2]

theorem hmul_test3 (m q : Nat) : (m + 1) * q = q + m * q := by
  simp [Nat.add_mul, Nat.one_mul, Nat.add_comm]













theorem plan0_sumOver_range_const : ∀ (n : Nat) (c : Int),
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  intro n c
  induction n with
  | zero => simp
  | succ n ih =>
    have h : List.range (n+1) = List.range n ++ [n] := by
      have h2 := List.range_succ (n := n)
      simpa using h2
    rw [h]
    have happ : ∀ (l1 l2 : List Nat) (f : Nat → Int), sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
      intro l1 l2 f
      induction l1 with
      | nil => simp
      | cons a t iht => simp [iht]; omega
    rw [happ, ih]
    simp only [sumOver_cons, sumOver_nil]
    have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
    rw [hcast, Int.add_mul, Int.one_mul]
    omega

theorem plan0_indicator_test_aux2 : ∀ (n m : Nat), m ≤ n →
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    simp
  | succ n ih =>
    intro m hm
    have hrange : List.range (n + 1) = List.range n ++ [n] := by
      have h2 := List.range_succ (n := n)
      simpa using h2
    by_cases hmn : m ≤ n
    · have heq : sumOver (List.range (n+1)) (fun i => if i < m then (1:Int) else 0)
          = sumOver (List.range n) (fun i => if i < m then (1:Int) else 0)
            + sumOver ([n] : List Nat) (fun i => if i < m then (1:Int) else 0) := by
        rw [hrange]
        exact probe_append (List.range n) [n] _
      rw [heq, ih m hmn]
      have hnm : ¬ (n < m) := by omega
      have hsing : sumOver ([n] : List Nat) (fun i => if i < m then (1:Int) else 0) = 0 := by
        simp [hnm]
      rw [hsing, Int.add_zero]
    · have hmeq : m = n + 1 := by omega
      subst hmeq
      have heq : sumOver (List.range (n+1)) (fun i => if i < (n+1) then (1:Int) else 0)
          = sumOver (List.range n) (fun i => if i < (n+1) then (1:Int) else 0)
            + sumOver ([n] : List Nat) (fun i => if i < (n+1) then (1:Int) else 0) := by
        rw [hrange]
        exact probe_append (List.range n) [n] _
      rw [heq]
      have hsing : sumOver ([n] : List Nat) (fun i => if i < (n+1) then (1:Int) else 0) = 1 := by
        simp
      have hcongr : sumOver (List.range n) (fun i => if i < (n+1) then (1:Int) else 0)
          = sumOver (List.range n) (fun i => if i < n then (1:Int) else 0) := by
        apply sumOver_congr
        intro a ha
        have ham : a < n := List.mem_range.mp ha
        have h1 : a < n + 1 := by omega
        simp [h1, ham]
      rw [hcongr, ih n (Nat.le_refl n), hsing]
      push_cast
      omega

theorem plan0_sumOver_range_indicator : ∀ (n m : Nat), m ≤ n →
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := by
  intro n m hm
  exact plan0_indicator_test_aux2 n m hm

theorem probe_cast_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  simp

theorem plan0_sumOver_range_fairShare : ∀ (amount n : Nat), 0 < n →
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int)) =
      (amount : Int) := by
  intro amount n hn
  have hle : amount % n ≤ n := Nat.le_of_lt (Nat.mod_lt amount hn)
  have hcast : ∀ i, ((fairShare amount n i : Nat) : Int)
      = ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) := by
    intro i
    unfold fairShare
    by_cases h : i < amount % n <;> simp [h]
  have hcongr : sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int))
      = sumOver (List.range n) (fun i => ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0)) := by
    apply sumOver_congr
    intro a _; exact hcast a
  rw [hcongr, sumOver_add]
  rw [plan0_sumOver_range_const, plan0_sumOver_range_indicator n (amount % n) hle]
  have hdivmod : n * (amount / n) + amount % n = amount := Nat.div_add_mod amount n
  have hcast2 : ((n * (amount / n) + amount % n : Nat) : Int) = (amount : Int) := by
    rw [hdivmod]
  have hexpand : ((n * (amount / n) + amount % n : Nat) : Int)
      = (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) := by
    simp
  omega

theorem sumOver_map_test (l : List Nat) (f : Nat → Nat) (g : Nat → Int) :
    sumOver (l.map f) g = sumOver l (fun x => g (f x)) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem plan0_shift_aux3 (F : Nat → Int) (m k : Nat) :
    F k + sumOver (List.range m) (fun i => F (k + 1 + i)) =
    sumOver (List.range m) (fun i => F (k + i)) + F (k + m) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    have h1 : List.range (m + 1) = List.range m ++ [m] := by
      have h2 := List.range_succ (n := m)
      simpa using h2
    have e1 : sumOver (List.range (m+1)) (fun i => F (k + i))
        = sumOver (List.range m) (fun i => F (k + i)) + F (k + m) := by
      rw [h1, probe_append]
      simp
    have e2 : sumOver (List.range (m+1)) (fun i => F (k + 1 + i))
        = sumOver (List.range m) (fun i => F (k + 1 + i)) + F (k + 1 + m) := by
      rw [h1, probe_append]
      simp
    have ihm := ih k
    have hkm : k + 1 + m = k + (m + 1) := by omega
    calc F k + sumOver (List.range (m+1)) (fun i => F (k + 1 + i))
        = F k + (sumOver (List.range m) (fun i => F (k + 1 + i)) + F (k + 1 + m)) := by rw [e2]
      _ = (F k + sumOver (List.range m) (fun i => F (k + 1 + i))) + F (k + 1 + m) := by omega
      _ = (sumOver (List.range m) (fun i => F (k + i)) + F (k + m)) + F (k + 1 + m) := by rw [ihm]
      _ = (sumOver (List.range m) (fun i => F (k + i)) + F (k + m)) + F (k + (m + 1)) := by rw [hkm]
      _ = sumOver (List.range (m+1)) (fun i => F (k + i)) + F (k + (m+1)) := by rw [e1]

theorem plan1_indexOf?_cons_map : ∀ (x a : AccountId) (xs : List AccountId),
    a ≠ x → indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  intro x a xs h
  have h' : ¬ (x = a) := fun he => h he.symm
  simp [indexOf?, h']


theorem plan1_match_map_add : ∀ (o : Option Nat) (F : Nat → Int) (k : Nat),
    (match o.map (· + 1) with
      | some i => F (k + i)
      | none => 0) =
    (match o with
      | some i => F (k + 1 + i)
      | none => 0) := by
  intro o F k
  cases o with
  | none => rfl
  | some n =>
    simp only [Option.map_some]
    have h : k + (n + 1) = k + 1 + n := by omega
    rw [h]


theorem plan1_sumOver_tail_indexOf : ∀ (F : Nat → Int) (k : Nat) (x : AccountId)
    (xs : List AccountId), (x :: xs).Nodup →
    sumOver xs (fun a => match indexOf? (x :: xs) a with
      | some i => F (k + i)
      | none => 0) =
    sumOver xs (fun a => match indexOf? xs a with
      | some i => F (k + 1 + i)
      | none => 0) := by
  intro F k x xs hnodup
  apply sumOver_congr
  intro a ha
  have hnotin : x ∉ xs := (List.nodup_cons.mp hnodup).1
  have hne : a ≠ x := by
    intro heq
    subst heq
    exact hnotin ha
  have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) :=
    plan1_indexOf?_cons_map x a xs hne
  rw [hidx]
  exact plan1_match_map_add (indexOf? xs a) F k




theorem plan1_indexOf?_cons_map_proof : ∀ (x a : AccountId) (xs : List AccountId),
    a ≠ x → indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  intro x a xs h
  have h' : ¬ (x = a) := fun he => h he.symm
  simp [indexOf?, h']

theorem plan1_match_map_add_proof : ∀ (o : Option Nat) (F : Nat → Int) (k : Nat),
    (match o.map (· + 1) with
      | some i => F (k + i)
      | none => 0) =
    (match o with
      | some i => F (k + 1 + i)
      | none => 0) := by
  intro o F k
  cases o with
  | none => rfl
  | some n =>
    simp only [Option.map_some]
    have h : k + (n + 1) = k + 1 + n := by omega
    rw [h]

theorem plan1_sumOver_tail_indexOf_proof : ∀ (F : Nat → Int) (k : Nat) (x : AccountId)
    (xs : List AccountId), (x :: xs).Nodup →
    sumOver xs (fun a => match indexOf? (x :: xs) a with
      | some i => F (k + i)
      | none => 0) =
    sumOver xs (fun a => match indexOf? xs a with
      | some i => F (k + 1 + i)
      | none => 0) := by
  intro F k x xs hnodup
  apply sumOver_congr
  intro a ha
  have hnotin : x ∉ xs := (List.nodup_cons.mp hnodup).1
  have hne : a ≠ x := by
    intro heq
    subst heq
    exact hnotin ha
  have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) :=
    plan1_indexOf?_cons_map x a xs hne
  rw [hidx]
  exact plan1_match_map_add (indexOf? xs a) F k

theorem plan1_sumOver_range_succ_shift : ∀ (F : Nat → Int) (k m : Nat),
    F k + sumOver (List.range m) (fun i => F (k + 1 + i)) =
      sumOver (List.range (m + 1)) (fun i => F (k + i)) := by
  intro F k m
  have h := plan0_shift_aux3 F m k
  have h1 : List.range (m + 1) = List.range m ++ [m] := by
    have h2 := List.range_succ (n := m)
    simpa using h2
  have e1 : sumOver (List.range (m+1)) (fun i => F (k + i))
        = sumOver (List.range m) (fun i => F (k + i)) + F (k + m) := by
    rw [h1, probe_append]
    simp
  omega

theorem plan0_sumOver_indexOf_offset_aux2 : ∀ (amount n k : Nat) (l : List AccountId),
    l.Nodup →
    sumOver l (fun a => match indexOf? l a with
      | some i => ((fairShare amount n (k + i) : Nat) : Int)
      | none => 0) =
    sumOver (List.range l.length) (fun i => ((fairShare amount n (k + i) : Nat) : Int)) := by
  intro amount n k l
  induction l generalizing k with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hnodup
    have htail_nodup : xs.Nodup := (List.nodup_cons.mp hnodup).2
    have hx_head : (match indexOf? (x :: xs) x with
        | some i => ((fairShare amount n (k + i) : Nat) : Int)
        | none => (0 : Int)) = ((fairShare amount n k : Nat) : Int) := by
      simp [indexOf?]
    have lhs_eq : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with
        | some i => ((fairShare amount n (k + i) : Nat) : Int)
        | none => (0 : Int))
        = ((fairShare amount n k : Nat) : Int) + sumOver xs (fun a => match indexOf? (x :: xs) a with
          | some i => ((fairShare amount n (k + i) : Nat) : Int)
          | none => 0) := by
      simp only [sumOver_cons]
      rw [hx_head]
    have tail_shift : sumOver xs (fun a => match indexOf? (x :: xs) a with
          | some i => ((fairShare amount n (k + i) : Nat) : Int)
          | none => (0 : Int))
        = sumOver xs (fun a => match indexOf? xs a with
          | some i => ((fairShare amount n (k + 1 + i) : Nat) : Int)
          | none => 0) := by
      have h := plan1_sumOver_tail_indexOf_proof (fun j => ((fairShare amount n j : Nat) : Int)) k x xs hnodup
      exact h
    have ih_at : sumOver xs (fun a => match indexOf? xs a with
          | some i => ((fairShare amount n ((k + 1) + i) : Nat) : Int)
          | none => (0 : Int))
        = sumOver (List.range xs.length) (fun i => ((fairShare amount n ((k + 1) + i) : Nat) : Int)) :=
      ih (k + 1) htail_nodup
    have rhs_eq : sumOver (List.range (x :: xs).length) (fun i => ((fairShare amount n (k + i) : Nat) : Int))
        = ((fairShare amount n k : Nat) : Int) + sumOver (List.range xs.length) (fun i => ((fairShare amount n (k + 1 + i) : Nat) : Int)) := by
      have hlen : (x :: xs).length = xs.length + 1 := rfl
      rw [hlen]
      have hshift := plan1_sumOver_range_succ_shift (fun j => ((fairShare amount n j : Nat) : Int)) k xs.length
      exact hshift.symm
    calc sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with
          | some i => ((fairShare amount n (k + i) : Nat) : Int)
          | none => (0 : Int))
        = ((fairShare amount n k : Nat) : Int) + sumOver xs (fun a => match indexOf? (x :: xs) a with
            | some i => ((fairShare amount n (k + i) : Nat) : Int)
            | none => 0) := lhs_eq
      _ = ((fairShare amount n k : Nat) : Int) + sumOver xs (fun a => match indexOf? xs a with
            | some i => ((fairShare amount n (k + 1 + i) : Nat) : Int)
            | none => 0) := by rw [tail_shift]
      _ = ((fairShare amount n k : Nat) : Int) + sumOver (List.range xs.length) (fun i => ((fairShare amount n (k + 1 + i) : Nat) : Int)) := by rw [ih_at]
      _ = sumOver (List.range (x :: xs).length) (fun i => ((fairShare amount n (k + i) : Nat) : Int)) := by rw [rhs_eq]

theorem plan0_sumOver_indexOf_offset : ∀ (amount n k : Nat) (l : List AccountId),
    l.Nodup →
    sumOver l (fun a => match indexOf? l a with
      | some i => ((fairShare amount n (k + i) : Nat) : Int)
      | none => 0) =
    sumOver (List.range l.length) (fun i => ((fairShare amount n (k + i) : Nat) : Int)) :=
  fun amount n k l h => plan0_sumOver_indexOf_offset_aux2 amount n k l h

def eraseEq2 (l : List Nat) (y : Nat) : List Nat :=
  match l with
  | [] => []
  | x :: xs => if x = y then xs else x :: eraseEq2 xs y

theorem eraseEq2_mem (l : List Nat) (y x : Nat) (h : x ∈ eraseEq2 l y) : x ∈ l := by
  induction l with
  | nil => simp [eraseEq2] at h
  | cons z zs ih =>
    simp only [eraseEq2] at h
    by_cases hzy : z = y
    · simp [hzy] at h
      exact List.mem_cons_of_mem z h
    · simp [hzy] at h
      cases h with
      | inl heq => exact List.mem_cons.mpr (Or.inl heq)
      | inr hmem => exact List.mem_cons.mpr (Or.inr (ih hmem))

theorem sumOver_zero2 (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem eraseEq2_of_not_mem2 : ∀ (l : List Nat) (y : Nat), y ∉ l → eraseEq2 l y = l := by
  intro l y h
  induction l with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.mem_cons, not_or] at h
    simp [eraseEq2, Ne.symm h.1, ih h.2]

theorem probeNodupB (z : Nat) (l : List Nat) : (z :: l).Nodup ↔ z ∉ l ∧ l.Nodup := by
  exact List.nodup_cons

theorem eraseEq2_nodup_fix2 (l : List Nat) (y : Nat) (h : l.Nodup) : (eraseEq2 l y).Nodup := by
  induction l with
  | nil => simp [eraseEq2]
  | cons z zs ih =>
    have hcons : z ∉ zs ∧ zs.Nodup := List.nodup_cons.mp h
    by_cases hzy : z = y
    · simp only [eraseEq2, hzy, ite_true]
      exact hcons.2
    · have heq : eraseEq2 (z :: zs) y = z :: eraseEq2 zs y := by simp [eraseEq2, hzy]
      rw [heq]
      rw [List.nodup_cons]
      constructor
      · intro hmem
        have hmem2 : z ∈ zs := eraseEq2_mem zs y z hmem
        exact hcons.1 hmem2
      · exact ih hcons.2

theorem plan2_mem_erase_iff_nodup : ∀ (l : List AccountId) (a x : AccountId),
    l.Nodup → (x ∈ List.erase l a ↔ x ≠ a ∧ x ∈ l) := by
  intro l a x hnodup
  induction l with
  | nil => simp
  | cons y ys ih =>
    have hcons := (List.nodup_cons.mp hnodup)
    obtain ⟨hynin, hnodup_ys⟩ := hcons
    have ih' : (x ∈ List.erase ys a ↔ x ≠ a ∧ x ∈ ys) := ih hnodup_ys
    by_cases hya : y = a
    · have herase : List.erase (y :: ys) a = ys := by simp [hya]
      rw [herase]
      have haya : a = y := hya.symm
      constructor
      · intro hx
        refine ⟨?_, List.mem_cons.mpr (Or.inr hx)⟩
        intro heq
        rw [heq, haya] at hx
        exact hynin hx
      · intro ⟨hne, hm⟩
        simp only [List.mem_cons] at hm
        cases hm with
        | inl heq =>
          have : x = a := by rw [heq, haya]
          exact absurd this hne
        | inr hmem => exact hmem
    · have herase : List.erase (y :: ys) a = y :: List.erase ys a := by simp [hya]
      rw [herase]
      simp only [List.mem_cons]
      constructor
      · intro h
        cases h with
        | inl heq =>
          rw [heq]
          exact ⟨hya, Or.inl rfl⟩
        | inr hmem =>
          obtain ⟨hne, hmem2⟩ := (ih'.mp hmem)
          exact ⟨hne, Or.inr hmem2⟩
      · intro h
        obtain ⟨hne, hm⟩ := h
        cases hm with
        | inl heq =>
          exact Or.inl heq
        | inr hmem =>
          exact Or.inr (ih'.mpr ⟨hne, hmem⟩)




theorem plan2_sumOver_erase_mem : ∀ (l : List AccountId) (f : AccountId → Int) (a : AccountId),
    l.Nodup → a ∈ l → sumOver l f = f a + sumOver (List.erase l a) f := by
  intro l
  induction l with
  | nil => intro f a _ hm; simp at hm
  | cons y ys ih =>
    intro f a hn hm
    have hcons := List.nodup_cons.mp hn
    obtain ⟨hynin, hnodup_ys⟩ := hcons
    by_cases hya : y = a
    · subst hya
      have herase : List.erase (y :: ys) y = ys := by simp
      simp only [sumOver_cons, herase]
    · have hya' : y ≠ a := hya
      have herase : List.erase (y :: ys) a = y :: List.erase ys a := by simp [hya']
      rw [herase]
      simp only [sumOver_cons]
      have hmem_ys : a ∈ ys := by
        simp only [List.mem_cons] at hm
        cases hm with
        | inl h => exact absurd h (fun he => hya he.symm)
        | inr h => exact h
      have ih_eq := ih f a hnodup_ys hmem_ys
      omega




theorem plan2_mem_erase_iff_nodup_try : ∀ (l : List AccountId) (a x : AccountId),
    l.Nodup → (x ∈ List.erase l a ↔ x ≠ a ∧ x ∈ l) := by
  intro l a x hnodup
  induction l with
  | nil => simp
  | cons y ys ih =>
    have hcons := (List.nodup_cons.mp hnodup)
    obtain ⟨hynin, hnodup_ys⟩ := hcons
    have ih' : (x ∈ List.erase ys a ↔ x ≠ a ∧ x ∈ ys) := ih hnodup_ys
    by_cases hya : y = a
    · have herase : List.erase (y :: ys) a = ys := by simp [hya]
      rw [herase]
      have haya : a = y := hya.symm
      constructor
      · intro hx
        refine ⟨?_, List.mem_cons.mpr (Or.inr hx)⟩
        intro heq
        rw [heq, haya] at hx
        exact hynin hx
      · intro ⟨hne, hm⟩
        simp only [List.mem_cons] at hm
        cases hm with
        | inl heq =>
          have : x = a := by rw [heq, haya]
          exact absurd this hne
        | inr hmem => exact hmem
    · have herase : List.erase (y :: ys) a = y :: List.erase ys a := by simp [hya]
      rw [herase]
      simp only [List.mem_cons]
      constructor
      · intro h
        cases h with
        | inl heq =>
          rw [heq]
          exact ⟨hya, Or.inl rfl⟩
        | inr hmem =>
          obtain ⟨hne, hmem2⟩ := (ih'.mp hmem)
          exact ⟨hne, Or.inr hmem2⟩
      · intro h
        obtain ⟨hne, hm⟩ := h
        cases hm with
        | inl heq =>
          exact Or.inl heq
        | inr hmem =>
          exact Or.inr (ih'.mpr ⟨hne, hmem⟩)

theorem plan2_nodup_erase : ∀ (l : List AccountId) (a : AccountId),
    l.Nodup → (List.erase l a).Nodup := by
  intro l
  induction l with
  | nil => intro a h; simp
  | cons y ys ih =>
    intro a hnodup
    have hcons := List.nodup_cons.mp hnodup
    obtain ⟨hynin, hnodup_ys⟩ := hcons
    by_cases hya : y = a
    · have herase : List.erase (y :: ys) a = ys := by simp [hya]
      rw [herase]
      exact hnodup_ys
    · have herase : List.erase (y :: ys) a = y :: List.erase ys a := by simp [hya]
      rw [herase]
      rw [List.nodup_cons]
      constructor
      · intro hmem
        have hmem2 := (plan2_mem_erase_iff_nodup ys a y hnodup_ys).mp hmem
        exact hynin hmem2.2
      · exact ih a hnodup_ys

theorem myEraseMemProof : ∀ (l : List AccountId) (f : AccountId → Int) (a : AccountId),
    l.Nodup → a ∈ l → sumOver l f = f a + sumOver (List.erase l a) f := by
  intro l
  induction l with
  | nil => intro f a _ hm; simp at hm
  | cons y ys ih =>
    intro f a hn hm
    have hcons := List.nodup_cons.mp hn
    obtain ⟨hynin, hnodup_ys⟩ := hcons
    by_cases hya : y = a
    · subst hya
      have herase : List.erase (y :: ys) y = ys := by simp
      simp only [sumOver_cons, herase]
    · have hya' : y ≠ a := hya
      have herase : List.erase (y :: ys) a = y :: List.erase ys a := by simp [hya']
      rw [herase]
      simp only [sumOver_cons]
      have hmem_ys : a ∈ ys := by
        simp only [List.mem_cons] at hm
        cases hm with
        | inl h => exact absurd h (fun he => hya he.symm)
        | inr h => exact h
      have ih_eq := ih f a hnodup_ys hmem_ys
      omega

theorem test_absurd_branch (y : AccountId) (ys : List AccountId)
    (hynin : y ∉ ys) (x : AccountId) (hxin_ys : x ∈ ys) (hxy : x = y) :
    (5 : Int) = 0 := by
  subst hxy
  exact absurd hxin_ys hynin

theorem hvan_aux_ok (y : AccountId) (ys sub : List AccountId)
    (f : AccountId → Int)
    (hsubNodup : sub.Nodup)
    (hynin : y ∉ ys)
    (hvan : ∀ x ∈ y :: ys, x ∉ sub → f x = 0) :
    ∀ x ∈ ys, x ∉ List.erase sub y → f x = 0 := by
  intro x hxin_ys hxnotin
  have hxsub_dec : x ∈ sub ∨ x ∉ sub := by
    have h : Decidable (x ∈ sub) := inferInstance
    exact Decidable.em (x ∈ sub)
  cases hxsub_dec with
  | inl hxsub =>
    have heq_dec : x = y ∨ x ≠ y := by
      have h : Decidable (x = y) := inferInstance
      exact Decidable.em (x = y)
    cases heq_dec with
    | inl heq =>
      have hcontra : y ∈ ys := by rw [heq] at hxin_ys; exact hxin_ys
      exact False.elim (hynin hcontra)
    | inr hne =>
      have hmem : x ∈ List.erase sub y :=
        (plan2_mem_erase_iff_nodup sub y x hsubNodup).mpr ⟨hne, hxsub⟩
      exact False.elim (hxnotin hmem)
  | inr hxsub =>
    have hxin_cons : x ∈ y :: ys := List.mem_cons.mpr (Or.inr hxin_ys)
    exact hvan x hxin_cons hxsub

theorem plan2_sumOver_eq_of_subset_gen : ∀ (l sub : List AccountId) (f : AccountId → Int),
    l.Nodup → sub.Nodup →
    (∀ x ∈ sub, x ∈ l) →
    (∀ x ∈ l, x ∉ sub → f x = 0) →
    sumOver l f = sumOver sub f := by
  intro l
  induction l with
  | nil =>
    intro sub f _ hsubNodup hsubL hvan
    have hsubNil : sub = [] := by
      cases sub with
      | nil => rfl
      | cons y ys =>
        have hm : y ∈ y :: ys := by simp
        have hl := hsubL y hm
        simp at hl
    subst hsubNil
    simp
  | cons y ys ih =>
    intro sub f hnodup hsubNodup hsubL hvan
    have hnodup_ys : ys.Nodup := (List.nodup_cons.mp hnodup).2
    have hynin : y ∉ ys := (List.nodup_cons.mp hnodup).1
    have hcons_sum : sumOver (y :: ys) f = f y + sumOver ys f := rfl
    have hmem_dec : y ∈ sub ∨ y ∉ sub := by
      have h : Decidable (y ∈ sub) := inferInstance
      exact Decidable.em (y ∈ sub)
    cases hmem_dec with
    | inl hmem =>
      have herase_nodup : (List.erase sub y).Nodup := plan2_nodup_erase sub y hsubNodup
      have hsub_eq : sumOver sub f = f y + sumOver (List.erase sub y) f :=
        plan2_sumOver_erase_mem sub f y hsubNodup hmem
      have hsubL' : ∀ x ∈ List.erase sub y, x ∈ ys := by
        intro x hx
        have hmem2 := (plan2_mem_erase_iff_nodup sub y x hsubNodup).mp hx
        obtain ⟨hne, hxin_sub⟩ := hmem2
        have hxin_cons := hsubL x hxin_sub
        simp only [List.mem_cons] at hxin_cons
        cases hxin_cons with
        | inl heq =>
          have habs : x = y := heq
          rw [habs] at hne
          exact False.elim (hne rfl)
        | inr h => exact h
      have hvan' : ∀ x ∈ ys, x ∉ List.erase sub y → f x = 0 :=
        hvan_aux_ok y ys sub f hsubNodup hynin hvan
      have ih_eq := ih (List.erase sub y) f hnodup_ys herase_nodup hsubL' hvan'
      rw [hcons_sum, hsub_eq, ih_eq]
    | inr hmem =>
      have hfy : f y = 0 := by
        apply hvan y
        · simp
        · exact hmem
      have hsubL' : ∀ x ∈ sub, x ∈ ys := by
        intro x hx
        have hxin_cons := hsubL x hx
        simp only [List.mem_cons] at hxin_cons
        cases hxin_cons with
        | inl heq =>
          rw [heq] at hx
          exact False.elim (hmem hx)
        | inr h => exact h
      have hvan' : ∀ x ∈ ys, x ∉ sub → f x = 0 := by
        intro x hxin_ys hxnotin
        have hxin_cons : x ∈ y :: ys := List.mem_cons.mpr (Or.inr hxin_ys)
        exact hvan x hxin_cons hxnotin
      have ih_eq := ih sub f hnodup_ys hsubNodup hsubL' hvan'
      rw [hcons_sum, hfy, Int.zero_add]
      exact ih_eq

theorem plan0_sumOver_eq_of_subset : ∀ (l sub : List AccountId) (f : AccountId → Int),
    l.Nodup → sub.Nodup →
    (∀ x ∈ sub, x ∈ l) →
    (∀ x, x ∉ sub → f x = 0) →
    sumOver l f = sumOver sub f := by
  intro l sub f hl hsub hsubL hvan
  exact plan2_sumOver_eq_of_subset_gen l sub f hl hsub hsubL (fun x _ hx => hvan x hx)

theorem plan0_sumOver_expectedBalance : ∀ (s : State) (r : Request),
    s.accounts.Nodup → r.source ∈ s.accounts →
    sumOver s.accounts (fun a => expectedBalance s r a) =
      total s - (r.amount : Int) +
        sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by
  intro s r hnodup hmem
  have hExp : ∀ a, expectedBalance s r a =
      (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + ((shareOf r a : Nat) : Int) := by
    intro a
    rfl
  have hcongr1 : sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + ((shareOf r a : Nat) : Int)) := by
    apply sumOver_congr
    intro a _
    exact hExp a
  rw [hcongr1, sumOver_add]
  have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) := by
    exact sumOver_sub s.accounts _ _
  rw [hsub]
  have hind : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodup r.source ((r.amount : Int))
    simpa [hmem] using h
  rw [hind]
  rfl

theorem shareVanish (r : Request) (x : AccountId) (h : x ∉ r.recipients) :
    ((shareOf r x : Nat) : Int) = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none h]
  rfl

theorem shareSum_eq_amount (s : State) (r : Request)
    (hAccNodup : s.accounts.Nodup) (hRecNodup : r.recipients.Nodup)
    (hRecSub : ∀ x ∈ r.recipients, x ∈ s.accounts)
    (hn : 0 < r.recipients.length) :
    sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) = (r.amount : Int) := by
  have hvan : ∀ x, x ∉ r.recipients → (fun a => ((shareOf r a : Nat) : Int)) x = 0 := by
    intro x hx
    exact shareVanish r x hx
  have hsub := plan0_sumOver_eq_of_subset s.accounts r.recipients
    (fun a => ((shareOf r a : Nat) : Int)) hAccNodup hRecNodup hRecSub hvan
  rw [hsub]
  have hidx : sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int))
      = sumOver r.recipients (fun a => match indexOf? r.recipients a with
        | some i => ((fairShare r.amount r.recipients.length (0 + i) : Nat) : Int)
        | none => 0) := by
    apply sumOver_congr
    intro a _
    unfold shareOf
    cases h : indexOf? r.recipients a with
    | none => rfl
    | some i => simp [Nat.zero_add]
  rw [hidx]
  have hoff := plan0_sumOver_indexOf_offset r.amount r.recipients.length 0 r.recipients hRecNodup
  rw [hoff] at hidx
  -- hidx now? Actually need to rewrite using hoff
  have heq : sumOver r.recipients (fun a => match indexOf? r.recipients a with
        | some i => ((fairShare r.amount r.recipients.length (0 + i) : Nat) : Int)
        | none => 0)
      = sumOver (List.range r.recipients.length) (fun i => ((fairShare r.amount r.recipients.length (0 + i) : Nat) : Int)) := hoff
  rw [heq]
  have hzero : ∀ i, (0 + i) = i := fun i => Nat.zero_add i
  have hcongr : sumOver (List.range r.recipients.length) (fun i => ((fairShare r.amount r.recipients.length (0 + i) : Nat) : Int))
      = sumOver (List.range r.recipients.length) (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int)) := by
    apply sumOver_congr
    intro a _
    rw [Nat.zero_add]
  rw [hcongr]
  exact plan0_sumOver_range_fairShare r.amount r.recipients.length hn

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
  simp only [step] at h
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · simp [hv] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step; simp [hv]
    have h2 : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
      rw [hstep]
    rw [h2]
    exact ⟨rfl, rfl, fun a => rfl⟩
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hv]
    rw [hstep] at h
    simp at h

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv : ValidPayout s r := by
    by_cases hc : ValidPayout s r
    · exact hc
    · have hre : (step s r).1 = .rejected := by simp only [step, hc, ite_false]
      rw [hre] at hok
      exact absurd hok (by decide)
  have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
    simp only [step, hv, ite_true]
  have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
    rw [hstep]
  have hNotValid : ¬ ValidPayout ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r := by
    intro hV
    obtain ⟨_, _, _, _, _, _, _, _, _, hnot⟩ := hV
    exact hnot (by simp)
  refine ⟨?_, ?_⟩
  · intro x
    rw [h2]
    simp
  · rw [h2]
    simp only [step, hNotValid, ite_false]

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      simp [step, hv]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have hbal : (step s r).2.balance a = expectedBalance s r a := by rw [hstep]
    rw [hacc] at ha
    rw [hbal]
    obtain ⟨hnodup, hpos, hne, hnodupR, hnotmem, hsrcMem, hrecMem, hauth, hle, htx⟩ := hv
    unfold expectedBalance
    by_cases hsrc : a = r.source
    · subst hsrc
      have hshare : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hnotmem]
      rw [if_pos rfl, hshare]
      simp
      omega
    · rw [if_neg hsrc]
      have h1 : 0 ≤ s.balance a := hnn a ha
      have h2 : (0 : Int) ≤ ((shareOf r a : Nat) : Int) := by exact_mod_cast Nat.zero_le _
      omega
  · have hstep : step s r = (.rejected, s) := by simp [step, hv]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have hbal : (step s r).2.balance a = s.balance a := by rw [hstep]
    rw [hacc] at ha
    rw [hbal]
    exact hnn a ha

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      simp [step, hv]
    have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by rw [hstep]
    rw [hbal]
    obtain ⟨hnodup, hpos, hne, hnodupR, hnotmem, hsrcMem, hrecMem, hauth, hle, htx⟩ := hv
    have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hnei : r.recipients[i] ≠ r.source := fun h => hnotmem (h ▸ hmem)
    have hshare : shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
      unfold shareOf
      rw [indexOf?_getElem hnodupR i hi]
    unfold expectedBalance
    rw [if_neg hnei, hshare]
    omega
  · have hre : (step s r).1 = .rejected := by simp [step, hv]
    rw [hre] at hok
    exact absurd hok (by decide)

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      simp [step, hv]
    have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      rw [hstep]
    obtain ⟨hnodup, hpos, hne, hnodupR, hnotmem, hsrcMem, hrecMem, hauth, hle, htx⟩ := hv
    have hn : 0 < r.recipients.length := by
      cases hlen : r.recipients.length with
      | zero =>
        have : r.recipients = [] := List.length_eq_zero_iff.mp hlen
        exact absurd this hne
      | succ _ => exact Nat.zero_lt_succ _
    have hshares := shareSum_eq_amount s r hnodup hnodupR hrecMem hn
    have hexp := plan0_sumOver_expectedBalance s r hnodup hsrcMem
    -- unfold total
    have htotal2 : total (step s r).2 = sumOver s.accounts (fun a => expectedBalance s r a) := by
      rw [h2]
      rfl
    have htotal : total s = sumOver s.accounts s.balance := rfl
    rw [htotal2, htotal, hexp, hshares]
    omega
  · have hre : (step s r).1 = .rejected := by simp [step, hv]
    rw [hre] at hok
    exact absurd hok (by decide)

end Payout
