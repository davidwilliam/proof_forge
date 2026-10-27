import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := expectedBalance s r,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_idempotency_aux : Idempotent step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hstep2 : step s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
      simp [step, hv]
    rw [hstep2]
    simp only
    apply And.intro
    · intro x
      simp
    · have hnotvalid : ¬ ValidPayout ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) r := by
        intro hcon
        obtain ⟨_, _, _, _, _, _, _, _, _, hmem⟩ := hcon
        simp at hmem
      simp [step, hnotvalid]
  · have hstep : (step s r).1 = .rejected := by simp [step, hv]
    rw [hstep] at hok
    contradiction

theorem fair_of_ok {s : State} {r : Request} (hok : (step s r).1 = .ok) : ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · have h : (step s r).1 = .rejected := by simp [step, hv]
    rw [h] at hok
    contradiction

theorem t1 : List.range 0 = ([] : List Nat) := rfl

theorem t2 : List.range 1 = [0] := rfl

theorem t3 : List.range 2 = [0, 1] := rfl

theorem mytestA : True := trivial
#check List.range
#check List.nodup_cons
#check Nat.div_add_mod

theorem mycheckA : True := trivial
#check @List.range_zero
#check @List.length_range
#check @List.getElem_range
#check @Nat.div_add_mod
#check @List.mem_range

theorem sumOver_append' {α : Type} (l1 l2 : List α) (f : α → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem sumOver_singleton' (a : Nat) (f : Nat → Int) :
    sumOver [a] f = f a := by simp

theorem mycheckB : True := trivial
#check @List.append_assoc
#check @List.length_append

theorem probe_take_mem (l : List Nat) (n : Nat) (a : Nat) (h : a ∈ l.take n) : a ∈ l := by
  exact List.mem_of_mem_take h
#check @List.mem_of_mem_take

theorem plan0_sum_fairShare_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by
  have hcast : ∀ i ∈ List.range n,
      ((fairShare amount n i : Nat) : Int) =
        ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) := by
    intro i _
    unfold fairShare
    by_cases h : i < amount % n
    · simp [h]
    · simp [h]
  rw [sumOver_congr _ _ _ hcast, sumOver_add]
  have hgen_const : ∀ (m : Nat) (c : Int),
      sumOver (List.range m) (fun _ => c) = (m : Int) * c := by
    intro m c
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : List.range (m + 1) = List.range m ++ [m] := by simp [List.range_succ]
      rw [h1, sumOver_append']
      simp only [sumOver_cons, sumOver_nil]
      rw [ih]
      have hcast2 : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by simp
      rw [hcast2, Int.add_mul, Int.one_mul]
      omega
  have hgen_ite : ∀ (m k : Nat),
      sumOver (List.range m) (fun i => if i < k then (1 : Int) else 0) =
        ((Nat.min m k : Nat) : Int) := by
    intro m k
    induction m generalizing k with
    | zero => simp
    | succ m ih =>
      have hrange : List.range (m + 1) = List.range m ++ [m] := by simp [List.range_succ]
      rw [hrange, sumOver_append']
      simp only [sumOver_cons, sumOver_nil]
      rw [ih k]
      by_cases h : m < k
      · have hle : m ≤ k := by omega
        have hle2 : m + 1 ≤ k := by omega
        have e1 : Nat.min m k = m := Nat.min_eq_left hle
        have e2 : Nat.min (m + 1) k = m + 1 := Nat.min_eq_left hle2
        rw [e1, e2, if_pos h]
        simp
      · have hle : k ≤ m := by omega
        have hle2 : k ≤ m + 1 := by omega
        have e1 : Nat.min m k = k := Nat.min_eq_right hle
        have e2 : Nat.min (m + 1) k = k := Nat.min_eq_right hle2
        rw [e1, e2, if_neg h]
        simp
  rw [hgen_const, hgen_ite]
  have hmod : amount % n < n := Nat.mod_lt _ hn
  have hmin : Nat.min n (amount % n) = amount % n := Nat.min_eq_right (Nat.le_of_lt hmod)
  rw [hmin]
  have h := Nat.div_add_mod amount n
  have hc : ((n * (amount / n) + amount % n : Nat) : Int) = (amount : Int) := by
    rw [h]
  simp at hc
  omega




theorem plan0_sumOver_shareOf_recipients (r : Request) (hnd : r.recipients.Nodup)
    (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have hshift : ∀ (n : Nat) (g : Nat → Int),
      sumOver (List.range (n + 1)) g = g 0 + sumOver (List.range n) (fun i => g (i + 1)) := by
    intro n g
    induction n generalizing g with
    | zero => simp
    | succ n ih =>
      have hr1 : List.range (n + 2) = List.range (n + 1) ++ [n + 1] := by simp [List.range_succ]
      have hL : sumOver (List.range (n + 2)) g = sumOver (List.range (n + 1)) g + g (n + 1) := by
        rw [hr1, sumOver_append']
        simp
      have hR : sumOver (List.range (n + 1)) (fun i => g (i + 1)) =
          sumOver (List.range n) (fun i => g (i + 1)) + g (n + 1) := by
        have hr2 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
        rw [hr2, sumOver_append']
        simp
      rw [hL, hR, ih g]
      omega
  have hmap : ∀ (l : List AccountId) (hl : l.Nodup) (f : Nat → Int),
      sumOver l (fun a => match indexOf? l a with | some i => f i | none => 0) =
        sumOver (List.range l.length) f := by
    intro l
    induction l with
    | nil => intro _ f; simp
    | cons x xs ih =>
      intro hl f
      rw [List.nodup_cons] at hl
      obtain ⟨hxnotin, hnodup⟩ := hl
      have hhead : (match indexOf? (x :: xs) x with | some i => f i | none => 0) = f 0 := by
        simp [indexOf?]
      have htail : ∀ a ∈ xs,
          (match indexOf? (x :: xs) a with | some i => f i | none => 0) =
          (match indexOf? xs a with | some i => f (i + 1) | none => 0) := by
        intro a ha
        have hne2 : x ≠ a := fun h => hxnotin (h ▸ ha)
        have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
          simp [indexOf?, hne2]
        rw [hidx]
        cases h : indexOf? xs a with
        | none => simp
        | some i => simp
      have hcons : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0)
          = (match indexOf? (x :: xs) x with | some i => f i | none => 0) +
            sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0) := rfl
      rw [hcons, hhead]
      have hcongr : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0)
          = sumOver xs (fun a => match indexOf? xs a with | some i => f (i + 1) | none => 0) :=
        sumOver_congr _ _ _ htail
      rw [hcongr, ih hnodup (fun i => f (i + 1))]
      have hlen : (x :: xs).length = xs.length + 1 := rfl
      rw [hlen]
      exact (hshift xs.length f).symm
  have hcongr : ∀ a ∈ r.recipients,
      ((shareOf r a : Nat) : Int) =
        (match indexOf? r.recipients a with | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int) | none => (0 : Int)) := by
    intro a _
    unfold shareOf
    cases h : indexOf? r.recipients a with
    | none => simp
    | some i => simp
  rw [sumOver_congr _ _ _ hcongr]
  rw [hmap r.recipients hnd]
  have hn : 0 < r.recipients.length := by
    cases h : r.recipients with
    | nil => contradiction
    | cons _ _ => simp
  exact plan0_sum_fairShare_range r.amount r.recipients.length hn








theorem dummyCheck2 : True := trivial

theorem dummyCheck3 : True := trivial

theorem probe_tac1 (n : Nat) : n = n := by omega

theorem probe_tac2 (a b : Int) : a + b = b + a := by omega

theorem probe_tac3 (a : Int) : a * 1 = a := by simp

theorem probe_cast2 (n : Nat) : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp

theorem probe_cast3 (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp

theorem dummyMul : True := trivial

theorem sigCheck (m n : Nat) : n * (m / n) + m % n = m := Nat.div_add_mod m n











theorem plan1_sumOver_range_fairShare_decomp (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int)) =
      (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) := by
  have hcast : ∀ i ∈ List.range n,
      ((fairShare amount n i : Nat) : Int) =
        ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) := by
    intro i _
    unfold fairShare
    by_cases h : i < amount % n
    · simp [h]
    · simp [h]
  rw [sumOver_congr _ _ _ hcast, sumOver_add]
  have hgen_const : ∀ (m : Nat) (c : Int),
      sumOver (List.range m) (fun _ => c) = (m : Int) * c := by
    intro m c
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : List.range (m + 1) = List.range m ++ [m] := by simp [List.range_succ]
      rw [h1, sumOver_append']
      simp only [sumOver_cons, sumOver_nil]
      rw [ih]
      have hcast2 : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by simp
      rw [hcast2, Int.add_mul, Int.one_mul]
      omega
  have hgen_ite : ∀ (m k : Nat),
      sumOver (List.range m) (fun i => if i < k then (1 : Int) else 0) =
        ((Nat.min m k : Nat) : Int) := by
    intro m k
    induction m generalizing k with
    | zero => simp
    | succ m ih =>
      have hrange : List.range (m + 1) = List.range m ++ [m] := by simp [List.range_succ]
      rw [hrange, sumOver_append']
      simp only [sumOver_cons, sumOver_nil]
      rw [ih k]
      by_cases h : m < k
      · have hle : m ≤ k := by omega
        have hle2 : m + 1 ≤ k := by omega
        have e1 : Nat.min m k = m := Nat.min_eq_left hle
        have e2 : Nat.min (m + 1) k = m + 1 := Nat.min_eq_left hle2
        rw [e1, e2, if_pos h]
        simp
      · have hle : k ≤ m := by omega
        have hle2 : k ≤ m + 1 := by omega
        have e1 : Nat.min m k = k := Nat.min_eq_right hle
        have e2 : Nat.min (m + 1) k = k := Nat.min_eq_right hle2
        rw [e1, e2, if_neg h]
        simp
  rw [hgen_const, hgen_ite]
  have hmod : amount % n < n := Nat.mod_lt _ hn
  have hmin : Nat.min n (amount % n) = amount % n := Nat.min_eq_right (Nat.le_of_lt hmod)
  rw [hmin]


theorem probe_distrib (n : Nat) (c : Int) : ((n : Int) + 1) * c = (n : Int) * c + c := by
  simp [Int.add_mul, Int.one_mul]

theorem probe_cast_succ (n : Nat) : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp

theorem probe_range_succ (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]

theorem tmp_const2 (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    rw [h1, sumOver_append']
    simp only [sumOver_cons, sumOver_nil]
    rw [ih]
    have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
    rw [hcast, Int.add_mul, Int.one_mul]
    omega

theorem plan1_sumOver_range_const (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    rw [h1, sumOver_append']
    simp only [sumOver_cons, sumOver_nil]
    rw [ih]
    have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
    rw [hcast, Int.add_mul, Int.one_mul]
    omega

theorem plan1_sumOver_range_ite_min (n k : Nat) :
    sumOver (List.range n) (fun i => if i < k then (1 : Int) else 0) =
      ((Nat.min n k : Nat) : Int) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    have hrange : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    rw [hrange, sumOver_append']
    simp only [sumOver_cons, sumOver_nil]
    rw [ih]
    by_cases h : n < k
    · have hle : n ≤ k := by omega
      have hle2 : n + 1 ≤ k := by omega
      have e1 : Nat.min n k = n := Nat.min_eq_left hle
      have e2 : Nat.min (n + 1) k = n + 1 := Nat.min_eq_left hle2
      rw [e1, e2, if_pos h]
      simp
    · have hle : k ≤ n := by omega
      have hle2 : k ≤ n + 1 := by omega
      have e1 : Nat.min n k = k := Nat.min_eq_right hle
      have e2 : Nat.min (n + 1) k = k := Nat.min_eq_right hle2
      rw [e1, e2, if_neg h]
      simp

theorem plan1_fairShare_cast (amount n i : Nat) :
    ((fairShare amount n i : Nat) : Int) =
      ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) := by
  unfold fairShare
  by_cases h : i < amount % n
  · simp [h]
  · simp [h]

theorem plan1_mul_div_add_mod_nat (amount n : Nat) :
    n * (amount / n) + amount % n = amount := Nat.div_add_mod amount n

theorem probeCastA (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp

theorem probeCastB (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by simp

theorem plan1_mul_div_add_mod_int (amount n : Nat) :
    (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) =
      (amount : Int) := by
  have h := Nat.div_add_mod amount n
  have hc : ((n * (amount / n) + amount % n : Nat) : Int) = (amount : Int) := by
    rw [h]
  simp at hc
  omega

theorem plan1_sumOver_range_fairShare_decomp_aux (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int)) =
      (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) := by
  have h1 : ∀ i ∈ List.range n,
      ((fairShare amount n i : Nat) : Int) =
        ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) := by
    intro i _
    exact plan1_fairShare_cast amount n i
  rw [sumOver_congr _ _ _ h1, sumOver_add]
  rw [plan1_sumOver_range_const, plan1_sumOver_range_ite_min]
  have hmod : amount % n < n := Nat.mod_lt _ hn
  have hmin : Nat.min n (amount % n) = amount % n := Nat.min_eq_right (Nat.le_of_lt hmod)
  rw [hmin]

theorem plan1_decomp_selfcontained_test2 (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int)) =
      (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) := by
  have hcast : ∀ i ∈ List.range n,
      ((fairShare amount n i : Nat) : Int) =
        ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) := by
    intro i _
    unfold fairShare
    by_cases h : i < amount % n
    · simp [h]
    · simp [h]
  rw [sumOver_congr _ _ _ hcast, sumOver_add]
  have hgen_const : ∀ (m : Nat) (c : Int),
      sumOver (List.range m) (fun _ => c) = (m : Int) * c := by
    intro m c
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : List.range (m + 1) = List.range m ++ [m] := by simp [List.range_succ]
      rw [h1, sumOver_append']
      simp only [sumOver_cons, sumOver_nil]
      rw [ih]
      have hcast2 : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by simp
      rw [hcast2, Int.add_mul, Int.one_mul]
      omega
  have hgen_ite : ∀ (m k : Nat),
      sumOver (List.range m) (fun i => if i < k then (1 : Int) else 0) =
        ((Nat.min m k : Nat) : Int) := by
    intro m k
    induction m generalizing k with
    | zero => simp
    | succ m ih =>
      have hrange : List.range (m + 1) = List.range m ++ [m] := by simp [List.range_succ]
      rw [hrange, sumOver_append']
      simp only [sumOver_cons, sumOver_nil]
      rw [ih k]
      by_cases h : m < k
      · have hle : m ≤ k := by omega
        have hle2 : m + 1 ≤ k := by omega
        have e1 : Nat.min m k = m := Nat.min_eq_left hle
        have e2 : Nat.min (m + 1) k = m + 1 := Nat.min_eq_left hle2
        rw [e1, e2, if_pos h]
        simp
      · have hle : k ≤ m := by omega
        have hle2 : k ≤ m + 1 := by omega
        have e1 : Nat.min m k = k := Nat.min_eq_right hle
        have e2 : Nat.min (m + 1) k = k := Nat.min_eq_right hle2
        rw [e1, e2, if_neg h]
        simp
  rw [hgen_const, hgen_ite]
  have hmod : amount % n < n := Nat.mod_lt _ hn
  have hmin : Nat.min n (amount % n) = amount % n := Nat.min_eq_right (Nat.le_of_lt hmod)
  rw [hmin]

theorem plan0_sum_fairShare_range_check (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by
  rw [plan1_sumOver_range_fairShare_decomp_aux amount n hn]
  exact plan1_mul_div_add_mod_int amount n

theorem aux_range_shift2 (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f = f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have hr1 : List.range (n + 2) = List.range (n + 1) ++ [n + 1] := by simp [List.range_succ]
    have hL : sumOver (List.range (n + 2)) f = sumOver (List.range (n + 1)) f + f (n + 1) := by
      rw [hr1, sumOver_append']
      simp
    have hR : sumOver (List.range (n + 1)) (fun i => f (i + 1)) =
        sumOver (List.range n) (fun i => f (i + 1)) + f (n + 1) := by
      have hr2 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
      rw [hr2, sumOver_append']
      simp
    rw [hL, hR, ih f]
    omega

theorem plan0_sumOver_indexOf_range_aux2 {l : List AccountId} (hl : l.Nodup) (f : Nat → Int) :
    sumOver l (fun a => match indexOf? l a with | some i => f i | none => 0) =
      sumOver (List.range l.length) f := by
  induction l generalizing f with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hxnotin, hnodup⟩ := hl
    have hhead : (match indexOf? (x :: xs) x with | some i => f i | none => 0) = f 0 := by
      simp [indexOf?]
    have htail : ∀ a ∈ xs,
        (match indexOf? (x :: xs) a with | some i => f i | none => 0) =
        (match indexOf? xs a with | some i => f (i + 1) | none => 0) := by
      intro a ha
      have hne : x ≠ a := fun h => hxnotin (h ▸ ha)
      have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
        simp [indexOf?, hne]
      rw [hidx]
      cases h : indexOf? xs a with
      | none => simp
      | some i => simp
    have hcons : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0)
        = (match indexOf? (x :: xs) x with | some i => f i | none => 0) +
          sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0) := rfl
    rw [hcons, hhead]
    have hcongr : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0)
        = sumOver xs (fun a => match indexOf? xs a with | some i => f (i + 1) | none => 0) :=
      sumOver_congr _ _ _ htail
    rw [hcongr, ih hnodup (fun i => f (i + 1))]
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    rw [hlen]
    exact (aux_range_shift2 xs.length f).symm

theorem plan0_sumOver_indexOf_range {l : List AccountId} (hl : l.Nodup) (f : Nat → Int) :
    sumOver l (fun a => match indexOf? l a with | some i => f i | none => 0) =
      sumOver (List.range l.length) f := by
  have hshift : ∀ (n : Nat) (g : Nat → Int),
      sumOver (List.range (n + 1)) g = g 0 + sumOver (List.range n) (fun i => g (i + 1)) := by
    intro n g
    induction n generalizing g with
    | zero => simp
    | succ n ih =>
      have hr1 : List.range (n + 2) = List.range (n + 1) ++ [n + 1] := by simp [List.range_succ]
      have hL : sumOver (List.range (n + 2)) g = sumOver (List.range (n + 1)) g + g (n + 1) := by
        rw [hr1, sumOver_append']
        simp
      have hR : sumOver (List.range (n + 1)) (fun i => g (i + 1)) =
          sumOver (List.range n) (fun i => g (i + 1)) + g (n + 1) := by
        have hr2 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
        rw [hr2, sumOver_append']
        simp
      rw [hL, hR, ih g]
      omega
  induction l generalizing f with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hxnotin, hnodup⟩ := hl
    have hhead : (match indexOf? (x :: xs) x with | some i => f i | none => 0) = f 0 := by
      simp [indexOf?]
    have htail : ∀ a ∈ xs,
        (match indexOf? (x :: xs) a with | some i => f i | none => 0) =
        (match indexOf? xs a with | some i => f (i + 1) | none => 0) := by
      intro a ha
      have hne : x ≠ a := fun h => hxnotin (h ▸ ha)
      have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
        simp [indexOf?, hne]
      rw [hidx]
      cases h : indexOf? xs a with
      | none => simp
      | some i => simp
    have hcons : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0)
        = (match indexOf? (x :: xs) x with | some i => f i | none => 0) +
          sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0) := rfl
    rw [hcons, hhead]
    have hcongr : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0)
        = sumOver xs (fun a => match indexOf? xs a with | some i => f (i + 1) | none => 0) :=
      sumOver_congr _ _ _ htail
    rw [hcongr, ih hnodup (fun i => f (i + 1))]
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    rw [hlen]
    exact (hshift xs.length f).symm

theorem selfContainedCheck (r : Request) (hnd : r.recipients.Nodup)
    (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have hshift : ∀ (n : Nat) (g : Nat → Int),
      sumOver (List.range (n + 1)) g = g 0 + sumOver (List.range n) (fun i => g (i + 1)) := by
    intro n g
    induction n generalizing g with
    | zero => simp
    | succ n ih =>
      have hr1 : List.range (n + 2) = List.range (n + 1) ++ [n + 1] := by simp [List.range_succ]
      have hL : sumOver (List.range (n + 2)) g = sumOver (List.range (n + 1)) g + g (n + 1) := by
        rw [hr1, sumOver_append']
        simp
      have hR : sumOver (List.range (n + 1)) (fun i => g (i + 1)) =
          sumOver (List.range n) (fun i => g (i + 1)) + g (n + 1) := by
        have hr2 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
        rw [hr2, sumOver_append']
        simp
      rw [hL, hR, ih g]
      omega
  have hmap : ∀ (l : List AccountId) (hl : l.Nodup) (f : Nat → Int),
      sumOver l (fun a => match indexOf? l a with | some i => f i | none => 0) =
        sumOver (List.range l.length) f := by
    intro l
    induction l with
    | nil => intro _ f; simp
    | cons x xs ih =>
      intro hl f
      rw [List.nodup_cons] at hl
      obtain ⟨hxnotin, hnodup⟩ := hl
      have hhead : (match indexOf? (x :: xs) x with | some i => f i | none => 0) = f 0 := by
        simp [indexOf?]
      have htail : ∀ a ∈ xs,
          (match indexOf? (x :: xs) a with | some i => f i | none => 0) =
          (match indexOf? xs a with | some i => f (i + 1) | none => 0) := by
        intro a ha
        have hne2 : x ≠ a := fun h => hxnotin (h ▸ ha)
        have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
          simp [indexOf?, hne2]
        rw [hidx]
        cases h : indexOf? xs a with
        | none => simp
        | some i => simp
      have hcons : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0)
          = (match indexOf? (x :: xs) x with | some i => f i | none => 0) +
            sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0) := rfl
      rw [hcons, hhead]
      have hcongr : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0)
          = sumOver xs (fun a => match indexOf? xs a with | some i => f (i + 1) | none => 0) :=
        sumOver_congr _ _ _ htail
      rw [hcongr, ih hnodup (fun i => f (i + 1))]
      have hlen : (x :: xs).length = xs.length + 1 := rfl
      rw [hlen]
      exact (hshift xs.length f).symm
  have hcongr : ∀ a ∈ r.recipients,
      ((shareOf r a : Nat) : Int) =
        (match indexOf? r.recipients a with | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int) | none => (0 : Int)) := by
    intro a _
    unfold shareOf
    cases h : indexOf? r.recipients a with
    | none => simp
    | some i => simp
  rw [sumOver_congr _ _ _ hcongr]
  rw [hmap r.recipients hnd]
  have hn : 0 < r.recipients.length := by
    cases h : r.recipients with
    | nil => contradiction
    | cons _ _ => simp
  exact plan0_sum_fairShare_range r.amount r.recipients.length hn

theorem helperZero (l : List AccountId) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [sumOver_cons, ih, Int.add_zero]

theorem plan0_sumOver_super_of_zero_outside (big small : List AccountId) (f : AccountId → Int)
    (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big) (hzero : ∀ a, a ∉ small → f a = 0) :
    sumOver big f = sumOver small f := by
  induction small generalizing big f with
  | nil =>
    have hzero2 : ∀ a ∈ big, f a = (0 : Int) := by
      intro a _
      exact hzero a (by simp)
    rw [sumOver_congr big f _ hzero2]
    exact helperZero big
  | cons y ys ih =>
    rw [List.nodup_cons] at hsmall
    obtain ⟨hynotin, hysnodup⟩ := hsmall
    have hymem : y ∈ big := hsub y (by simp)
    have hsubys : ∀ x ∈ ys, x ∈ big := fun x hx => hsub x (by simp [hx])
    let g : AccountId → Int := fun a => if a = y then 0 else f a
    have hzero_g : ∀ a, a ∉ ys → g a = 0 := by
      intro a ha
      show (if a = y then (0 : Int) else f a) = 0
      by_cases heq : a = y
      · simp [heq]
      · simp [heq, hzero a (by simp [heq, ha])]
    have hcongr_ys : ∀ a ∈ ys, g a = f a := by
      intro a ha
      show (if a = y then (0 : Int) else f a) = f a
      have hne : ¬ (a = y) := fun h => hynotin (h ▸ ha)
      simp [hne]
    have hys_g : sumOver ys g = sumOver ys f := sumOver_congr ys g f hcongr_ys
    have hsplit : ∀ a ∈ big, f a = (if a = y then f y else 0) + g a := by
      intro a _
      show f a = (if a = y then f y else (0 : Int)) + (if a = y then (0 : Int) else f a)
      by_cases heq : a = y
      · simp [heq]
      · simp [heq]
    have hbig_split : sumOver big f =
        sumOver big (fun a => if a = y then f y else 0) + sumOver big g := by
      rw [← sumOver_add]
      exact sumOver_congr big _ _ hsplit
    have hbig_ind : sumOver big (fun a => if a = y then f y else (0 : Int)) = f y := by
      have h := sumOver_ite_eq (l := big) hbig y (f y)
      simp [hymem] at h
      exact h
    have hIH : sumOver big g = sumOver ys g :=
      ih big g hbig hysnodup hsubys hzero_g
    calc sumOver big f
        = sumOver big (fun a => if a = y then f y else (0 : Int)) + sumOver big g := hbig_split
      _ = f y + sumOver ys g := by rw [hbig_ind, hIH]
      _ = f y + sumOver ys f := by rw [hys_g]

theorem test_accounts_shareOf (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup) (hne : r.recipients ≠ [])
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have hzero : ∀ a, a ∉ r.recipients → (fun a => ((shareOf r a : Nat) : Int)) a = 0 := by
    intro a ha
    simp only
    unfold shareOf
    rw [indexOf?_eq_none ha]
    simp
  have hsuper := plan0_sumOver_super_of_zero_outside s.accounts r.recipients
    (fun a => ((shareOf r a : Nat) : Int)) hacc hrec hsub hzero
  rw [hsuper]
  exact selfContainedCheck r hrec hne

theorem plan0_sumOver_accounts_shareOf (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup) (hne : r.recipients ≠ [])
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have hzero : ∀ a, a ∉ r.recipients → (fun a => ((shareOf r a : Nat) : Int)) a = 0 := by
    intro a ha
    simp only
    unfold shareOf
    rw [indexOf?_eq_none ha]
    simp
  have hsuper := plan0_sumOver_super_of_zero_outside s.accounts r.recipients
    (fun a => ((shareOf r a : Nat) : Int)) hacc hrec hsub hzero
  rw [hsuper]
  exact selfContainedCheck r hrec hne

theorem plan0_sumOver_expectedBalance (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hsrc : r.source ∈ s.accounts)
    (hshare : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int)) :
    sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance := by
  have hcongr : ∀ a ∈ s.accounts, expectedBalance s r a =
      ((s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (shareOf r a : Int)) := by
    intro a _
    unfold expectedBalance
    omega
  rw [sumOver_congr s.accounts _ _ hcongr, sumOver_add]
  have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) =
      sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) := by
    exact sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
  rw [hsub, hshare]
  have hind : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hacc r.source (r.amount : Int)
    simp [hsrc] at h
    exact h
  rw [hind]
  omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · have hstep : (step s r).1 = .rejected := by simp [step, hv]
    rw [hstep] at hok
    contradiction

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · simp [step, hv]
  · have hstep : (step s r).1 = .rejected := by simp [step, hv]
    rw [hstep] at hok
    contradiction

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hstep2 : step s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
      simp [step, hv]
    rw [hstep2]
    simp only
    apply And.intro
    · intro x
      simp
    · have hnotvalid : ¬ ValidPayout ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) r := by
        intro hcon
        obtain ⟨_, _, _, _, _, _, _, _, _, hmem⟩ := hcon
        simp at hmem
      simp [step, hnotvalid]
  · have hstep : (step s r).1 = .rejected := by simp [step, hv]
    rw [hstep] at hok
    contradiction

theorem req_nonnegative : NonNegative step := by
  intro s r hnonneg a ha
  by_cases hv : ValidPayout s r
  · have hacc : (step s r).2.accounts = s.accounts := by simp [step, hv]
    have hbal : (step s r).2.balance a = expectedBalance s r a := by simp [step, hv]
    have ha' : a ∈ s.accounts := hacc ▸ ha
    rw [hbal]
    have h0 : 0 ≤ s.balance a := hnonneg a ha'
    obtain ⟨hnodup, hpos, hne, hrnodup, hsrc_notin, hsrc_mem, hrec_mem, hauth, hle, htx⟩ := hv
    unfold expectedBalance
    by_cases hsrc : a = r.source
    · subst hsrc
      have hshare0 : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hsrc_notin]
      rw [if_pos rfl, hshare0]
      omega
    · rw [if_neg hsrc]
      omega
  · have hst : step s r = (.rejected, s) := by simp [step, hv]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hst]
    have hbal : (step s r).2.balance a = s.balance a := by rw [hst]
    have ha' : a ∈ s.accounts := hacc ▸ ha
    rw [hbal]
    exact hnonneg a ha'

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  have hv := fair_of_ok hok
  have heff := req_effects s r hok
  obtain ⟨_, _, hbal⟩ := heff
  have hbal_i : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := hbal _
  rw [hbal_i]
  obtain ⟨hnodup, hpos, hne, hrnodup, hsrc_notin, hsrc_mem, hrec_mem, hauth, hle, htx⟩ := hv
  have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hne_src : r.recipients[i] ≠ r.source := fun h => hsrc_notin (h ▸ hmem)
  have hidx : indexOf? r.recipients r.recipients[i] = some i := indexOf?_getElem hrnodup i hi
  have hexp : expectedBalance s r r.recipients[i] = s.balance r.recipients[i] + ((fairShare r.amount r.recipients.length i : Nat) : Int) := by
    unfold expectedBalance shareOf
    rw [hidx, if_neg hne_src]
    simp
  rw [hexp]
  omega

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv := fair_of_ok hok
  have hv0 := hv
  obtain ⟨hacc, hpos, hne, hrnodup, hsrc_notin, hsrc_mem, hrec_mem, hauth, hle, htx⟩ := hv
  have hshare : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
    plan0_sumOver_accounts_shareOf s r hacc hrnodup hne hrec_mem
  have htot : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance :=
    plan0_sumOver_expectedBalance s r hacc hsrc_mem hshare
  have hstep : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
    simp [step, hv0]
  have h2 : (step s r).2 = ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) := by
    rw [hstep]
  unfold total
  rw [h2]
  simp only
  exact htot

end Payout
