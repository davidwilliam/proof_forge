import EqualSplit.Spec
namespace EqualSplit

def split : Impl := fun amount n =>
  if n = 0 then none
  else
    let an := amount.natAbs
    let q := an / n
    let r := an % n
    let base : List Nat := (List.range n).map fun p => q + if p < r then 1 else 0
    if amount < 0 then some (base.map fun (k : Nat) => - (k : Int))
    else some (base.map fun (k : Nat) => (k : Int))

theorem req_one_share_each_test : OneShareEach split := by
  intro amount n shares h
  unfold OneShareEachOn
  unfold split at h
  by_cases h0 : n = 0
  · simp [h0] at h
  · simp only [h0, ↓reduceIte] at h
    by_cases ham : amount < 0
    · simp only [ham, ↓reduceIte] at h
      have h2 := Option.some_inj.mp h
      subst h2
      simp
    · simp only [ham, ↓reduceIte] at h
      have h2 := Option.some_inj.mp h
      subst h2
      simp

theorem probe1 (a : Int) (h : 0 ≤ a) : ((a.natAbs : Nat) : Int) = a := Int.natAbs_of_nonneg h

theorem probe2 : True := trivial

theorem wiu_probe_d (a : Int) : ((-a).natAbs : Nat) = (a.natAbs : Nat) := Int.natAbs_neg a

theorem wiu_probe_e (an n : Nat) : n * (an / n) + an % n = an := Nat.div_add_mod an n

theorem wiu_probe_f : True := trivial

theorem req_sign_tmp : Sign split := by
  intro amount n shares h
  unfold split at h
  by_cases h0 : n = 0
  · simp [h0] at h
  · simp only [h0, ↓reduceIte] at h
    by_cases ham : amount < 0
    · simp only [ham, ↓reduceIte] at h
      have h2 := Option.some_inj.mp h
      subst h2
      unfold SignOn
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨k, _, rfl⟩ := hx
      constructor
      · intro hge
        omega
      · intro _
        have hk : (0 : Int) ≤ (k : Int) := Int.ofNat_nonneg k
        omega
    · simp only [ham, ↓reduceIte] at h
      have h2 := Option.some_inj.mp h
      subst h2
      unfold SignOn
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨k, hkbase, rfl⟩ := hx
      constructor
      · intro _
        exact Int.ofNat_nonneg k
      · intro hle
        have hzero : amount = 0 := by omega
        have han : amount.natAbs = 0 := by simp [hzero]
        have hmem := (List.mem_map.mp hkbase)
        obtain ⟨p, _, hp⟩ := hmem
        simp only [han, Nat.zero_div, Nat.zero_mod, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add] at hp
        subst hp
        simp

theorem cons_min_succ2 (r n : Nat) :
    min r n + (if n < r then 1 else 0) = min r (n + 1) := by
  by_cases h : n < r
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte, Nat.add_zero]; omega

theorem cons_hmul (n q : Nat) : (n + 1) * q = n * q + q := by
  simp [Nat.add_mul, Nat.one_mul]

theorem cons_base_sum4 (n q r : Nat) :
    (((List.range n).map fun p => q + if p < r then 1 else 0).sum) = n * q + min r n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    rw [h1, List.map_append]
    simp only [List.map_singleton, List.sum_append, List.sum_cons, List.sum_nil]
    rw [ih]
    have hmul := cons_hmul n q
    have hmin := cons_min_succ2 r n
    omega



theorem plan0_sum_map_neg_coe (l : List Nat) :
    (l.map fun k : Nat => -(k : Int)).sum = -((l.sum : Nat) : Int) := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega


theorem plan0_div_add_min (an n : Nat) (hn : 0 < n) :
    n * (an / n) + min (an % n) n = an := by
  have hmod : an % n < n := Nat.mod_lt an hn
  have hmin : min (an % n) n = an % n := Nat.min_eq_left (Nat.le_of_lt hmod)
  rw [hmin]
  exact Nat.div_add_mod an n




theorem plan0_base_sum_neg_coe (n q r : Nat) :
    (((List.range n).map fun p => q + if p < r then 1 else 0).map
      fun k : Nat => -(k : Int)).sum
      = -((n * q + min r n : Nat) : Int) := by
  rw [plan0_sum_map_neg_coe, cons_base_sum4]


theorem plan0_sum_map_coe_try (l : List Nat) :
    (l.map fun k : Nat => (k : Int)).sum = ((l.sum : Nat) : Int) := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem plan0_sum_map_coe (l : List Nat) :
    (l.map fun k : Nat => (k : Int)).sum = ((l.sum : Nat) : Int) := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem plan0_sum_map_neg_coe_try3 (l : List Nat) :
    (l.map fun k : Nat => -(k : Int)).sum = -((l.sum : Nat) : Int) := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem plan0_div_add_min_aux (an n : Nat) (hn : 0 < n) :
    n * (an / n) + min (an % n) n = an := by
  have hmod : an % n < n := Nat.mod_lt an hn
  have hmin : min (an % n) n = an % n := Nat.min_eq_left (Nat.le_of_lt hmod)
  rw [hmin]
  exact Nat.div_add_mod an n

theorem plan0_div_add_min_proof : ∀ (an n : Nat), 0 < n →
    n * (an / n) + min (an % n) n = an := by
  intro an n hn
  have hmod : an % n < n := Nat.mod_lt an hn
  have hmin : min (an % n) n = an % n := Nat.min_eq_left (Nat.le_of_lt hmod)
  rw [hmin]
  exact Nat.div_add_mod an n

theorem plan0_base_sum_coe (n q r : Nat) :
    (((List.range n).map fun p => q + if p < r then 1 else 0).map
      fun k : Nat => (k : Int)).sum
      = ((n * q + min r n : Nat) : Int) := by
  rw [plan0_sum_map_coe, cons_base_sum4]

theorem plan0_base_sum_neg_coe_proof (n q r : Nat) :
    (((List.range n).map fun p => q + if p < r then 1 else 0).map
      fun k : Nat => -(k : Int)).sum
      = -((n * q + min r n : Nat) : Int) := by
  rw [plan0_sum_map_neg_coe, cons_base_sum4]

theorem probe_addmul_ok (a b c : Int) : (a + b) * c = a * c + b * c := Int.add_mul a b c

theorem probe_negmul_ok (a b : Int) : (-a) * b = -(a * b) := Int.neg_mul a b

theorem probe_mulcomm_ok (a b : Int) : a * b = b * a := Int.mul_comm a b

theorem probe_muladd_ok (a b c : Int) : a * (b + c) = a * b + a * c := Int.mul_add a b c

theorem probe_one_mul (N : Int) : (1 : Int) * N = N := Int.one_mul N

theorem probe_expand (Q N : Int) : (Q + 1) * N = Q * N + N := by
  rw [probe_addmul_ok, probe_one_mul]

theorem probe_eq_neg3 (N Q R amt K : Int) (hdiv : N * Q + R = -amt) (hK : K = Q + 1) :
    (-K) * N - amt = R - N := by
  have hcomm : N * Q = Q * N := Int.mul_comm _ _
  rw [hcomm] at hdiv
  have hKN : K * N = Q * N + N := by rw [hK, probe_expand]
  have hneg : (-K) * N = -(K * N) := probe_negmul_ok _ _
  rw [hneg, hKN]
  omega

theorem probe_eq_zero (N Q R amt K : Int) (hdiv : N * Q + R = -amt) (hK : K = Q) :
    (-K) * N - amt = R := by
  have hcomm : N * Q = Q * N := Int.mul_comm _ _
  rw [hcomm] at hdiv
  have hKN : K * N = Q * N := by rw [hK]
  have hneg : (-K) * N = -(K * N) := probe_negmul_ok _ _
  rw [hneg, hKN]
  omega

theorem probe_eq_pos1 (N Q R amt K : Int) (hdiv : N * Q + R = amt) (hK : K = Q + 1) :
    K * N - amt = N - R := by
  have hcomm : N * Q = Q * N := Int.mul_comm _ _
  rw [hcomm] at hdiv
  have hKN : K * N = Q * N + N := by rw [hK, probe_expand]
  rw [hKN]
  omega

theorem probe_eq_pos0 (N Q R amt K : Int) (hdiv : N * Q + R = amt) (hK : K = Q) :
    K * N - amt = -R := by
  have hcomm : N * Q = Q * N := Int.mul_comm _ _
  rw [hcomm] at hdiv
  have hKN : K * N = Q * N := by rw [hK]
  rw [hKN]
  omega

theorem plan1_base_mem_cases (n q r k : Nat)
    (hk : k ∈ (List.range n).map fun p => q + if p < r then 1 else 0) :
    k = q ∨ k = q + 1 := by
  rw [List.mem_map] at hk
  obtain ⟨p, _, hp⟩ := hk
  by_cases h : p < r
  · simp only [h, ↓reduceIte] at hp
    subst hp
    right; omega
  · simp only [h, ↓reduceIte] at hp
    subst hp
    left; omega






theorem plan1_within_pos (N Q R amt K : Int) (hR0 : 0 ≤ R) (hRN : R < N)
    (hdiv : Q * N + R = amt) (hK : K = Q ∨ (K = Q + 1 ∧ 0 < R)) :
    -N < K * N - amt ∧ K * N - amt < N := by
  rcases hK with hK | ⟨hK, hRpos⟩
  · have hKN : K * N = Q * N := by rw [hK]
    have heq : K * N - amt = -R := by omega
    constructor <;> omega
  · have hKN : K * N = Q * N + N := by rw [hK]; rw [probe_addmul_ok, probe_one_mul]
    have heq : K * N - amt = N - R := by omega
    constructor <;> omega


theorem plan1_within_neg (N Q R amt K : Int) (hR0 : 0 ≤ R) (hRN : R < N)
    (hdiv : Q * N + R = -amt) (hK : K = Q ∨ (K = Q + 1 ∧ 0 < R)) :
    -N < (-K) * N - amt ∧ (-K) * N - amt < N := by
  have hneg : ∀ K : Int, (-K) * N = -(K * N) := fun K => probe_negmul_ok K N
  rcases hK with hK | ⟨hK, hRpos⟩
  · have hKN : K * N = Q * N := by rw [hK]
    have h1 : (-K) * N = -(Q * N) := by rw [hneg, hKN]
    constructor <;> omega
  · have hKN : K * N = Q * N + N := by rw [hK]; rw [probe_addmul_ok, probe_one_mul]
    have h1 : (-K) * N = -((Q * N + N)) := by rw [hneg, hKN]
    constructor <;> omega


theorem plan1_base_mem_cases_proof (n q r k : Nat)
    (hk : k ∈ (List.range n).map fun p => q + if p < r then 1 else 0) :
    k = q ∨ k = q + 1 := by
  rw [List.mem_map] at hk
  obtain ⟨p, _, hp⟩ := hk
  by_cases h : p < r
  · simp only [h, ↓reduceIte] at hp
    subst hp
    right; omega
  · simp only [h, ↓reduceIte] at hp
    subst hp
    left; omega

theorem plan1_mod_bounds_int (an n : Nat) (hn : 0 < n) :
    0 ≤ ((an % n : Nat) : Int) ∧ ((an % n : Nat) : Int) < (n : Int) := by
  constructor
  · exact Int.ofNat_nonneg _
  · have hmod : an % n < n := Nat.mod_lt an hn
    exact_mod_cast hmod

theorem plan1_div_eq_int_aux (an n : Nat) :
    ((an / n : Nat) : Int) * (n : Int) + ((an % n : Nat) : Int)
      = ((an : Nat) : Int) := by
  have h := Nat.div_add_mod an n
  have hc : (((n * (an / n) + an % n : Nat)) : Int) = ((an : Nat) : Int) := by
    rw [h]
  simp at hc
  have hcomm : ((an / n : Nat) : Int) * (n : Int) = (n : Int) * ((an / n : Nat) : Int) := by
    rw [Int.mul_comm]
  rw [hcomm]
  omega

theorem plan1_div_eq_int (an n : Nat) :
    ((an / n : Nat) : Int) * (n : Int) + ((an % n : Nat) : Int)
      = ((an : Nat) : Int) := by
  have h := Nat.div_add_mod an n
  have hc : (((n * (an / n) + an % n : Nat)) : Int) = ((an : Nat) : Int) := by
    rw [h]
  simp at hc
  have hcomm : ((an / n : Nat) : Int) * (n : Int) = (n : Int) * ((an / n : Nat) : Int) := by
    rw [Int.mul_comm]
  rw [hcomm]
  omega

theorem plan1_within_pos_ok (N Q R amt K : Int) (hR0 : 0 ≤ R) (hRN : R < N)
    (hdiv : Q * N + R = amt) (hK : K = Q ∨ (K = Q + 1 ∧ 0 < R)) :
    -N < K * N - amt ∧ K * N - amt < N := by
  rcases hK with hK | ⟨hK, hRpos⟩
  · have hKN : K * N = Q * N := by rw [hK]
    have heq : K * N - amt = -R := by omega
    constructor <;> omega
  · have hKN : K * N = Q * N + N := by rw [hK]; rw [probe_addmul_ok, probe_one_mul]
    have heq : K * N - amt = N - R := by omega
    constructor <;> omega

theorem plan1_within_neg_ok (N Q R amt K : Int) (hR0 : 0 ≤ R) (hRN : R < N)
    (hdiv : Q * N + R = -amt) (hK : K = Q ∨ (K = Q + 1 ∧ 0 < R)) :
    -N < (-K) * N - amt ∧ (-K) * N - amt < N := by
  have hneg : ∀ K : Int, (-K) * N = -(K * N) := fun K => probe_negmul_ok K N
  rcases hK with hK | ⟨hK, hRpos⟩
  · have hKN : K * N = Q * N := by rw [hK]
    have h1 : (-K) * N = -(Q * N) := by rw [hneg, hKN]
    constructor <;> omega
  · have hKN : K * N = Q * N + N := by rw [hK]; rw [probe_addmul_ok, probe_one_mul]
    have h1 : (-K) * N = -((Q * N + N)) := by rw [hneg, hKN]
    constructor <;> omega

theorem base_mem_refined (n q r k : Nat)
    (hk : k ∈ (List.range n).map fun p => q + if p < r then 1 else 0) :
    k = q ∨ (k = q + 1 ∧ 0 < r) := by
  rw [List.mem_map] at hk
  obtain ⟨p, _, hp⟩ := hk
  by_cases h : p < r
  · simp only [h, ↓reduceIte] at hp
    subst hp
    refine Or.inr ⟨by omega, by omega⟩
  · simp only [h, ↓reduceIte] at hp
    subst hp
    exact Or.inl rfl

theorem cast_add_one_test (q : Nat) (k : Nat) (hk : k = q + 1) :
    (k : Int) = ((q : Nat) : Int) + 1 := by
  rw [hk]
  simp

theorem cast_lt_test (r : Nat) (hr : 0 < r) : (0 : Int) < ((r : Nat) : Int) := by
  exact_mod_cast hr

theorem natcast_add_one (q : Nat) : (((q + 1 : Nat)) : Int) = ((q : Nat) : Int) + 1 := by
  simp

theorem req_valid_succeeds  : ValidSucceeds split := by
  intro amount n hn
  unfold split
  have h : n ≠ 0 := Nat.ne_of_gt hn
  simp only [h, ↓reduceIte]
  by_cases ham : amount < 0 <;> simp [ham]

theorem req_invalid_fails : InvalidFails split := by
  intro amount
  unfold split
  simp

theorem req_one_share_each  : OneShareEach split := by
  intro amount n shares h
  unfold OneShareEachOn
  unfold split at h
  by_cases h0 : n = 0
  · simp [h0] at h
  · simp only [h0, ↓reduceIte] at h
    by_cases ham : amount < 0
    · simp only [ham, ↓reduceIte] at h
      have h2 := Option.some_inj.mp h
      subst h2
      simp
    · simp only [ham, ↓reduceIte] at h
      have h2 := Option.some_inj.mp h
      subst h2
      simp

theorem req_conservation : Conserves split := by
  intro amount n shares h
  unfold ConservesOn
  unfold split at h
  by_cases h0 : n = 0
  · simp [h0] at h
  · simp only [h0, ↓reduceIte] at h
    have hn : 0 < n := Nat.pos_of_ne_zero h0
    by_cases ham : amount < 0
    · simp only [ham, ↓reduceIte] at h
      have h2 := Option.some_inj.mp h
      subst h2
      have hsum := plan0_base_sum_neg_coe n (amount.natAbs / n) (amount.natAbs % n)
      have hdiv := plan0_div_add_min amount.natAbs n hn
      have h1 : (0 : Int) ≤ -amount := by omega
      have h2c : (((-amount).natAbs : Nat) : Int) = -amount := Int.natAbs_of_nonneg h1
      have h3 : (-amount).natAbs = amount.natAbs := Int.natAbs_neg amount
      rw [h3] at h2c
      have hcast : ((amount.natAbs : Nat) : Int) = -amount := h2c
      have heq : ((n * (amount.natAbs / n) + min (amount.natAbs % n) n : Nat) : Int) = -amount := by
        rw [hdiv, hcast]
      rw [hsum, heq]
      omega
    · simp only [ham, ↓reduceIte] at h
      have h2 := Option.some_inj.mp h
      subst h2
      have hsum := plan0_base_sum_coe n (amount.natAbs / n) (amount.natAbs % n)
      have hdiv := plan0_div_add_min amount.natAbs n hn
      have h0le : (0 : Int) ≤ amount := by omega
      have hcast : ((amount.natAbs : Nat) : Int) = amount := Int.natAbs_of_nonneg h0le
      have heq : ((n * (amount.natAbs / n) + min (amount.natAbs % n) n : Nat) : Int) = amount := by
        rw [hdiv, hcast]
      rw [hsum, heq]

theorem req_within_one_unit : WithinOneUnit split := by
  intro amount n shares h
  unfold split at h
  by_cases h0 : n = 0
  · simp [h0] at h
  · simp only [h0, ↓reduceIte] at h
    have hn : 0 < n := Nat.pos_of_ne_zero h0
    have hdivI := plan1_div_eq_int amount.natAbs n
    have hbounds := plan1_mod_bounds_int amount.natAbs n hn
    by_cases ham : amount < 0
    · simp only [ham, ↓reduceIte] at h
      have h2 := Option.some_inj.mp h
      subst h2
      unfold WithinOneUnitOn
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨k, hkbase, rfl⟩ := hx
      have hkr := base_mem_refined n (amount.natAbs / n) (amount.natAbs % n) k hkbase
      have h1 : (0 : Int) ≤ -amount := by omega
      have h2c : (((-amount).natAbs : Nat) : Int) = -amount := Int.natAbs_of_nonneg h1
      have h3 : (-amount).natAbs = amount.natAbs := Int.natAbs_neg amount
      have hcast : ((amount.natAbs : Nat) : Int) = -amount := by rw [← h3, h2c]
      have hdiv : ((amount.natAbs / n : Nat) : Int) * (n : Int) + ((amount.natAbs % n : Nat) : Int) = -amount := by
        rw [← hcast]; exact hdivI
      have hR0 : (0 : Int) ≤ ((amount.natAbs % n : Nat) : Int) := hbounds.1
      have hRN : ((amount.natAbs % n : Nat) : Int) < (n : Int) := hbounds.2
      have hK : ((k : Int) = ((amount.natAbs / n : Nat) : Int)) ∨ (((k : Int) = ((amount.natAbs / n : Nat) : Int) + 1) ∧ (0 : Int) < ((amount.natAbs % n : Nat) : Int)) := by
        rcases hkr with hk | ⟨hk, hr⟩
        · left; rw [hk]
        · right
          constructor
          · have he : ((k : Nat) : Int) = ((((amount.natAbs / n + 1 : Nat))) : Int) := by rw [hk]
            rw [he, natcast_add_one]
          · exact cast_lt_test _ hr
      have hres := plan1_within_neg_ok (n : Int) (((amount.natAbs / n : Nat)) : Int) (((amount.natAbs % n : Nat)) : Int) amount ((k : Int)) hR0 hRN hdiv hK
      exact hres
    · simp only [ham, ↓reduceIte] at h
      have h2 := Option.some_inj.mp h
      subst h2
      unfold WithinOneUnitOn
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨k, hkbase, rfl⟩ := hx
      have hkr := base_mem_refined n (amount.natAbs / n) (amount.natAbs % n) k hkbase
      have h0le : (0 : Int) ≤ amount := by omega
      have hcast : ((amount.natAbs : Nat) : Int) = amount := Int.natAbs_of_nonneg h0le
      have hdiv : ((amount.natAbs / n : Nat) : Int) * (n : Int) + ((amount.natAbs % n : Nat) : Int) = amount := by
        rw [← hcast]; exact hdivI
      have hR0 : (0 : Int) ≤ ((amount.natAbs % n : Nat) : Int) := hbounds.1
      have hRN : ((amount.natAbs % n : Nat) : Int) < (n : Int) := hbounds.2
      have hK : ((k : Int) = ((amount.natAbs / n : Nat) : Int)) ∨ (((k : Int) = ((amount.natAbs / n : Nat) : Int) + 1) ∧ (0 : Int) < ((amount.natAbs % n : Nat) : Int)) := by
        rcases hkr with hk | ⟨hk, hr⟩
        · left; rw [hk]
        · right
          constructor
          · have he : ((k : Nat) : Int) = ((((amount.natAbs / n + 1 : Nat))) : Int) := by rw [hk]
            rw [he, natcast_add_one]
          · exact cast_lt_test _ hr
      have hres := plan1_within_pos_ok (n : Int) (((amount.natAbs / n : Nat)) : Int) (((amount.natAbs % n : Nat)) : Int) amount ((k : Int)) hR0 hRN hdiv hK
      exact hres

theorem req_sign : Sign split := by
  intro amount n shares h
  unfold split at h
  by_cases h0 : n = 0
  · simp [h0] at h
  · simp only [h0, ↓reduceIte] at h
    by_cases ham : amount < 0
    · simp only [ham, ↓reduceIte] at h
      have h2 := Option.some_inj.mp h
      subst h2
      unfold SignOn
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨k, _, rfl⟩ := hx
      constructor
      · intro hge
        omega
      · intro _
        have hk : (0 : Int) ≤ (k : Int) := Int.ofNat_nonneg k
        omega
    · simp only [ham, ↓reduceIte] at h
      have h2 := Option.some_inj.mp h
      subst h2
      unfold SignOn
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨k, hkbase, rfl⟩ := hx
      constructor
      · intro _
        exact Int.ofNat_nonneg k
      · intro hle
        have hzero : amount = 0 := by omega
        have han : amount.natAbs = 0 := by simp [hzero]
        have hmem := (List.mem_map.mp hkbase)
        obtain ⟨p, _, hp⟩ := hmem
        simp only [han, Nat.zero_div, Nat.zero_mod, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add] at hp
        subst hp
        simp

end EqualSplit
