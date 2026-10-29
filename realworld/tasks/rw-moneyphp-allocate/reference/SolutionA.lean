import Allocation.Spec
/-!
# Reference solution (build team; hidden from agents)

Hamilton apportionment by a greedy loop. Every party first gets the floor of its exact share
`amount * r / S`; then each leftover minor unit goes to the party whose share is currently
furthest below exact (the first such party on ties).
-/

namespace Allocation

/-- `f 0 + f 1 + ... + f (n - 1)`. -/
def sumTo (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- The first index below `n` where `g` is largest (`0` when `n = 0`). -/
def argmaxTo (g : Nat → Int) : Nat → Nat
  | 0 => 0
  | n + 1 => let k := argmaxTo g n; if g k < g n then n else k

/-- How far share `x j` is below exact, in units of `1 / S`: `a * r j - x j * S`. -/
def need (a S : Int) (r x : Nat → Int) (j : Nat) : Int := a * r j - x j * S

/-- Give one more unit to party `k`. -/
def bump (x : Nat → Int) (k : Nat) : Nat → Int := fun j => if j = k then x j + 1 else x j

/-- Hand out `t` leftover units, one at a time, to the party furthest below exact. -/
def hand (a S : Int) (r : Nat → Int) (n : Nat) : Nat → (Nat → Int) → (Nat → Int)
  | 0, x => x
  | t + 1, x => hand a S r n t (bump x (argmaxTo (need a S r x) n))

def ratioAt (ratios : List Nat) (j : Nat) : Int := (ratios.getD j 0 : Int)

def floors (a S : Int) (r : Nat → Int) : Nat → Int := fun j => a * r j / S

def shares (amount : Int) (ratios : List Nat) : List Int :=
  let S : Int := ratios.sum
  let r := ratioAt ratios
  let n := ratios.length
  let x0 := floors amount S r
  let left := amount - sumTo x0 n
  (List.range n).map (hand amount S r n left.toNat x0)

def allocate : Impl := fun amount ratios =>
  if Valid amount ratios then some (shares amount ratios) else none

/-! ## Sums -/

theorem sumTo_update (f : Nat → Int) (k : Nat) (v : Int) :
    ∀ n, k < n → sumTo (fun j => if j = k then f j + v else f j) n = sumTo f n + v := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    simp only [sumTo]
    by_cases hk : k = n
    · subst hk
      have e : sumTo (fun j => if j = k then f j + v else f j) k = sumTo f k := by
        clear ih h
        have : ∀ m, m ≤ k → sumTo (fun j => if j = k then f j + v else f j) m = sumTo f m := by
          intro m hm
          induction m with
          | zero => rfl
          | succ m ihm =>
            simp only [sumTo]
            rw [ihm (by omega)]
            have : m ≠ k := by omega
            simp [this]
        exact this k (Nat.le_refl k)
      rw [e]; simp; omega
    · rw [ih (by omega)]
      simp [Ne.symm hk]
      omega

theorem sumTo_sub (f g : Nat → Int) : ∀ n, sumTo (fun j => f j - g j) n = sumTo f n - sumTo g n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => simp only [sumTo, ih]; omega

theorem sumTo_mul_left (c : Int) (f : Nat → Int) : ∀ n, sumTo (fun j => c * f j) n = c * sumTo f n := by
  intro n; induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih, Int.mul_add]

theorem sumTo_mul_right (c : Int) (f : Nat → Int) : ∀ n, sumTo (fun j => f j * c) n = sumTo f n * c := by
  intro n; induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih, Int.add_mul]

theorem sumTo_congr (f g : Nat → Int) : ∀ n, (∀ j, j < n → f j = g j) → sumTo f n = sumTo g n := by
  intro n; induction n with
  | zero => intro _; rfl
  | succ n ih => intro h; simp only [sumTo]; rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem sumTo_nonneg (f : Nat → Int) : ∀ n, (∀ j, j < n → 0 ≤ f j) → 0 ≤ sumTo f n := by
  intro n; induction n with
  | zero => intro _; simp [sumTo]
  | succ n ih => intro h; simp only [sumTo]; have := ih (fun j hj => h j (by omega)); have := h n (by omega); omega

theorem exists_pos_of_sumTo_pos (f : Nat → Int) : ∀ n, 0 < sumTo f n → ∃ j, j < n ∧ 0 < f j := by
  intro n; induction n with
  | zero => intro h; simp [sumTo] at h
  | succ n ih =>
    intro h
    simp only [sumTo] at h
    by_cases hn : 0 < f n
    · exact ⟨n, by omega, hn⟩
    · obtain ⟨j, hj, hp⟩ := ih (by omega)
      exact ⟨j, by omega, hp⟩

theorem sumTo_shift (f : Nat → Int) : ∀ n, sumTo f (n + 1) = f 0 + sumTo (fun j => f (j + 1)) n := by
  intro n; induction n with
  | zero => simp [sumTo]
  | succ n ih => rw [sumTo, ih]; simp only [sumTo]; omega

theorem sum_ratioAt : ∀ ratios : List Nat, ((ratios.sum : Nat) : Int) = sumTo (ratioAt ratios) ratios.length := by
  intro ratios
  induction ratios with
  | nil => simp [sumTo]
  | cons x xs ih =>
    rw [List.length_cons, sumTo_shift]
    simp only [List.sum_cons, ratioAt, List.getD_cons_zero, List.getD_cons_succ]
    rw [Int.natCast_add, ih]
    rfl

theorem sum_map_range (f : Nat → Int) : ∀ n, ((List.range n).map f).sum = sumTo f n := by
  intro n; induction n with
  | zero => simp [sumTo]
  | succ n ih => simp [List.range_succ, List.sum_append, ih, sumTo]

/-! ## Argmax -/

theorem argmaxTo_lt (g : Nat → Int) : ∀ n, 0 < n → argmaxTo g n < n := by
  intro n; induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    simp only [argmaxTo]
    split
    · omega
    · rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [argmaxTo]
      · have := ih h; omega

theorem argmaxTo_max (g : Nat → Int) : ∀ n j, j < n → g j ≤ g (argmaxTo g n) := by
  intro n; induction n with
  | zero => intro j h; omega
  | succ n ih =>
    intro j hj
    simp only [argmaxTo]
    split
    · rename_i hlt
      rcases Nat.lt_or_ge j n with h | h
      · have := ih j h; omega
      · have : j = n := by omega
        subst this; exact Int.le_refl _
    · rename_i hnot
      rcases Nat.lt_or_ge j n with h | h
      · exact ih j h
      · have : j = n := by omega
        subst this; omega

/-! ## The loop invariant -/

/-- Invariant with `m` units still to hand out. -/
structure Inv (a S : Int) (r : Nat → Int) (n : Nat) (x : Nat → Int) (m : Nat) : Prop where
  bound : ∀ j, j < n → -S < need a S r x j ∧ need a S r x j < S
  order : ∀ i j, i < n → j < n → need a S r x i < 0 → 0 ≤ need a S r x j →
    need a S r x j ≤ need a S r x i + S
  total : sumTo (need a S r x) n = (m : Int) * S

theorem need_bump (a S : Int) (r x : Nat → Int) (k : Nat) :
    need a S r (bump x k) = fun j => if j = k then need a S r x j + (-S) else need a S r x j := by
  funext j
  simp only [need, bump]
  split <;> simp [Int.add_mul] <;> omega

theorem inv_step (a S : Int) (r : Nat → Int) (n : Nat) (x : Nat → Int) (m : Nat)
    (hS : 0 < S) (hn : 0 < n) (h : Inv a S r n x (m + 1)) :
    Inv a S r n (bump x (argmaxTo (need a S r x) n)) m := by
  have hk := argmaxTo_lt (need a S r x) n hn
  generalize hK : argmaxTo (need a S r x) n = k at hk
  have hmax : ∀ j, j < n → need a S r x j ≤ need a S r x k := by
    intro j hj; rw [← hK]; exact argmaxTo_max _ n j hj
  have hpos : 0 < need a S r x k := by
    have ht := h.total
    have : 0 < sumTo (need a S r x) n := by
      rw [ht]; have : (0 : Int) < ((m + 1 : Nat) : Int) := by omega
      exact Int.mul_pos this hS
    obtain ⟨j, hj, hp⟩ := exists_pos_of_sumTo_pos _ n this
    have := hmax j hj; omega
  have hkS := (h.bound k hk).2
  have hnb := need_bump a S r x k
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [hnb]
    have := h.bound j hj
    by_cases hjk : j = k
    · subst hjk; simp; omega
    · simp [hjk]; omega
  · intro i j hi hj hni hnj
    rw [hnb] at hni hnj ⊢
    simp only at hni hnj ⊢
    by_cases hik : i = k <;> by_cases hjk : j = k
    · subst hik; subst hjk; simp at hni hnj; omega
    · subst hik; simp [hjk] at hni hnj ⊢; have := hmax j hj; omega
    · subst hjk; simp [hik] at hni hnj; omega
    · simp [hik, hjk] at hni hnj ⊢; exact h.order i j hi hj hni hnj
  · rw [hnb, sumTo_update _ k (-S) n hk, h.total]
    rw [Int.natCast_add, Int.add_mul]; simp; omega

theorem inv_hand (a S : Int) (r : Nat → Int) (n : Nat) (hS : 0 < S) (hn : 0 < n) :
    ∀ m x, Inv a S r n x m → Inv a S r n (hand a S r n m x) 0 := by
  intro m
  induction m with
  | zero => intro x h; exact h
  | succ m ih => intro x h; exact ih _ (inv_step a S r n x m hS hn h)

theorem sum_need (a S : Int) (r x : Nat → Int) (n : Nat) (hr : sumTo r n = S) :
    sumTo (need a S r x) n = a * S - sumTo x n * S := by
  unfold need
  rw [sumTo_sub, sumTo_mul_left, sumTo_mul_right, hr]

theorem inv_start (a S : Int) (r : Nat → Int) (n : Nat) (hS : 0 < S) (hr : sumTo r n = S) :
    Inv a S r n (floors a S r) (a - sumTo (floors a S r) n).toNat := by
  have hneed : ∀ j, need a S r (floors a S r) j = a * r j % S := by
    intro j; simp only [need, floors]; rw [Int.emod_def]; rw [Int.mul_comm S]
  have hnn : ∀ j, 0 ≤ need a S r (floors a S r) j := by
    intro j; rw [hneed]; exact Int.emod_nonneg _ (by omega)
  have hlt : ∀ j, need a S r (floors a S r) j < S := by
    intro j; rw [hneed]; exact Int.emod_lt_of_pos _ hS
  have hsum := sum_need a S r (floors a S r) n hr
  have hL : 0 ≤ a - sumTo (floors a S r) n := by
    have h0 : 0 ≤ sumTo (need a S r (floors a S r)) n := sumTo_nonneg _ n (fun j _ => hnn j)
    rw [hsum] at h0
    have : 0 ≤ (a - sumTo (floors a S r) n) * S := by rw [Int.sub_mul]; omega
    rcases Int.lt_or_le (a - sumTo (floors a S r) n) 0 with hneg | hok
    · have := Int.mul_neg_of_neg_of_pos hneg hS; omega
    · exact hok
  refine ⟨?_, ?_, ?_⟩
  · intro j _; have := hnn j; have := hlt j; omega
  · intro i j _ _ hi _; have := hnn i; omega
  · rw [hsum, Int.toNat_of_nonneg hL, Int.sub_mul]

/-! ## Correctness -/

theorem mul_bound_zero (x S : Int) (hS : 0 < S) (h1 : -S < x * S) (h2 : x * S < S) : x = 0 := by
  rcases Int.lt_trichotomy x 0 with h | h | h
  · have : x * S ≤ (-1) * S := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega
  · exact h
  · have : 1 * S ≤ x * S := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega

theorem final_inv (amount : Int) (ratios : List Nat) (hv : Valid amount ratios) :
    let S : Int := ratios.sum
    let r := ratioAt ratios
    let n := ratios.length
    let x0 := floors amount S r
    Inv amount S r n (hand amount S r n (amount - sumTo x0 n).toNat x0) 0 := by
  intro S r n x0
  have hS : 0 < S := by have := hv.2; simp only [S]; omega
  have hn : 0 < n := by
    have := hv.1; simp only [n]; cases ratios with
    | nil => contradiction
    | cons _ _ => simp
  have hr : sumTo r n = S := (sum_ratioAt ratios).symm
  exact inv_hand amount S r n hS hn _ _ (inv_start amount S r n hS hr)

theorem shares_spec (amount : Int) (ratios : List Nat) (hv : Valid amount ratios) :
    ∃ x : Nat → Int,
      shares amount ratios = (List.range ratios.length).map x ∧
      Inv amount (ratios.sum : Int) (ratioAt ratios) ratios.length x 0 :=
  ⟨_, rfl, final_inv amount ratios hv⟩

theorem allocate_some {amount : Int} {ratios : List Nat} {out : List Int}
    (h : allocate amount ratios = some out) :
    Valid amount ratios ∧ out = shares amount ratios := by
  unfold allocate at h
  split at h
  · rename_i hv; exact ⟨hv, (Option.some.inj h).symm⟩
  · contradiction

theorem excess_eq (amount : Int) (ratios : List Nat) (x : Nat → Int) (i : Nat)
    (hi : i < ratios.length) :
    excess amount ratios.sum (x i) ratios[i] = -(need amount (ratios.sum : Int) (ratioAt ratios) x i) := by
  simp only [excess, need, ratioAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  omega

theorem req_valid_succeeds : ValidSucceeds allocate := by
  intro amount ratios hv
  simp [allocate, hv]

theorem req_invalid_fails : InvalidFails allocate := by
  intro amount ratios hv
  simp [allocate, hv]

theorem req_one_share_each : OneShareEach allocate := by
  intro amount ratios out h
  obtain ⟨hv, rfl⟩ := allocate_some h
  simp [OneShareEachOn, shares]

theorem req_conservation : Conserves allocate := by
  intro amount ratios out h
  obtain ⟨hv, rfl⟩ := allocate_some h
  obtain ⟨x, hx, hinv⟩ := shares_spec amount ratios hv
  rw [hx]
  unfold ConservesOn
  rw [sum_map_range]
  have hS : (0 : Int) < (ratios.sum : Int) := by have := hv.2; omega
  have ht := hinv.total
  rw [sum_need _ _ _ _ _ (sum_ratioAt ratios).symm] at ht
  simp at ht
  have : (amount - sumTo x ratios.length) * (ratios.sum : Int) = 0 := by rw [Int.sub_mul]; omega
  rcases Int.mul_eq_zero.mp this with h0 | h0
  · omega
  · omega

theorem getElem_shares {amount : Int} {ratios : List Nat} {x : Nat → Int}
    (hx : shares amount ratios = (List.range ratios.length).map x) (i : Nat)
    (h : i < (shares amount ratios).length) :
    (shares amount ratios)[i] = x i := by
  simp only [hx, List.getElem_map, List.getElem_range]

theorem req_within_one_unit : WithinOneUnit allocate := by
  intro amount ratios out h
  obtain ⟨hv, rfl⟩ := allocate_some h
  obtain ⟨x, hx, hinv⟩ := shares_spec amount ratios hv
  intro i hi hr
  rw [getElem_shares hx i hi, excess_eq amount ratios x i hr]
  have := hinv.bound i hr
  omega

theorem req_zero_ratio : ZeroRatio allocate := by
  intro amount ratios out h
  obtain ⟨hv, rfl⟩ := allocate_some h
  obtain ⟨x, hx, hinv⟩ := shares_spec amount ratios hv
  intro i hi hr h0
  rw [getElem_shares hx i hi]
  have hb := hinv.bound i hr
  have hS : (0 : Int) < (ratios.sum : Int) := by have := hv.2; omega
  have hz : ratioAt ratios i = 0 := by
    simp [ratioAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, h0]
  simp only [need, hz, Int.mul_zero, Int.zero_sub] at hb
  exact mul_bound_zero (x i) _ hS (by omega) (by omega)

theorem req_sign : Sign allocate := by
  intro amount ratios out h
  obtain ⟨hv, rfl⟩ := allocate_some h
  obtain ⟨x, hx, hinv⟩ := shares_spec amount ratios hv
  intro y hy
  rw [hx] at hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
  have hi : i < ratios.length := List.mem_range.mp hi
  have hb := hinv.bound i hi
  have hS : (0 : Int) < (ratios.sum : Int) := by have := hv.2; omega
  have hr0 : 0 ≤ ratioAt ratios i := by simp [ratioAt]
  simp only [need] at hb
  generalize ratioAt ratios i = r at hb hr0
  generalize (ratios.sum : Int) = S at hb hS
  constructor
  · intro ha
    have : 0 ≤ amount * r := Int.mul_nonneg ha hr0
    rcases Int.lt_or_le (x i) 0 with hneg | hok
    · have : x i * S ≤ (-1) * S := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
    · exact hok
  · intro ha
    have : amount * r ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg ha hr0
    rcases Int.lt_or_le 0 (x i) with hpos | hok
    · have : 1 * S ≤ x i * S := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
    · exact hok

theorem req_largest_remainder : LargestRemainder allocate := by
  intro amount ratios out h
  obtain ⟨hv, rfl⟩ := allocate_some h
  obtain ⟨x, hx, hinv⟩ := shares_spec amount ratios hv
  intro i hi hri j hj hrj hpi hnj
  rw [getElem_shares hx i hi, excess_eq amount ratios x i hri] at hpi ⊢
  rw [getElem_shares hx j hj, excess_eq amount ratios x j hrj] at hnj ⊢
  have := hinv.order i j hri hrj (by omega) (by omega)
  omega

end Allocation
