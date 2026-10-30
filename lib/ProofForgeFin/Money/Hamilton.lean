import ProofForgeFin.Money.Allocation
/-!
# Allocation by the largest-remainder method

`largestRemainder a rs` is Hamilton apportionment: every party first receives the floor of its
exact share `a * r / S`, then each leftover unit goes to the party whose share is currently
furthest below exact, the first such party on ties. A party that has received its extra unit
is above exact and is not chosen again while units remain, which is the selection rule of
moneyphp's `Money::allocate` from 3.2.1 on (pull request 526: the largest fractional parts
first); the equality with a sort-based implementation is not proved here.

For every amount (negative ones too, under the floor convention of
`ProofForgeFin.Money.Allocation`) and every ratio list with a positive sum, the result has one
share per ratio, conserves the amount, is within strictly less than one unit of every exact
share, gives nothing to a zero ratio, has the sign of the amount, follows the
largest-remainder rule and is monotone in the ratios. These are exactly the requirements of
`realworld/tasks/rw-moneyphp-allocate` and `rw-spliit-balances`.

The proof is a loop invariant over the units handed out (`Hamilton.Inv`): every share stays
within one unit of exact, a share rounded up is never further from exact than a share rounded
down, and the total shortfall is the number of units still to hand out.
-/

namespace ProofForgeFin.Money

namespace Hamilton

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

/-- The ratio at position `j` (zero past the end). -/
def ratioAt (rs : List Nat) (j : Nat) : Int := (rs.getD j 0 : Int)

/-- The floor of every exact share. -/
def floorsAt (a S : Int) (r : Nat → Int) : Nat → Int := fun j => a * r j / S

/-! ## Sums -/

/-- Raising one term below `n` by `v` raises the sum by `v`. -/
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

/-- The sum of a difference. -/
theorem sumTo_sub (f g : Nat → Int) : ∀ n, sumTo (fun j => f j - g j) n = sumTo f n - sumTo g n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => simp only [sumTo, ih]; omega

/-- A constant factor on the left. -/
theorem sumTo_mul_left (c : Int) (f : Nat → Int) : ∀ n, sumTo (fun j => c * f j) n = c * sumTo f n := by
  intro n; induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih, Int.mul_add]

/-- A constant factor on the right. -/
theorem sumTo_mul_right (c : Int) (f : Nat → Int) : ∀ n, sumTo (fun j => f j * c) n = sumTo f n * c := by
  intro n; induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih, Int.add_mul]

/-- A sum of nonnegative terms is nonnegative. -/
theorem sumTo_nonneg (f : Nat → Int) : ∀ n, (∀ j, j < n → 0 ≤ f j) → 0 ≤ sumTo f n := by
  intro n; induction n with
  | zero => intro _; simp [sumTo]
  | succ n ih =>
    intro h; simp only [sumTo]
    have := ih (fun j hj => h j (by omega)); have := h n (by omega); omega

/-- A positive sum has a positive term. -/
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

/-- Peeling off the first term. -/
theorem sumTo_shift (f : Nat → Int) : ∀ n, sumTo f (n + 1) = f 0 + sumTo (fun j => f (j + 1)) n := by
  intro n; induction n with
  | zero => simp [sumTo]
  | succ n ih => rw [sumTo, ih]; simp only [sumTo]; omega

/-- The ratios add up to `S`. -/
theorem sum_ratioAt : ∀ rs : List Nat, ((rs.sum : Nat) : Int) = sumTo (ratioAt rs) rs.length := by
  intro rs
  induction rs with
  | nil => simp [sumTo]
  | cons x xs ih =>
    rw [List.length_cons, sumTo_shift]
    simp only [List.sum_cons, ratioAt, List.getD_cons_zero, List.getD_cons_succ]
    rw [Int.natCast_add, ih]
    rfl

/-- A list built from indices sums to `sumTo`. -/
theorem sum_map_range (f : Nat → Int) : ∀ n, ((List.range n).map f).sum = sumTo f n := by
  intro n; induction n with
  | zero => simp [sumTo]
  | succ n ih => simp [List.range_succ, List.sum_append, ih, sumTo]

/-! ## The first largest index -/

/-- `argmaxTo g n` is below `n` for `n > 0`. -/
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

/-- `argmaxTo g n` is where `g` is largest below `n`. -/
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

/-- The invariant of the loop with `m` units still to hand out. -/
structure Inv (a S : Int) (r : Nat → Int) (n : Nat) (x : Nat → Int) (m : Nat) : Prop where
  /-- Every share is less than one unit from exact. -/
  bound : ∀ j, j < n → -S < need a S r x j ∧ need a S r x j < S
  /-- A share above exact is no further from exact than a share below exact is, plus one
  unit. -/
  order : ∀ i j, i < n → j < n → need a S r x i < 0 → 0 ≤ need a S r x j →
    need a S r x j ≤ need a S r x i + S
  /-- The total shortfall is `m` units. -/
  total : sumTo (need a S r x) n = (m : Int) * S

/-- Bumping party `k` lowers its shortfall by `S`. -/
theorem need_bump (a S : Int) (r x : Nat → Int) (k : Nat) :
    need a S r (bump x k) = fun j => if j = k then need a S r x j + (-S) else need a S r x j := by
  funext j
  simp only [need, bump]
  split <;> simp [Int.add_mul] <;> omega

/-- One step of the loop keeps the invariant with one unit fewer to hand out. -/
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

/-- The whole loop ends with the invariant and nothing left to hand out. -/
theorem inv_hand (a S : Int) (r : Nat → Int) (n : Nat) (hS : 0 < S) (hn : 0 < n) :
    ∀ m x, Inv a S r n x m → Inv a S r n (hand a S r n m x) 0 := by
  intro m
  induction m with
  | zero => intro x h; exact h
  | succ m ih => intro x h; exact ih _ (inv_step a S r n x m hS hn h)

/-- The total shortfall is `a * S` minus the shares times `S`. -/
theorem sum_need (a S : Int) (r x : Nat → Int) (n : Nat) (hr : sumTo r n = S) :
    sumTo (need a S r x) n = a * S - sumTo x n * S := by
  unfold need
  rw [sumTo_sub, sumTo_mul_left, sumTo_mul_right, hr]

/-- The floors satisfy the invariant with the leftover still to hand out. -/
theorem inv_start (a S : Int) (r : Nat → Int) (n : Nat) (hS : 0 < S) (hr : sumTo r n = S) :
    Inv a S r n (floorsAt a S r) (a - sumTo (floorsAt a S r) n).toNat := by
  have hneed : ∀ j, need a S r (floorsAt a S r) j = a * r j % S := by
    intro j; simp only [need, floorsAt]; rw [Int.emod_def]; rw [Int.mul_comm S]
  have hnn : ∀ j, 0 ≤ need a S r (floorsAt a S r) j := by
    intro j; rw [hneed]; exact Int.emod_nonneg _ (by omega)
  have hlt : ∀ j, need a S r (floorsAt a S r) j < S := by
    intro j; rw [hneed]; exact Int.emod_lt_of_pos _ hS
  have hsum := sum_need a S r (floorsAt a S r) n hr
  have hL : 0 ≤ a - sumTo (floorsAt a S r) n := by
    have h0 : 0 ≤ sumTo (need a S r (floorsAt a S r)) n := sumTo_nonneg _ n (fun j _ => hnn j)
    rw [hsum] at h0
    have : 0 ≤ (a - sumTo (floorsAt a S r) n) * S := by rw [Int.sub_mul]; omega
    rcases Int.lt_or_le (a - sumTo (floorsAt a S r) n) 0 with hneg | hok
    · have := Int.mul_neg_of_neg_of_pos hneg hS; omega
    · exact hok
  refine ⟨?_, ?_, ?_⟩
  · intro j _; have := hnn j; have := hlt j; omega
  · intro i j _ _ hi _; have := hnn i; omega
  · rw [hsum, Int.toNat_of_nonneg hL, Int.sub_mul]

end Hamilton

open Hamilton

/-- Hamilton apportionment of `a` among the ratios `rs`: floors first, then one leftover unit
at a time to the party furthest below exact (the first such party on ties). -/
def largestRemainder (a : Int) (rs : List Nat) : List Int :=
  (List.range rs.length).map
    (hand a rs.sum (ratioAt rs) rs.length
      (a - sumTo (floorsAt a rs.sum (ratioAt rs)) rs.length).toNat (floorsAt a rs.sum (ratioAt rs)))

/-- One share per ratio. -/
@[simp] theorem length_largestRemainder (a : Int) (rs : List Nat) :
    (largestRemainder a rs).length = rs.length := by
  simp [largestRemainder]

/-- The shares of `largestRemainder` come from a function of the index that satisfies the
loop invariant with nothing left to hand out. -/
theorem largestRemainder_spec (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    ∃ x : Nat → Int, largestRemainder a rs = (List.range rs.length).map x ∧
      Inv a (rs.sum : Int) (ratioAt rs) rs.length x 0 := by
  refine ⟨_, rfl, ?_⟩
  have hS' : (0 : Int) < (rs.sum : Int) := by omega
  have hn : 0 < rs.length := by
    rcases rs with _ | ⟨r, rs⟩
    · simp at hS
    · simp
  exact inv_hand _ _ _ _ hS' hn _ _ (inv_start _ _ _ _ hS' (sum_ratioAt rs).symm)

/-- The excess of a share is minus its shortfall. -/
theorem excess_eq_neg_need (a : Int) (rs : List Nat) (x : Nat → Int) (i : Nat) (hi : i < rs.length) :
    excess a rs.sum (x i) rs[i] = -(need a (rs.sum : Int) (ratioAt rs) x i) := by
  simp only [excess, need, ratioAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]
  omega

/-- Reading a share built from an index function. -/
theorem getElem_range_map {x : Nat → Int} {n : Nat} {xs : List Int} (hx : xs = (List.range n).map x)
    (i : Nat) (h : i < xs.length) : xs[i] = x i := by
  subst hx; simp

/-- `largestRemainder` conserves the amount. -/
theorem largestRemainder_conserves (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    ConservesOn a (largestRemainder a rs) := by
  obtain ⟨x, hx, hinv⟩ := largestRemainder_spec a hS
  rw [hx]
  unfold ConservesOn
  rw [sum_map_range]
  have hS' : (0 : Int) < (rs.sum : Int) := by omega
  have ht := hinv.total
  rw [sum_need _ _ _ _ _ (sum_ratioAt rs).symm] at ht
  simp at ht
  have : (a - sumTo x rs.length) * (rs.sum : Int) = 0 := by rw [Int.sub_mul]; omega
  rcases Int.mul_eq_zero.mp this with h0 | h0 <;> omega

/-- `largestRemainder` gives one share per ratio. -/
theorem largestRemainder_oneShareEach (a : Int) (rs : List Nat) :
    OneShareEachOn rs (largestRemainder a rs) := length_largestRemainder a rs

/-- Every share of `largestRemainder` is less than one unit from exact. -/
theorem largestRemainder_within (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    WithinOneUnitOn a rs (largestRemainder a rs) := by
  obtain ⟨x, hx, hinv⟩ := largestRemainder_spec a hS
  intro i hi hr
  rw [getElem_range_map hx i hi, excess_eq_neg_need a rs x i hr]
  have := hinv.bound i hr
  omega

/-- `largestRemainder` follows the largest-remainder rule. -/
theorem largestRemainder_largestRemainder (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    LargestRemainderOn a rs (largestRemainder a rs) := by
  obtain ⟨x, hx, hinv⟩ := largestRemainder_spec a hS
  intro i hi hri j hj hrj hpi hnj
  rw [getElem_range_map hx i hi, excess_eq_neg_need a rs x i hri] at hpi ⊢
  rw [getElem_range_map hx j hj, excess_eq_neg_need a rs x j hrj] at hnj ⊢
  have := hinv.order i j hri hrj (by omega) (by omega)
  omega

/-- `largestRemainder` gives nothing to a zero ratio. -/
theorem largestRemainder_zeroRatio (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    ZeroRatioOn rs (largestRemainder a rs) :=
  zeroRatioOn_of_withinOneUnitOn (largestRemainder_within a hS)

/-- The shares of `largestRemainder` have the sign of the amount. -/
theorem largestRemainder_sign (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    SignOn a (largestRemainder a rs) :=
  signOn_of_withinOneUnitOn (largestRemainder_oneShareEach a rs) (largestRemainder_within a hS)

/-- The shares of `largestRemainder` are monotone in the ratios. -/
theorem largestRemainder_monotone (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    MonotoneOn a rs (largestRemainder a rs) :=
  monotoneOn_of_largestRemainderOn (largestRemainder_within a hS)
    (largestRemainder_largestRemainder a hS)

/-- Every share of `largestRemainder` is the floor or the ceiling of the exact share. -/
theorem largestRemainder_floor_or_ceil (a : Int) {rs : List Nat} (hS : 0 < rs.sum) (i : Nat)
    (h : i < (largestRemainder a rs).length) (hr : i < rs.length) :
    (largestRemainder a rs)[i] = a * (rs[i] : Int) / rs.sum ∨
      (largestRemainder a rs)[i] = divCeil (a * (rs[i] : Int)) rs.sum :=
  (within_iff_floor_or_ceil _ hS).1 (largestRemainder_within a hS i h hr)

/-! ## The symmetric convention -/

/-- Under the symmetric convention (allocate `-a` and negate for a negative amount) the
largest-remainder method conserves the amount. -/
theorem symAlloc_largestRemainder_conserves (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    ConservesOn a (symAlloc largestRemainder a rs) :=
  symAlloc_of_forall_nonneg largestRemainder rs (fun a xs => ConservesOn a xs)
    (fun _ _ h => conservesOn_neg h) (fun a _ => largestRemainder_conserves a hS) a

/-- Under the symmetric convention the largest-remainder method is within one unit. -/
theorem symAlloc_largestRemainder_within (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    WithinOneUnitOn a rs (symAlloc largestRemainder a rs) :=
  symAlloc_of_forall_nonneg largestRemainder rs (fun a xs => WithinOneUnitOn a rs xs)
    (fun _ _ h => withinOneUnitOn_neg h) (fun a _ => largestRemainder_within a hS) a

/-- Under the symmetric convention the largest-remainder method follows the
largest-remainder rule. -/
theorem symAlloc_largestRemainder_largestRemainder (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    LargestRemainderOn a rs (symAlloc largestRemainder a rs) :=
  symAlloc_of_forall_nonneg largestRemainder rs (fun a xs => LargestRemainderOn a rs xs)
    (fun _ _ h => largestRemainderOn_neg h) (fun a _ => largestRemainder_largestRemainder a hS) a

/-- Under the symmetric convention the largest-remainder method gives one share per ratio. -/
theorem symAlloc_largestRemainder_oneShareEach (a : Int) (rs : List Nat) :
    OneShareEachOn rs (symAlloc largestRemainder a rs) :=
  symAlloc_of_forall_nonneg largestRemainder rs (fun _ xs => OneShareEachOn rs xs)
    (fun _ _ h => oneShareEachOn_neg h) (fun a _ => largestRemainder_oneShareEach a rs) a

/-- The allocation of issue 436 of moneyphp, by the largest-remainder method. -/
theorem largestRemainder_example : largestRemainder 5 [0, 7, 3] = [0, 4, 1] := by decide

/-- Spliit issue 374: 100 units split three ways by the largest-remainder method. -/
theorem largestRemainder_example_thirds : largestRemainder 100 [1, 1, 1] = [34, 33, 33] := by decide

end ProofForgeFin.Money
