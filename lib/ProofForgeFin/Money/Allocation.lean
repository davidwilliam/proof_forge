import ProofForgeFin.Money.Round
/-!
# Allocation by ratios: requirements and the remainder-to-the-first methods

An allocation splits an amount `a` (in minor units, possibly negative) among parties in
proportion to whole-number ratios `rs`, with `S = rs.sum > 0`. The exact share of the party
with ratio `r` is the rational `a * r / S`; a share `x` is measured against it by its excess
`x * S - a * r` (the share minus the exact value, in units of `1 / S`).

This module states the requirements of an allocation on one input and its output, in the
same form the task specifications use (`ConservesOn`, `WithinOneUnitOn`, `ZeroRatioOn`,
`SignOn`, `LargestRemainderOn`), proves the implications between them, and defines the
allocation methods that hand the leftover units to the first parties:

* `allocFirst a rs`: every party receives the floor `a * r / S`; the leftover
  `a - Σ floors` (between `0` and the number of parties) goes one unit each to the first
  parties in list order, whatever their ratio. This is moneyphp's `Money::allocate` in
  3.0.9, go-money's `Allocate` for a nonnegative amount, and the weighted payout of
  `tasks/payouts-weighted-*`.
* `allocFirstNonzero a rs`: the same, skipping parties whose ratio is zero (moneyphp 3.1.3
  to 3.2.0).

Both conserve the amount and give every party its floor or its floor plus one, so every share
is at most one unit from exact (`-S < excess ≤ S`); `allocFirstNonzero` also gives zero to a
zero ratio. Neither is within strictly less than one unit (a party whose exact share is an
integer can receive one more), which is what the largest-remainder method of
`ProofForgeFin.Money.Hamilton` adds.

Negative amounts: with the floor convention used here (Euclidean division, remainders in
`[0, S)`), the leftover is nonnegative for every amount and units are added. The symmetric
convention of go-money (truncating division, units of `-1` for a negative amount) is
`symAlloc f`: allocate `-a` and negate. `symAlloc` preserves every requirement above and
makes any method odd in the amount.
-/

namespace ProofForgeFin.Money

/-! ## Requirements on one allocation -/

/-- How far share `x` is above the exact share `a * r / S` of a party with ratio `r`, in units
of `1 / S`: `x * S - a * r`. -/
def excess (a : Int) (S : Nat) (x : Int) (r : Nat) : Int := x * (S : Int) - a * (r : Int)

/-- One share per ratio. -/
def OneShareEachOn (rs : List Nat) (xs : List Int) : Prop := xs.length = rs.length

/-- The shares add up to exactly the amount. -/
def ConservesOn (a : Int) (xs : List Int) : Prop := xs.sum = a

/-- Every share is less than one unit away from its exact share: `-S < excess < S`. -/
def WithinOneUnitOn (a : Int) (rs : List Nat) (xs : List Int) : Prop :=
  ∀ i (hx : i < xs.length) (hr : i < rs.length),
    -(rs.sum : Int) < excess a rs.sum xs[i] rs[i] ∧ excess a rs.sum xs[i] rs[i] < (rs.sum : Int)

/-- Every share is at most one unit away from its exact share: `-S ≤ excess ≤ S`. -/
def AtMostOneUnitOn (a : Int) (rs : List Nat) (xs : List Int) : Prop :=
  ∀ i (hx : i < xs.length) (hr : i < rs.length),
    -(rs.sum : Int) ≤ excess a rs.sum xs[i] rs[i] ∧ excess a rs.sum xs[i] rs[i] ≤ (rs.sum : Int)

/-- A party whose ratio is zero receives nothing. -/
def ZeroRatioOn (rs : List Nat) (xs : List Int) : Prop :=
  ∀ i (hx : i < xs.length) (hr : i < rs.length), rs[i] = 0 → xs[i] = 0

/-- Shares have the sign of the amount. -/
def SignOn (a : Int) (xs : List Int) : Prop :=
  ∀ x ∈ xs, (0 ≤ a → 0 ≤ x) ∧ (a ≤ 0 → x ≤ 0)

/-- Leftover units go to the largest remainders: if share `i` was rounded up and share `j`
rounded down, moving one unit from `i` to `j` would not bring the shares closer to exact
(`excess i - excess j ≤ S`). -/
def LargestRemainderOn (a : Int) (rs : List Nat) (xs : List Int) : Prop :=
  ∀ i (hi : i < xs.length) (hri : i < rs.length) j (hj : j < xs.length) (hrj : j < rs.length),
    0 < excess a rs.sum xs[i] rs[i] → excess a rs.sum xs[j] rs[j] < 0 →
    excess a rs.sum xs[i] rs[i] - excess a rs.sum xs[j] rs[j] ≤ (rs.sum : Int)

/-- Shares are monotone in the ratios: a smaller ratio never receives more for a nonnegative
amount, nor less for a nonpositive amount. -/
def MonotoneOn (a : Int) (rs : List Nat) (xs : List Int) : Prop :=
  ∀ i (hi : i < xs.length) (hri : i < rs.length) j (hj : j < xs.length) (hrj : j < rs.length),
    rs[i] < rs[j] → (0 ≤ a → xs[i] ≤ xs[j]) ∧ (a ≤ 0 → xs[j] ≤ xs[i])

/-! ## One share against its exact value -/

/-- A share is less than one unit from exact exactly when it is the floor or the ceiling of
the exact share. -/
theorem within_iff_floor_or_ceil {a x : Int} {S : Nat} (r : Nat) (hS : 0 < S) :
    (-(S : Int) < excess a S x r ∧ excess a S x r < S) ↔
      x = a * r / S ∨ x = divCeil (a * r) S := by
  have hS' : (0 : Int) < S := by omega
  have hb := ediv_bounds (a * r) hS'
  have hc := divCeil_bounds (a * r) hS'
  unfold excess
  constructor
  · intro h
    by_cases h0 : x * S ≤ a * r
    · exact Or.inl ((ediv_eq_iff hS').2 ⟨h0, by omega⟩).symm
    · exact Or.inr ((divCeil_eq_iff hS').2 ⟨by omega, by omega⟩).symm
  · rintro (h | h) <;> subst h <;> omega

/-- A share that is the floor or the floor plus one is within `(-S, S]` of exact. -/
theorem excess_bounds_of_floor_or_succ {a x : Int} {S : Nat} (r : Nat) (hS : 0 < S)
    (h : x = a * r / S ∨ x = a * r / S + 1) :
    -(S : Int) < excess a S x r ∧ excess a S x r ≤ S := by
  have hb := ediv_bounds (a * r) (show (0 : Int) < S by omega)
  unfold excess
  rcases h with rfl | rfl
  · omega
  · rw [Int.add_mul, Int.one_mul]; omega

/-- A share within one unit of an exact share of zero is zero. -/
theorem eq_zero_of_within_zero {a x : Int} {S : Nat} (hS : 0 < S)
    (h : -(S : Int) < excess a S x 0 ∧ excess a S x 0 < S) : x = 0 := by
  unfold excess at h
  simp only [Int.natCast_zero, Int.mul_zero, Int.sub_zero] at h
  have hS' : (0 : Int) < S := by omega
  have := le_of_mul_lt_mul_add (q := x) (q' := 0) hS' (by rw [Int.zero_mul]; omega)
  have := le_of_mul_lt_mul_add (q := 0) (q' := x) hS' (by rw [Int.zero_mul]; omega)
  omega

/-- A share within one unit of a nonnegative exact share is nonnegative. -/
theorem nonneg_of_within {a x : Int} {S : Nat} (r : Nat) (ha : 0 ≤ a)
    (h : -(S : Int) < excess a S x r) : 0 ≤ x := by
  unfold excess at h
  have : 0 ≤ a * (r : Int) := Int.mul_nonneg ha (by omega)
  have hS' : (0 : Int) < S := by
    rcases Int.lt_or_le 0 (S : Int) with h' | h'
    · exact h'
    · have : (S : Int) = 0 := by omega
      rw [this] at h; simp at h; omega
  exact le_of_mul_lt_mul_add (q := 0) (q' := x) hS' (by rw [Int.zero_mul]; omega)

/-- A share within one unit of a nonpositive exact share is nonpositive. -/
theorem nonpos_of_within {a x : Int} {S : Nat} (r : Nat) (ha : a ≤ 0)
    (h : excess a S x r < S) : x ≤ 0 := by
  unfold excess at h
  have : a * (r : Int) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg ha (by omega)
  have hS' : (0 : Int) < S := by
    rcases Int.lt_or_le 0 (S : Int) with h' | h'
    · exact h'
    · have : (S : Int) = 0 := by omega
      rw [this] at h; simp at h; omega
  exact le_of_mul_lt_mul_add (q := x) (q' := 0) hS' (by rw [Int.zero_mul]; omega)

/-! ## Implications between the requirements -/

/-- Within one unit implies at most one unit. -/
theorem atMostOneUnitOn_of_withinOneUnitOn {a : Int} {rs : List Nat} {xs : List Int}
    (h : WithinOneUnitOn a rs xs) : AtMostOneUnitOn a rs xs := fun i hx hr => by
  have := h i hx hr; omega

/-- Within one unit implies that a zero ratio receives nothing. -/
theorem zeroRatioOn_of_withinOneUnitOn {a : Int} {rs : List Nat} {xs : List Int}
    (h : WithinOneUnitOn a rs xs) : ZeroRatioOn rs xs := by
  intro i hx hr h0
  have hb := h i hx hr
  rw [h0] at hb
  have hS : 0 < rs.sum := by unfold excess at hb; omega
  exact eq_zero_of_within_zero hS hb

/-- Within one unit, with one share per ratio, implies that shares have the sign of the
amount. -/
theorem signOn_of_withinOneUnitOn {a : Int} {rs : List Nat} {xs : List Int}
    (hl : OneShareEachOn rs xs) (h : WithinOneUnitOn a rs xs) : SignOn a xs := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hr : i < rs.length := by unfold OneShareEachOn at hl; omega
  have hb := h i hi hr
  exact ⟨fun ha => nonneg_of_within _ ha hb.1, fun ha => nonpos_of_within _ ha hb.2⟩

/-- Within one unit and the largest-remainder rule imply that, for a nonnegative amount, a
smaller ratio never receives more. -/
theorem le_of_lt_ratio {a : Int} {rs : List Nat} {xs : List Int}
    (hw : WithinOneUnitOn a rs xs) (hlr : LargestRemainderOn a rs xs) (ha : 0 ≤ a)
    (i : Nat) (hi : i < xs.length) (hri : i < rs.length) (j : Nat) (hj : j < xs.length)
    (hrj : j < rs.length) (hlt : rs[i] < rs[j]) : xs[i] ≤ xs[j] := by
  have wi := hw i hi hri
  have wj := hw j hj hrj
  have l := hlr i hi hri j hj hrj
  unfold excess at wi wj l
  generalize hS : (rs.sum : Int) = S at wi wj l
  generalize hri' : ((rs[i] : Nat) : Int) = ri at wi wj l
  generalize hrj' : ((rs[j] : Nat) : Int) = rj at wi wj l
  have hlt' : ri < rj := by omega
  have hS0 : 0 < S := by omega
  generalize xs[i] = xi at wi l ⊢
  generalize xs[j] = xj at wj l ⊢
  have m1 : a * ri ≤ a * rj := Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hlt') ha
  rcases Int.lt_or_le xj xi with hc | hc
  · exfalso
    have m2 := mul_le_mul_of_le (Int.le_of_lt hS0) (show xj + 1 ≤ xi by omega)
    rw [Int.add_mul, Int.one_mul] at m2
    have l' := l (by omega) (by omega)
    have e : a * ri = a * rj := by omega
    rcases Int.lt_or_eq_of_le ha with ha' | ha'
    · have := Int.mul_lt_mul_of_pos_left hlt' ha'
      omega
    · subst ha'
      simp only [Int.zero_mul] at wi
      have := le_of_mul_lt_mul_add (q := xi) (q' := 0) hS0 (by rw [Int.zero_mul]; omega)
      have := le_of_mul_lt_mul_add (q := 1) (q' := xi) hS0 (by rw [Int.one_mul]; omega)
      omega
  · exact hc

/-- A share at most one unit above exact and another less than one unit below exact, for a
nonnegative amount and a ratio no larger than the other's: the first exceeds the second by at
most one unit. -/
theorem le_add_one_of_le_ratio {a xi xj : Int} {S ri rj : Nat} (hS : 0 < S) (ha : 0 ≤ a)
    (hle : ri ≤ rj) (hi : excess a S xi ri ≤ S) (hj : -(S : Int) < excess a S xj rj) :
    xi ≤ xj + 1 := by
  unfold excess at hi hj
  have m1 : a * (ri : Int) ≤ a * (rj : Int) := Int.mul_le_mul_of_nonneg_left (by omega) ha
  have e : (xj + 1) * (S : Int) = xj * S + S := by rw [Int.add_mul, Int.one_mul]
  exact le_of_mul_lt_mul_add (show (0 : Int) < S by omega) (by omega)

/-! ## Negation -/

/-- Negating the amount and the share negates the excess. -/
theorem excess_neg (a : Int) (S : Nat) (x : Int) (r : Nat) :
    excess (-a) S (-x) r = -excess a S x r := by
  unfold excess; rw [Int.neg_mul, Int.neg_mul]; omega

/-- The sum of the negated list. -/
theorem sum_map_neg (xs : List Int) : (xs.map Neg.neg).sum = -xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Negation preserves one share per ratio. -/
theorem oneShareEachOn_neg {rs : List Nat} {xs : List Int} (h : OneShareEachOn rs xs) :
    OneShareEachOn rs (xs.map Neg.neg) := by
  unfold OneShareEachOn at *; simpa using h

/-- Negation preserves conservation. -/
theorem conservesOn_neg {a : Int} {xs : List Int} (h : ConservesOn a xs) :
    ConservesOn (-a) (xs.map Neg.neg) := by
  unfold ConservesOn at *; rw [sum_map_neg, h]

/-- Negation preserves the within-one-unit bound. -/
theorem withinOneUnitOn_neg {a : Int} {rs : List Nat} {xs : List Int}
    (h : WithinOneUnitOn a rs xs) : WithinOneUnitOn (-a) rs (xs.map Neg.neg) := by
  intro i hx hr
  have := h i (by simpa using hx) hr
  simp only [List.getElem_map, excess_neg]
  omega

/-- Negation preserves the at-most-one-unit bound. -/
theorem atMostOneUnitOn_neg {a : Int} {rs : List Nat} {xs : List Int}
    (h : AtMostOneUnitOn a rs xs) : AtMostOneUnitOn (-a) rs (xs.map Neg.neg) := by
  intro i hx hr
  have := h i (by simpa using hx) hr
  simp only [List.getElem_map, excess_neg]
  omega

/-- Negation preserves the zero-ratio requirement. -/
theorem zeroRatioOn_neg {rs : List Nat} {xs : List Int} (h : ZeroRatioOn rs xs) :
    ZeroRatioOn rs (xs.map Neg.neg) := by
  intro i hx hr h0
  have := h i (by simpa using hx) hr h0
  simp [this]

/-- Negation preserves the sign requirement. -/
theorem signOn_neg {a : Int} {xs : List Int} (h : SignOn a xs) : SignOn (-a) (xs.map Neg.neg) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  have := h x hx
  constructor <;> intro _ <;> omega

/-- Negation preserves the largest-remainder rule. -/
theorem largestRemainderOn_neg {a : Int} {rs : List Nat} {xs : List Int}
    (h : LargestRemainderOn a rs xs) : LargestRemainderOn (-a) rs (xs.map Neg.neg) := by
  intro i hi hri j hj hrj h1 h2
  simp only [List.getElem_map, excess_neg] at h1 h2 ⊢
  have := h j (by simpa using hj) hrj i (by simpa using hi) hri (by omega) (by omega)
  omega

/-- Within one unit and the largest-remainder rule imply monotonicity in the ratios. -/
theorem monotoneOn_of_largestRemainderOn {a : Int} {rs : List Nat} {xs : List Int}
    (hw : WithinOneUnitOn a rs xs) (hlr : LargestRemainderOn a rs xs) : MonotoneOn a rs xs := by
  intro i hi hri j hj hrj hlt
  refine ⟨fun ha => le_of_lt_ratio hw hlr ha i hi hri j hj hrj hlt, fun ha => ?_⟩
  have := le_of_lt_ratio (withinOneUnitOn_neg hw) (largestRemainderOn_neg hlr) (by omega)
    i (by simpa using hi) hri j (by simpa using hj) hrj hlt
  simp only [List.getElem_map] at this
  omega

/-! ## The symmetric convention for negative amounts -/

/-- The symmetric convention: allocate a nonnegative amount with `f`, and a negative amount
`a` as the negation of the allocation of `-a`. Truncating division with units of `-1` for a
negative amount (go-money) is this convention applied to the floor-based methods. -/
def symAlloc (f : Int → List Nat → List Int) (a : Int) (rs : List Nat) : List Int :=
  if 0 ≤ a then f a rs else (f (-a) rs).map Neg.neg

/-- On a nonnegative amount the symmetric convention is the method itself. -/
theorem symAlloc_of_nonneg (f : Int → List Nat → List Int) {a : Int} (rs : List Nat)
    (ha : 0 ≤ a) : symAlloc f a rs = f a rs := by simp [symAlloc, ha]

/-- On a negative amount the symmetric convention negates the allocation of `-a`. -/
theorem symAlloc_of_neg (f : Int → List Nat → List Int) {a : Int} (rs : List Nat)
    (ha : a < 0) : symAlloc f a rs = (f (-a) rs).map Neg.neg := by
  simp [symAlloc, show ¬ 0 ≤ a by omega]

/-- The symmetric convention is odd in a nonzero amount. -/
theorem symAlloc_neg (f : Int → List Nat → List Int) {a : Int} (rs : List Nat) (ha : a ≠ 0) :
    symAlloc f (-a) rs = (symAlloc f a rs).map Neg.neg := by
  by_cases h : 0 ≤ a
  · rw [symAlloc_of_neg f rs (by omega), symAlloc_of_nonneg f rs h, Int.neg_neg]
  · rw [symAlloc_of_nonneg f rs (by omega), symAlloc_of_neg f rs (by omega), List.map_map]
    have : (Neg.neg ∘ Neg.neg : Int → Int) = id := by funext x; simp
    rw [this, List.map_id]

/-- A requirement preserved by negation and met by `f` on nonnegative amounts is met by the
symmetric convention on every amount. -/
theorem symAlloc_of_forall_nonneg (f : Int → List Nat → List Int) (rs : List Nat)
    (P : Int → List Int → Prop) (hneg : ∀ a xs, P a xs → P (-a) (xs.map Neg.neg))
    (h : ∀ a, 0 ≤ a → P a (f a rs)) (a : Int) : P a (symAlloc f a rs) := by
  by_cases ha : 0 ≤ a
  · rw [symAlloc_of_nonneg f rs ha]; exact h a ha
  · rw [symAlloc_of_neg f rs (by omega)]
    have := hneg _ _ (h (-a) (by omega))
    rwa [Int.neg_neg] at this

/-! ## Floors and the leftover -/

/-- The exact share `a * r / S` rounded down. -/
def floorShare (a : Int) (S r : Nat) : Int := a * (r : Int) / (S : Int)

/-- Every party's floor share. -/
def floors (a : Int) (rs : List Nat) : List Int := rs.map (floorShare a rs.sum)

/-- The units left after every party receives its floor share: `a - Σ floors`. -/
def leftover (a : Int) (rs : List Nat) : Int := a - (floors a rs).sum

/-- The floors and the remainders `a * r % S` account for the whole of `a * Σ r`. -/
theorem sum_floorShare_mul_add_sum_emod (a : Int) (S : Nat) (rs : List Nat) :
    (rs.map (floorShare a S)).sum * (S : Int) + (rs.map (fun r : Nat => a * (r : Int) % S)).sum
      = a * (rs.sum : Int) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : a * (r : Int) % S = a * r - S * (a * r / S) := Int.emod_def _ _
    have e : ((r + rs.sum : Nat) : Int) = (r : Int) + rs.sum := by push_cast; rfl
    rw [e]
    unfold floorShare at *
    rw [h1]
    grind

/-- The leftover times `S` is the sum of the remainders. -/
theorem leftover_mul (a : Int) (rs : List Nat) :
    leftover a rs * (rs.sum : Int) = (rs.map (fun r : Nat => a * (r : Int) % rs.sum)).sum := by
  have := sum_floorShare_mul_add_sum_emod a rs.sum rs
  unfold leftover floors
  rw [Int.sub_mul]
  omega

/-- Remainders are nonnegative. -/
theorem sum_emod_nonneg (a : Int) {S : Nat} (hS : 0 < S) (rs : List Nat) :
    0 ≤ (rs.map (fun r : Nat => a * (r : Int) % S)).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons]
    have := Int.emod_nonneg (a * (r : Int)) (show (S : Int) ≠ 0 by omega)
    omega

/-- Each remainder is below `S`, and a zero ratio has remainder zero, so the remainders add
up to at most `(S - 1)` times the number of nonzero ratios. -/
theorem sum_emod_le (a : Int) {S : Nat} (hS : 0 < S) (rs : List Nat) :
    (rs.map (fun r : Nat => a * (r : Int) % S)).sum ≤
      ((S : Int) - 1) * (rs.countP (0 < ·) : Nat) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rw [List.map_cons, List.sum_cons, List.countP_cons]
    have := Int.emod_lt_of_pos (a * (r : Int)) (show (0 : Int) < S by omega)
    by_cases hr : 0 < r
    · simp only [hr, decide_true, ↓reduceIte]
      have e : ((S : Int) - 1) * ((rs.countP (0 < ·) + 1 : Nat) : Int) =
          ((S : Int) - 1) * (rs.countP (0 < ·) : Nat) + ((S : Int) - 1) := by
        push_cast; rw [Int.mul_add, Int.mul_one]
      rw [e]
      omega
    · have h0 : r = 0 := by omega
      subst h0
      simp only [Nat.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
        Int.natCast_zero, Int.mul_zero, Int.zero_emod]
      omega

/-- The leftover is nonnegative. -/
theorem leftover_nonneg (a : Int) {rs : List Nat} (hS : 0 < rs.sum) : 0 ≤ leftover a rs := by
  have h1 := leftover_mul a rs
  have h2 := sum_emod_nonneg a hS rs
  have hS' : (0 : Int) < rs.sum := by omega
  exact le_of_mul_lt_mul_add (q := 0) (q' := leftover a rs) hS' (by rw [Int.zero_mul]; omega)

/-- The leftover is at most the number of nonzero ratios. -/
theorem leftover_le_countP (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    leftover a rs ≤ (rs.countP (0 < ·) : Nat) := by
  have h1 := leftover_mul a rs
  have h2 := sum_emod_le a hS rs
  have hS' : (0 : Int) < rs.sum := by omega
  have hc0 : (0 : Int) ≤ ((rs.countP (0 < ·) : Nat) : Int) := by omega
  generalize ((rs.countP (0 < ·) : Nat) : Int) = c at h2 hc0 ⊢
  have e : (rs.sum - 1 : Int) * c = c * rs.sum - c := by rw [Int.sub_mul, Int.one_mul, Int.mul_comm]
  exact le_of_mul_lt_mul_add hS' (by omega)

/-- The leftover is below the number of parties. -/
theorem leftover_lt_length (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    leftover a rs < rs.length := by
  have h1 := leftover_mul a rs
  have h2 := sum_emod_le a hS rs
  have h3 := leftover_nonneg a hS
  have hc : rs.countP (0 < ·) ≤ rs.length := List.countP_le_length
  have hl : 0 < rs.length := by
    rcases rs with _ | ⟨r, rs⟩
    · simp at hS
    · simp
  have hS' : (0 : Int) < rs.sum := by omega
  have m := Int.mul_le_mul_of_nonneg_left (show ((rs.countP (0 < ·) : Nat) : Int) ≤ rs.length by omega)
    (show (0 : Int) ≤ (rs.sum : Int) - 1 by omega)
  have e : ((rs.sum : Int) - 1) * (rs.length : Int) = (rs.length : Int) * rs.sum - rs.length := by
    rw [Int.sub_mul, Int.one_mul, Int.mul_comm]
  rcases Int.lt_or_le (leftover a rs) rs.length with h | h
  · exact h
  · have := mul_le_mul_of_le (Int.le_of_lt hS') h
    omega

/-- The sum of the floor shares is at most the amount. -/
theorem sum_floors_le (a : Int) {rs : List Nat} (hS : 0 < rs.sum) : (floors a rs).sum ≤ a := by
  have := leftover_nonneg a hS; unfold leftover at this; omega

/-- Reading a floor share. -/
@[simp] theorem getElem_floors (a : Int) (rs : List Nat) (i : Nat) (h : i < (floors a rs).length) :
    (floors a rs)[i] = a * (rs[i]'(by simpa [floors] using h) : Int) / rs.sum := by
  simp [floors, floorShare]

/-- There is one floor share per ratio. -/
@[simp] theorem length_floors (a : Int) (rs : List Nat) : (floors a rs).length = rs.length := by
  simp [floors]

/-! ## Remainder to the first parties -/

/-- Add one unit to each of the first `k` entries. -/
def addFirst : Nat → List Int → List Int
  | 0, xs => xs
  | _ + 1, [] => []
  | k + 1, x :: xs => (x + 1) :: addFirst k xs

/-- `addFirst` keeps the length. -/
@[simp] theorem length_addFirst (k : Nat) (xs : List Int) : (addFirst k xs).length = xs.length := by
  induction xs generalizing k with
  | nil => cases k <;> rfl
  | cons x xs ih => cases k <;> simp [addFirst, ih]

/-- `addFirst k` adds `min k length` to the sum. -/
theorem sum_addFirst (k : Nat) (xs : List Int) :
    (addFirst k xs).sum = xs.sum + (min k xs.length : Nat) := by
  induction xs generalizing k with
  | nil => cases k <;> simp [addFirst]
  | cons x xs ih =>
    cases k with
    | zero => simp [addFirst]
    | succ k =>
      simp only [addFirst, List.sum_cons, ih, List.length_cons]
      have : min (k + 1) (xs.length + 1) = min k xs.length + 1 := by omega
      rw [this]; push_cast; omega

/-- Entry `i` of `addFirst k xs` is `xs[i]` plus one if `i < k`. -/
theorem getElem_addFirst (k : Nat) (xs : List Int) (i : Nat) (h : i < (addFirst k xs).length) :
    (addFirst k xs)[i] = xs[i]'(by simpa using h) + if i < k then 1 else 0 := by
  induction xs generalizing k i with
  | nil => simp at h
  | cons x xs ih =>
    cases k with
    | zero => simp [addFirst]
    | succ k =>
      cases i with
      | zero => simp [addFirst]
      | succ i =>
        simp only [addFirst, List.getElem_cons_succ]
        rw [ih k i (by simpa using h)]
        simp

/-- Remainder to the first parties: every party receives its floor share, and the leftover
units go one each to the first parties in list order. -/
def allocFirst (a : Int) (rs : List Nat) : List Int := addFirst (leftover a rs).toNat (floors a rs)

/-- One share per ratio. -/
@[simp] theorem length_allocFirst (a : Int) (rs : List Nat) : (allocFirst a rs).length = rs.length := by
  simp [allocFirst]

/-- Share `i` of `allocFirst`: the floor share, plus one for the first `leftover` parties. -/
theorem getElem_allocFirst (a : Int) (rs : List Nat) (i : Nat) (h : i < (allocFirst a rs).length) :
    (allocFirst a rs)[i] = a * (rs[i]'(by simpa using h) : Int) / rs.sum +
      if i < (leftover a rs).toNat then 1 else 0 := by
  simp [allocFirst, getElem_addFirst]

/-- `allocFirst` conserves the amount. -/
theorem allocFirst_conserves (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    ConservesOn a (allocFirst a rs) := by
  unfold ConservesOn allocFirst
  rw [sum_addFirst]
  have h1 := leftover_nonneg a hS
  have h2 := leftover_lt_length a hS
  simp only [length_floors]
  have : min (leftover a rs).toNat rs.length = (leftover a rs).toNat := by omega
  rw [this]
  unfold leftover at *
  omega

/-- `allocFirst` gives one share per ratio. -/
theorem allocFirst_oneShareEach (a : Int) (rs : List Nat) : OneShareEachOn rs (allocFirst a rs) :=
  length_allocFirst a rs

/-- Every share of `allocFirst` is the floor share or the floor share plus one. -/
theorem allocFirst_floor_or_succ (a : Int) (rs : List Nat) (i : Nat) (h : i < (allocFirst a rs).length) :
    (allocFirst a rs)[i] = a * (rs[i]'(by simpa using h) : Int) / rs.sum ∨
      (allocFirst a rs)[i] = a * (rs[i]'(by simpa using h) : Int) / rs.sum + 1 := by
  rw [getElem_allocFirst]
  split <;> simp

/-- Every share of `allocFirst` is within `(-S, S]` of exact: below exact by less than one
unit, or above it by at most one unit. -/
theorem allocFirst_excess_bounds (a : Int) {rs : List Nat} (hS : 0 < rs.sum) (i : Nat)
    (h : i < (allocFirst a rs).length) (hr : i < rs.length) :
    -(rs.sum : Int) < excess a rs.sum (allocFirst a rs)[i] rs[i] ∧
      excess a rs.sum (allocFirst a rs)[i] rs[i] ≤ rs.sum :=
  excess_bounds_of_floor_or_succ _ hS (allocFirst_floor_or_succ a rs i h)

/-- `allocFirst` is at most one unit from exact. -/
theorem allocFirst_atMostOneUnit (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    AtMostOneUnitOn a rs (allocFirst a rs) := fun i h hr => by
  have := allocFirst_excess_bounds a hS i h hr; omega

/-- For a nonnegative amount every share of `allocFirst` is nonnegative. -/
theorem allocFirst_nonneg {a : Int} (rs : List Nat) (ha : 0 ≤ a) :
    ∀ x ∈ allocFirst a rs, 0 ≤ x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [getElem_allocFirst]
  have : 0 ≤ a * ((rs[i]'(by simpa using hi) : Nat) : Int) / rs.sum :=
    Int.ediv_nonneg (Int.mul_nonneg ha (by omega)) (by omega)
  split <;> omega

/-- Allocating nothing gives nothing to everyone. -/
theorem allocFirst_zero_amount (rs : List Nat) : ∀ x ∈ allocFirst 0 rs, x = 0 := by
  have hf : ∀ l : List Nat, (l.map (floorShare 0 rs.sum)).sum = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons r l ih => simp [floorShare, ih]
  have hl : leftover 0 rs = 0 := by unfold leftover floors; rw [hf]; rfl
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [getElem_allocFirst, hl]
  simp

/-- For a nonnegative amount the shares of `allocFirst` have the sign of the amount. -/
theorem allocFirst_sign {a : Int} (rs : List Nat) (ha : 0 ≤ a) : SignOn a (allocFirst a rs) := by
  intro x hx
  refine ⟨fun _ => allocFirst_nonneg rs ha x hx, fun h0 => ?_⟩
  have : a = 0 := by omega
  subst this
  have := allocFirst_zero_amount rs x hx
  omega

/-- Remainder to the first parties under the symmetric convention (go-money's `Allocate`
computes with truncating division and hands out units of `-1` when the leftover is negative,
which is this convention; that identification is not proved here) conserves the amount. -/
theorem symAlloc_allocFirst_conserves (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    ConservesOn a (symAlloc allocFirst a rs) :=
  symAlloc_of_forall_nonneg allocFirst rs (fun a xs => ConservesOn a xs)
    (fun _ _ h => conservesOn_neg h) (fun a _ => allocFirst_conserves a hS) a

/-- Remainder to the first parties under the symmetric convention is at most one unit from
exact. -/
theorem symAlloc_allocFirst_atMostOneUnit (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    AtMostOneUnitOn a rs (symAlloc allocFirst a rs) :=
  symAlloc_of_forall_nonneg allocFirst rs (fun a xs => AtMostOneUnitOn a rs xs)
    (fun _ _ h => atMostOneUnitOn_neg h) (fun a _ => allocFirst_atMostOneUnit a hS) a

/-- Remainder to the first parties under the symmetric convention gives shares with the sign
of the amount, for every amount. -/
theorem symAlloc_allocFirst_sign (a : Int) (rs : List Nat) :
    SignOn a (symAlloc allocFirst a rs) :=
  symAlloc_of_forall_nonneg allocFirst rs (fun a xs => SignOn a xs)
    (fun _ _ h => signOn_neg h) (fun _ ha => allocFirst_sign rs ha) a

/-- On a natural-number amount the floor share is the `Nat` quotient. -/
theorem floorShare_natCast (A S r : Nat) : floorShare (A : Int) S r = ((A * r / S : Nat) : Int) := by
  unfold floorShare; rw [Int.natCast_ediv, Int.natCast_mul]

/-- On a natural-number amount the floor shares add up to the `Nat` sum of the quotients. -/
theorem sum_floors_natCast (A : Nat) (rs : List Nat) :
    (floors (A : Int) rs).sum = ((rs.map (fun r => A * r / rs.sum)).sum : Nat) := by
  unfold floors
  generalize rs.sum = S
  induction rs with
  | nil => simp
  | cons r rs ih => simp only [List.map_cons, List.sum_cons, ih, floorShare_natCast]; push_cast; rfl

/-- On a natural-number amount the leftover is the `Nat` leftover
`A - Σ A * r / S`. -/
theorem leftover_toNat_natCast (A : Nat) (rs : List Nat) :
    (leftover (A : Int) rs).toNat = A - (rs.map (fun r => A * r / rs.sum)).sum := by
  unfold leftover; rw [sum_floors_natCast]; omega

/-- On a natural-number amount, share `i` of `allocFirst` is the `Nat` floor share plus one
for the first `A - Σ A * r / S` parties (the form of `tasks/payouts-weighted-*`). -/
theorem getElem_allocFirst_natCast (A : Nat) (rs : List Nat) (i : Nat)
    (h : i < (allocFirst (A : Int) rs).length) :
    (allocFirst (A : Int) rs)[i] = ((A * rs[i]'(by simpa using h) / rs.sum +
      if i < A - (rs.map (fun r => A * r / rs.sum)).sum then 1 else 0 : Nat) : Int) := by
  rw [getElem_allocFirst, leftover_toNat_natCast]
  have := floorShare_natCast A rs.sum (rs[i]'(by simpa using h))
  unfold floorShare at this
  rw [this]
  split <;> simp

/-- The allocation of issue 436 of moneyphp: 5 units with ratios `[0, 7, 3]` give a unit to
the zero ratio. -/
theorem allocFirst_example : allocFirst 5 [0, 7, 3] = [1, 3, 1] := by decide

/-! ## Remainder to the first parties with a nonzero ratio -/

/-- Hand out `k` units, one each, to the entries in list order whose ratio is nonzero. -/
def handOutNonzero : List (Int × Nat) → Nat → List Int
  | [], _ => []
  | (x, r) :: ps, k => if r = 0 ∨ k = 0 then x :: handOutNonzero ps k else (x + 1) :: handOutNonzero ps (k - 1)

/-- `handOutNonzero` keeps the length. -/
@[simp] theorem length_handOutNonzero (ps : List (Int × Nat)) (k : Nat) :
    (handOutNonzero ps k).length = ps.length := by
  induction ps generalizing k with
  | nil => rfl
  | cons p ps ih => obtain ⟨x, r⟩ := p; simp only [handOutNonzero]; split <;> simp [ih]

/-- `handOutNonzero` adds `min k (number of nonzero ratios)` to the sum. -/
theorem sum_handOutNonzero (ps : List (Int × Nat)) (k : Nat) :
    (handOutNonzero ps k).sum = (ps.map (·.1)).sum + (min k (ps.countP (0 < ·.2)) : Nat) := by
  induction ps generalizing k with
  | nil => simp [handOutNonzero]
  | cons p ps ih =>
    obtain ⟨x, r⟩ := p
    rw [List.countP_cons]
    simp only [handOutNonzero, List.map_cons, List.sum_cons]
    by_cases hr : 0 < r
    · have hr' : ¬ r = 0 := by omega
      simp only [decide_eq_true_eq, hr, ↓reduceIte]
      by_cases hk : k = 0
      · subst hk; simp only [hr', or_true, ↓reduceIte, List.sum_cons, ih]; omega
      · simp only [hr', hk, or_self, ↓reduceIte, List.sum_cons, ih]
        have : min k (ps.countP (0 < ·.2) + 1) = min (k - 1) (ps.countP (0 < ·.2)) + 1 := by omega
        rw [this]; push_cast; omega
    · have hr' : r = 0 := by omega
      subst hr'
      simp only [decide_eq_true_eq, Nat.lt_irrefl, ↓reduceIte, true_or, List.sum_cons, ih]
      omega

/-- Entry `i` of `handOutNonzero` is the base value or one more, and the base value when its
ratio is zero. -/
theorem getElem_handOutNonzero (ps : List (Int × Nat)) (k i : Nat)
    (h : i < (handOutNonzero ps k).length) :
    ((handOutNonzero ps k)[i] = (ps[i]'(by simpa using h)).1 ∨
      (handOutNonzero ps k)[i] = (ps[i]'(by simpa using h)).1 + 1) ∧
    ((ps[i]'(by simpa using h)).2 = 0 → (handOutNonzero ps k)[i] = (ps[i]'(by simpa using h)).1) := by
  induction ps generalizing k i with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨x, r⟩ := p
    cases i with
    | zero =>
      simp only [handOutNonzero]
      by_cases hc : r = 0 ∨ k = 0
      · simp only [hc, ↓reduceIte, List.getElem_cons_zero]; simp
      · simp only [hc, ↓reduceIte, List.getElem_cons_zero]
        exact ⟨by simp, fun h0 => absurd (Or.inl h0) hc⟩
    | succ i =>
      simp only [handOutNonzero]
      split
      · simp only [List.getElem_cons_succ]; exact ih k i (by simpa using h)
      · simp only [List.getElem_cons_succ]; exact ih (k - 1) i (by simpa using h)

/-- Remainder to the first parties with a nonzero ratio (moneyphp 3.1.3 to 3.2.0). -/
def allocFirstNonzero (a : Int) (rs : List Nat) : List Int :=
  handOutNonzero ((floors a rs).zip rs) (leftover a rs).toNat

/-- One share per ratio. -/
@[simp] theorem length_allocFirstNonzero (a : Int) (rs : List Nat) :
    (allocFirstNonzero a rs).length = rs.length := by
  simp [allocFirstNonzero]

/-- `allocFirstNonzero` conserves the amount. -/
theorem allocFirstNonzero_conserves (a : Int) {rs : List Nat} (hS : 0 < rs.sum) :
    ConservesOn a (allocFirstNonzero a rs) := by
  unfold ConservesOn allocFirstNonzero
  rw [sum_handOutNonzero]
  have hz : ((floors a rs).zip rs).map (·.1) = floors a rs := List.map_fst_zip (by simp)
  have hc : ((floors a rs).zip rs).countP (0 < ·.2) = rs.countP (0 < ·) := by
    have e := List.map_snd_zip (l₁ := floors a rs) (l₂ := rs) (by simp)
    conv => rhs; rw [← e]
    rw [List.countP_map]
    rfl
  rw [hz, hc]
  have h1 := leftover_nonneg a hS
  have h2 := leftover_le_countP a hS
  have : min (leftover a rs).toNat (rs.countP (0 < ·)) = (leftover a rs).toNat := by omega
  rw [this]
  unfold leftover at *
  omega

/-- Every share of `allocFirstNonzero` is the floor share or one more, and the floor share
(zero) for a zero ratio. -/
theorem allocFirstNonzero_floor_or_succ (a : Int) (rs : List Nat) (i : Nat)
    (h : i < (allocFirstNonzero a rs).length) :
    ((allocFirstNonzero a rs)[i] = a * (rs[i]'(by simpa using h) : Int) / rs.sum ∨
      (allocFirstNonzero a rs)[i] = a * (rs[i]'(by simpa using h) : Int) / rs.sum + 1) ∧
    (rs[i]'(by simpa using h) = 0 → (allocFirstNonzero a rs)[i] = 0) := by
  have := getElem_handOutNonzero ((floors a rs).zip rs) (leftover a rs).toNat i
    (by simpa [allocFirstNonzero] using h)
  simp only [List.getElem_zip, getElem_floors] at this
  refine ⟨this.1, fun h0 => (this.2 h0).trans ?_⟩
  rw [h0]
  simp

/-- `allocFirstNonzero` gives nothing to a zero ratio. -/
theorem allocFirstNonzero_zeroRatio (a : Int) (rs : List Nat) :
    ZeroRatioOn rs (allocFirstNonzero a rs) := fun i h _ h0 =>
  (allocFirstNonzero_floor_or_succ a rs i h).2 h0

/-- Every share of `allocFirstNonzero` is within `(-S, S]` of exact. -/
theorem allocFirstNonzero_excess_bounds (a : Int) {rs : List Nat} (hS : 0 < rs.sum) (i : Nat)
    (h : i < (allocFirstNonzero a rs).length) (hr : i < rs.length) :
    -(rs.sum : Int) < excess a rs.sum (allocFirstNonzero a rs)[i] rs[i] ∧
      excess a rs.sum (allocFirstNonzero a rs)[i] rs[i] ≤ rs.sum :=
  excess_bounds_of_floor_or_succ _ hS (allocFirstNonzero_floor_or_succ a rs i h).1

/-- For a nonnegative amount every share of `allocFirstNonzero` is nonnegative. -/
theorem allocFirstNonzero_nonneg {a : Int} (rs : List Nat) (ha : 0 ≤ a) :
    ∀ x ∈ allocFirstNonzero a rs, 0 ≤ x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have : 0 ≤ a * ((rs[i]'(by simpa using hi) : Nat) : Int) / rs.sum :=
    Int.ediv_nonneg (Int.mul_nonneg ha (by omega)) (by omega)
  rcases (allocFirstNonzero_floor_or_succ a rs i hi).1 with h | h <;> omega

end ProofForgeFin.Money
