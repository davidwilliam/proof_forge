import ProofForgeFin.Money.Allocation
import ProofForgeFin.Ledger
/-!
# Equal splits of signed amounts

Splitting an amount `a` (possibly negative) into `n > 0` parts that are as equal as possible,
under the two conventions in deployed code:

* `splitEven a n` (floor convention): every part is `a / n` (Euclidean division, rounded
  toward negative infinity) and the first `a % n` parts (the remainder lies in `[0, n)`)
  receive one more unit. For a natural-number amount this is `Ledger.equalSplit`
  (`splitEven_natCast`).
* `splitSym a n` (symmetric convention): the split of `|a|`, negated for a negative amount.
  This is go-money's `Money.Split` from 1.0.6 on: the quotient `a.tdiv n` (Go's truncating
  division) for every part, and the `|a.tmod n|` leftover units handed one each to the first
  parts, as `-1` for a negative amount and `+1` otherwise (`splitSym_eq_tdiv`).

Both conserve the amount, give every part within strictly less than one unit of `a / n`
(`-n < x * n - a < n`), give parts with the sign of the amount, and give parts that differ by
at most one unit; the larger parts come first (`splitEven`) or the parts of largest magnitude
come first (`splitSym`).
-/

namespace ProofForgeFin.Money

/-- The sum of `q` plus an indicator of the first `m` indices, over `n` indices. -/
theorem sum_range_add_indicator (q : Int) (m : Nat) : ∀ n,
    ((List.range n).map (fun i => q + if i < m then (1 : Int) else 0)).sum = (n : Int) * q + (min m n : Nat) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero]
    have e : ((n + 1 : Nat) : Int) * q = (n : Int) * q + q := by push_cast; rw [Int.add_mul, Int.one_mul]
    rw [e]
    by_cases h : n < m
    · simp only [h, ↓reduceIte]
      have : min m (n + 1) = min m n + 1 := by omega
      rw [this]; push_cast; omega
    · simp only [h, ↓reduceIte]
      have : min m (n + 1) = min m n := by omega
      rw [this]; omega

/-! ## The floor convention -/

/-- `a` split into `n` parts: `a / n` each, and one more unit for the first `a % n` parts. -/
def splitEven (a : Int) (n : Nat) : List Int :=
  (List.range n).map fun p => a / (n : Int) + if p < (a % (n : Int)).toNat then 1 else 0

/-- A split has `n` parts. -/
@[simp] theorem length_splitEven (a : Int) (n : Nat) : (splitEven a n).length = n := by
  simp [splitEven]

/-- Part `i` of `splitEven a n`. -/
theorem getElem_splitEven (a : Int) (n i : Nat) (h : i < (splitEven a n).length) :
    (splitEven a n)[i] = a / (n : Int) + if i < (a % (n : Int)).toNat then 1 else 0 := by
  simp [splitEven]

/-- A split conserves the amount. -/
theorem sum_splitEven (a : Int) {n : Nat} (hn : 0 < n) : (splitEven a n).sum = a := by
  unfold splitEven
  rw [sum_range_add_indicator]
  have hn' : (0 : Int) < n := by omega
  have h1 : a % (n : Int) = a - (n : Int) * (a / n) := Int.emod_def a n
  have h2 := Int.emod_nonneg a (show (n : Int) ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos a hn'
  have : min (a % (n : Int)).toNat n = (a % (n : Int)).toNat := by omega
  rw [this, Int.toNat_of_nonneg h2]
  omega

/-- Every part is `a / n`, or `a / n + 1` when `n` does not divide `a`. -/
theorem mem_splitEven {a x : Int} {n : Nat} (hx : x ∈ splitEven a n) :
    x = a / (n : Int) ∨ (x = a / (n : Int) + 1 ∧ a % (n : Int) ≠ 0) := by
  unfold splitEven at hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  by_cases hi : i < (a % (n : Int)).toNat
  · right; simp only [hi, ↓reduceIte]; exact ⟨trivial, by omega⟩
  · left; simp [hi]

/-- Every part is less than one unit from the exact share: `-n < x * n - a < n`. -/
theorem splitEven_within {a x : Int} {n : Nat} (hn : 0 < n) (hx : x ∈ splitEven a n) :
    -(n : Int) < x * n - a ∧ x * n - a < n := by
  have hn' : (0 : Int) < n := by omega
  have h1 : a % (n : Int) = a - a / n * n := by rw [Int.emod_def, Int.mul_comm]
  have h2 := Int.emod_nonneg a (show (n : Int) ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos a hn'
  rcases mem_splitEven hx with rfl | ⟨rfl, h⟩
  · omega
  · rw [Int.add_mul, Int.one_mul]; omega

/-- The parts of a split have the sign of the amount. -/
theorem splitEven_sign {a x : Int} {n : Nat} (hn : 0 < n) (hx : x ∈ splitEven a n) :
    (0 ≤ a → 0 ≤ x) ∧ (a ≤ 0 → x ≤ 0) := by
  have hw := splitEven_within hn hx
  have hn' : (0 : Int) < n := by omega
  constructor
  · intro ha; exact le_of_mul_lt_mul_add (q := 0) (q' := x) hn' (by rw [Int.zero_mul]; omega)
  · intro ha; exact le_of_mul_lt_mul_add (q := x) (q' := 0) hn' (by rw [Int.zero_mul]; omega)

/-- Any two parts differ by at most one unit. -/
theorem splitEven_le_add_one {a x y : Int} {n : Nat} (hx : x ∈ splitEven a n)
    (hy : y ∈ splitEven a n) : x ≤ y + 1 := by
  rcases mem_splitEven hx with h | h <;> rcases mem_splitEven hy with h' | h' <;> omega

/-- Larger parts come first: the parts are nonincreasing along the list. -/
theorem splitEven_antitone (a : Int) (n : Nat) {i j : Nat} (hij : i ≤ j)
    (hj : j < (splitEven a n).length) :
    (splitEven a n)[j] ≤ (splitEven a n)[i]'(Nat.lt_of_le_of_lt hij hj) := by
  rw [getElem_splitEven, getElem_splitEven]
  split <;> split <;> omega

/-- The floor-convention split of a natural-number amount is `Ledger.equalSplit`. -/
theorem splitEven_natCast (a : Nat) {n : Nat} (hn : 0 < n) :
    splitEven (a : Int) n = (Ledger.equalSplit a n).map (fun x : Nat => (x : Int)) := by
  apply List.ext_getElem
  · simp [Ledger.length_equalSplit a hn]
  · intro i h1 h2
    rw [getElem_splitEven]
    simp only [List.getElem_map, Ledger.equalSplit, List.getElem_append, List.length_replicate,
      List.getElem_replicate]
    have e1 : ((a : Int) / (n : Int)) = ((a / n : Nat) : Int) := (Int.natCast_ediv a n).symm
    have e2 : ((a : Int) % (n : Int)) = ((a % n : Nat) : Int) := (Int.natCast_emod a n).symm
    rw [e1, e2]
    split <;> split <;> push_cast <;> omega

/-! ## The symmetric convention -/

/-- The symmetric split: `splitEven` of `|a|`, negated for a negative amount. -/
def splitSym (a : Int) (n : Nat) : List Int :=
  if 0 ≤ a then splitEven a n else (splitEven (-a) n).map Neg.neg

/-- go-money's `Money.Split` (1.0.6 and later) is the symmetric split: the truncated quotient
for every part, and the absolute truncated remainder handed out as units of the amount's sign
to the first parts. -/
theorem splitSym_eq_tdiv (a : Int) (n : Nat) :
    splitSym a n = (List.range n).map fun p =>
      a.tdiv n + if p < (a.tmod n).natAbs then (if a < 0 then -1 else 1) else 0 := by
  unfold splitSym splitEven
  by_cases ha : 0 ≤ a
  · simp only [ha, ↓reduceIte, Int.tdiv_eq_ediv_of_nonneg ha, Int.tmod_eq_emod_of_nonneg ha,
      show ¬ a < 0 by omega]
    apply List.map_congr_left
    intro p hp
    have h2 := Int.emod_nonneg a (b := (n : Int))
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at hp
    · have := h2 (by omega)
      have e : (a % (n : Int)).natAbs = (a % (n : Int)).toNat := by omega
      rw [e]
  · simp only [ha, ↓reduceIte, show a < 0 by omega, List.map_map]
    apply List.map_congr_left
    intro p _
    have t1 : a.tdiv n = -((-a) / (n : Int)) := by
      rw [show a.tdiv n = -((-a).tdiv n) by rw [Int.neg_tdiv, Int.neg_neg],
        Int.tdiv_eq_ediv_of_nonneg (by omega)]
    have t2 : (a.tmod n).natAbs = ((-a) % (n : Int)).toNat := by
      rw [show a.tmod n = -((-a).tmod n) by rw [Int.neg_tmod, Int.neg_neg],
        Int.tmod_eq_emod_of_nonneg (by omega)]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp; omega
      · have := Int.emod_nonneg (-a) (show (n : Int) ≠ 0 by omega)
        omega
    simp only [Function.comp_apply, t1, t2]
    split <;> omega

/-- A symmetric split has `n` parts. -/
@[simp] theorem length_splitSym (a : Int) (n : Nat) : (splitSym a n).length = n := by
  unfold splitSym; split <;> simp

/-- A symmetric split conserves the amount. -/
theorem sum_splitSym (a : Int) {n : Nat} (hn : 0 < n) : (splitSym a n).sum = a := by
  unfold splitSym
  split
  · exact sum_splitEven a hn
  · rw [sum_map_neg, sum_splitEven _ hn, Int.neg_neg]

/-- The symmetric split is odd in the amount. -/
theorem splitSym_neg {a : Int} (n : Nat) (ha : a ≠ 0) :
    splitSym (-a) n = (splitSym a n).map Neg.neg := by
  unfold splitSym
  by_cases h : 0 ≤ a
  · simp only [show ¬ 0 ≤ -a by omega, ↓reduceIte, Int.neg_neg, h]
  · simp only [show 0 ≤ -a by omega, ↓reduceIte, h, List.map_map]
    have : (Neg.neg ∘ Neg.neg : Int → Int) = id := by funext x; simp
    rw [this, List.map_id]

/-- Every part of a symmetric split is less than one unit from the exact share. -/
theorem splitSym_within {a x : Int} {n : Nat} (hn : 0 < n) (hx : x ∈ splitSym a n) :
    -(n : Int) < x * n - a ∧ x * n - a < n := by
  unfold splitSym at hx
  split at hx
  · exact splitEven_within hn hx
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have := splitEven_within hn hy
    rw [Int.neg_mul]; omega

/-- The parts of a symmetric split have the sign of the amount. -/
theorem splitSym_sign {a x : Int} {n : Nat} (hn : 0 < n) (hx : x ∈ splitSym a n) :
    (0 ≤ a → 0 ≤ x) ∧ (a ≤ 0 → x ≤ 0) := by
  have hw := splitSym_within hn hx
  have hn' : (0 : Int) < n := by omega
  constructor
  · intro ha; exact le_of_mul_lt_mul_add (q := 0) (q' := x) hn' (by rw [Int.zero_mul]; omega)
  · intro ha; exact le_of_mul_lt_mul_add (q := x) (q' := 0) hn' (by rw [Int.zero_mul]; omega)

/-- Any two parts of a symmetric split differ by at most one unit. -/
theorem splitSym_le_add_one {a x y : Int} {n : Nat} (hx : x ∈ splitSym a n)
    (hy : y ∈ splitSym a n) : x ≤ y + 1 := by
  unfold splitSym at hx hy
  split at hx
  · simp only [*, ↓reduceIte] at hy; exact splitEven_le_add_one hx hy
  · simp only [*, ↓reduceIte] at hy
    obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    have := splitEven_le_add_one hy' hx'
    omega

/-- go-money 1.0.3 panicked on `Split(-101, 4)`; the symmetric split gives four parts. -/
theorem splitSym_example : splitSym (-101) 4 = [-26, -25, -25, -25] := by decide

end ProofForgeFin.Money
