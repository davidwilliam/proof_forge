import ProofForgeFin
/-!
# Demonstration: the weighted-share arithmetic of `payouts-weighted-b1` with the library

The definitions `natSum`, `floorShare`, `leftover` and `weightedShare` are copied without
change from `tasks/payouts-weighted-b1/spec/WeightedPayout/Spec.lean`, and `sumRange` from
`tasks/payouts-weighted-b1/reference/SolutionA.lean`. The task files are not imported or
modified.

The reference solution proves three arithmetic facts behind REQ-CONSERVATION and
REQ-ROUNDING-BOUND in its section "Arithmetic of weighted shares": `leftover_lt` (the floors add
up to at most the amount and the leftover is below the number of recipients), `sum_weighted`
(the weighted shares add up to the amount) and `weighted_bound` (every share is within one
cent of its exact pro-rata share), with eight helper lemmas about `sumRange`, `natSum` and
floor sums (about 125 lines). Here the weighted shares are the library's `allocFirst`
(remainder to the first parties) on a natural-number amount (`weightedShare_eq`), and the three
facts are `leftover_nonneg`, `leftover_lt_length`, `allocFirst_conserves` and
`excess_bounds_of_floor_or_succ`.
-/

namespace ProofForgeFinDemo.Money.WeightedPayout

/-! ## Copied from `spec/WeightedPayout/Spec.lean` and `reference/SolutionA.lean` -/

/-- Sum of a list of naturals. -/
def natSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + natSum xs

/-- Exact pro-rata share `amount * w / W`, rounded down. -/
def floorShare (amount W w : Nat) : Nat := amount * w / W

/-- Cents left over after every weight receives its floor share. -/
def leftover (amount : Nat) (ws : List Nat) : Nat :=
  amount - natSum (ws.map (floorShare amount (natSum ws)))

/-- Share of the recipient at position `i`: the floor share of its weight, plus one extra
cent for the first `leftover amount ws` positions in list order. -/
def weightedShare (amount : Nat) (ws : List Nat) (i : Nat) : Nat :=
  floorShare amount (natSum ws) (ws.getD i 0) + if i < leftover amount ws then 1 else 0

/-- Sum of `F 0 + ... + F (n-1)`, recursing on the first index. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, F => F 0 + sumRange n (fun i => F (i + 1))

/-! ## The task's definitions are the library's -/

/-- The task's `natSum` is `List.sum`. -/
theorem natSum_eq (l : List Nat) : natSum l = l.sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [natSum, ih]

/-- The reference's `sumRange` is the sum of a list built from indices. -/
theorem sumRange_eq (n : Nat) (F : Nat → Int) : sumRange n F = ((List.range n).map F).sum := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih => rw [sumRange, ih, List.range_succ_eq_map]; simp [List.map_map]; rfl

/-- The task's leftover is the library's leftover on a natural-number amount. -/
theorem leftover_eq (A : Nat) (ws : List Nat) :
    leftover A ws = (ProofForgeFin.Money.leftover (A : Int) ws).toNat := by
  rw [ProofForgeFin.Money.leftover_toNat_natCast]
  simp only [leftover, natSum_eq]
  rfl

/-- The weighted shares are the library's remainder-to-the-first allocation. -/
theorem weightedShare_eq (A : Nat) (ws : List Nat) (i : Nat) (h : i < ws.length) :
    (weightedShare A ws i : Int) = (ProofForgeFin.Money.allocFirst (A : Int) ws)[i]'(by simpa using h) := by
  rw [ProofForgeFin.Money.getElem_allocFirst_natCast]
  simp only [weightedShare, floorShare, leftover, natSum_eq, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h, Option.getD_some]
  rfl

/-! ## The three arithmetic facts of the reference solution -/

/-- Positive weights of a nonempty list have a positive sum. -/
theorem natSum_pos (ws : List Nat) (hl : 0 < ws.length) (hp : ∀ w ∈ ws, 0 < w) : 0 < ws.sum := by
  cases ws with
  | nil => simp at hl
  | cons x xs => have := hp x (by simp); simp only [List.sum_cons]; omega

/-- `leftover_lt` of the reference: `sum_floors_le` and `leftover_lt_length`. -/
theorem leftover_lt (A : Nat) (ws : List Nat) (hl : 0 < ws.length) (hp : ∀ w ∈ ws, 0 < w) :
    natSum (ws.map (floorShare A (natSum ws))) ≤ A ∧ leftover A ws < ws.length := by
  have hS := natSum_pos ws hl hp
  have h1 := ProofForgeFin.Money.sum_floors_le (A : Int) hS
  have h2 := ProofForgeFin.Money.leftover_lt_length (A : Int) hS
  have h3 := ProofForgeFin.Money.leftover_nonneg (A : Int) hS
  rw [ProofForgeFin.Money.sum_floors_natCast] at h1
  rw [leftover_eq]
  have e : ws.map (floorShare A ws.sum) = ws.map (fun r => A * r / ws.sum) := rfl
  simp only [natSum_eq, e]
  omega

/-- `sum_weighted` of the reference: `allocFirst_conserves`. -/
theorem sum_weighted (A : Nat) (ws : List Nat) (hl : 0 < ws.length) (hp : ∀ w ∈ ws, 0 < w) :
    sumRange ws.length (fun i => (weightedShare A ws i : Int)) = A := by
  have hS := natSum_pos ws hl hp
  rw [sumRange_eq]
  have : (List.range ws.length).map (fun i => (weightedShare A ws i : Int)) =
      ProofForgeFin.Money.allocFirst (A : Int) ws := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      exact weightedShare_eq A ws i (by simpa using h1)
  rw [this]
  exact ProofForgeFin.Money.allocFirst_conserves (A : Int) hS

/-- `weighted_bound` of the reference: `excess_bounds_of_floor_or_succ`. -/
theorem weighted_bound (A : Nat) (ws : List Nat) (i : Nat) (hW : 0 < natSum ws) :
    (weightedShare A ws i : Int) * (natSum ws : Int) ≤ ((A * ws.getD i 0 : Nat) : Int) + (natSum ws : Int) ∧
    ((A * ws.getD i 0 : Nat) : Int) < (weightedShare A ws i : Int) * (natSum ws : Int) + (natSum ws : Int) := by
  have h : (weightedShare A ws i : Int) = (A : Int) * (ws.getD i 0 : Int) / (natSum ws : Int) ∨
      (weightedShare A ws i : Int) = (A : Int) * (ws.getD i 0 : Int) / (natSum ws : Int) + 1 := by
    unfold weightedShare floorShare
    rw [← Int.natCast_mul, ← Int.natCast_ediv]
    split <;> simp
  have := ProofForgeFin.Money.excess_bounds_of_floor_or_succ (ws.getD i 0) hW h
  unfold ProofForgeFin.Money.excess at this
  push_cast
  omega

end ProofForgeFinDemo.Money.WeightedPayout
