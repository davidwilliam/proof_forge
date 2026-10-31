import ProofForgeFin
/-!
# Tactic tests: `lib_defs`, and the sum lemmas it opens

Specifications restate library definitions: a sum over accounts by `List.foldr`, a function
update, a ceiling division, a fixed-point product with a named scale. The definitions below are
written the way specifications write them (generic names; no task file is copied). After
`lib_defs` the library's lemmas apply to them by name (and `exact?` finds them). A recursive restatement
(`sumRec`) is not definitionally equal to a fold; `ProofForgeFin.Sums.eq_sum_map_of_eqns`
identifies it by its equations, and `lib_defs` rewrites it with them. The last example checks
that `lib_defs` fails cleanly when nothing applies.
-/

namespace ProofForgeFinDemo.Tactic.LibDefs

open ProofForgeFin

/-- Sum over a list of accounts, as specifications write it. -/
def total {α : Type} (l : List α) (f : α → Int) : Int :=
  l.foldr (fun a acc => f a + acc) 0

/-- Point update of a function on account numbers. -/
def setAt {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α :=
  fun j => if j = k then v else f j

/-- Ceiling division as deployed code writes it. -/
def divUp (a b : Nat) : Nat := (a + b - 1) / b

/-- A named fixed-point scale. -/
def SCALE : Nat := 1000000

/-- A fixed-point product at that scale, rounded down. -/
def mulScaled (a b : Nat) : Nat := a * b / SCALE

/-- A sum restated by recursion. -/
def sumRec : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumRec xs

/-- Overwriting one account changes the total by the new balance minus the old. -/
example (l : List Nat) (hl : l.Nodup) (f : Nat → Int) (k : Nat) (hk : k ∈ l) (v : Int) :
    total l (setAt f k v) = total l f - f k + v := by
  lib_defs
  exact Machine.sumOver_upd hl f hk v

/-- A delta on one account, written with an `if` as specifications write it. -/
example (l : List Nat) (hl : l.Nodup) (f : Nat → Int) (x : Nat) (d : Int) :
    total l (fun a => f a + if a = x then d else 0) = total l f + if x ∈ l then d else 0 := by
  lib_defs
  exact Sums.sumOver_add_ite hl f x d

/-- A restated ceiling division meets the library's ceiling bounds. -/
example (a b : Nat) (h : 0 < b) : a ≤ divUp a b * b := by
  lib_defs
  exact le_ceilDiv_mul a b h

/-- A restated fixed-point product, in a hypothesis, is the library's. -/
example (a b c : Nat) (h : mulScaled a b ≤ c) : a * b / SCALE ≤ c := by
  lib_defs
  exact h

/-- A recursive restatement of a sum, identified by its equations. -/
theorem sumRec_eq (l : List Nat) : sumRec l = l.sum := by
  simpa using Sums.eq_sum_map_of_eqns (F := sumRec) id rfl (fun _ _ => rfl) l

/-- Setting one entry of a list of balances, with the old entry added back. -/
example (l : List Nat) (i x : Nat) (h : i < l.length) :
    sumRec (l.set i x) + l[i] = sumRec l + x := by
  rw [sumRec_eq, sumRec_eq]
  exact Sums.sum_set_add l i x h

/-- A part rounded down plus one leftover unit is within one unit of the exact value. -/
example (a W : Nat) (hW : 0 < W) : (a / W + 1) * W ≤ a + W ∧ a < (a / W + 1) * W + W :=
  Accrual.floor_add_bit_within a W 1 hW (Nat.le_refl 1)

/-- `lib_defs` rewrites a sum restated by recursion into `List.sum`, after which the library
lemma applies. -/
example (l : List Nat) (i x : Nat) (h : i < l.length) :
    sumRec (l.set i x) + l[i] = sumRec l + x := by
  lib_defs
  exact Sums.sum_set_add l i x h

/-- A label, which no library definition equals. -/
def label (n : Nat) : String := toString n

/-- `lib_defs` fails when no definition of the goal equals a library definition or is a sum by
recursion, and leaves the goal unchanged. -/
example (n : Nat) : label n = label n := by
  fail_if_success lib_defs
  rfl

end ProofForgeFinDemo.Tactic.LibDefs
