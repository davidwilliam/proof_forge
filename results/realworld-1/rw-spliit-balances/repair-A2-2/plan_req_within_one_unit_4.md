**Proof plan**

For a non-negative amount, `allocateNonneg` gives each party either its floor `A * r / S` or that floor plus `1`. The extra unit is only chosen among indices whose remainder `(A * r) % S` is positive, because `findMaxAux` skips zero remainders and `chooseIter` only sets such an index. Writing `A * r = (A * r / S) * S + (A * r) % S`, the excess is then `δ * S - (A * r) % S` with `δ ∈ {0,1}` and, when `δ = 1`, the remainder is in `(0, S)`, so the excess lies in `(-S, S)`. For a negative amount the shares are exactly the negations of the non-negative shares for `amount.natAbs`, and the excess likewise negates, preserving the same bound.

```lean
theorem plan4_chooseIter_true_rem_pos (rems : List Nat) (mask : List Bool) (k : Nat)
    (i : Nat) (hlen : mask.length = rems.length)
    (h : (chooseIter rems mask k)[i]? = some true) :
    mask[i]? = some true ∨ ∃ v, rems[i]? = some v ∧ 0 < v := by sorry

theorem plan4_choose_true_rem_pos (rems : List Nat) (k : Nat) (i : Nat)
    (h : (choose rems k)[i]? = some true) :
    ∃ v, rems[i]? = some v ∧ 0 < v := by sorry

theorem plan4_allocateNonneg_getElem (A : Nat) (ratios : List Nat) (S : Nat)
    (i : Nat) (r : Nat) (hr : ratios[i]? = some r) :
    ∃ b : Bool, (allocateNonneg A ratios S)[i]? =
      some (((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) ∧
      (b = true → 0 < (A * r) % S) := by sorry

theorem plan4_floor_succ_excess_bounds (A S r : Nat) (hS : 0 < S) (b : Bool)
    (hb : b = true → 0 < (A * r) % S) :
    -(S : Int) < (((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) * (S : Int)
        - (A : Int) * (r : Int) ∧
    (((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) * (S : Int)
        - (A : Int) * (r : Int) < (S : Int) := by sorry

theorem plan4_within_one_allocateNonneg (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    WithinOneUnitOn (A : Int) ratios (allocateNonneg A ratios ratios.sum) := by sorry

theorem plan4_within_one_allocateNonneg_neg (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    WithinOneUnitOn (-(A : Int)) ratios
      ((allocateNonneg A ratios ratios.sum).map (fun x => -x)) := by sorry
```