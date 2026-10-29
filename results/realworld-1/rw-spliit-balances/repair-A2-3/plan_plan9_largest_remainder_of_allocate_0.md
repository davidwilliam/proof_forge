**Proof plan.** For a nonnegative amount, each share is a floor plus possibly one, where the added unit is recorded by `choose`. If share `i` has positive `excess`, it must have received a unit; if share `j` has negative `excess`, it must not have. Its excesses are respectively `S - rem i` and `-rem j`, so the required bound reduces to `rem j ≤ rem i`, which is exactly the dominance property of repeatedly choosing a largest remaining remainder. The negative-amount case follows by negating all shares and excesses, then splitting on the sign of `amount` and rewriting with `Int.natAbs`.

```lean
theorem plan0_lr_allocateNonneg_getElem (A : Nat) (ratios : List Nat) (S : Nat)
    (i : Nat) (r : Nat) (hr : ratios[i]? = some r) :
    ∃ b : Bool,
      (choose (ratios.map (fun x => (A * x) % S))
        (A - (ratios.map (fun x => (A * x) / S)).sum))[i]? = some b ∧
      (allocateNonneg A ratios S)[i]? =
        some (((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) ∧
      (b = true → 0 < (A * r) % S) := by sorry

theorem plan0_lr_choose_dominates (rems : List Nat) (k i j : Nat) (vi vj : Nat)
    (hi_rem : rems[i]? = some vi) (hj_rem : rems[j]? = some vj)
    (hj_pos : 0 < vj)
    (hi_final : (choose rems k)[i]? = some true)
    (hj_final : (choose rems k)[j]? = some false) :
    vj ≤ vi := by sorry

theorem plan0_lr_excess_formula (A S r : Nat) (b : Bool) :
    excess (A : Int) S (((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) r =
      if b then (S : Int) - ((A * r % S : Nat) : Int)
      else -((A * r % S : Nat) : Int) := by sorry

theorem plan0_lr_pair_bound (A : Nat) (ratios : List Nat) (hS : 0 < ratios.sum)
    (i : Nat) (hi : i < (allocateNonneg A ratios ratios.sum).length)
    (hri : i < ratios.length)
    (j : Nat) (hj : j < (allocateNonneg A ratios ratios.sum).length)
    (hrj : j < ratios.length)
    (hpos : 0 < excess (A : Int) ratios.sum
      (allocateNonneg A ratios ratios.sum)[i] ratios[i])
    (hneg : excess (A : Int) ratios.sum
      (allocateNonneg A ratios ratios.sum)[j] ratios[j] < 0) :
    excess (A : Int) ratios.sum (allocateNonneg A ratios ratios.sum)[i] ratios[i] -
      excess (A : Int) ratios.sum (allocateNonneg A ratios ratios.sum)[j] ratios[j] ≤
      (ratios.sum : Int) := by sorry

theorem plan0_lr_allocateNonneg (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    LargestRemainderOn (A : Int) ratios (allocateNonneg A ratios ratios.sum) := by sorry

theorem plan0_lr_neg_transfer (A : Int) (ratios : List Nat) (shares : List Int)
    (h : LargestRemainderOn A ratios shares) :
    LargestRemainderOn (-A) ratios (shares.map (fun x => -x)) := by sorry
```