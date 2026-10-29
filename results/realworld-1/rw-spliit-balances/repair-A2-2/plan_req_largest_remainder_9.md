Short proof plan: analyse the non‑negative Hamilton allocation pointwise.
A positive excess forces the party to have been rounded up and a negative
excess forces rounding down; its excess is then `S - rem` respectively
`-rem`. Hence the required inequality reduces to `rem_j ≤ rem_i` whenever
`i` was chosen by `choose/chooseIter` and `j` was not. Prove this greedy
maximality by induction on `chooseIter`, using the existing `findMaxAux`
maximality lemmas, specialise it to the initially all‑false mask, obtain
largest‑remainder for `allocateNonneg`, transport it through negation of
amount and shares, and finally split on the sign of `amount` in `allocate`.

```lean
theorem plan9_chooseIter_dominates (rems : List Nat) (mask : List Bool)
    (k i j : Nat) (vi vj : Nat)
    (hlen : mask.length = rems.length)
    (hi_mask : mask[i]? = some false)
    (hi_rem : rems[i]? = some vi)
    (hj_rem : rems[j]? = some vj)
    (hj_pos : 0 < vj)
    (hi_final : (chooseIter rems mask k)[i]? = some true)
    (hj_final : (chooseIter rems mask k)[j]? = some false) :
    vj ≤ vi := by sorry

theorem plan9_choose_dominates (rems : List Nat) (k i j : Nat) (vi vj : Nat)
    (hi_rem : rems[i]? = some vi)
    (hj_rem : rems[j]? = some vj)
    (hj_pos : 0 < vj)
    (hi_final : (choose rems k)[i]? = some true)
    (hj_final : (choose rems k)[j]? = some false) :
    vj ≤ vi := by sorry

theorem plan9_largest_remainder_nonneg (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    LargestRemainderOn (A : Int) ratios (allocateNonneg A ratios ratios.sum) := by sorry

theorem plan9_largest_remainder_neg (A : Int) (ratios : List Nat)
    (shares : List Int)
    (h : LargestRemainderOn A ratios shares) :
    LargestRemainderOn (-A) ratios (shares.map (fun x => -x)) := by sorry

theorem plan9_largest_remainder_of_allocate (amount : Int) (ratios : List Nat)
    (shares : List Int)
    (h : allocate amount ratios = some shares) :
    LargestRemainderOn amount ratios shares := by sorry
```