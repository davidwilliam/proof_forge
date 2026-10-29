**Proof plan.** For non-negative amounts, write each floor as `An * r / S` with remainder `An * r % S`. Summing the division identity over all ratios shows the remainders are exactly divisible by `S`, so the floors plus `R = rems.sum / S` recover `An`. The sorted index list is a duplicate-free permutation of `range n`, hence its first `R` entries contribute exactly `R` extra units, one per bumped party. This gives conservation for `sharesNonneg`; the negative case follows by negating every share.

```lean
theorem plan0_floor_rem_sum (An S : Nat) (l : List Nat) :
    (l.map (fun r => An * r % S)).sum + S * (l.map (fun r => An * r / S)).sum
      = An * l.sum := by sorry

theorem plan0_range_map_getD (f : Nat → Nat) (l : List Nat) :
    (List.range l.length).map (fun i => f (l.getD i 0)) = l.map f := by sorry

theorem plan0_sortedIdxs_props (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup ∧ ∀ i : Nat, i ∈ sortedIdxs rems n ↔ i < n := by sorry

theorem plan0_sum_shareAt (An S : Nat) (ratios : List Nat) (bset : List Nat)
    (hnd : bset.Nodup) (hmem : ∀ i : Nat, i ∈ bset → i < ratios.length) :
    ((List.range ratios.length).map (fun i => shareAt An S ratios bset i)).sum
      = ((ratios.map (fun r => An * r / S)).sum : Int) + (bset.length : Int) := by sorry

theorem plan0_floors_add_quotient (An : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    (ratios.map (fun r => An * r / ratios.sum)).sum
        + (ratios.map (fun r => An * r % ratios.sum)).sum / ratios.sum = An
      ∧ (ratios.map (fun r => An * r % ratios.sum)).sum / ratios.sum
          ≤ ratios.length := by sorry

theorem plan0_sharesNonneg_sum (An : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    (sharesNonneg An ratios).sum = (An : Int) := by sorry
```