**Proof plan.** The key computation is in `allocateNonneg`: its shares are floors plus at most one extra unit, where the extra units are recorded by the Boolean mask produced by `choose`. First isolate one successful step of `findMaxAux`: it must select an unchosen positive remainder, and setting that entry increases the mask count by one while decreasing the available-remainder count by one. Induction on the number of requested units then shows `chooseIter` adds exactly `k` mask units, provided at least `k` positive remainders are available. Such availability holds for `k = A - floors.sum` because each remainder is `< S` and the remainders sum to `k * S` (via the existing division/modulus identity). A separate zip-sum lemma turns the mask count into the sum of the allocated shares, giving `allocateNonneg A ratios ratios.sum` sum `A`; the final conservation proof then only needs to unfold `allocate`, split on the sign of `amount`, and use `sum` of a negated list in the negative case.

```lean
theorem plan1_chooseIter_step_properties (rems : List Nat) (mask : List Bool)
    (hlen : mask.length = rems.length)
    (h : 0 < (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0) rems mask).sum) :
    ∃ idx val, findMaxAux rems mask 0 none = some (idx, val) ∧
      mask[idx]? = some false ∧ 0 < val ∧
      ((mask.set idx true).map (fun b => if b then (1 : Nat) else 0)).sum =
        (mask.map (fun b => if b then (1 : Nat) else 0)).sum + 1 ∧
      (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
        rems (mask.set idx true)).sum + 1 =
        (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0) rems mask).sum := by sorry

theorem plan1_chooseIter_mask_sum_add (rems : List Nat) (mask : List Bool) (k : Nat)
    (hlen : mask.length = rems.length)
    (hk : k ≤ (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0) rems mask).sum) :
    ((chooseIter rems mask k).map (fun b => if b then (1 : Nat) else 0)).sum =
      (mask.map (fun b => if b then (1 : Nat) else 0)).sum + k := by sorry

theorem plan1_zipWith_share_sum (floors : List Nat) (mask : List Bool)
    (hlen : mask.length = floors.length) :
    (List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0) floors mask).sum =
      (floors.sum : Int) + ((mask.map (fun b => if b then (1 : Nat) else 0)).sum : Int) := by sorry

theorem plan1_k_le_available_initial (A : Nat) (ratios : List Nat) (hS : 0 < ratios.sum) :
    A - (ratios.map (fun r => (A * r) / ratios.sum)).sum ≤
      (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
        (ratios.map (fun r => (A * r) % ratios.sum))
        (List.replicate (ratios.map (fun r => (A * r) % ratios.sum)).length false)).sum := by sorry

theorem plan1_allocateNonneg_sum_eq (A : Nat) (ratios : List Nat) (hS : 0 < ratios.sum) :
    (allocateNonneg A ratios ratios.sum).sum = (A : Int) := by sorry
```