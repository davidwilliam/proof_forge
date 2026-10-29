Allocate by writing each share as its floor plus at most one bonus unit. The chosen mask therefore has exactly `k = A - floors.sum` true entries: whenever a bonus remains to distribute, `findMaxAux` finds an unchosen positive remainder, choosing it increases the mask count by one and decreases the available positive remainders by one. The initial `k` is bounded by the number of positive remainders because the remainders sum to `k * S` and each is `< S`. Finally, the zip sum is the floor sum plus the mask count, and `floors.sum + k = A`.

```lean
theorem plan3_findMaxAux_general (rems : List Nat) (mask : List Bool)
    (start : Nat) (best : Option (Nat × Nat))
    (hlen : mask.length = rems.length)
    (h : 0 < (List.zipWith
      (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems mask).sum) :
    ∃ idx val, findMaxAux rems mask start best = some (idx, val) ∧
      0 < val ∧
      ((∃ bi br, best = some (bi, br) ∧ idx = bi ∧ val = br) ∨
       (∃ rel, idx = start + rel ∧ rel < mask.length ∧
         mask[rel]? = some false ∧ rems[rel]? = some val)) := by sorry

theorem plan3_mask_count_set_true (mask : List Bool) (idx : Nat)
    (h : mask[idx]? = some false) :
    ((mask.set idx true).map (fun b => if b then (1 : Nat) else 0)).sum =
      (mask.map (fun b => if b then (1 : Nat) else 0)).sum + 1 := by sorry

theorem plan3_avail_set_true (rems : List Nat) (mask : List Bool)
    (idx : Nat) (val : Nat)
    (hlen : mask.length = rems.length)
    (hmask : mask[idx]? = some false)
    (hrem : rems[idx]? = some val)
    (hval : 0 < val) :
    (List.zipWith
      (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems (mask.set idx true)).sum + 1 =
      (List.zipWith
        (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
        rems mask).sum := by sorry

theorem plan3_chooseIter_count_add (rems : List Nat) (mask : List Bool) (k : Nat)
    (hlen : mask.length = rems.length)
    (hk : k ≤ (List.zipWith
      (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems mask).sum) :
    ((chooseIter rems mask k).map (fun b => if b then (1 : Nat) else 0)).sum =
      (mask.map (fun b => if b then (1 : Nat) else 0)).sum + k := by sorry

theorem plan3_choose_count_initial (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    ((choose (ratios.map (fun r => (A * r) % ratios.sum))
      (A - (ratios.map (fun r => (A * r) / ratios.sum)).sum)).map
        (fun b => if b then (1 : Nat) else 0)).sum =
      A - (ratios.map (fun r => (A * r) / ratios.sum)).sum := by sorry

theorem plan3_zipWith_share_sum (floors : List Nat) (mask : List Bool)
    (hlen : mask.length = floors.length) :
    (List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0)
      floors mask).sum =
      (floors.sum : Int) +
        ((mask.map (fun b => if b then (1 : Nat) else 0)).sum : Int) := by sorry
```