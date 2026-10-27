(1) Proof plan: Prove the target by induction on `l`, generalizing `k`. The nil case is by `simp`. For `x :: xs`, decompose the left sum with `sumOver_cons`: the head index is `0`, while indices in the tail are successor indices in `xs`. Shift those tail indices from `k + (i + 1)` to `k + 1 + i`, apply the induction hypothesis at `k + 1`, and decompose the right-hand range sum at its head. The helpers below isolate the index calculations, the range decomposition, and the tail-sum congruence.

(2)
```lean
theorem plan1_indexOf_cons_ne (x : AccountId) (xs : List AccountId) (a : AccountId)
    (h : a ≠ x) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by sorry

theorem plan1_fairShare_shift (amount n k i : Nat) :
    fairShare amount n (k + (i + 1)) = fairShare amount n (k + 1 + i) := by sorry

theorem plan1_sumOver_range_succ (m : Nat) (f : Nat → Int) :
    sumOver (List.range (m + 1)) f
      = f 0 + sumOver (List.range m) (fun i => f (i + 1)) := by sorry

theorem plan1_indexOf_cons_self (x : AccountId) (xs : List AccountId) :
    indexOf? (x :: xs) x = some 0 := by sorry

theorem plan1_sumOver_shift_cons (x : AccountId) (xs : List AccountId) (hx : x ∉ xs)
    (amount n k : Nat) :
    sumOver xs (fun a => ((match indexOf? (x :: xs) a with
      | some i => fairShare amount n (k + i)
      | none => 0 : Nat) : Int))
      = sumOver xs (fun a => ((match indexOf? xs a with
      | some i => fairShare amount n (k + 1 + i)
      | none => 0 : Nat) : Int)) := by sorry
```