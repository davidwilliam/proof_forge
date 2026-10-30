A specialized `Option.bind` success lemma avoids the failed generic rewrite. First show that the supply-speed update succeeds in a consistent state and that any resulting state still has its borrow side no later than its current block. The borrow-speed update then succeeds in that state, so unfolding `setCompSpeedInternal` and the `setSpeeds` case of `comptroller` finishes the proof.

```lean
theorem plan2_bind_isSome_true (m : Option St) (f : St → Option St)
    (hm : m.isSome = true)
    (hf : ∀ t, m = some t → (f t).isSome = true) :
    (Option.bind m f).isSome = true := by sorry

theorem plan2_setSupplySpeed_isSome (s : St) (a : Nat) (h : Consistent s) :
    (setSupplySpeed s a).isSome = true := by sorry

theorem plan2_setSupplySpeed_borrow_le (s s' : St) (a : Nat)
    (h : Consistent s) (hs : setSupplySpeed s a = some s') :
    s'.borrowState.block ≤ s'.blockNumber := by sorry

theorem plan2_setBorrowSpeed_isSome (s : St) (b : Nat)
    (h : s.borrowState.block ≤ s.blockNumber) :
    (setBorrowSpeed s b).isSome = true := by sorry

theorem plan2_setCompSpeedInternal_isSome (s : St) (a b : Nat) (h : Consistent s) :
    (setCompSpeedInternal s a b).isSome = true := by sorry
```