Short proof plan: decompose `setCompSpeedInternal` into its supply-speed and borrow-speed steps. Show that the supply step leaves the borrow side, block number, and accounts unchanged, so the borrow block condition and `totalBorrows` transfer from the intermediate state back to the original state. Combine the known state equations for the two steps (via `plan4_setSupplySpeed_state` and `plan4_setBorrowSpeed_state_proof`) to get the exact final-state equation required by `SpeedsSet`, and supply the two block conditions from the existing `plan4_*_block` helpers.

```lean
theorem plan5_setCompSpeedInternal_steps (s : St) (sup bor : Nat) (s' : St)
    (h : setCompSpeedInternal s sup bor = some s') :
    ∃ sI, setSupplySpeed s sup = some sI ∧ setBorrowSpeed sI bor = some s' := by sorry

theorem plan5_setSupplySpeed_preserves (s : St) (sup : Nat) (sI : St)
    (h : setSupplySpeed s sup = some sI) :
    sI.borrowState = s.borrowState ∧ sI.blockNumber = s.blockNumber ∧
      sI.accts = s.accts ∧ totalBorrows sI = totalBorrows s := by sorry

theorem plan5_borrow_block_after_supply (s : St) (sup bor : Nat) (sI s' : St)
    (hI : setSupplySpeed s sup = some sI)
    (hB : setBorrowSpeed sI bor = some s')
    (hne : s.borrowState.speed ≠ bor) :
    s.borrowState.block ≤ s.blockNumber := by sorry

theorem plan5_setCompSpeedInternal_final_state (s : St) (sup bor : Nat) (sI s' : St)
    (hI : setSupplySpeed s sup = some sI)
    (hB : setBorrowSpeed sI bor = some s') :
    s' = { s with
      supplyState := if s.supplyState.speed = sup then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by sorry

theorem plan5_speedsSet_of_steps (s : St) (sup bor : Nat) (sI s' : St)
    (hI : setSupplySpeed s sup = some sI)
    (hB : setBorrowSpeed sI bor = some s') :
    SpeedsSet s sup bor s' := by sorry
```