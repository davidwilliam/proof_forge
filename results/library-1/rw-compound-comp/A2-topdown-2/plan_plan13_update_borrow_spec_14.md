Short proof plan: isolate the block-number bound forced by `subChecked`, then split on whether the block delta, borrow speed, and total borrows are positive. In the all-positive case the update's `fraction` calculation is exactly the index increase in `accrueSide`; in the zero-total and zero-speed cases both sides only advance the block, and in the zero-delta case the state is unchanged up to that same block update.

```lean
theorem plan14_block_le_of_update (s : St) (t : St) :
    updateCompBorrowIndex s = some t →
    s.borrowState.block ≤ s.blockNumber := by sorry

theorem plan14_eq_of_pos (s : St) (t : St) :
    0 < s.blockNumber - s.borrowState.block →
    0 < s.borrowState.speed →
    0 < totalBorrows s →
    updateCompBorrowIndex s = some t →
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem plan14_eq_of_zero_total (s : St) (t : St) :
    0 < s.blockNumber - s.borrowState.block →
    0 < s.borrowState.speed →
    totalBorrows s = 0 →
    updateCompBorrowIndex s = some t →
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem plan14_eq_of_zero_speed (s : St) (t : St) :
    0 < s.blockNumber - s.borrowState.block →
    s.borrowState.speed = 0 →
    updateCompBorrowIndex s = some t →
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem plan14_eq_of_zero_delta (s : St) (t : St) :
    s.blockNumber - s.borrowState.block = 0 →
    updateCompBorrowIndex s = some t →
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem plan13_update_borrow_spec (s : St) (t : St) :
    updateCompBorrowIndex s = some t →
    s.borrowState.block ≤ s.blockNumber ∧
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  intro h
  refine ⟨plan14_block_le_of_update s t h, ?_⟩
  by_cases hd : 0 < s.blockNumber - s.borrowState.block
  · by_cases hs : 0 < s.borrowState.speed
    · by_cases ht : 0 < totalBorrows s
      · exact plan14_eq_of_pos s t hd hs ht h
      · have ht0 : totalBorrows s = 0 := by omega
        exact plan14_eq_of_zero_total s t hd hs ht0 h
    · have hs0 : s.borrowState.speed = 0 := by omega
      exact plan14_eq_of_zero_speed s t hd hs0 h
  · have hd0 : s.blockNumber - s.borrowState.block = 0 := by omega
    exact plan14_eq_of_zero_delta s t hd0 h
```