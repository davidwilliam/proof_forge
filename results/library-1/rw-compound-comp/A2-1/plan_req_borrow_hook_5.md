Short proof plan: mirror the proved supply-hook argument on the borrow side. First identify the implementation's adjusted borrower index with `accrualStart`, then characterize `distributeBorrowerComp` as exactly the credit recorded in `BorrowDistributed`. Next characterize `updateCompBorrowIndex` as `accrueSide` on the borrow state, transfer that characterization back to the original state, and combine the update and distribution steps. Finally decompose a borrow-hook call into those two steps, so `req_borrow_hook` follows directly.

```lean
theorem plan5_borrower_adjusted_eq_accrualStart (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by sorry

theorem plan5_distributeBorrower_char (mid : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp mid who = some s') :
    accrualStart (mid.acct who).borrowerIndex mid.borrowState.index ≤
        mid.borrowState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by sorry

theorem plan5_updateBorrow_accrueSide (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem plan5_borrow_eq_transfer (s mid s' : St) (who : Account)
    (hmid : mid = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) })
    (heq : s' = { mid with
      accts := mid.accts.modify who fun a =>
        { a with
          borrowerIndex := mid.borrowState.index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex mid.borrowState.index)
            mid.borrowState.index } }) :
    s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by sorry

theorem plan5_borrowDistributed_of_steps (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by sorry

theorem plan5_borrowHook_decomp (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    ∃ mid, updateCompBorrowIndex s = some mid ∧ distributeBorrowerComp mid who = some s' := by sorry
```