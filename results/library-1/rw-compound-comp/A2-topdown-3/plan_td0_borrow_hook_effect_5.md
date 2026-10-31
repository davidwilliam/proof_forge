(1) Proof plan: Decompose `comptroller s (.borrowHook who)` into `updateCompBorrowIndex` followed by `distributeBorrowerComp`. Use the already-proved `plan3_updateBorrow_accrue` to rewrite the first step as `accrueSide` over `totalBorrows s`. Prove a standalone specification for `distributeBorrowerComp`, identifying its conditional start index with `accrualStart` and its `mulDouble` credit with `creditFor`. Finally, transport that specification across the preceding `accrueSide` state update—whose accounts are unchanged—to obtain exactly `BorrowDistributed s who s'`.

(2)
```lean
theorem plan5_borrower_start_eq (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by sorry

theorem plan5_accrue_borrow_acct_eq (s : St) (who : Account) :
    ({ s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who =
      s.acct who := by sorry

theorem plan5_accrue_borrow_withAcct_eq (s : St) (who : Account) (f : Acct → Acct) :
    ({ s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who f =
    { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who f } := by sorry

theorem plan5_distributeBorrowerComp_spec (s : St) (who : Account) (s' : St) :
    distributeBorrowerComp s who = some s' →
      accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
          s.borrowState.index ∧
        s' = s.withAcct who fun a =>
          { a with
            borrowerIndex := s.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex s.borrowState.index)
              s.borrowState.index } := by sorry

theorem plan5_borrowHook_decomp (s : St) (who : Account) (s' : St) :
    comptroller s (.borrowHook who) = some s' →
      ∃ t, updateCompBorrowIndex s = some t ∧
        distributeBorrowerComp t who = some s' := by sorry

theorem plan5_borrowDistributed_of_steps (s : St) (who : Account) (t s' : St) :
    s.borrowState.block ≤ s.blockNumber →
      t = { s with
        borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } →
        distributeBorrowerComp t who = some s' →
          BorrowDistributed s who s' := by sorry
```