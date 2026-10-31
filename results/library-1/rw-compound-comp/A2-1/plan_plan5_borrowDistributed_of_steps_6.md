(1) Proof plan: Decompose `BorrowDistributed s who s'` into its block bound, starting-index bound, and state-equality components. The update step preserves accounts and replaces the borrow state by `accrueSide`; transfer the characterization of `distributeBorrowerComp` along these equalities to obtain the remaining two components, then combine them.

(2)
```lean
theorem plan6_borrow_update_accts (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by sorry

theorem plan6_borrow_mid_acct (s mid : St) (who : Account)
    (h : updateCompBorrowIndex s = some mid) :
    mid.acct who = s.acct who := by sorry

theorem plan6_borrow_mid_state (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by sorry

theorem plan6_borrow_start_le (s mid s' : St) (who : Account)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by sorry

theorem plan6_borrow_eq (s mid s' : St) (who : Account)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by sorry
```