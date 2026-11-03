(1) Proof plan: Split `BorrowDistributed` into accruing the borrow index and then settling `who`. The already-proved `plan7_pot_accrueBorrow_le4` bounds the accrual step by `Pot s`. For the settlement step, the credited amount scaled by `doubleScale` is at most the account's borrow pending, the account's post-settlement pending is zero, and supply pending is unchanged; summing over the modified account list therefore does not increase `Pot`. Chaining the two steps gives `Pot s' ≤ Pot s`.

(2)
```lean
theorem plan8_accrualStart_self (I : Nat) : accrualStart I I = I := by sorry

theorem plan8_borrow_credit_scaled_le (units start idx : Nat) :
    doubleScale * creditFor units start idx ≤ units * (idx - start) := by sorry

theorem plan8_borrow_term_le (a : Acct) (I : Nat) :
    (a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex I) I + a.wallet) * doubleScale +
      a.borrow * (I - accrualStart I I) ≤
      (a.accrued + a.wallet) * doubleScale +
        a.borrow * (I - accrualStart a.borrowerIndex I) := by sorry

theorem plan8_sumPendSupply_modify_borrow (s : St) (who : Account) :
    sumPendSupply { s with accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index)
          s.borrowState.index } } =
      sumPendSupply s := by sorry

theorem plan8_pot_distribute_borrow_le (s : St) (who : Account) :
    Pot { s with accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index)
          s.borrowState.index } } ≤
      Pot s := by sorry

theorem plan8_pot_borrowDistributed_le_accrued (s : St) (who : Account) (s' : St)
    (h : BorrowDistributed s who s') :
    Pot s' ≤ Pot { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry
```