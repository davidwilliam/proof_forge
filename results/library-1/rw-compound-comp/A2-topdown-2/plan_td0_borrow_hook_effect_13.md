Mirror the already-proved supply hook: decompose the borrow hook’s `bind` into the borrow-index update and the borrower distribution, transport the accrual-start bound from the intermediate state to the original state, and recombine the two state updates into the exact form required by `BorrowDistributed`.

```lean
theorem plan13_update_borrow_spec (s : St) (t : St) :
    updateCompBorrowIndex s = some t →
    s.borrowState.block ≤ s.blockNumber ∧
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  sorry

theorem plan13_distribute_borrow_spec (t : St) (who : Account) (s' : St) :
    distributeBorrowerComp t who = some s' →
    accrualStart (t.acct who).borrowerIndex t.borrowState.index ≤ t.borrowState.index ∧
    s' = { t with accts := t.accts.modify who fun a =>
      { a with
        borrowerIndex := t.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex t.borrowState.index) t.borrowState.index } } := by
  sorry

theorem plan13_start_le_of_update (s t : St) (who : Account) :
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } →
    accrualStart (t.acct who).borrowerIndex t.borrowState.index ≤ t.borrowState.index →
    accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  sorry

theorem plan13_combine_borrow (s t s' : St) (who : Account) :
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } →
    s' = { t with accts := t.accts.modify who fun a =>
      { a with
        borrowerIndex := t.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex t.borrowState.index) t.borrowState.index } } →
    s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
  sorry

theorem td0_borrow_hook_effect : ∀ (s : St) (who : Account) (s' : St),
    comptroller s (.borrowHook who) = some s' → BorrowDistributed s who s' := by
  intro s who s' h
  have hb : (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) = some s' := h
  obtain ⟨t, ht, hd⟩ := plan12_bind_some _ _ _ hb
  obtain ⟨hblock, ht_eq⟩ := plan13_update_borrow_spec s t ht
  obtain ⟨hstart_t, hd_eq⟩ := plan13_distribute_borrow_spec t who s' hd
  have hstart := plan13_start_le_of_update s t who ht_eq hstart_t
  unfold BorrowDistributed
  exact ⟨hblock, hstart, plan13_combine_borrow s t s' who ht_eq hd_eq⟩
```