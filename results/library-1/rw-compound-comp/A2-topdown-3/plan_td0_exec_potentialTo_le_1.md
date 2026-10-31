**Proof plan.** Split `td0_exec_potentialTo_le` by operation. Policy hooks, claims, and speed changes are reduced through their already-stated effect lemmas to the first four potential bounds below: distributing one side can move at most the previously unindexed emission for that side into pending/credited amounts, because an account’s units are bounded by the corresponding market total, while grants only move accrued COMP into the wallet. After a hook, the touched account is settled at the current index and the side is at the current block; the next two lemmas show that the subsequent supply or borrow balance change therefore creates neither new pending rewards nor new unindexed rewards. Refused operations and `drip` leave the relevant quantities unchanged, and `advance k` is then a direct arithmetic bound using the invariant speeds and `emittedBy (advance k) = k * (sp.1 + sp.2)`.

```lean
theorem plan1_supply_distributed_potentialTo_le (sp : Nat × Nat) (s : St)
    (tgt who : Account) (s' : St) :
    td0_Inv sp s → SupplyDistributed s tgt s' →
      td0_potentialTo s' who ≤ td0_potentialTo s who := by sorry

theorem plan1_borrow_distributed_potentialTo_le (sp : Nat × Nat) (s : St)
    (tgt who : Account) (s' : St) :
    td0_Inv sp s → BorrowDistributed s tgt s' →
      td0_potentialTo s' who ≤ td0_potentialTo s who := by sorry

theorem plan1_claimed_potentialTo_le (sp : Nat × Nat) (s : St)
    (tgt who : Account) (s' : St) :
    td0_Inv sp s → Claimed s tgt s' →
      td0_potentialTo s' who ≤ td0_potentialTo s who := by sorry

theorem plan1_speeds_set_potentialTo_le (sp : Nat × Nat) (s : St)
    (a b : Nat) (who : Account) (s' : St) :
    td0_Inv sp s → SpeedsSet s a b s' →
      td0_potentialTo s' who ≤ td0_potentialTo s who := by sorry

theorem plan1_supply_change_potentialTo_le (s : St) (tgt who x : Nat) :
    s.supplyState.block = s.blockNumber →
    accrualStart (s.acct tgt).supplierIndex s.supplyState.index =
      s.supplyState.index →
    td0_potentialTo
        (s.withAcct tgt fun a => { a with supply := a.supply + x }) who ≤
      td0_potentialTo s who ∧
    td0_potentialTo
        (s.withAcct tgt fun a => { a with supply := a.supply - x }) who ≤
      td0_potentialTo s who := by sorry

theorem plan1_borrow_change_potentialTo_le (s : St) (tgt who x : Nat) :
    s.borrowState.block = s.blockNumber →
    accrualStart (s.acct tgt).borrowerIndex s.borrowState.index =
      s.borrowState.index →
    td0_potentialTo
        (s.withAcct tgt fun a => { a with borrow := a.borrow + x }) who ≤
      td0_potentialTo s who ∧
    td0_potentialTo
        (s.withAcct tgt fun a => { a with borrow := a.borrow - x }) who ≤
      td0_potentialTo s who := by sorry
```