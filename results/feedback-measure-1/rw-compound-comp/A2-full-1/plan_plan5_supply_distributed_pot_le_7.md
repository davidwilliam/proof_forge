(1) Proof plan: Split a supply distribution into two stages. First, `accrueSide` updates the supply index: each account’s scaled pending supply can increase by at most its supply times the index increase, while the total index increase, weighted by `totalSupply`, is bounded by the previously unindexed COMP emission; because the updated side is then at the current block, its unindexed term drops to zero, so the potential does not increase. Second, distributing to `who` transfers that account’s pending supply into `accrued`: the scaled credit is no larger than the account’s previous scaled pending supply, its new pending supply is zero, and borrow pending, other accounts, and unindexed terms are unchanged, so the potential again does not increase. Composing the two stages gives `Pot s' ≤ Pot s`.

(2)
```lean
theorem plan7_creditFor_scaled_le (units start idx : Nat) :
    doubleScale * creditFor units start idx ≤ units * (idx - start) := by
  sorry

theorem plan7_accrueSide_index_mul_le (sd : Side) (now total : Nat) :
    total * ((accrueSide sd now total).index - sd.index) ≤
      (now - sd.block) * sd.speed * doubleScale := by
  sorry

theorem plan7_pendSupply_step_le (a : Acct) (oldIdx newIdx : Nat)
    (h : oldIdx ≤ newIdx) :
    a.supply * (newIdx - accrualStart a.supplierIndex newIdx) ≤
      a.supply * (oldIdx - accrualStart a.supplierIndex oldIdx) +
        a.supply * (newIdx - oldIdx) := by
  sorry

theorem plan7_pot_accrueSupply_le (s : St) :
    Pot { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ≤
      Pot s := by
  sorry

theorem plan7_pot_distributeSupply_le (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index) :
    Pot { s with
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := s.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex s.supplyState.index)
            s.supplyState.index } } ≤
      Pot s := by
  sorry
```