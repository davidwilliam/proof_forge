**Proof plan.** `claimComp` is a four-step `Option` bind: update the borrow index, distribute borrower COMP, update the supply index, distribute supplier COMP, and finally apply `grantCompInternal`. Decompose a successful claim into those intermediate states, reuse the existing one-side characterisations (`aux_borrowProofB`, `tmp_supply_proofB`) to get `BorrowDistributed` and `SupplyDistributed`, convert `grantCompInternal` to the spec's `grant`, and assemble the two witnesses required by `Claimed`. The claim case of `comptroller` is definitionally `claimComp`, which closes `req_claim`.

```lean
theorem plan3_claimComp_steps (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    ∃ b1 m1 b2 m2,
      updateCompBorrowIndex s = some b1 ∧
      distributeBorrowerComp b1 who = some m1 ∧
      updateCompSupplyIndex m1 = some b2 ∧
      distributeSupplierComp b2 who = some m2 ∧
      s' = grantCompInternal m2 who := by sorry

theorem plan3_borrowDistributed_of_steps (s : St) (who : Account) (m1 b1 : St)
    (hU : updateCompBorrowIndex s = some b1)
    (hD : distributeBorrowerComp b1 who = some m1) :
    BorrowDistributed s who m1 := by sorry

theorem plan3_supplyDistributed_of_steps (s : St) (who : Account) (m2 b2 : St)
    (hU : updateCompSupplyIndex s = some b2)
    (hD : distributeSupplierComp b2 who = some m2) :
    SupplyDistributed s who m2 := by sorry

theorem plan3_grantCompInternal_eq_grant (s : St) (who : Account) :
    grantCompInternal s who = grant s who := by sorry

theorem plan3_claimed_of_claimComp (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    Claimed s who s' := by sorry
```