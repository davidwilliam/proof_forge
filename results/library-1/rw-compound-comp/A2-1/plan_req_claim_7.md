**Proof plan.** A claim unfolds into four successful steps: updating the borrow index, distributing borrower COMP, updating the supply index, and distributing supplier COMP, followed by the grant. The borrow pair is exactly `BorrowDistributed s who`, the supply pair applied to that post-borrow state is exactly `SupplyDistributed _ who`, and the candidate's `grantCompInternal` is the spec's `grant`. Packaging those two distributed states as the witnesses in `Claimed` then proves `req_claim` by decomposing the `Option` bind, applying the steps lemma, and rewriting the grant.

```lean
theorem plan7_claim_decomp (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') :
    ∃ b1 b2 u2 fin,
      updateCompBorrowIndex s = some b1 ∧
      distributeBorrowerComp b1 who = some b2 ∧
      updateCompSupplyIndex b2 = some u2 ∧
      distributeSupplierComp u2 who = some fin ∧
      s' = grantCompInternal fin who := by sorry

theorem plan7_grantCompInternal_eq_grant (s : St) (who : Account) :
    grantCompInternal s who = grant s who := by sorry

theorem plan7_claim_steps_distributed
    (s b1 b2 u2 fin : St) (who : Account)
    (hbUp : updateCompBorrowIndex s = some b1)
    (hbDist : distributeBorrowerComp b1 who = some b2)
    (hsUp : updateCompSupplyIndex b2 = some u2)
    (hsDist : distributeSupplierComp u2 who = some fin) :
    BorrowDistributed s who b2 ∧ SupplyDistributed b2 who fin := by sorry

theorem plan7_claim_of_raw_steps
    (s b1 b2 u2 fin s' : St) (who : Account)
    (hbUp : updateCompBorrowIndex s = some b1)
    (hbDist : distributeBorrowerComp b1 who = some b2)
    (hsUp : updateCompSupplyIndex b2 = some u2)
    (hsDist : distributeSupplierComp u2 who = some fin)
    (hfin : s' = grantCompInternal fin who) :
    Claimed s who s' := by sorry
```