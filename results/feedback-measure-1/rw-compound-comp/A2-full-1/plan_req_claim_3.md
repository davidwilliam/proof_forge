**Proof plan.** A claim is the candidate's sequential composition: update the borrow index, distribute borrower rewards, update the supply index, distribute supplier rewards, then grant. Split it at exactly those seams: prove that an update-then-distribute pair on one side yields that side's `*Distributed` relation (mirroring the already-proved hook lemmas, via the `update*Index = accrueSide` and `distribute*Comp` spec lemmas), prove the candidate's `grantCompInternal` is the spec's `grant` (the two modify-functions agree on the account actually modified, by modify-congruence at `getD`), then chain the three steps through the bind-decomposition of `claimComp` to assemble `Claimed`. The target theorem is then a direct application.

```lean
theorem plan3_borrow_step_distributed (s : St) (who : Account) (b1 d1 : St)
    (hU : updateCompBorrowIndex s = some b1)
    (hD : distributeBorrowerComp b1 who = some d1) :
    BorrowDistributed s who d1 := by sorry

theorem plan3_supply_step_distributed (s : St) (who : Account) (s1 d2 : St)
    (hU : updateCompSupplyIndex s = some s1)
    (hD : distributeSupplierComp s1 who = some d2) :
    SupplyDistributed s who d2 := by sorry

theorem plan3_grantCompInternal_eq_grant (s : St) (who : Account) :
    grantCompInternal s who = grant s who := by sorry

theorem plan3_claim_claimed (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') :
    Claimed s who s' := by sorry
```