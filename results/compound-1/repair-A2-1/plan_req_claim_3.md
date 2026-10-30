The candidate's `claimComp` is a bind-chain of borrow update/distribution, then supply update/distribution, then `grantCompInternal`. The earlier `plan2_*` lemmas already characterize each update+distribute pair as `BorrowDistributed`/`SupplyDistributed`, so the claim proof reduces to: decompose the bind-chain, identify `grantCompInternal` with the spec's `grant`, and reassemble the pieces as the existential `Claimed`. The following helpers isolate exactly those steps in dependency order.

```lean
theorem plan3_grantCompInternal_eq_grant (s : St) (who : Account) :
    grantCompInternal s who = grant s who := by sorry

theorem plan3_claimComp_decomp (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    ∃ m1 m2,
      (∃ t, updateCompBorrowIndex s = some t ∧
            distributeBorrowerComp t who = some m1) ∧
      (∃ u, updateCompSupplyIndex m1 = some u ∧
            distributeSupplierComp u who = some m2) ∧
      s' = grantCompInternal m2 who := by sorry

theorem plan3_claimed_of_distributed (s : St) (who : Account) (m1 m2 : St)
    (hB : BorrowDistributed s who m1) (hS : SupplyDistributed m1 who m2) :
    Claimed s who (grant m2 who) := by sorry

theorem plan3_claimComp_claimed (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    Claimed s who s' := by sorry
```