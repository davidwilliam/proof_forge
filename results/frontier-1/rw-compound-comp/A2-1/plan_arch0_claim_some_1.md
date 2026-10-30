(1) **Proof plan.** A claim performs the borrow distribution first, then the supply distribution, then a total grant operation. The supply step does not need the full consistency of the intermediate state: it only needs the supply side's block bound and the account's recorded supplier index bound. The borrow step leaves the supply state untouched and does not change the account's supplier index, so those two supply-side facts survive it. Prove: (a) the borrow step succeeds from a consistent state and preserves the two supply-side facts needed next; (b) the supply step succeeds from just those two facts (via the already-proved update-step monotonicity, `accrualStart` bound, and distribute-succeeds lemmas); (c) if both distribution steps succeed, the claim; which is exactly those steps followed by the total `grantCompInternal`; succeeds. Then `arch0_claim_some` chains (a), (b), (c).

(2)

```lean
theorem plan1_borrow_step_preserves_supply (s : St) (who : Account) (h : Consistent s) :
    ∃ s₁, Option.bind (updateCompBorrowIndex s) (fun t => distributeBorrowerComp t who) = some s₁ ∧
      s₁.supplyState.block ≤ s₁.blockNumber ∧
      (s₁.acct who).supplierIndex ≤ s₁.supplyState.index := by sorry

theorem plan1_supply_step_some (s : St) (who : Account)
    (hblock : s.supplyState.block ≤ s.blockNumber)
    (hidx : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    ∃ s₂, Option.bind (updateCompSupplyIndex s) (fun t => distributeSupplierComp t who) = some s₂ := by sorry

theorem plan1_claim_isSome_of_steps (s : St) (who : Account) (s₁ s₂ : St)
    (h₁ : Option.bind (updateCompBorrowIndex s) (fun t => distributeBorrowerComp t who) = some s₁)
    (h₂ : Option.bind (updateCompSupplyIndex s₁) (fun t => distributeSupplierComp t who) = some s₂) :
    (comptroller s (.claim who)).isSome := by sorry
```