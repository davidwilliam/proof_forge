(1) Proof plan: Decompose `claimComp` into its borrow update/distribution, then its supply update/distribution, then the grant. The first two phases are exactly the borrow and supply hooks, so reuse their known characterizations as `BorrowDistributed` and `SupplyDistributed`. Convert the implementation's `grantCompInternal` to the specification's `grant`, then assemble the three phases into the existential defining `Claimed`.

(2)
```lean
theorem plan3_claim_decompose (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') :
    ∃ m1 m2, comptroller s (.borrowHook who) = some m1 ∧
      comptroller m1 (.supplyHook who) = some m2 ∧
      s' = grantCompInternal m2 who := by sorry

theorem plan3_grantCompInternal_eq_grant (s : St) (who : Account) :
    grantCompInternal s who = grant s who := by sorry

theorem plan3_borrowHook_distributed (s : St) (who : Account) (m1 : St)
    (h : comptroller s (.borrowHook who) = some m1) :
    BorrowDistributed s who m1 := by sorry

theorem plan3_supplyHook_distributed (s : St) (who : Account) (m2 : St)
    (h : comptroller s (.supplyHook who) = some m2) :
    SupplyDistributed s who m2 := by sorry

theorem plan3_claimed_of_steps (s : St) (who : Account) (m1 m2 s' : St)
    (hb : BorrowDistributed s who m1)
    (hs : SupplyDistributed m1 who m2)
    (hg : s' = grantCompInternal m2 who) :
    Claimed s who s' := by sorry
```