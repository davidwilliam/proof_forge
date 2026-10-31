**Proof plan.** Split the single-operation bound by the mechanism of the operation: supply-balance operations, borrow-balance operations, claims, speed changes, block advancement, and COMP drips. Each helper states the per-account potential bound for its operation family under the invariant. The main theorem then performs case analysis on the operation and applies the corresponding helper directly; the emitted term is retained explicitly so no arithmetic rewriting is needed in the final step.

```lean
theorem plan2_potentialTo_supply_ops (sp : Nat × Nat) (s : St) (who : Account) :
    td0_Inv sp s →
    (∀ a x, td0_potentialTo (exec comptroller s (.mint a x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.mint a x)) ∧
    (∀ a x, td0_potentialTo (exec comptroller s (.redeem a x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.redeem a x)) ∧
    (∀ src dst x, td0_potentialTo (exec comptroller s (.transfer src dst x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.transfer src dst x)) := by
  sorry

theorem plan2_potentialTo_borrow_ops (sp : Nat × Nat) (s : St) (who : Account) :
    td0_Inv sp s →
    (∀ a x, td0_potentialTo (exec comptroller s (.borrow a x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.borrow a x)) ∧
    (∀ a x, td0_potentialTo (exec comptroller s (.repay a x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.repay a x)) := by
  sorry

theorem plan2_potentialTo_claim (sp : Nat × Nat) (s : St) (a who : Account) :
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s (.claim a)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.claim a) := by
  sorry

theorem plan2_potentialTo_setSpeeds (sp : Nat × Nat) (s : St) (a b : Nat)
    (who : Account) :
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s (.setSpeeds a b)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.setSpeeds a b) := by
  sorry

theorem plan2_potentialTo_advance (sp : Nat × Nat) (s : St) (k : Nat)
    (who : Account) :
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s (.advance k)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.advance k) := by
  sorry

theorem plan2_potentialTo_drip (sp : Nat × Nat) (s : St) (x : Nat)
    (who : Account) :
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s (.drip x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.drip x) := by
  sorry

theorem td0_exec_potentialTo_le : ∀ (sp : Nat × Nat) (s : St) (op : Op) (who : Account),
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s op) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp op := by
  intro sp s op who h
  cases op with
  | mint a x =>
      exact (plan2_potentialTo_supply_ops sp s who h).1 a x
  | redeem a x =>
      exact (plan2_potentialTo_supply_ops sp s who h).2.1 a x
  | transfer src dst x =>
      exact (plan2_potentialTo_supply_ops sp s who h).2.2 src dst x
  | borrow a x =>
      exact (plan2_potentialTo_borrow_ops sp s who h).1 a x
  | repay a x =>
      exact (plan2_potentialTo_borrow_ops sp s who h).2 a x
  | claim a =>
      exact plan2_potentialTo_claim sp s a who h
  | setSpeeds a b =>
      exact plan2_potentialTo_setSpeeds sp s a b who h
  | advance k =>
      exact plan2_potentialTo_advance sp s k who h
  | drip x =>
      exact plan2_potentialTo_drip sp s x who h
```