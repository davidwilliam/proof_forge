(1) The supply hook is an `Option.bind` of two steps, so prove it cannot fail by separating the concerns: a consistent state bounds every account's recorded supplier index, including the out-of-range account whose record is `noAcct`; bringing the supply index up to date succeeds from the block bound, never decreases the index, and does not touch accounts; from any recorded index not above the current index, `accrualStart` is also not above it, which is exactly the check `distributeSupplierComp` performs; and a bind of succeeding steps succeeds. The generic `getD` lemma isolates the only list induction needed.

(2)
```lean
theorem plan0_getD_supplierIndex_le (l : List Acct) (idx who : Nat)
    (h : ∀ a ∈ l, a.supplierIndex ≤ idx) :
    (l.getD who noAcct).supplierIndex ≤ idx := by sorry

theorem plan0_accrualStart_le (recorded index : Nat) (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by sorry

theorem plan0_updateCompSupplyIndex_step (s : St) (who : Account)
    (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ s₁, updateCompSupplyIndex s = some s₁ ∧
      s.supplyState.index ≤ s₁.supplyState.index ∧
      (s₁.acct who).supplierIndex = (s.acct who).supplierIndex := by sorry

theorem plan0_distributeSupplierComp_isSome (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index) :
    (distributeSupplierComp s who).isSome := by sorry

theorem plan0_option_bind_isSome {α β : Type} (m : Option α) (f : α → Option β)
    (hm : m.isSome) (hf : ∀ a, m = some a → (f a).isSome) :
    (Option.bind m f).isSome := by sorry
```