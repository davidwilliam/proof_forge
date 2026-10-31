(1) Proof plan: Split the goal by whether `who` is inside the account list. For an in-bounds index, `List.modify` at `who` followed by `getD who` returns `f` applied to the original account, so `hf` preserves its `supplierIndex`. For an out-of-bounds index, `List.modify` is the identity, so the account is unchanged. The remaining components follow because `St.withAcct` only replaces `accts`, leaving `supplyState` and `blockNumber` definitionally unchanged.

(2)
```lean
theorem plan1_modify_getD_self (l : List Acct) (n : Nat) (f : Acct → Acct)
    (h : n < l.length) :
    (l.modify n f).getD n noAcct = f (l.getD n noAcct) := by sorry

theorem plan1_modify_eq_self_of_le (l : List Acct) (n : Nat) (f : Acct → Acct)
    (h : l.length ≤ n) :
    l.modify n f = l := by sorry

theorem plan1_getD_modify_supplierIndex (l : List Acct) (n : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify n f).getD n noAcct).supplierIndex =
      (l.getD n noAcct).supplierIndex := by sorry

theorem plan1_withAcct_proj (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).supplyState = s.supplyState ∧
      (s.withAcct who f).blockNumber = s.blockNumber := by sorry
```