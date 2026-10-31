The missing step is a global potential argument. Let `credited + td0_owed` measure COMP already paid or accrued plus COMP still pending in the indices and not yet indexed. Each individual call cannot increase this potential: updating an index converts unindexed emission into pending rewards without creating COMP, distributing converts an account's pending rewards into accrued COMP without increasing their sum, and granting merely moves accrued COMP to the wallet. A balance-changing operation is safe because its hook first sets the acting account's recorded index to the current market index, so the subsequent balance change creates no pending rewards. Advancing blocks is the only operation that increases the potential, by exactly the newly unindexed emission. Induction over the operation list, using `td0_run_inv` to preserve the invariant, therefore gives the required bound after discarding the final nonnegative `td0_owed` term.

```lean
theorem plan1_supplyHook_global_potential (s s' : St) (who : Account)
    (h : comptroller s (.supplyHook who) = some s') :
    s'.credited + td0_owed s' ≤ s.credited + td0_owed s := by sorry

theorem plan1_borrowHook_global_potential (s s' : St) (who : Account)
    (h : comptroller s (.borrowHook who) = some s') :
    s'.credited + td0_owed s' ≤ s.credited + td0_owed s := by sorry

theorem plan1_claim_global_potential (s s' : St) (who : Account)
    (h : comptroller s (.claim who) = some s') :
    s'.credited + td0_owed s' ≤ s.credited + td0_owed s := by sorry

theorem plan1_setSpeeds_global_potential (s s' : St) (a b : Nat)
    (h : comptroller s (.setSpeeds a b) = some s') :
    s'.credited + td0_owed s' ≤ s.credited + td0_owed s := by sorry

theorem plan1_exec_global_potential (sp : Nat × Nat) (s : St) (op : Op)
    (h : td0_Inv sp s) :
    (exec comptroller s op).credited + td0_owed (exec comptroller s op) ≤
      s.credited + td0_owed s + emittedBy sp op := by sorry

theorem plan1_run_global_potential (sp : Nat × Nat) (s : St) (ops : List Op)
    (h : td0_Inv sp s) :
    (run comptroller s ops).credited + td0_owed (run comptroller s ops) ≤
      s.credited + td0_owed s + emitted sp ops := by sorry
```