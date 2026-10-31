Use the per-account potential `creditedTo who + td0_owedTo · who`. A hook converts unindexed emission into indexed pending rewards at a rate bounded by the account’s share of the total, distribution converts that pending amount into `accrued`, and a grant preserves `accrued + wallet`. Consequently, calls do not increase the potential. Balance-changing operations are safe because their hooks first set the participant’s index to the current market index, so newly acquired positions earn nothing retroactively. Only `advance` increases the potential, by at most the COMP emitted during those blocks. Induction over the operation list then gives the run bound, and dropping the final nonnegative `td0_owedTo` term yields `td0_run_creditedTo_bound`.

```lean
theorem plan0_supplyHook_potential (s s' : St) (actor who : Account)
    (h : comptroller s (.supplyHook actor) = some s') :
    s'.creditedTo who + td0_owedTo s' who ≤
      s.creditedTo who + td0_owedTo s who := by sorry

theorem plan0_borrowHook_potential (s s' : St) (actor who : Account)
    (h : comptroller s (.borrowHook actor) = some s') :
    s'.creditedTo who + td0_owedTo s' who ≤
      s.creditedTo who + td0_owedTo s who := by sorry

theorem plan0_claim_potential (s s' : St) (actor who : Account)
    (h : comptroller s (.claim actor) = some s') :
    s'.creditedTo who + td0_owedTo s' who ≤
      s.creditedTo who + td0_owedTo s who := by sorry

theorem plan0_setSpeeds_potential (s s' : St) (a b who : Account)
    (h : comptroller s (.setSpeeds a b) = some s') :
    s'.creditedTo who + td0_owedTo s' who ≤
      s.creditedTo who + td0_owedTo s who := by sorry

theorem plan0_exec_potential (sp : Nat × Nat) (s : St) (op : Op) (who : Account)
    (h : td0_Inv sp s) :
    (exec comptroller s op).creditedTo who +
        td0_owedTo (exec comptroller s op) who ≤
      s.creditedTo who + td0_owedTo s who + emittedBy sp op := by sorry

theorem plan0_run_potential (sp : Nat × Nat) (s : St) (ops : List Op) (who : Account)
    (h : td0_Inv sp s) :
    (run comptroller s ops).creditedTo who +
        td0_owedTo (run comptroller s ops) who ≤
      s.creditedTo who + td0_owedTo s who + emitted sp ops := by sorry
```