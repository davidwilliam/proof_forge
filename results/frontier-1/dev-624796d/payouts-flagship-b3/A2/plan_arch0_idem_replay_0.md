(1) Proof plan: From `(step s r).1 = .ok`, first recover `ValidPayout s r`. The successful step records `r.txId` in `applied`, so the post-step state contains that transaction ID. But `ValidPayout` requires `r.txId ∉ applied`, hence the same request is invalid in the post-step state. Finally, unfolding `step` on an invalid request gives `(.rejected, state)` unchanged, which is exactly the replay statement.

(2)
```lean
theorem plan0_validPayout_txId_not_mem {s : State} {r : Request}
    (h : ValidPayout s r) : r.txId ∉ s.applied := by sorry

theorem plan0_valid_of_ok (s : State) (r : Request)
    (hok : (step s r).1 = .ok) : ValidPayout s r := by sorry

theorem plan0_txId_mem_applied_of_ok (s : State) (r : Request)
    (hok : (step s r).1 = .ok) : r.txId ∈ (step s r).2.applied := by sorry

theorem plan0_not_valid_after_ok (s : State) (r : Request)
    (hok : (step s r).1 = .ok) : ¬ ValidPayout (step s r).2 r := by sorry

theorem plan0_step_eq_rejected_of_not_valid (t : State) (r : Request)
    (h : ¬ ValidPayout t r) : step t r = (.rejected, t) := by sorry
```