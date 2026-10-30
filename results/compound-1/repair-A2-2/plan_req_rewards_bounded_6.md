## Proof plan

Use the potential already defined in the candidate,
`potF s = s.credited * doubleScale + pendSum s + unidx s * doubleScale`:
credited COMP is the first summand, pending per-account rewards are the
second, and COMP emitted since each side's index was last updated is the
third. First bound the potential of the upgraded legacy state by the
initial credited amount plus `L.owed`, allowing one `doubleScale - 1`
slack for the single floor division in `L.owed` (each upgraded pending
term is below its legacy counterpart since `legacyStart ≤ accrualStart`
after initialization, and the upgraded un-indexed emission is below the
legacy one). Then show a single `exec` step never increases the
potential beyond the COMP that step emits: the already-proved hook,
claim and speed-change effect lemmas rewrite each implementation call,
index updates move emission from `unidx` into `pendSum` losing only a
division remainder, distributions move one account's pending term into
`credited` losing only a remainder, grants merely rename accrued COMP
as wallet COMP, balance changes happen right after a hook set that
account's pending coefficient to zero, `advance k` grows `unidx` by
exactly `k * (supplySpeed + borrowSpeed)`, and refused operations change
nothing. The same step argument preserves `Consistent` and the fact that
the state's speeds are the tracked speeds, so an induction over the
operation list (using `emitted`/`speedsAfter` unfolding) bounds
`potF (run ...)` by the initial potential plus total emitted COMP.
Finally `s.credited * doubleScale ≤ potF s` and `0 < doubleScale` let
`omega` cancel the scale and absorb the `doubleScale - 1` slack,
giving exactly `RewardsBounded`.

```lean
theorem plan6_credited_mul_le_potF (s : St) :
    s.credited * doubleScale ≤ potF s := by sorry

theorem plan6_potF_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    potF (upgrade L) ≤
      ((upgrade L).credited + L.owed) * doubleScale + (doubleScale - 1) := by sorry

theorem plan6_consistent_upgrade (L : Legacy) (hWF : L.WellFormed) :
    Consistent (upgrade L) ∧
    (upgrade L).supplyState.speed = L.compSpeed ∧
    (upgrade L).borrowState.speed = L.compSpeed := by sorry

theorem plan6_exec_potF_le (s : St) (sp : Nat × Nat) (op : Op)
    (hC : Consistent s)
    (hS : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2) :
    potF (exec comptroller s op) ≤ potF s + emittedBy sp op := by sorry

theorem plan6_exec_invariant (s : St) (sp : Nat × Nat) (op : Op)
    (hC : Consistent s)
    (hS : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2) :
    Consistent (exec comptroller s op) ∧
    (exec comptroller s op).supplyState.speed = (nextSpeeds sp op).1 ∧
    (exec comptroller s op).borrowState.speed = (nextSpeeds sp op).2 := by sorry

theorem plan6_run_potF_le (s : St) (sp : Nat × Nat) (ops : List Op)
    (hC : Consistent s)
    (hS : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2) :
    potF (run comptroller s ops) ≤ potF s + emitted sp ops := by sorry
```