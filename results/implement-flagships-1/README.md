# Implement mode on the three flagship tasks

Muse Spark 1.3 (Contributor tier, no planner, the E1 A1 configuration) in implement mode
(`agents/repair.py --mode implement`) on the three flagship real-world tasks. The starting file is
generated from the locked challenge only: each required definition keeps its signature with a
placeholder body, and each required theorem is stated with `sorry`. The model sees neither the
ported vulnerable code, nor the issue report, nor the reference solution. One run per task, decided
in advance, capped at $10 at list prices and 14,400 s.

| Task | Requirements | Status | Passport | Time | List | Charged |
|---|---|---|---|---|---|---|
| rw-cetus-shlw | 5 of 5 | VERIFIED | `b2cf6c2de4f91b8e` | 122 s | $0.12 | $0.008 |
| rw-euler-donate | 6 of 6 | VERIFIED | `27d4ec2838e9bbfc` | 1,324 s | $1.22 | $0.066 |
| rw-hundred-vault | 10 of 10 | VERIFIED | `eee7e2cdbedf658d` | 663 s | $0.60 | $0.033 |

Each Passport was issued by `bin/proofforge check` and reproduced by `bin/proofforge verify`
(`verify.txt` in each directory). Reproduce one with the command in its Passport's `reproduce` field,
for example:

```
bin/proofforge verify results/implement-flagships-1/rw-hundred-vault/passport.json --candidate results/implement-flagships-1/rw-hundred-vault/final.lean
```

What this shows: given the locked Lean specification of each task, Muse wrote an implementation and
proved every requirement, accepted by the same judge as the repairs in `results/cetus-1`,
`results/euler-1` and `results/vault-1`. The specifications are formal Lean statements, not prose.
The real-code comparisons in those directories were run against the repairs, not against these
implementations.
