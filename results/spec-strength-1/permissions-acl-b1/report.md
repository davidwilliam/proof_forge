# Specification strength: permissions-acl-b1

Reference `tasks/permissions-acl-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `7eea6a1815787f12`; report `8c380678668b8435`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 33 | 33 | 20 | 0 | 19 | 0 | 0 | 18 | 0 | 1 | 19 of 20 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-ANSWERED | 1 | 1 | kernel-checked |
| REQ-INVALID-NOOP | 1 | 0 | tested |
| REQ-EFFECTS | 3 | 3 | kernel-checked |
| REQ-DEFAULT-DENY | 9 | 5 | kernel-checked |
| REQ-DENY-OVERRIDES | 12 | 3 | kernel-checked |
| REQ-SPECIFIC-ALLOW | 13 | 4 | kernel-checked |
| REQ-GRANT-JUSTIFIED | 12 | 1 | kernel-checked |
| REQ-ORDER-INDEPENDENT | 0 | 0 | not shown |
| REQ-DENIAL-EXPLAINED | 13 | 1 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | boundary | `decide2` | `<` replaced by `≤` | killed by property tests | REQ-DENY-OVERRIDES, REQ-GRANT-JUSTIFIED | REQ-DENY-OVERRIDES |
| M002 | equality | `matchesB` | `==` replaced by `!=` | killed by property tests | REQ-DEFAULT-DENY, REQ-DENIAL-EXPLAINED, REQ-DENY-OVERRIDES, REQ-GRANT-JUSTIFIED, REQ-SPECIFIC-ALLOW | REQ-DEFAULT-DENY |
| M003 | equality | `matchesB` | `==` replaced by `!=` | killed by property tests | REQ-DEFAULT-DENY, REQ-DENIAL-EXPLAINED, REQ-DENY-OVERRIDES, REQ-GRANT-JUSTIFIED, REQ-SPECIFIC-ALLOW | REQ-SPECIFIC-ALLOW |
| M004 | logic | `matchesB` | `//` replaced by `&&` | killed by property tests | REQ-DENIAL-EXPLAINED, REQ-SPECIFIC-ALLOW | REQ-DENIAL-EXPLAINED |
| M005 | logic | `matchesB` | `&&` replaced by `//` | killed by property tests | REQ-DEFAULT-DENY, REQ-DENIAL-EXPLAINED, REQ-DENY-OVERRIDES, REQ-GRANT-JUSTIFIED, REQ-SPECIFIC-ALLOW | REQ-GRANT-JUSTIFIED |
| M006 | logic | `decide2` | `true` replaced by `false` | killed by property tests | REQ-DENIAL-EXPLAINED, REQ-SPECIFIC-ALLOW | REQ-SPECIFIC-ALLOW |
| M007 | logic | `decide2` | `false` replaced by `true` | killed by property tests | REQ-DEFAULT-DENY, REQ-DENY-OVERRIDES, REQ-GRANT-JUSTIFIED | REQ-DEFAULT-DENY |
| M008 | drop-conjunct | `matchesB` | conjunct `(e.subject == 0 // e.subject == r.user)` replaced by `true` | killed by property tests | REQ-DEFAULT-DENY, REQ-DENIAL-EXPLAINED, REQ-DENY-OVERRIDES, REQ-GRANT-JUSTIFIED, REQ-SPECIFIC-ALLOW | REQ-DEFAULT-DENY |
| M009 | drop-conjunct | `matchesB` | conjunct `e.path.isPrefixOf r.path` replaced by `true` | killed by property tests | REQ-DEFAULT-DENY, REQ-DENIAL-EXPLAINED, REQ-DENY-OVERRIDES, REQ-GRANT-JUSTIFIED, REQ-SPECIFIC-ALLOW | REQ-DEFAULT-DENY |
| M010 | guard | `scan` | condition `matchesB e r` replaced by `true` | killed by property tests | REQ-DEFAULT-DENY, REQ-DENIAL-EXPLAINED, REQ-DENY-OVERRIDES, REQ-GRANT-JUSTIFIED, REQ-SPECIFIC-ALLOW | REQ-DENY-OVERRIDES |
| M011 | guard | `scan` | condition `matchesB e r` replaced by `false` | killed by property tests | REQ-DENIAL-EXPLAINED, REQ-SPECIFIC-ALLOW | REQ-SPECIFIC-ALLOW |
| M012 | guard | `step` | condition `ValidQuery s r` replaced by `false` | killed by property tests | REQ-VALID-ANSWERED | REQ-VALID-ANSWERED |
| M013 | guard | `step` | condition `ValidQuery s r` replaced by `true` | killed by property tests | REQ-INVALID-NOOP |  |
| M014 | guard | `step` | condition `g` replaced by `true` | killed by property tests | REQ-DEFAULT-DENY, REQ-DENY-OVERRIDES, REQ-EFFECTS, REQ-GRANT-JUSTIFIED | REQ-EFFECTS |
| M015 | guard | `step` | condition `g` replaced by `false` | killed by property tests | REQ-DENIAL-EXPLAINED, REQ-EFFECTS, REQ-SPECIFIC-ALLOW | REQ-EFFECTS |
| M016 | field | `matchesB` | field read `r.user` replaced by `r.path` | does not compile |  |  |
| M017 | field | `matchesB` | field read `r.path` replaced by `r.user` | does not compile |  |  |
| M018 | field | `step` | field read `s.entries` replaced by `s.log` | does not compile |  |  |
| M019 | field | `step` | field read `r.user` replaced by `r.path` | does not compile |  |  |
| M020 | field | `step` | field read `r.path` replaced by `r.user` | does not compile |  |  |
| M021 | field | `step` | update of field `log` dropped | killed by property tests | REQ-EFFECTS | REQ-EFFECTS |
| M022 | field | `step` | field read `s.log` replaced by `s.entries` | does not compile |  |  |
| M023 | swap | `bump` | `max` replaced by `min` | killed by property tests | REQ-DENIAL-EXPLAINED, REQ-DENY-OVERRIDES, REQ-GRANT-JUSTIFIED, REQ-SPECIFIC-ALLOW | REQ-SPECIFIC-ALLOW |
| M024 | swap | `bump` | arguments `j` and `k` of `max` swapped | survived, no observed difference |  |  |
| M025 | swap | `scan` | arguments `r` and `es` of `scan` swapped | does not compile |  |  |
| M026 | swap | `scan` | arguments `e` and `r` of `matchesB` swapped | does not compile |  |  |
| M027 | swap | `scan` | arguments `a` and `(depth e)` of `bump` swapped | does not compile |  |  |
| M028 | swap | `scan` | arguments `d` and `(depth e)` of `bump` swapped | does not compile |  |  |
| M029 | swap | `decide2` | operands of `<` swapped | killed by property tests | REQ-DENIAL-EXPLAINED, REQ-DENY-OVERRIDES, REQ-GRANT-JUSTIFIED, REQ-SPECIFIC-ALLOW | REQ-DENY-OVERRIDES |
| M030 | swap | `decision` | arguments `r` and `l` of `scan` swapped | does not compile |  |  |
| M031 | swap | `step` | arguments `s` and `r` of `ValidQuery` swapped | does not compile |  |  |
| M032 | swap | `step` | arguments `s.entries` and `r` of `decision` swapped | does not compile |  |  |
| M033 | constant | `matchesB` | constant `0` replaced by `1` | killed by property tests | REQ-DEFAULT-DENY, REQ-DENIAL-EXPLAINED, REQ-DENY-OVERRIDES, REQ-GRANT-JUSTIFIED, REQ-SPECIFIC-ALLOW | REQ-DEFAULT-DENY |

## Survivors

### M024: survived, no observed difference

arguments `j` and `k` of `max` swapped in `bump` (line 21); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -20,3 +20,3 @@
   | none => some k
-  | some j => some (max j k)
+  | some j => some (max k j)
 
```

