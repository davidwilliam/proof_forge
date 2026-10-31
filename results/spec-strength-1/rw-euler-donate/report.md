# Specification strength: rw-euler-donate

Reference `realworld/tasks/rw-euler-donate/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `1f2419cb971dcc44`; report `7001e44b883c9085`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 257 | 257 | 160 | 0 | 121 | 0 | 0 | 110 | 0 | 39 | 121 of 160 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-HONEST-FLOW | 53 | 47 | kernel-checked |
| REQ-ALLOWED-SUCCEEDS | 57 | 34 | kernel-checked |
| REQ-EFFECTS | 88 | 13 | kernel-checked |
| REQ-ACTOR-HEALTHY | 18 | 12 | kernel-checked |
| REQ-STAYS-HEALTHY | 26 | 3 | kernel-checked |
| REQ-NO-BAD-DEBT | 26 | 1 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | boundary | `step` | `≤` replaced by `<` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M002 | boundary | `step` | `≤` replaced by `<` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M003 | boundary | `step` | `≤` replaced by `<` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M004 | boundary | `step` | `≤` replaced by `<` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M005 | boundary | `step` | `≤` replaced by `<` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M006 | boundary | `step` | `≤` replaced by `<` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M007 | boundary | `step` | `≤` replaced by `<` | survived, no observed difference |  |  |
| M008 | equality | `setAcct` | `=` replaced by `≠` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-EFFECTS |
| M009 | equality | `step` | `=` replaced by `≠` | survived, no observed difference |  |  |
| M010 | equality | `step` | `≠` replaced by `=` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M011 | equality | `step` | `=` replaced by `≠` | survived, no observed difference |  |  |
| M012 | equality | `step` | `≠` replaced by `=` | survived, no observed difference |  |  |
| M013 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M014 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M015 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M016 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M017 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M018 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M019 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-STAYS-HEALTHY |
| M020 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M021 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M022 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M023 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M024 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M025 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-EFFECTS |  |
| M026 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M027 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-EFFECTS |  |
| M028 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-EFFECTS |  |
| M029 | arith | `step` | `+` replaced by `-` | survived, no observed difference |  |  |
| M030 | arith | `step` | `+` replaced by `-` | survived, no observed difference |  |  |
| M031 | arith | `step` | `+` replaced by `-` | survived, no observed difference |  |  |
| M032 | arith | `step` | `-` replaced by `+` | survived, no observed difference |  |  |
| M033 | arith | `step` | `-` replaced by `+` | survived, no observed difference |  |  |
| M034 | arith | `step` | `+` replaced by `-` | survived, no observed difference |  |  |
| M035 | logic | `step` | `∨` replaced by `∧` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M036 | logic | `step` | `∧` replaced by `∨` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ACTOR-HEALTHY |
| M037 | logic | `step` | `∧` replaced by `∨` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-NO-BAD-DEBT |
| M038 | logic | `step` | `∧` replaced by `∨` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-EFFECTS |
| M039 | logic | `step` | `∧` replaced by `∨` | survived, no observed difference |  |  |
| M040 | logic | `step` | `∧` replaced by `∨` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ACTOR-HEALTHY |
| M041 | logic | `step` | `∧` replaced by `∨` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ACTOR-HEALTHY |
| M042 | logic | `step` | `∧` replaced by `∨` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ACTOR-HEALTHY |
| M043 | logic | `step` | `∨` replaced by `∧` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M044 | logic | `step` | `∧` replaced by `∨` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-EFFECTS |
| M045 | logic | `step` | `∧` replaced by `∨` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ACTOR-HEALTHY |
| M046 | logic | `step` | `∧` replaced by `∨` | killed by property tests | REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-EFFECTS |
| M047 | logic | `step` | `∧` replaced by `∨` | killed by property tests | REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-EFFECTS |
| M048 | drop-conjunct | `step` | conjunct `x ≤ (s.acct u).e` replaced by `True` | killed by property tests | REQ-EFFECTS | REQ-EFFECTS |
| M049 | drop-conjunct | `step` | conjunct `x ≤ s.cash` replaced by `True` | survived, no observed difference |  |  |
| M050 | drop-conjunct | `step` | conjunct `Healthy a` replaced by `True` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ACTOR-HEALTHY |
| M051 | drop-conjunct | `step` | conjunct `x ≤ s.cash` replaced by `True` | survived, no observed difference |  |  |
| M052 | drop-conjunct | `step` | conjunct `Healthy a` replaced by `True` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ACTOR-HEALTHY |
| M053 | drop-conjunct | `step` | conjunct `y ≤ (s.acct u).e` replaced by `True` | survived, no observed difference |  |  |
| M054 | drop-conjunct | `step` | conjunct `Healthy a` replaced by `True` | survived, no observed difference |  |  |
| M055 | drop-conjunct | `step` | conjunct `u ≠ v` replaced by `True` | killed by property tests | REQ-EFFECTS |  |
| M056 | drop-conjunct | `step` | conjunct `x ≤ (s.acct u).e` replaced by `True` | killed by property tests | REQ-EFFECTS |  |
| M057 | drop-conjunct | `step` | conjunct `Healthy a` replaced by `True` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ACTOR-HEALTHY |
| M058 | drop-conjunct | `step` | conjunct `((s.acct v).d = 0 ∨ Healthy b)` replaced by `True` | survived, no observed difference |  |  |
| M059 | drop-conjunct | `step` | conjunct `x ≤ (s.acct u).e` replaced by `True` | killed by property tests | REQ-EFFECTS | REQ-EFFECTS |
| M060 | drop-conjunct | `step` | conjunct `Healthy a` replaced by `True` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ACTOR-HEALTHY |
| M061 | drop-conjunct | `step` | conjunct `l ≠ v` replaced by `True` | survived, no observed difference |  |  |
| M062 | drop-conjunct | `step` | conjunct `¬ Healthy (s.acct v)` replaced by `True` | killed by property tests | REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-STAYS-HEALTHY |
| M063 | drop-conjunct | `step` | conjunct `r ≤ maxRepay (s.acct v)` replaced by `True` | survived, no observed difference |  |  |
| M064 | drop-conjunct | `step` | conjunct `Healthy b` replaced by `True` | survived, no observed difference |  |  |
| M065 | guard | `setAcct` | condition `w = u` replaced by `true` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M066 | guard | `setAcct` | condition `w = u` replaced by `false` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M067 | guard | `step` | condition `(s.acct u).d = 0 ∨ Healthy a` replaced by `false` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M068 | guard | `step` | condition `(s.acct u).d = 0 ∨ Healthy a` replaced by `true` | survived, no observed difference |  |  |
| M069 | guard | `step` | condition `x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy a` replaced by `false` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M070 | guard | `step` | condition `x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy a` replaced by `true` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-EFFECTS |
| M071 | guard | `step` | condition `x ≤ s.cash ∧ Healthy a` replaced by `true` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ACTOR-HEALTHY |
| M072 | guard | `step` | condition `x ≤ s.cash ∧ Healthy a` replaced by `false` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M073 | guard | `step` | condition `Healthy a` replaced by `false` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M074 | guard | `step` | condition `Healthy a` replaced by `true` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-STAYS-HEALTHY |
| M075 | guard | `step` | condition `y ≤ (s.acct u).e ∧ Healthy a` replaced by `false` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M076 | guard | `step` | condition `y ≤ (s.acct u).e ∧ Healthy a` replaced by `true` | survived, no observed difference |  |  |
| M077 | guard | `step` | condition `u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ ((s.acct v).d = 0 ...` replaced by `false` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M078 | guard | `step` | condition `u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ ((s.acct v).d = 0 ...` replaced by `true` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ACTOR-HEALTHY |
| M079 | guard | `step` | condition `x ≤ (s.acct u).e ∧ Healthy a` replaced by `false` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M080 | guard | `step` | condition `x ≤ (s.acct u).e ∧ Healthy a` replaced by `true` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-EFFECTS |
| M081 | guard | `step` | condition `l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ ...` replaced by `false` | survived, no observed difference |  |  |
| M082 | guard | `step` | condition `l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ ...` replaced by `true` | killed by property tests | REQ-ACTOR-HEALTHY, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ACTOR-HEALTHY |
| M083 | field | `setAcct` | update of field `acct` dropped | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M084 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M085 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M086 | field | `step` | projection `.e` replaced by `.d` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M087 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M088 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M089 | field | `step` | projection `.d` replaced by `.e` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ALLOWED-SUCCEEDS |
| M090 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M091 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M092 | field | `step` | projection `.d` replaced by `.e` | survived, no observed difference |  |  |
| M093 | field | `step` | update of field `cash` dropped | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M094 | field | `step` | field read `s.cash` replaced by `s.reserves` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW |  |
| M095 | field | `step` | field read `s.cash` replaced by `s.acct` | does not compile |  |  |
| M096 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M097 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M098 | field | `step` | projection `.e` replaced by `.d` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M099 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M100 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M101 | field | `step` | projection `.d` replaced by `.e` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M102 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M103 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M104 | field | `step` | projection `.e` replaced by `.d` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M105 | field | `step` | field read `s.cash` replaced by `s.acct` | does not compile |  |  |
| M106 | field | `step` | field read `s.cash` replaced by `s.reserves` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-ALLOWED-SUCCEEDS |
| M107 | field | `step` | update of field `cash` dropped | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M108 | field | `step` | field read `s.cash` replaced by `s.reserves` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M109 | field | `step` | field read `s.cash` replaced by `s.acct` | does not compile |  |  |
| M110 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M111 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M112 | field | `step` | projection `.e` replaced by `.d` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M113 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M114 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M115 | field | `step` | projection `.d` replaced by `.e` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M116 | field | `step` | field read `s.cash` replaced by `s.reserves` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-ALLOWED-SUCCEEDS |
| M117 | field | `step` | field read `s.cash` replaced by `s.acct` | does not compile |  |  |
| M118 | field | `step` | update of field `cash` dropped | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M119 | field | `step` | field read `s.cash` replaced by `s.acct` | does not compile |  |  |
| M120 | field | `step` | field read `s.cash` replaced by `s.reserves` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M121 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M122 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M123 | field | `step` | projection `.d` replaced by `.e` | killed by property tests | REQ-EFFECTS |  |
| M124 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M125 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M126 | field | `step` | projection `.e` replaced by `.d` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-HONEST-FLOW |
| M127 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M128 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M129 | field | `step` | projection `.d` replaced by `.e` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-HONEST-FLOW |
| M130 | field | `step` | update of field `cash` dropped | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M131 | field | `step` | field read `s.cash` replaced by `s.acct` | does not compile |  |  |
| M132 | field | `step` | field read `s.cash` replaced by `s.reserves` | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M133 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M134 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M135 | field | `step` | projection `.e` replaced by `.d` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M136 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M137 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M138 | field | `step` | projection `.d` replaced by `.e` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M139 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M140 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M141 | field | `step` | projection `.d` replaced by `.e` | killed by property tests | REQ-EFFECTS |  |
| M142 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M143 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M144 | field | `step` | projection `.e` replaced by `.d` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M145 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M146 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M147 | field | `step` | projection `.d` replaced by `.e` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M148 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M149 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M150 | field | `step` | projection `.e` replaced by `.d` | survived, no observed difference |  |  |
| M151 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M152 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M153 | field | `step` | projection `.e` replaced by `.d` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M154 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M155 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M156 | field | `step` | projection `.d` replaced by `.e` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M157 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M158 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M159 | field | `step` | projection `.e` replaced by `.d` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M160 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M161 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M162 | field | `step` | projection `.d` replaced by `.e` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-NO-BAD-DEBT, REQ-STAYS-HEALTHY | REQ-ALLOWED-SUCCEEDS |
| M163 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M164 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M165 | field | `step` | projection `.e` replaced by `.d` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M166 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M167 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M168 | field | `step` | projection `.d` replaced by `.e` | survived, no observed difference |  |  |
| M169 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M170 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M171 | field | `step` | projection `.e` replaced by `.d` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M172 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M173 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M174 | field | `step` | projection `.d` replaced by `.e` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M175 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M176 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M177 | field | `step` | projection `.e` replaced by `.d` | killed by property tests | REQ-ALLOWED-SUCCEEDS | REQ-ALLOWED-SUCCEEDS |
| M178 | field | `step` | update of field `reserves` dropped | killed by property tests | REQ-EFFECTS |  |
| M179 | field | `step` | field read `s.reserves` replaced by `s.cash` | killed by property tests | REQ-EFFECTS |  |
| M180 | field | `step` | field read `s.reserves` replaced by `s.acct` | does not compile |  |  |
| M181 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M182 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M183 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M184 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M185 | field | `step` | projection `.e` replaced by `.d` | survived, no observed difference |  |  |
| M186 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M187 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M188 | field | `step` | projection `.d` replaced by `.e` | survived, no observed difference |  |  |
| M189 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M190 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M191 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M192 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M193 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M194 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M195 | field | `step` | projection `.e` replaced by `.d` | survived, no observed difference |  |  |
| M196 | field | `step` | field read `s.acct` replaced by `s.reserves` | does not compile |  |  |
| M197 | field | `step` | field read `s.acct` replaced by `s.cash` | does not compile |  |  |
| M198 | field | `step` | projection `.d` replaced by `.e` | survived, no observed difference |  |  |
| M199 | field | `step` | update of field `reserves` dropped | survived, no observed difference |  |  |
| M200 | field | `step` | field read `s.reserves` replaced by `s.cash` | survived, no observed difference |  |  |
| M201 | field | `step` | field read `s.reserves` replaced by `s.acct` | does not compile |  |  |
| M202 | swap | `step` | arguments `u` and `x` of `deposit` swapped | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-EFFECTS |
| M203 | swap | `step` | arguments `s` and `u` of `setAcct` swapped | does not compile |  |  |
| M204 | swap | `step` | arguments `u` and `a` of `setAcct` swapped | does not compile |  |  |
| M205 | swap | `step` | arguments `u` and `x` of `withdraw` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M206 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M207 | swap | `step` | operands of `≤` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M208 | swap | `step` | operands of `≤` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M209 | swap | `step` | arguments `s` and `u` of `setAcct` swapped | does not compile |  |  |
| M210 | swap | `step` | arguments `u` and `a` of `setAcct` swapped | does not compile |  |  |
| M211 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M212 | swap | `step` | arguments `u` and `x` of `borrow` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M213 | swap | `step` | operands of `≤` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M214 | swap | `step` | arguments `s` and `u` of `setAcct` swapped | does not compile |  |  |
| M215 | swap | `step` | arguments `u` and `a` of `setAcct` swapped | does not compile |  |  |
| M216 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M217 | swap | `step` | arguments `u` and `x` of `repay` swapped | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M218 | swap | `step` | `min` replaced by `max` | killed by property tests | REQ-EFFECTS | REQ-EFFECTS |
| M219 | swap | `step` | arguments `x` and `(s.acct u).d` of `min` swapped | survived, no observed difference |  |  |
| M220 | swap | `step` | arguments `s` and `u` of `setAcct` swapped | does not compile |  |  |
| M221 | swap | `step` | arguments `u` and `⟨(s.acct u).e, (s.acct u).d - y⟩` of `setAcct` swapped | does not compile |  |  |
| M222 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-EFFECTS | REQ-EFFECTS |
| M223 | swap | `step` | arguments `u` and `x` of `mint` swapped | killed by property tests | REQ-EFFECTS | REQ-EFFECTS |
| M224 | swap | `step` | arguments `s` and `u` of `setAcct` swapped | does not compile |  |  |
| M225 | swap | `step` | arguments `u` and `a` of `setAcct` swapped | does not compile |  |  |
| M226 | swap | `step` | arguments `u` and `x` of `burn` swapped | killed by property tests | REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M227 | swap | `step` | `min` replaced by `max` | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M228 | swap | `step` | arguments `x` and `(s.acct u).d` of `min` swapped | survived, no observed difference |  |  |
| M229 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M230 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-EFFECTS |  |
| M231 | swap | `step` | operands of `≤` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-HONEST-FLOW | REQ-HONEST-FLOW |
| M232 | swap | `step` | arguments `s` and `u` of `setAcct` swapped | does not compile |  |  |
| M233 | swap | `step` | arguments `u` and `a` of `setAcct` swapped | does not compile |  |  |
| M234 | swap | `step` | arguments `u` and `v` of `transfer` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M235 | swap | `step` | arguments `v` and `x` of `transfer` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M236 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M237 | swap | `step` | operands of `≤` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M238 | swap | `step` | arguments `(setAcct s u a)` and `v` of `setAcct` swapped | does not compile |  |  |
| M239 | swap | `step` | arguments `s` and `u` of `setAcct` swapped | does not compile |  |  |
| M240 | swap | `step` | arguments `u` and `a` of `setAcct` swapped | does not compile |  |  |
| M241 | swap | `step` | arguments `v` and `b` of `setAcct` swapped | does not compile |  |  |
| M242 | swap | `step` | arguments `u` and `x` of `donate` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M243 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M244 | swap | `step` | operands of `≤` swapped | killed by property tests | REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS | REQ-ALLOWED-SUCCEEDS |
| M245 | swap | `step` | arguments `s` and `u` of `setAcct` swapped | does not compile |  |  |
| M246 | swap | `step` | arguments `u` and `a` of `setAcct` swapped | does not compile |  |  |
| M247 | swap | `step` | arguments `l` and `v` of `liquidate` swapped | survived, no observed difference |  |  |
| M248 | swap | `step` | arguments `v` and `r` of `liquidate` swapped | survived, no observed difference |  |  |
| M249 | swap | `step` | arguments `(s.acct v)` and `r` of `liqYield` swapped | does not compile |  |  |
| M250 | swap | `step` | arguments `(setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩)` and `l` of `setAcct` swapped | does not compile |  |  |
| M251 | swap | `step` | arguments `s` and `v` of `setAcct` swapped | does not compile |  |  |
| M252 | swap | `step` | arguments `v` and `⟨(s.acct v).e - y, (s.acct v).d - r⟩` of `setAcct` swapped | does not compile |  |  |
| M253 | swap | `step` | operands of `-` swapped | survived, no observed difference |  |  |
| M254 | swap | `step` | operands of `-` swapped | survived, no observed difference |  |  |
| M255 | swap | `step` | arguments `l` and `b` of `setAcct` swapped | does not compile |  |  |
| M256 | constant | `step` | constant `0` replaced by `1` | survived, no observed difference |  |  |
| M257 | constant | `step` | constant `0` replaced by `1` | survived, no observed difference |  |  |

## Survivors

### M007: survived, no observed difference

`≤` replaced by `<` in `step` (line 47); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -46,3 +46,3 @@
     let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
-    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
+    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r < maxRepay (s.acct v) ∧ Healthy b then
       some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
```

### M009: survived, no observed difference

`=` replaced by `≠` in `step` (line 17); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -16,3 +16,3 @@
     let a : Acct := ⟨(s.acct u).e + x, (s.acct u).d⟩
-    if (s.acct u).d = 0 ∨ Healthy a then some { setAcct s u a with cash := s.cash + x } else none
+    if (s.acct u).d ≠ 0 ∨ Healthy a then some { setAcct s u a with cash := s.cash + x } else none
   | .withdraw u x =>
```

### M011: survived, no observed difference

`=` replaced by `≠` in `step` (line 38); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -37,3 +37,3 @@
     let b : Acct := ⟨(s.acct v).e + x, (s.acct v).d⟩
-    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ ((s.acct v).d = 0 ∨ Healthy b) then
+    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ ((s.acct v).d ≠ 0 ∨ Healthy b) then
       some (setAcct (setAcct s u a) v b) else none
```

### M012: survived, no observed difference

`≠` replaced by `=` in `step` (line 47); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -46,3 +46,3 @@
     let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
-    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
+    if l = v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
       some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
```

### M029: survived, no observed difference

`+` replaced by `-` in `step` (line 46); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -45,3 +45,3 @@
     let y := liqYield (s.acct v) r
-    let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
+    let b : Acct := ⟨(s.acct l).e - y, (s.acct l).d + r + liqFee r⟩
     if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
```

### M030: survived, no observed difference

`+` replaced by `-` in `step` (line 46); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -45,3 +45,3 @@
     let y := liqYield (s.acct v) r
-    let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
+    let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d - r + liqFee r⟩
     if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
```

### M031: survived, no observed difference

`+` replaced by `-` in `step` (line 46); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -45,3 +45,3 @@
     let y := liqYield (s.acct v) r
-    let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
+    let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r - liqFee r⟩
     if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
```

### M032: survived, no observed difference

`-` replaced by `+` in `step` (line 48); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -47,3 +47,3 @@
     if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
-      some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
+      some { setAcct (setAcct s v ⟨(s.acct v).e + y, (s.acct v).d - r⟩) l b with
         reserves := s.reserves + liqFee r } else none
```

### M033: survived, no observed difference

`-` replaced by `+` in `step` (line 48); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -47,3 +47,3 @@
     if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
-      some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
+      some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d + r⟩) l b with
         reserves := s.reserves + liqFee r } else none
```

### M034: survived, no observed difference

`+` replaced by `-` in `step` (line 49); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -48,3 +48,3 @@
       some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
-        reserves := s.reserves + liqFee r } else none
+        reserves := s.reserves - liqFee r } else none
 
```

### M039: survived, no observed difference

`∧` replaced by `∨` in `step` (line 34); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -33,3 +33,3 @@
     let a : Acct := ⟨(s.acct u).e - y, (s.acct u).d - y⟩
-    if y ≤ (s.acct u).e ∧ Healthy a then some (setAcct s u a) else none
+    if y ≤ (s.acct u).e ∨ Healthy a then some (setAcct s u a) else none
   | .transfer u v x =>
```

### M049: survived, no observed difference

conjunct `x ≤ s.cash` replaced by `True` in `step` (line 20); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -19,3 +19,3 @@
     let a : Acct := ⟨(s.acct u).e - x, (s.acct u).d⟩
-    if x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy a then
+    if x ≤ (s.acct u).e ∧ True ∧ Healthy a then
       some { setAcct s u a with cash := s.cash - x } else none
```

### M051: survived, no observed difference

conjunct `x ≤ s.cash` replaced by `True` in `step` (line 24); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -23,3 +23,3 @@
     let a : Acct := ⟨(s.acct u).e, (s.acct u).d + x⟩
-    if x ≤ s.cash ∧ Healthy a then some { setAcct s u a with cash := s.cash - x } else none
+    if True ∧ Healthy a then some { setAcct s u a with cash := s.cash - x } else none
   | .repay u x =>
```

### M053: survived, no observed difference

conjunct `y ≤ (s.acct u).e` replaced by `True` in `step` (line 34); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -33,3 +33,3 @@
     let a : Acct := ⟨(s.acct u).e - y, (s.acct u).d - y⟩
-    if y ≤ (s.acct u).e ∧ Healthy a then some (setAcct s u a) else none
+    if True ∧ Healthy a then some (setAcct s u a) else none
   | .transfer u v x =>
```

### M054: survived, no observed difference

conjunct `Healthy a` replaced by `True` in `step` (line 34); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -33,3 +33,3 @@
     let a : Acct := ⟨(s.acct u).e - y, (s.acct u).d - y⟩
-    if y ≤ (s.acct u).e ∧ Healthy a then some (setAcct s u a) else none
+    if y ≤ (s.acct u).e ∧ True then some (setAcct s u a) else none
   | .transfer u v x =>
```

### M058: survived, no observed difference

conjunct `((s.acct v).d = 0 ∨ Healthy b)` replaced by `True` in `step` (line 38); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -37,3 +37,3 @@
     let b : Acct := ⟨(s.acct v).e + x, (s.acct v).d⟩
-    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ ((s.acct v).d = 0 ∨ Healthy b) then
+    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ True then
       some (setAcct (setAcct s u a) v b) else none
```

### M061: survived, no observed difference

conjunct `l ≠ v` replaced by `True` in `step` (line 47); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -46,3 +46,3 @@
     let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
-    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
+    if True ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
       some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
```

### M063: survived, no observed difference

conjunct `r ≤ maxRepay (s.acct v)` replaced by `True` in `step` (line 47); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -46,3 +46,3 @@
     let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
-    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
+    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ True ∧ Healthy b then
       some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
```

### M064: survived, no observed difference

conjunct `Healthy b` replaced by `True` in `step` (line 47); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -46,3 +46,3 @@
     let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
-    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
+    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ True then
       some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
```

### M068: survived, no observed difference

condition `(s.acct u).d = 0 ∨ Healthy a` replaced by `true` in `step` (line 17); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -16,3 +16,3 @@
     let a : Acct := ⟨(s.acct u).e + x, (s.acct u).d⟩
-    if (s.acct u).d = 0 ∨ Healthy a then some { setAcct s u a with cash := s.cash + x } else none
+    if true then some { setAcct s u a with cash := s.cash + x } else none
   | .withdraw u x =>
```

### M076: survived, no observed difference

condition `y ≤ (s.acct u).e ∧ Healthy a` replaced by `true` in `step` (line 34); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -33,3 +33,3 @@
     let a : Acct := ⟨(s.acct u).e - y, (s.acct u).d - y⟩
-    if y ≤ (s.acct u).e ∧ Healthy a then some (setAcct s u a) else none
+    if true then some (setAcct s u a) else none
   | .transfer u v x =>
```

### M081: survived, no observed difference

condition `l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ ...` replaced by `false` in `step` (line 47); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -46,3 +46,3 @@
     let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
-    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
+    if false then
       some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
```

### M092: survived, no observed difference

projection `.d` replaced by `.e` in `step` (line 17); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -16,3 +16,3 @@
     let a : Acct := ⟨(s.acct u).e + x, (s.acct u).d⟩
-    if (s.acct u).d = 0 ∨ Healthy a then some { setAcct s u a with cash := s.cash + x } else none
+    if (s.acct u).e = 0 ∨ Healthy a then some { setAcct s u a with cash := s.cash + x } else none
   | .withdraw u x =>
```

### M150: survived, no observed difference

projection `.e` replaced by `.d` in `step` (line 34); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -33,3 +33,3 @@
     let a : Acct := ⟨(s.acct u).e - y, (s.acct u).d - y⟩
-    if y ≤ (s.acct u).e ∧ Healthy a then some (setAcct s u a) else none
+    if y ≤ (s.acct u).d ∧ Healthy a then some (setAcct s u a) else none
   | .transfer u v x =>
```

### M168: survived, no observed difference

projection `.d` replaced by `.e` in `step` (line 38); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -37,3 +37,3 @@
     let b : Acct := ⟨(s.acct v).e + x, (s.acct v).d⟩
-    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ ((s.acct v).d = 0 ∨ Healthy b) then
+    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ ((s.acct v).e = 0 ∨ Healthy b) then
       some (setAcct (setAcct s u a) v b) else none
```

### M185: survived, no observed difference

projection `.e` replaced by `.d` in `step` (line 46); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -45,3 +45,3 @@
     let y := liqYield (s.acct v) r
-    let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
+    let b : Acct := ⟨(s.acct l).d + y, (s.acct l).d + r + liqFee r⟩
     if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
```

### M188: survived, no observed difference

projection `.d` replaced by `.e` in `step` (line 46); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -45,3 +45,3 @@
     let y := liqYield (s.acct v) r
-    let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
+    let b : Acct := ⟨(s.acct l).e + y, (s.acct l).e + r + liqFee r⟩
     if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
```

### M195: survived, no observed difference

projection `.e` replaced by `.d` in `step` (line 48); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -47,3 +47,3 @@
     if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
-      some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
+      some { setAcct (setAcct s v ⟨(s.acct v).d - y, (s.acct v).d - r⟩) l b with
         reserves := s.reserves + liqFee r } else none
```

### M198: survived, no observed difference

projection `.d` replaced by `.e` in `step` (line 48); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -47,3 +47,3 @@
     if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
-      some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
+      some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).e - r⟩) l b with
         reserves := s.reserves + liqFee r } else none
```

### M199: survived, no observed difference

update of field `reserves` dropped in `step` (line 49); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -48,3 +48,3 @@
       some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
-        reserves := s.reserves + liqFee r } else none
+         } else none
 
```

### M200: survived, no observed difference

field read `s.reserves` replaced by `s.cash` in `step` (line 49); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -48,3 +48,3 @@
       some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
-        reserves := s.reserves + liqFee r } else none
+        reserves := s.cash + liqFee r } else none
 
```

### M219: survived, no observed difference

arguments `x` and `(s.acct u).d` of `min` swapped in `step` (line 26); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -25,3 +25,3 @@
   | .repay u x =>
-    let y := min x (s.acct u).d
+    let y := min (s.acct u).d x
     some { setAcct s u ⟨(s.acct u).e, (s.acct u).d - y⟩ with cash := s.cash + y }
```

### M228: survived, no observed difference

arguments `x` and `(s.acct u).d` of `min` swapped in `step` (line 32); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -31,3 +31,3 @@
   | .burn u x =>
-    let y := min x (s.acct u).d
+    let y := min (s.acct u).d x
     let a : Acct := ⟨(s.acct u).e - y, (s.acct u).d - y⟩
```

### M247: survived, no observed difference

arguments `l` and `v` of `liquidate` swapped in `step` (line 44); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -43,3 +43,3 @@
       some { setAcct s u a with reserves := s.reserves + x } else none
-  | .liquidate l v r =>
+  | .liquidate v l r =>
     let y := liqYield (s.acct v) r
```

### M248: survived, no observed difference

arguments `v` and `r` of `liquidate` swapped in `step` (line 44); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -43,3 +43,3 @@
       some { setAcct s u a with reserves := s.reserves + x } else none
-  | .liquidate l v r =>
+  | .liquidate l r v =>
     let y := liqYield (s.acct v) r
```

### M253: survived, no observed difference

operands of `-` swapped in `step` (line 48); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -47,3 +47,3 @@
     if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
-      some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
+      some { setAcct (setAcct s v ⟨y - (s.acct v).e, (s.acct v).d - r⟩) l b with
         reserves := s.reserves + liqFee r } else none
```

### M254: survived, no observed difference

operands of `-` swapped in `step` (line 48); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -47,3 +47,3 @@
     if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
-      some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
+      some { setAcct (setAcct s v ⟨(s.acct v).e - y, r - (s.acct v).d⟩) l b with
         reserves := s.reserves + liqFee r } else none
```

### M256: survived, no observed difference

constant `0` replaced by `1` in `step` (line 17); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -16,3 +16,3 @@
     let a : Acct := ⟨(s.acct u).e + x, (s.acct u).d⟩
-    if (s.acct u).d = 0 ∨ Healthy a then some { setAcct s u a with cash := s.cash + x } else none
+    if (s.acct u).d = 1 ∨ Healthy a then some { setAcct s u a with cash := s.cash + x } else none
   | .withdraw u x =>
```

### M257: survived, no observed difference

constant `0` replaced by `1` in `step` (line 38); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -37,3 +37,3 @@
     let b : Acct := ⟨(s.acct v).e + x, (s.acct v).d⟩
-    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ ((s.acct v).d = 0 ∨ Healthy b) then
+    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ ((s.acct v).d = 1 ∨ Healthy b) then
       some (setAcct (setAcct s u a) v b) else none
```

