# Specification strength: rc-knight-router

Reference `realworld/tasks/rc-knight-router/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `0fbc5447b6d56ddb`; report `9aab1e1c34799bb1`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 238 | 238 | 109 | 0 | 96 | 0 | 0 | 92 | 0 | 13 | 96 of 109 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-NORMAL-ORDER-ROUTED | 37 | 34 | kernel-checked |
| REQ-ROUTES-AVAILABLE | 48 | 10 | kernel-checked |
| REQ-NEVER-OVERROUTE | 20 | 2 | kernel-checked |
| REQ-STOP-WHEN-FILLED | 23 | 1 | kernel-checked |
| REQ-NO-EXCESS-EXECUTION | 20 | 1 | kernel-checked |
| REQ-FILL-ACCOUNTING | 58 | 44 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | boundary | `step` | `<` replaced by `≤` | survived, no observed difference |  |  |
| M002 | boundary | `step` | `<` replaced by `≤` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M003 | boundary | `step` | `<` replaced by `≤` | survived, no observed difference |  |  |
| M004 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-ROUTES-AVAILABLE |
| M005 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-STOP-WHEN-FILLED |
| M006 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NEVER-OVERROUTE |
| M007 | arith | `step` | `-` replaced by `+` | survived, no observed difference |  |  |
| M008 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M009 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M010 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-FILL-ACCOUNTING, REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-ROUTES-AVAILABLE | REQ-NO-EXCESS-EXECUTION |
| M011 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M012 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M013 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M014 | arith | `step` | `-` replaced by `+` | survived, no observed difference |  |  |
| M015 | logic | `step` | `∧` replaced by `∨` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M016 | drop-conjunct | `step` | conjunct `id < s.nParents` replaced by `True` | survived, no observed difference |  |  |
| M017 | drop-conjunct | `step` | conjunct `0 < min liq ((s.parents id).qty - (s.parents id).sent)` replaced by `True` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M018 | guard | `step` | condition `id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.pa...` replaced by `false` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M019 | guard | `step` | condition `id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.pa...` replaced by `true` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M020 | guard | `step` | condition `k < s.nChildren` replaced by `false` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M021 | guard | `step` | condition `k < s.nChildren` replaced by `true` | survived, no observed difference |  |  |
| M022 | field | `step` | update of field `nParents` dropped | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M023 | field | `step` | field read `s.nParents` replaced by `s.parents` | does not compile |  |  |
| M024 | field | `step` | field read `s.nParents` replaced by `s.children` | does not compile |  |  |
| M025 | field | `step` | field read `s.nParents` replaced by `s.nChildren` | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-ROUTES-AVAILABLE |
| M026 | field | `step` | update of field `parents` dropped | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M027 | field | `step` | field read `s.parents` replaced by `s.children` | does not compile |  |  |
| M028 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M029 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M030 | field | `step` | field read `s.nParents` replaced by `s.parents` | does not compile |  |  |
| M031 | field | `step` | field read `s.nParents` replaced by `s.nChildren` | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-ROUTES-AVAILABLE |
| M032 | field | `step` | field read `s.nParents` replaced by `s.children` | does not compile |  |  |
| M033 | field | `step` | field read `s.nParents` replaced by `s.parents` | does not compile |  |  |
| M034 | field | `step` | field read `s.nParents` replaced by `s.children` | does not compile |  |  |
| M035 | field | `step` | field read `s.nParents` replaced by `s.nChildren` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M036 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M037 | field | `step` | field read `s.parents` replaced by `s.children` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M038 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M039 | field | `step` | projection `.qty` replaced by `.parent` | does not compile |  |  |
| M040 | field | `step` | projection `.qty` replaced by `.done` | does not compile |  |  |
| M041 | field | `step` | projection `.qty` replaced by `.cum` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M042 | field | `step` | projection `.qty` replaced by `.sent` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M043 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M044 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M045 | field | `step` | field read `s.parents` replaced by `s.children` | does not compile |  |  |
| M046 | field | `step` | projection `.sent` replaced by `.qty` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M047 | field | `step` | projection `.sent` replaced by `.parent` | does not compile |  |  |
| M048 | field | `step` | projection `.sent` replaced by `.done` | does not compile |  |  |
| M049 | field | `step` | projection `.sent` replaced by `.cum` | killed by property tests | REQ-ROUTES-AVAILABLE | REQ-ROUTES-AVAILABLE |
| M050 | field | `step` | update of field `parents` dropped | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M051 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M052 | field | `step` | field read `s.parents` replaced by `s.children` | does not compile |  |  |
| M053 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M054 | field | `step` | field read `s.parents` replaced by `s.children` | does not compile |  |  |
| M055 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M056 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M057 | field | `step` | update of field `sent` dropped | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M058 | field | `step` | field read `s.parents` replaced by `s.children` | does not compile |  |  |
| M059 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M060 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M061 | field | `step` | projection `.sent` replaced by `.done` | does not compile |  |  |
| M062 | field | `step` | projection `.sent` replaced by `.cum` | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NEVER-OVERROUTE |
| M063 | field | `step` | projection `.sent` replaced by `.parent` | does not compile |  |  |
| M064 | field | `step` | projection `.sent` replaced by `.qty` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M065 | field | `step` | field read `s.parents` replaced by `s.children` | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M066 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M067 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M068 | field | `step` | projection `.qty` replaced by `.sent` | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M069 | field | `step` | projection `.qty` replaced by `.cum` | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M070 | field | `step` | projection `.qty` replaced by `.parent` | does not compile |  |  |
| M071 | field | `step` | projection `.qty` replaced by `.done` | does not compile |  |  |
| M072 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M073 | field | `step` | field read `s.parents` replaced by `s.children` | does not compile |  |  |
| M074 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M075 | field | `step` | projection `.sent` replaced by `.cum` | survived, no observed difference |  |  |
| M076 | field | `step` | projection `.sent` replaced by `.qty` | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M077 | field | `step` | projection `.sent` replaced by `.done` | does not compile |  |  |
| M078 | field | `step` | projection `.sent` replaced by `.parent` | does not compile |  |  |
| M079 | field | `step` | update of field `nChildren` dropped | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M080 | field | `step` | field read `s.nChildren` replaced by `s.nParents` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M081 | field | `step` | field read `s.nChildren` replaced by `s.children` | does not compile |  |  |
| M082 | field | `step` | field read `s.nChildren` replaced by `s.parents` | does not compile |  |  |
| M083 | field | `step` | update of field `children` dropped | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M084 | field | `step` | field read `s.children` replaced by `s.parents` | does not compile |  |  |
| M085 | field | `step` | field read `s.children` replaced by `s.nParents` | does not compile |  |  |
| M086 | field | `step` | field read `s.children` replaced by `s.nChildren` | does not compile |  |  |
| M087 | field | `step` | field read `s.nChildren` replaced by `s.nParents` | killed by property tests | REQ-FILL-ACCOUNTING |  |
| M088 | field | `step` | field read `s.nChildren` replaced by `s.parents` | does not compile |  |  |
| M089 | field | `step` | field read `s.nChildren` replaced by `s.children` | does not compile |  |  |
| M090 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M091 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M092 | field | `step` | field read `s.parents` replaced by `s.children` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M093 | field | `step` | projection `.qty` replaced by `.parent` | does not compile |  |  |
| M094 | field | `step` | projection `.qty` replaced by `.sent` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M095 | field | `step` | projection `.qty` replaced by `.done` | does not compile |  |  |
| M096 | field | `step` | projection `.qty` replaced by `.cum` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M097 | field | `step` | field read `s.parents` replaced by `s.children` | does not compile |  |  |
| M098 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M099 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M100 | field | `step` | projection `.sent` replaced by `.parent` | does not compile |  |  |
| M101 | field | `step` | projection `.sent` replaced by `.done` | does not compile |  |  |
| M102 | field | `step` | projection `.sent` replaced by `.cum` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M103 | field | `step` | projection `.sent` replaced by `.qty` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M104 | field | `step` | field read `s.parents` replaced by `s.children` | killed by property tests | REQ-FILL-ACCOUNTING, REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M105 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M106 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M107 | field | `step` | projection `.qty` replaced by `.cum` | killed by property tests | REQ-FILL-ACCOUNTING, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M108 | field | `step` | projection `.qty` replaced by `.done` | does not compile |  |  |
| M109 | field | `step` | projection `.qty` replaced by `.sent` | killed by property tests | REQ-FILL-ACCOUNTING, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M110 | field | `step` | projection `.qty` replaced by `.parent` | does not compile |  |  |
| M111 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M112 | field | `step` | field read `s.parents` replaced by `s.children` | does not compile |  |  |
| M113 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M114 | field | `step` | projection `.sent` replaced by `.parent` | does not compile |  |  |
| M115 | field | `step` | projection `.sent` replaced by `.cum` | killed by property tests | REQ-FILL-ACCOUNTING, REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-ROUTES-AVAILABLE | REQ-ROUTES-AVAILABLE |
| M116 | field | `step` | projection `.sent` replaced by `.done` | does not compile |  |  |
| M117 | field | `step` | projection `.sent` replaced by `.qty` | killed by property tests | REQ-FILL-ACCOUNTING, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M118 | field | `step` | field read `s.nChildren` replaced by `s.children` | does not compile |  |  |
| M119 | field | `step` | field read `s.nChildren` replaced by `s.parents` | does not compile |  |  |
| M120 | field | `step` | field read `s.nChildren` replaced by `s.nParents` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M121 | field | `step` | update of field `parents` dropped | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M122 | field | `step` | field read `s.parents` replaced by `s.children` | does not compile |  |  |
| M123 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M124 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M125 | field | `step` | field read `s.children` replaced by `s.parents` | does not compile |  |  |
| M126 | field | `step` | field read `s.children` replaced by `s.nChildren` | does not compile |  |  |
| M127 | field | `step` | field read `s.children` replaced by `s.nParents` | does not compile |  |  |
| M128 | field | `step` | projection `.parent` replaced by `.qty` | killed by property tests | REQ-FILL-ACCOUNTING, REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-ROUTES-AVAILABLE |
| M129 | field | `step` | projection `.parent` replaced by `.sent` | does not compile |  |  |
| M130 | field | `step` | projection `.parent` replaced by `.cum` | does not compile |  |  |
| M131 | field | `step` | projection `.parent` replaced by `.done` | killed by property tests | REQ-FILL-ACCOUNTING, REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-ROUTES-AVAILABLE |
| M132 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M133 | field | `step` | field read `s.parents` replaced by `s.children` | does not compile |  |  |
| M134 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M135 | field | `step` | field read `s.children` replaced by `s.nChildren` | does not compile |  |  |
| M136 | field | `step` | field read `s.children` replaced by `s.nParents` | does not compile |  |  |
| M137 | field | `step` | field read `s.children` replaced by `s.parents` | does not compile |  |  |
| M138 | field | `step` | projection `.parent` replaced by `.done` | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-ROUTES-AVAILABLE |
| M139 | field | `step` | projection `.parent` replaced by `.sent` | does not compile |  |  |
| M140 | field | `step` | projection `.parent` replaced by `.qty` | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M141 | field | `step` | projection `.parent` replaced by `.cum` | does not compile |  |  |
| M142 | field | `step` | update of field `cum` dropped | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M143 | field | `step` | field read `s.parents` replaced by `s.nChildren` | does not compile |  |  |
| M144 | field | `step` | field read `s.parents` replaced by `s.children` | does not compile |  |  |
| M145 | field | `step` | field read `s.parents` replaced by `s.nParents` | does not compile |  |  |
| M146 | field | `step` | field read `s.children` replaced by `s.nParents` | does not compile |  |  |
| M147 | field | `step` | field read `s.children` replaced by `s.nChildren` | does not compile |  |  |
| M148 | field | `step` | field read `s.children` replaced by `s.parents` | does not compile |  |  |
| M149 | field | `step` | projection `.parent` replaced by `.cum` | does not compile |  |  |
| M150 | field | `step` | projection `.parent` replaced by `.sent` | does not compile |  |  |
| M151 | field | `step` | projection `.parent` replaced by `.qty` | killed by property tests | REQ-FILL-ACCOUNTING |  |
| M152 | field | `step` | projection `.parent` replaced by `.done` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M153 | field | `step` | projection `.cum` replaced by `.done` | does not compile |  |  |
| M154 | field | `step` | projection `.cum` replaced by `.qty` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M155 | field | `step` | projection `.cum` replaced by `.parent` | does not compile |  |  |
| M156 | field | `step` | projection `.cum` replaced by `.sent` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M157 | field | `step` | field read `s.children` replaced by `s.parents` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M158 | field | `step` | field read `s.children` replaced by `s.nChildren` | does not compile |  |  |
| M159 | field | `step` | field read `s.children` replaced by `s.nParents` | does not compile |  |  |
| M160 | field | `step` | projection `.qty` replaced by `.parent` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M161 | field | `step` | projection `.qty` replaced by `.sent` | does not compile |  |  |
| M162 | field | `step` | projection `.qty` replaced by `.done` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M163 | field | `step` | projection `.qty` replaced by `.cum` | does not compile |  |  |
| M164 | field | `step` | field read `s.children` replaced by `s.nChildren` | does not compile |  |  |
| M165 | field | `step` | field read `s.children` replaced by `s.parents` | does not compile |  |  |
| M166 | field | `step` | field read `s.children` replaced by `s.nParents` | does not compile |  |  |
| M167 | field | `step` | projection `.done` replaced by `.cum` | does not compile |  |  |
| M168 | field | `step` | projection `.done` replaced by `.qty` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M169 | field | `step` | projection `.done` replaced by `.sent` | does not compile |  |  |
| M170 | field | `step` | projection `.done` replaced by `.parent` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M171 | field | `step` | update of field `children` dropped | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M172 | field | `step` | field read `s.children` replaced by `s.nParents` | does not compile |  |  |
| M173 | field | `step` | field read `s.children` replaced by `s.parents` | does not compile |  |  |
| M174 | field | `step` | field read `s.children` replaced by `s.nChildren` | does not compile |  |  |
| M175 | field | `step` | field read `s.children` replaced by `s.parents` | does not compile |  |  |
| M176 | field | `step` | field read `s.children` replaced by `s.nChildren` | does not compile |  |  |
| M177 | field | `step` | field read `s.children` replaced by `s.nParents` | does not compile |  |  |
| M178 | field | `step` | update of field `done` dropped | killed by property tests | REQ-FILL-ACCOUNTING |  |
| M179 | field | `step` | field read `s.children` replaced by `s.parents` | does not compile |  |  |
| M180 | field | `step` | field read `s.children` replaced by `s.nChildren` | does not compile |  |  |
| M181 | field | `step` | field read `s.children` replaced by `s.nParents` | does not compile |  |  |
| M182 | field | `step` | projection `.done` replaced by `.parent` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M183 | field | `step` | projection `.done` replaced by `.cum` | does not compile |  |  |
| M184 | field | `step` | projection `.done` replaced by `.sent` | does not compile |  |  |
| M185 | field | `step` | projection `.done` replaced by `.qty` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M186 | field | `step` | field read `s.children` replaced by `s.nParents` | does not compile |  |  |
| M187 | field | `step` | field read `s.children` replaced by `s.parents` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M188 | field | `step` | field read `s.children` replaced by `s.nChildren` | does not compile |  |  |
| M189 | field | `step` | projection `.qty` replaced by `.sent` | does not compile |  |  |
| M190 | field | `step` | projection `.qty` replaced by `.cum` | does not compile |  |  |
| M191 | field | `step` | projection `.qty` replaced by `.done` | killed by property tests | REQ-FILL-ACCOUNTING |  |
| M192 | field | `step` | projection `.qty` replaced by `.parent` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M193 | field | `step` | field read `s.children` replaced by `s.nChildren` | does not compile |  |  |
| M194 | field | `step` | field read `s.children` replaced by `s.parents` | does not compile |  |  |
| M195 | field | `step` | field read `s.children` replaced by `s.nParents` | does not compile |  |  |
| M196 | field | `step` | projection `.done` replaced by `.qty` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M197 | field | `step` | projection `.done` replaced by `.cum` | does not compile |  |  |
| M198 | field | `step` | projection `.done` replaced by `.parent` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M199 | field | `step` | projection `.done` replaced by `.sent` | does not compile |  |  |
| M200 | swap | `step` | arguments `s` and `e` of `_` swapped | does not compile |  |  |
| M201 | swap | `step` | arguments `q` and `f` of `parent` swapped | does not compile |  |  |
| M202 | swap | `step` | arguments `s.parents` and `s.nParents` of `upd` swapped | does not compile |  |  |
| M203 | swap | `step` | arguments `s.nParents` and `⟨q, f, 0, 0⟩` of `upd` swapped | does not compile |  |  |
| M204 | swap | `step` | arguments `id` and `liq` of `route` swapped | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M205 | swap | `step` | operands of `<` swapped | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M206 | swap | `step` | `min` replaced by `max` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M207 | swap | `step` | arguments `liq` and `((s.parents id).qty - (s.parents id).sent)` of `min` swapped | survived, no observed difference |  |  |
| M208 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M209 | swap | `step` | arguments `s.parents` and `id` of `upd` swapped | does not compile |  |  |
| M210 | swap | `step` | `min` replaced by `max` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M211 | swap | `step` | arguments `liq` and `((s.parents id).qty - (s.parents id).sent)` of `min` swapped | survived, no observed difference |  |  |
| M212 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M213 | swap | `step` | arguments `s.children` and `s.nChildren` of `upd` swapped | does not compile |  |  |
| M214 | swap | `step` | arguments `s.nChildren` and `⟨id, min liq ((s.parents id).qty - (s.parents id).sent), 0⟩` of `upd` swapped | does not compile |  |  |
| M215 | swap | `step` | `min` replaced by `max` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M216 | swap | `step` | arguments `liq` and `((s.parents id).qty - (s.parents id).sent)` of `min` swapped | survived, no observed difference |  |  |
| M217 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M218 | swap | `step` | `min` replaced by `max` | killed by property tests | REQ-FILL-ACCOUNTING, REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-NORMAL-ORDER-ROUTED |
| M219 | swap | `step` | arguments `liq` and `((s.parents id).qty - (s.parents id).sent)` of `min` swapped | survived, no observed difference |  |  |
| M220 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-FILL-ACCOUNTING, REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M221 | swap | `step` | arguments `k` and `q` of `fill` swapped | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M222 | swap | `step` | operands of `<` swapped | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M223 | swap | `step` | arguments `s.parents` and `(s.children k).parent` of `upd` swapped | does not compile |  |  |
| M224 | swap | `step` | `min` replaced by `max` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M225 | swap | `step` | arguments `q` and `((s.children k).qty - (s.children k).done)` of `min` swapped | survived, no observed difference |  |  |
| M226 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M227 | swap | `step` | arguments `s.children` and `k` of `upd` swapped | does not compile |  |  |
| M228 | swap | `step` | `min` replaced by `max` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M229 | swap | `step` | arguments `q` and `((s.children k).qty - (s.children k).done)` of `min` swapped | survived, no observed difference |  |  |
| M230 | swap | `step` | operands of `-` swapped | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M231 | constant | `step` | constant `1` replaced by `2` | killed by property tests | REQ-NEVER-OVERROUTE, REQ-NO-EXCESS-EXECUTION, REQ-ROUTES-AVAILABLE, REQ-STOP-WHEN-FILLED | REQ-ROUTES-AVAILABLE |
| M232 | constant | `step` | constant `1` replaced by `0` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M233 | constant | `step` | constant `0` replaced by `1` | killed by property tests | REQ-NORMAL-ORDER-ROUTED, REQ-ROUTES-AVAILABLE | REQ-NORMAL-ORDER-ROUTED |
| M234 | constant | `step` | constant `0` replaced by `1` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M235 | constant | `step` | constant `0` replaced by `1` | killed by property tests | REQ-ROUTES-AVAILABLE | REQ-ROUTES-AVAILABLE |
| M236 | constant | `step` | constant `1` replaced by `2` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M237 | constant | `step` | constant `1` replaced by `0` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |
| M238 | constant | `step` | constant `0` replaced by `1` | killed by property tests | REQ-FILL-ACCOUNTING | REQ-FILL-ACCOUNTING |

## Survivors

### M001: survived, no observed difference

`<` replaced by `≤` in `step` (line 16); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -15,3 +15,3 @@
   | .route id liq =>
-    if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
+    if id ≤ s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
       ({ s with parents := upd s.parents id
```

### M003: survived, no observed difference

`<` replaced by `≤` in `step` (line 26); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -25,3 +25,3 @@
   | .fill k q =>
-    if k < s.nChildren then
+    if k ≤ s.nChildren then
       ({ s with parents := upd s.parents (s.children k).parent
```

### M007: survived, no observed difference

`-` replaced by `+` in `step` (line 18); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -17,3 +17,3 @@
       ({ s with parents := upd s.parents id
-                  { s.parents id with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) },
+                  { s.parents id with sent := (s.parents id).sent + min liq ((s.parents id).qty + (s.parents id).sent) },
                 nChildren := s.nChildren + 1,
```

### M014: survived, no observed difference

`-` replaced by `+` in `step` (line 31); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -30,3 +30,3 @@
                 children := upd s.children k
-                  { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) } },
+                  { s.children k with done := (s.children k).done + min q ((s.children k).qty + (s.children k).done) } },
        [])
```

### M016: survived, no observed difference

conjunct `id < s.nParents` replaced by `True` in `step` (line 16); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -15,3 +15,3 @@
   | .route id liq =>
-    if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
+    if True ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
       ({ s with parents := upd s.parents id
```

### M021: survived, no observed difference

condition `k < s.nChildren` replaced by `true` in `step` (line 26); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -25,3 +25,3 @@
   | .fill k q =>
-    if k < s.nChildren then
+    if true then
       ({ s with parents := upd s.parents (s.children k).parent
```

### M075: survived, no observed difference

projection `.sent` replaced by `.cum` in `step` (line 18); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -17,3 +17,3 @@
       ({ s with parents := upd s.parents id
-                  { s.parents id with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) },
+                  { s.parents id with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).cum) },
                 nChildren := s.nChildren + 1,
```

### M207: survived, no observed difference

arguments `liq` and `((s.parents id).qty - (s.parents id).sent)` of `min` swapped in `step` (line 16); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -15,3 +15,3 @@
   | .route id liq =>
-    if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
+    if id < s.nParents ∧ 0 < min ((s.parents id).qty - (s.parents id).sent) liq then
       ({ s with parents := upd s.parents id
```

### M211: survived, no observed difference

arguments `liq` and `((s.parents id).qty - (s.parents id).sent)` of `min` swapped in `step` (line 18); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -17,3 +17,3 @@
       ({ s with parents := upd s.parents id
-                  { s.parents id with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) },
+                  { s.parents id with sent := (s.parents id).sent + min ((s.parents id).qty - (s.parents id).sent) liq },
                 nChildren := s.nChildren + 1,
```

### M216: survived, no observed difference

arguments `liq` and `((s.parents id).qty - (s.parents id).sent)` of `min` swapped in `step` (line 21); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -20,3 +20,3 @@
                 children := upd s.children s.nChildren
-                  ⟨id, min liq ((s.parents id).qty - (s.parents id).sent), 0⟩ },
+                  ⟨id, min ((s.parents id).qty - (s.parents id).sent) liq, 0⟩ },
        [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩])
```

### M219: survived, no observed difference

arguments `liq` and `((s.parents id).qty - (s.parents id).sent)` of `min` swapped in `step` (line 22); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -21,3 +21,3 @@
                   ⟨id, min liq ((s.parents id).qty - (s.parents id).sent), 0⟩ },
-       [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩])
+       [⟨id, min ((s.parents id).qty - (s.parents id).sent) liq⟩])
     else (s, [])
```

### M225: survived, no observed difference

arguments `q` and `((s.children k).qty - (s.children k).done)` of `min` swapped in `step` (line 29); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -28,3 +28,3 @@
                   { s.parents (s.children k).parent with
-                    cum := (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) },
+                    cum := (s.parents (s.children k).parent).cum + min ((s.children k).qty - (s.children k).done) q },
                 children := upd s.children k
```

### M229: survived, no observed difference

arguments `q` and `((s.children k).qty - (s.children k).done)` of `min` swapped in `step` (line 31); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -30,3 +30,3 @@
                 children := upd s.children k
-                  { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) } },
+                  { s.children k with done := (s.children k).done + min ((s.children k).qty - (s.children k).done) q } },
        [])
```

