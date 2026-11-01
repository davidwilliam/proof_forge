# Specification strength: rw-kyber-swapstep

Reference `realworld/tasks/rw-kyber-swapstep/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `46d3ba5391739b16`; report `b84f75bfae396bd1`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 151 | 151 | 138 | 0 | 70 | 0 | 0 | 70 | 31 | 37 | 70 of 138 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-IN-WITHIN-TARGET | 25 | 23 | kernel-checked |
| REQ-OUT-WITHIN-TARGET | 28 | 16 | kernel-checked |
| REQ-STEP-REACH | 23 | 10 | kernel-checked |
| REQ-STEP-PAID | 23 | 18 | kernel-checked |
| REQ-IN-FEE-LIQUIDITY | 9 | 1 | kernel-checked |
| REQ-OUT-FEE-LIQUIDITY | 8 | 1 | kernel-checked |
| REQ-POOL-CROSSES | 33 | 1 | kernel-checked |
| REQ-DEPLOYED-STEP | 0 | 0 | not shown |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | boundary | `reachAmount` | `≥` replaced by `>` | survived, no observed difference |  |  |
| M002 | boundary | `incrementalDeltaL` | `>` replaced by `≥` | survived, no observed difference |  |  |
| M003 | boundary | `computeSwapStep` | `>` replaced by `≥` | survived, behaviour differs |  |  |
| M004 | boundary | `computeSwapStep` | `≤` replaced by `<` | survived, behaviour differs |  |  |
| M005 | equality | `returnedAmount` | `==` replaced by `!=` | survived, behaviour differs |  |  |
| M006 | equality | `computeSwapStep` | `=` replaced by `≠` | killed by property tests | REQ-STEP-REACH | REQ-STEP-REACH |
| M007 | equality | `computeSwapStep` | `=` replaced by `≠` | killed by property tests | REQ-STEP-REACH | REQ-STEP-REACH |
| M008 | arith | `reachAmount` | `-` replaced by `+` | killed by property tests | REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-REACH | REQ-OUT-WITHIN-TARGET |
| M009 | arith | `reachAmount` | `-` replaced by `+` | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-REACH | REQ-IN-WITHIN-TARGET |
| M010 | arith | `incrementalDeltaL` | `-` replaced by `+` | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M011 | arith | `returnedAmount` | `+` replaced by `-` | survived, behaviour differs |  |  |
| M012 | arith | `returnedAmount` | `+` replaced by `-` | survived, behaviour differs |  |  |
| M013 | logic | `returnedAmount` | `&&` replaced by `//` | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M014 | logic | `computeSwapStep` | `&&` replaced by `//` | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-POOL-CROSSES |
| M015 | logic | `computeSwapStep` | `//` replaced by `&&` | killed by property tests | REQ-STEP-REACH | REQ-STEP-REACH |
| M016 | logic | `computeSwapStep` | `&&` replaced by `//` | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-IN-WITHIN-TARGET |
| M017 | drop-conjunct | `returnedAmount` | conjunct `isExactInput` replaced by `true` | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M018 | drop-conjunct | `returnedAmount` | conjunct `x + y == 1` replaced by `true` | survived, behaviour differs |  |  |
| M019 | drop-conjunct | `computeSwapStep` | conjunct `isExactInput` replaced by `true` | killed by property tests | REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-OUT-WITHIN-TARGET |
| M020 | drop-conjunct | `computeSwapStep` | conjunct `decide (reach > specifiedAmount)` replaced by `true` | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-IN-WITHIN-TARGET |
| M021 | drop-conjunct | `computeSwapStep` | conjunct `!isExactInput` replaced by `true` | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-IN-WITHIN-TARGET |
| M022 | drop-conjunct | `computeSwapStep` | conjunct `decide (reach ≤ specifiedAmount)` replaced by `true` | killed by property tests | REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-OUT-WITHIN-TARGET |
| M023 | guard | `reachAmount` | condition `currentSqrtP.toNat ≥ targetSqrtP.toNat` replaced by `false` | killed by property tests | REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-OUT-WITHIN-TARGET |
| M024 | guard | `reachAmount` | condition `currentSqrtP.toNat ≥ targetSqrtP.toNat` replaced by `true` | survived, behaviour differs |  |  |
| M025 | guard | `reachAmount` | condition `isExactInput` replaced by `false` | killed by property tests | REQ-STEP-REACH | REQ-STEP-REACH |
| M026 | guard | `reachAmount` | condition `isExactInput` replaced by `true` | killed by property tests | REQ-STEP-REACH | REQ-STEP-REACH |
| M027 | guard | `estimateDeltaL` | condition `isExactInput` replaced by `true` | killed by property tests | REQ-OUT-FEE-LIQUIDITY, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-OUT-FEE-LIQUIDITY |
| M028 | guard | `estimateDeltaL` | condition `isExactInput` replaced by `false` | killed by property tests | REQ-IN-FEE-LIQUIDITY, REQ-IN-WITHIN-TARGET | REQ-IN-FEE-LIQUIDITY |
| M029 | guard | `finalPrice` | condition `isExactInput` replaced by `true` | killed by property tests | REQ-OUT-WITHIN-TARGET | REQ-OUT-WITHIN-TARGET |
| M030 | guard | `finalPrice` | condition `isExactInput` replaced by `false` | killed by property tests | REQ-IN-WITHIN-TARGET | REQ-IN-WITHIN-TARGET |
| M031 | guard | `incrementalDeltaL` | condition `isExactInput` replaced by `false` | survived, behaviour differs |  |  |
| M032 | guard | `incrementalDeltaL` | condition `isExactInput` replaced by `true` | survived, behaviour differs |  |  |
| M033 | guard | `incrementalDeltaL` | condition `tmp3.toNat > liquidity.toNat` replaced by `false` | survived, behaviour differs |  |  |
| M034 | guard | `incrementalDeltaL` | condition `tmp3.toNat > liquidity.toNat` replaced by `true` | survived, behaviour differs |  |  |
| M035 | guard | `returnedAmount` | condition `isExactInput && x + y == 1` replaced by `true` | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M036 | guard | `returnedAmount` | condition `isExactInput && x + y == 1` replaced by `false` | survived, behaviour differs |  |  |
| M037 | guard | `computeSwapStep` | condition `currentSqrtP = targetSqrtP` replaced by `true` | killed by property tests | REQ-STEP-REACH | REQ-STEP-REACH |
| M038 | guard | `computeSwapStep` | condition `currentSqrtP = targetSqrtP` replaced by `false` | survived, no observed difference |  |  |
| M039 | guard | `computeSwapStep` | condition `notReached` replaced by `true` | survived, behaviour differs |  |  |
| M040 | guard | `computeSwapStep` | condition `notReached` replaced by `false` | killed by property tests | REQ-STEP-REACH | REQ-STEP-REACH |
| M041 | guard | `computeSwapStep` | condition `notReached` replaced by `false` | survived, behaviour differs |  |  |
| M042 | guard | `computeSwapStep` | condition `notReached` replaced by `true` | killed by property tests | REQ-STEP-REACH | REQ-STEP-REACH |
| M043 | guard | `computeSwapStep` | condition `nextSqrtP = 0` replaced by `true` | killed by property tests | REQ-STEP-REACH | REQ-STEP-REACH |
| M044 | guard | `computeSwapStep` | condition `nextSqrtP = 0` replaced by `false` | survived, behaviour differs |  |  |
| M045 | swap | `reachAmount` | operands of `≥` swapped | killed by property tests | REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-OUT-WITHIN-TARGET |
| M046 | swap | `reachAmount` | operands of `-` swapped | killed by property tests | REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-OUT-WITHIN-TARGET |
| M047 | swap | `reachAmount` | operands of `-` swapped | survived, behaviour differs |  |  |
| M048 | swap | `reachAmount` | arguments `(← mul TWO_FEE_UNITS currentSqrtP)` and `(← mul feeInFeeUnits targetSqrtP)` of `sub` swapped | survived, behaviour differs |  |  |
| M049 | swap | `reachAmount` | arguments `TWO_FEE_UNITS` and `currentSqrtP` of `mul` swapped | survived, no observed difference |  |  |
| M050 | swap | `reachAmount` | arguments `feeInFeeUnits` and `targetSqrtP` of `mul` swapped | survived, no observed difference |  |  |
| M051 | swap | `reachAmount` | arguments `liquidity` and `(← mul TWO_FEE_UNITS absPriceDiff)` of `mulDivFloor` swapped | survived, no observed difference |  |  |
| M052 | swap | `reachAmount` | arguments `(← mul TWO_FEE_UNITS absPriceDiff)` and `denominator` of `mulDivFloor` swapped | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-REACH | REQ-IN-WITHIN-TARGET |
| M053 | swap | `reachAmount` | arguments `TWO_FEE_UNITS` and `absPriceDiff` of `mul` swapped | survived, no observed difference |  |  |
| M054 | swap | `reachAmount` | arguments `numerator` and `currentSqrtP` of `mulDivFloor` swapped | survived, no observed difference |  |  |
| M055 | swap | `reachAmount` | arguments `currentSqrtP` and `TWO_POW_96` of `mulDivFloor` swapped | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-REACH | REQ-IN-WITHIN-TARGET |
| M056 | swap | `reachAmount` | arguments `(← mul TWO_FEE_UNITS targetSqrtP)` and `(← mul feeInFeeUnits currentSqrtP)` of `sub` swapped | survived, behaviour differs |  |  |
| M057 | swap | `reachAmount` | arguments `TWO_FEE_UNITS` and `targetSqrtP` of `mul` swapped | survived, no observed difference |  |  |
| M058 | swap | `reachAmount` | arguments `feeInFeeUnits` and `currentSqrtP` of `mul` swapped | survived, no observed difference |  |  |
| M059 | swap | `reachAmount` | arguments `denominator` and `(← mul feeInFeeUnits targetSqrtP)` of `sub` swapped | killed by property tests | REQ-STEP-REACH | REQ-STEP-REACH |
| M060 | swap | `reachAmount` | arguments `feeInFeeUnits` and `targetSqrtP` of `mul` swapped | survived, no observed difference |  |  |
| M061 | swap | `reachAmount` | arguments `liquidity` and `numerator` of `mulDivFloor` swapped | survived, no observed difference |  |  |
| M062 | swap | `reachAmount` | arguments `numerator` and `denominator` of `mulDivFloor` swapped | killed by property tests | REQ-OUT-WITHIN-TARGET, REQ-STEP-REACH | REQ-OUT-WITHIN-TARGET |
| M063 | swap | `reachAmount` | arguments `numerator` and `absPriceDiff` of `mulDivFloor` swapped | survived, no observed difference |  |  |
| M064 | swap | `reachAmount` | arguments `absPriceDiff` and `TWO_POW_96` of `mulDivFloor` swapped | killed by property tests | REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-REACH | REQ-OUT-WITHIN-TARGET |
| M065 | swap | `smallerRoot` | arguments `(← mul b b)` and `(← mul a c)` of `sub` swapped | survived, behaviour differs |  |  |
| M066 | swap | `smallerRoot` | arguments `a` and `c` of `mul` swapped | survived, no observed difference |  |  |
| M067 | swap | `smallerRoot` | arguments `(← sub b s)` and `a` of `divFloor` swapped | killed by property tests | REQ-OUT-FEE-LIQUIDITY, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-OUT-WITHIN-TARGET |
| M068 | swap | `smallerRoot` | arguments `b` and `s` of `sub` swapped | survived, behaviour differs |  |  |
| M069 | swap | `estimateDeltaL` | arguments `(← mulDivFloor absDelta TWO_POW_96 currentSqrtP)` and `feeInFeeUnits` of `mulDivCeiling` swapped | survived, no observed difference |  |  |
| M070 | swap | `estimateDeltaL` | arguments `absDelta` and `TWO_POW_96` of `mulDivFloor` swapped | survived, no observed difference |  |  |
| M071 | swap | `estimateDeltaL` | arguments `TWO_POW_96` and `currentSqrtP` of `mulDivFloor` swapped | killed by property tests | REQ-IN-FEE-LIQUIDITY, REQ-IN-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-IN-WITHIN-TARGET |
| M072 | swap | `estimateDeltaL` | arguments `feeInFeeUnits` and `TWO_FEE_UNITS` of `mulDivCeiling` swapped | killed by property tests | REQ-IN-FEE-LIQUIDITY, REQ-IN-WITHIN-TARGET | REQ-IN-WITHIN-TARGET |
| M073 | swap | `estimateDeltaL` | arguments `(← sub FEE_UNITS feeInFeeUnits)` and `liquidity` of `mul` swapped | survived, no observed difference |  |  |
| M074 | swap | `estimateDeltaL` | arguments `FEE_UNITS` and `feeInFeeUnits` of `sub` swapped | survived, behaviour differs |  |  |
| M075 | swap | `estimateDeltaL` | arguments `(← mul feeInFeeUnits liquidity)` and `absDelta` of `mul` swapped | survived, no observed difference |  |  |
| M076 | swap | `estimateDeltaL` | arguments `feeInFeeUnits` and `liquidity` of `mul` swapped | survived, no observed difference |  |  |
| M077 | swap | `estimateDeltaL` | arguments `b` and `(← mulDivFloor (← mul FEE_UNITS absDelta) TWO_POW_96 curr...` of `sub` swapped | survived, behaviour differs |  |  |
| M078 | swap | `estimateDeltaL` | arguments `(← mul FEE_UNITS absDelta)` and `TWO_POW_96` of `mulDivFloor` swapped | survived, no observed difference |  |  |
| M079 | swap | `estimateDeltaL` | arguments `FEE_UNITS` and `absDelta` of `mul` swapped | survived, no observed difference |  |  |
| M080 | swap | `estimateDeltaL` | arguments `TWO_POW_96` and `currentSqrtP` of `mulDivFloor` swapped | killed by property tests | REQ-OUT-FEE-LIQUIDITY, REQ-OUT-WITHIN-TARGET | REQ-OUT-WITHIN-TARGET |
| M081 | swap | `estimateDeltaL` | arguments `c` and `TWO_POW_96` of `mulDivFloor` swapped | survived, no observed difference |  |  |
| M082 | swap | `estimateDeltaL` | arguments `TWO_POW_96` and `currentSqrtP` of `mulDivFloor` swapped | killed by property tests | REQ-OUT-FEE-LIQUIDITY, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-OUT-WITHIN-TARGET |
| M083 | swap | `estimateDeltaL` | arguments `feeInFeeUnits` and `b` of `smallerRoot` swapped | survived, behaviour differs |  |  |
| M084 | swap | `estimateDeltaL` | arguments `b` and `c` of `smallerRoot` swapped | killed by property tests | REQ-OUT-FEE-LIQUIDITY, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-OUT-WITHIN-TARGET |
| M085 | swap | `finalPrice` | arguments `absDelta` and `TWO_POW_96` of `mulDivFloor` swapped | survived, no observed difference |  |  |
| M086 | swap | `finalPrice` | arguments `TWO_POW_96` and `currentSqrtP` of `mulDivFloor` swapped | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-PAID | REQ-IN-WITHIN-TARGET |
| M087 | swap | `finalPrice` | arguments `(← add liquidity tmp)` and `currentSqrtP` of `mulDivFloor` swapped | survived, no observed difference |  |  |
| M088 | swap | `finalPrice` | arguments `liquidity` and `tmp` of `add` swapped | survived, no observed difference |  |  |
| M089 | swap | `finalPrice` | arguments `currentSqrtP` and `(← add liquidity deltaL)` of `mulDivFloor` swapped | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-PAID | REQ-IN-WITHIN-TARGET |
| M090 | swap | `finalPrice` | arguments `liquidity` and `deltaL` of `add` swapped | survived, no observed difference |  |  |
| M091 | swap | `finalPrice` | arguments `(← sub liquidity tmp)` and `currentSqrtP` of `mulDivCeiling` swapped | survived, no observed difference |  |  |
| M092 | swap | `finalPrice` | arguments `liquidity` and `tmp` of `sub` swapped | survived, behaviour differs |  |  |
| M093 | swap | `finalPrice` | arguments `currentSqrtP` and `(← add liquidity deltaL)` of `mulDivCeiling` swapped | killed by property tests | REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-OUT-WITHIN-TARGET |
| M094 | swap | `finalPrice` | arguments `liquidity` and `deltaL` of `add` swapped | survived, no observed difference |  |  |
| M095 | swap | `incrementalDeltaL` | arguments `liquidity` and `currentSqrtP` of `mulDivFloor` swapped | survived, no observed difference |  |  |
| M096 | swap | `incrementalDeltaL` | arguments `currentSqrtP` and `TWO_POW_96` of `mulDivFloor` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M097 | swap | `incrementalDeltaL` | arguments `tmp1` and `absDelta` of `add` swapped | survived, no observed difference |  |  |
| M098 | swap | `incrementalDeltaL` | arguments `tmp1` and `absDelta` of `sub` swapped | survived, behaviour differs |  |  |
| M099 | swap | `incrementalDeltaL` | arguments `tmp2` and `TWO_POW_96` of `mulDivFloor` swapped | survived, no observed difference |  |  |
| M100 | swap | `incrementalDeltaL` | arguments `TWO_POW_96` and `nextSqrtP` of `mulDivFloor` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M101 | swap | `incrementalDeltaL` | operands of `>` swapped | survived, behaviour differs |  |  |
| M102 | swap | `incrementalDeltaL` | operands of `-` swapped | survived, behaviour differs |  |  |
| M103 | swap | `returnedAmount` | arguments `(← add liquidity deltaL)` and `TWO_POW_96` of `mulDivCeiling` swapped | survived, no observed difference |  |  |
| M104 | swap | `returnedAmount` | arguments `liquidity` and `deltaL` of `add` swapped | survived, no observed difference |  |  |
| M105 | swap | `returnedAmount` | arguments `TWO_POW_96` and `nextSqrtP` of `mulDivCeiling` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M106 | swap | `returnedAmount` | arguments `liquidity` and `TWO_POW_96` of `mulDivFloor` swapped | survived, no observed difference |  |  |
| M107 | swap | `returnedAmount` | arguments `TWO_POW_96` and `currentSqrtP` of `mulDivFloor` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M108 | swap | `computeSwapStep` | arguments `currentSqrtP` and `targetSqrtP` of `liquidity` swapped | killed by property tests | REQ-IN-FEE-LIQUIDITY, REQ-IN-WITHIN-TARGET, REQ-OUT-FEE-LIQUIDITY, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-PAID, REQ-STEP-REACH | REQ-IN-WITHIN-TARGET |
| M109 | swap | `computeSwapStep` | arguments `targetSqrtP` and `feeInFeeUnits` of `liquidity` swapped | killed by property tests | REQ-IN-FEE-LIQUIDITY, REQ-IN-WITHIN-TARGET, REQ-STEP-REACH | REQ-IN-WITHIN-TARGET |
| M110 | swap | `computeSwapStep` | arguments `feeInFeeUnits` and `specifiedAmount` of `liquidity` swapped | does not compile |  |  |
| M111 | swap | `computeSwapStep` | arguments `specifiedAmount` and `isExactInput` of `liquidity` swapped | does not compile |  |  |
| M112 | swap | `computeSwapStep` | arguments `liquidity` and `currentSqrtP` of `reachAmount` swapped | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-REACH | REQ-IN-WITHIN-TARGET |
| M113 | swap | `computeSwapStep` | arguments `currentSqrtP` and `targetSqrtP` of `reachAmount` swapped | killed by property tests | REQ-OUT-WITHIN-TARGET, REQ-STEP-REACH | REQ-OUT-WITHIN-TARGET |
| M114 | swap | `computeSwapStep` | arguments `targetSqrtP` and `feeInFeeUnits` of `reachAmount` swapped | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-REACH | REQ-IN-WITHIN-TARGET |
| M115 | swap | `computeSwapStep` | arguments `feeInFeeUnits` and `isExactInput` of `reachAmount` swapped | does not compile |  |  |
| M116 | swap | `computeSwapStep` | operands of `>` swapped | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-REACH | REQ-IN-WITHIN-TARGET |
| M117 | swap | `computeSwapStep` | operands of `≤` swapped | killed by property tests | REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-REACH | REQ-OUT-WITHIN-TARGET |
| M118 | swap | `computeSwapStep` | arguments `256` and `usedAmount.natAbs` of `BitVec.ofNat` swapped | does not compile |  |  |
| M119 | swap | `computeSwapStep` | arguments `absDelta` and `liquidity` of `estimateDeltaL` swapped | killed by property tests | REQ-IN-FEE-LIQUIDITY, REQ-IN-WITHIN-TARGET, REQ-OUT-FEE-LIQUIDITY, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-IN-WITHIN-TARGET |
| M120 | swap | `computeSwapStep` | arguments `liquidity` and `currentSqrtP` of `estimateDeltaL` swapped | killed by property tests | REQ-IN-FEE-LIQUIDITY, REQ-IN-WITHIN-TARGET, REQ-OUT-FEE-LIQUIDITY, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-IN-WITHIN-TARGET |
| M121 | swap | `computeSwapStep` | arguments `currentSqrtP` and `feeInFeeUnits` of `estimateDeltaL` swapped | killed by property tests | REQ-IN-FEE-LIQUIDITY, REQ-IN-WITHIN-TARGET | REQ-IN-WITHIN-TARGET |
| M122 | swap | `computeSwapStep` | arguments `feeInFeeUnits` and `isExactInput` of `estimateDeltaL` swapped | does not compile |  |  |
| M123 | swap | `computeSwapStep` | arguments `absDelta` and `liquidity` of `finalPrice` swapped | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-PAID | REQ-IN-WITHIN-TARGET |
| M124 | swap | `computeSwapStep` | arguments `liquidity` and `deltaL` of `finalPrice` swapped | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-IN-WITHIN-TARGET |
| M125 | swap | `computeSwapStep` | arguments `deltaL` and `currentSqrtP` of `finalPrice` swapped | killed by property tests | REQ-IN-WITHIN-TARGET, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES, REQ-STEP-PAID | REQ-IN-WITHIN-TARGET |
| M126 | swap | `computeSwapStep` | arguments `currentSqrtP` and `isExactInput` of `finalPrice` swapped | does not compile |  |  |
| M127 | swap | `computeSwapStep` | arguments `liquidity` and `currentSqrtP` of `returnedAmount` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M128 | swap | `computeSwapStep` | arguments `currentSqrtP` and `nextSqrtP` of `returnedAmount` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M129 | swap | `computeSwapStep` | arguments `nextSqrtP` and `deltaL` of `returnedAmount` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M130 | swap | `computeSwapStep` | arguments `deltaL` and `isExactInput` of `returnedAmount` swapped | does not compile |  |  |
| M131 | swap | `computeSwapStep` | arguments `absDelta` and `liquidity` of `incrementalDeltaL` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M132 | swap | `computeSwapStep` | arguments `liquidity` and `currentSqrtP` of `incrementalDeltaL` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M133 | swap | `computeSwapStep` | arguments `currentSqrtP` and `nextSqrtP` of `incrementalDeltaL` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M134 | swap | `computeSwapStep` | arguments `nextSqrtP` and `isExactInput` of `incrementalDeltaL` swapped | does not compile |  |  |
| M135 | swap | `computeSwapStep` | arguments `liquidity` and `currentSqrtP` of `returnedAmount` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M136 | swap | `computeSwapStep` | arguments `currentSqrtP` and `nextSqrtP` of `returnedAmount` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M137 | swap | `computeSwapStep` | arguments `nextSqrtP` and `deltaL` of `returnedAmount` swapped | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M138 | swap | `computeSwapStep` | arguments `deltaL` and `isExactInput` of `returnedAmount` swapped | does not compile |  |  |
| M139 | constant | `incrementalDeltaL` | constant `0` replaced by `1` | killed by property tests | REQ-STEP-PAID | REQ-STEP-PAID |
| M140 | constant | `returnedAmount` | constant `1` replaced by `2` | survived, behaviour differs |  |  |
| M141 | constant | `returnedAmount` | constant `1` replaced by `0` | survived, behaviour differs |  |  |
| M142 | constant | `returnedAmount` | constant `0` replaced by `1` | survived, behaviour differs |  |  |
| M143 | constant | `computeSwapStep` | constant `0` replaced by `1` | survived, no observed difference |  |  |
| M144 | constant | `computeSwapStep` | constant `0` replaced by `1` | survived, no observed difference |  |  |
| M145 | constant | `computeSwapStep` | constant `0` replaced by `1` | survived, no observed difference |  |  |
| M146 | constant | `computeSwapStep` | constant `0` replaced by `1` | killed by property tests | REQ-IN-FEE-LIQUIDITY, REQ-IN-WITHIN-TARGET, REQ-OUT-WITHIN-TARGET, REQ-POOL-CROSSES | REQ-IN-WITHIN-TARGET |
| M147 | constant | `computeSwapStep` | constant `256` replaced by `255` | does not compile |  |  |
| M148 | constant | `computeSwapStep` | constant `256` replaced by `2560` | does not compile |  |  |
| M149 | constant | `computeSwapStep` | constant `256` replaced by `25` | does not compile |  |  |
| M150 | constant | `computeSwapStep` | constant `256` replaced by `257` | does not compile |  |  |
| M151 | constant | `computeSwapStep` | constant `0` replaced by `1` | survived, behaviour differs |  |  |

## Survivors

### M001: survived, no observed difference

`≥` replaced by `>` in `reachAmount` (line 45); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -44,3 +44,3 @@
   let absPriceDiff : U256 :=
-    if currentSqrtP.toNat ≥ targetSqrtP.toNat then currentSqrtP - targetSqrtP
+    if currentSqrtP.toNat > targetSqrtP.toNat then currentSqrtP - targetSqrtP
     else targetSqrtP - currentSqrtP
```

### M002: survived, no observed difference

`>` replaced by `≥` in `incrementalDeltaL` (line 108); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -107,3 +107,3 @@
   let tmp3 ← mulDivFloor tmp2 TWO_POW_96 nextSqrtP
-  pure (if tmp3.toNat > liquidity.toNat then tmp3 - liquidity else 0)
+  pure (if tmp3.toNat ≥ liquidity.toNat then tmp3 - liquidity else 0)
 
```

### M003: survived, behaviour differs

`>` replaced by `≥` in `computeSwapStep` (line 122); outputs differ from the reference on 486 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -121,3 +121,3 @@
   let reach ← reachAmount liquidity currentSqrtP targetSqrtP feeInFeeUnits isExactInput
-  let notReached : Bool := (isExactInput && decide (reach > specifiedAmount)) ||
+  let notReached : Bool := (isExactInput && decide (reach ≥ specifiedAmount)) ||
     (!isExactInput && decide (reach ≤ specifiedAmount))
```

First differing case:

```json
{"input": {"F": 1, "L": 11835631486589, "exact_input": true, "limit": 8134326689118409383055140654667763559952, "op": "loop", "p": 8134245346664942733627804376623997319982, "spec": 12151539065453226750, "tick": 8134326689118409383055140654667763559952}, "output": {"crossed": false, "deltaL": 592, "next": 8134326689117122948799492216544171321652, "returned": 0, "used": 12151539065453226750}, "reference_output": {"crossed": true, "deltaL": 591, "next": 8134326689118409383055140654667763559952, "returned": 0, "used": 12151539065453226750}}
```

### M004: survived, behaviour differs

`≤` replaced by `<` in `computeSwapStep` (line 123); outputs differ from the reference on 671 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -122,3 +122,3 @@
   let notReached : Bool := (isExactInput && decide (reach > specifiedAmount)) ||
-    (!isExactInput && decide (reach ≤ specifiedAmount))
+    (!isExactInput && decide (reach < specifiedAmount))
   let usedAmount := if notReached then specifiedAmount else reach
```

First differing case:

```json
{"input": {"F": 8, "L": 488099447615, "c": 12702106732281905876958584314416, "exact_input": false, "op": "step", "spec": -76421257163, "t": 12689701559484189505314970178876}, "output": {"deltaL": 19086, "next": 12689701559484189505314970178876, "returned": 2976330, "used": -76421257163}, "reference_output": {"deltaL": 19086, "next": 12689701559509978602990516944905, "returned": 2976330, "used": -76421257163}}
```

### M005: survived, behaviour differs

`==` replaced by `!=` in `returnedAmount` (line 115); outputs differ from the reference on 5847 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -114,3 +114,3 @@
   let y ← revToInt256 (← mulDivFloor liquidity TWO_POW_96 currentSqrtP)
-  pure (if isExactInput && x + y == 1 then 0 else x + y)
+  pure (if isExactInput && x + y != 1 then 0 else x + y)
 
```

First differing case:

```json
{"input": {"F": 300, "L": 529700652, "c": 26908681593376338809905220921561871, "exact_input": true, "op": "step", "spec": 1816821696332, "t": 27180014754403994732126507336932861}, "output": {"deltaL": 8024, "next": 27180014703364498790021120733517497, "returned": 0, "used": 1816821696332}, "reference_output": {"deltaL": 8024, "next": 27180014703364498790021120733517497, "returned": -14, "used": 1816821696332}}
```

### M011: survived, behaviour differs

`+` replaced by `-` in `returnedAmount` (line 115); outputs differ from the reference on 964 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -114,3 +114,3 @@
   let y ← revToInt256 (← mulDivFloor liquidity TWO_POW_96 currentSqrtP)
-  pure (if isExactInput && x + y == 1 then 0 else x + y)
+  pure (if isExactInput && x - y == 1 then 0 else x + y)
 
```

First differing case:

```json
{"input": {"F": 1, "L": 11835631486589, "exact_input": true, "limit": 8134326689118409383055140654667763559952, "op": "loop", "p": 8134245346664942733627804376623997319982, "spec": 12151539065453226750, "tick": 8134326689118409383055140654667763559952}, "output": {"crossed": true, "deltaL": 591, "next": 8134326689118409383055140654667763559952, "returned": 1, "used": 12151539065453226750}, "reference_output": {"crossed": true, "deltaL": 591, "next": 8134326689118409383055140654667763559952, "returned": 0, "used": 12151539065453226750}}
```

### M012: survived, behaviour differs

`+` replaced by `-` in `returnedAmount` (line 115); outputs differ from the reference on 8351 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -114,3 +114,3 @@
   let y ← revToInt256 (← mulDivFloor liquidity TWO_POW_96 currentSqrtP)
-  pure (if isExactInput && x + y == 1 then 0 else x + y)
+  pure (if isExactInput && x + y == 1 then 0 else x - y)
 
```

First differing case:

```json
{"input": {"F": 300, "L": 529700652, "c": 26908681593376338809905220921561871, "exact_input": true, "op": "step", "spec": 1816821696332, "t": 27180014754403994732126507336932861}, "output": {"deltaL": 8024, "next": 27180014703364498790021120733517497, "returned": 3104, "used": 1816821696332}, "reference_output": {"deltaL": 8024, "next": 27180014703364498790021120733517497, "returned": -14, "used": 1816821696332}}
```

### M018: survived, behaviour differs

conjunct `x + y == 1` replaced by `true` in `returnedAmount` (line 115); outputs differ from the reference on 4032 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -114,3 +114,3 @@
   let y ← revToInt256 (← mulDivFloor liquidity TWO_POW_96 currentSqrtP)
-  pure (if isExactInput && x + y == 1 then 0 else x + y)
+  pure (if isExactInput && true then 0 else x + y)
 
```

First differing case:

```json
{"input": {"F": 300, "L": 529700652, "c": 26908681593376338809905220921561871, "exact_input": true, "op": "step", "spec": 1816821696332, "t": 27180014754403994732126507336932861}, "output": {"deltaL": 8024, "next": 27180014703364498790021120733517497, "returned": 0, "used": 1816821696332}, "reference_output": {"deltaL": 8024, "next": 27180014703364498790021120733517497, "returned": -14, "used": 1816821696332}}
```

### M024: survived, behaviour differs

condition `currentSqrtP.toNat ≥ targetSqrtP.toNat` replaced by `true` in `reachAmount` (line 45); outputs differ from the reference on 5934 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -44,3 +44,3 @@
   let absPriceDiff : U256 :=
-    if currentSqrtP.toNat ≥ targetSqrtP.toNat then currentSqrtP - targetSqrtP
+    if true then currentSqrtP - targetSqrtP
     else targetSqrtP - currentSqrtP
```

First differing case:

```json
{"input": {"F": 300, "L": 529700652, "c": 26908681593376338809905220921561871, "exact_input": true, "op": "step", "spec": 1816821696332, "t": 27180014754403994732126507336932861}, "output": {"revert": true}, "reference_output": {"deltaL": 8024, "next": 27180014703364498790021120733517497, "returned": -14, "used": 1816821696332}}
```

### M031: survived, behaviour differs

condition `isExactInput` replaced by `false` in `incrementalDeltaL` (line 106); outputs differ from the reference on 1313 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -105,3 +105,3 @@
   let tmp1 ← mulDivFloor liquidity currentSqrtP TWO_POW_96
-  let tmp2 ← if isExactInput then add tmp1 absDelta else sub tmp1 absDelta
+  let tmp2 ← if false then add tmp1 absDelta else sub tmp1 absDelta
   let tmp3 ← mulDivFloor tmp2 TWO_POW_96 nextSqrtP
```

First differing case:

```json
{"input": {"F": 5000, "L": 114511474751133240, "c": 1768618780558846531704109, "exact_input": true, "op": "step", "spec": 117759443580777905, "t": 1768620549177627090550637}, "output": {"deltaL": 0, "next": 1768620549177627090550637, "returned": -5129723125488622, "used": 2621796}, "reference_output": {"deltaL": 2936124348, "next": 1768620549177627090550637, "returned": -4998194778657190, "used": 2621796}}
```

### M032: survived, behaviour differs

condition `isExactInput` replaced by `true` in `incrementalDeltaL` (line 106); outputs differ from the reference on 921 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -105,3 +105,3 @@
   let tmp1 ← mulDivFloor liquidity currentSqrtP TWO_POW_96
-  let tmp2 ← if isExactInput then add tmp1 absDelta else sub tmp1 absDelta
+  let tmp2 ← if true then add tmp1 absDelta else sub tmp1 absDelta
   let tmp3 ← mulDivFloor tmp2 TWO_POW_96 nextSqrtP
```

First differing case:

```json
{"input": {"F": 40, "L": 108217392398391914380679, "c": 593096295975945169826734454010, "exact_input": false, "op": "step", "spec": -389171309622958030772848263925050973890866947489, "t": 593036986346347575309751780568}, "output": {"deltaL": 21643478046635609164, "next": 593036986346347575309751780568, "returned": 4337266596271834561, "used": -80994552088830996549}, "reference_output": {"deltaL": 2164997347171989, "next": 593036986346347575309751780568, "returned": 1446044789256704914, "used": -80994552088830996549}}
```

### M033: survived, behaviour differs

condition `tmp3.toNat > liquidity.toNat` replaced by `false` in `incrementalDeltaL` (line 108); outputs differ from the reference on 2181 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -107,3 +107,3 @@
   let tmp3 ← mulDivFloor tmp2 TWO_POW_96 nextSqrtP
-  pure (if tmp3.toNat > liquidity.toNat then tmp3 - liquidity else 0)
+  pure (if false then tmp3 - liquidity else 0)
 
```

First differing case:

```json
{"input": {"F": 40, "L": 108217392398391914380679, "c": 593096295975945169826734454010, "exact_input": false, "op": "step", "spec": -389171309622958030772848263925050973890866947489, "t": 593036986346347575309751780568}, "output": {"deltaL": 0, "next": 593036986346347575309751780568, "returned": 1445755551375065409, "used": -80994552088830996549}, "reference_output": {"deltaL": 2164997347171989, "next": 593036986346347575309751780568, "returned": 1446044789256704914, "used": -80994552088830996549}}
```

### M034: survived, behaviour differs

condition `tmp3.toNat > liquidity.toNat` replaced by `true` in `incrementalDeltaL` (line 108); outputs differ from the reference on 4007 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -107,3 +107,3 @@
   let tmp3 ← mulDivFloor tmp2 TWO_POW_96 nextSqrtP
-  pure (if tmp3.toNat > liquidity.toNat then tmp3 - liquidity else 0)
+  pure (if true then tmp3 - liquidity else 0)
 
```

First differing case:

```json
{"input": {"F": 8, "L": 25161464621522265473872234, "c": 6923045277, "exact_input": false, "op": "step", "spec": -2, "t": 6923044695}, "output": {"revert": true}, "reference_output": {"deltaL": 0, "next": 6923044695, "returned": 24207178820697488421421831942848940349, "used": 0}}
```

### M036: survived, behaviour differs

condition `isExactInput && x + y == 1` replaced by `false` in `returnedAmount` (line 115); outputs differ from the reference on 1815 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -114,3 +114,3 @@
   let y ← revToInt256 (← mulDivFloor liquidity TWO_POW_96 currentSqrtP)
-  pure (if isExactInput && x + y == 1 then 0 else x + y)
+  pure (if false then 0 else x + y)
 
```

First differing case:

```json
{"input": {"F": 70816, "L": 100, "c": 258160166490085118035590902532276590381579843345, "exact_input": true, "op": "step", "spec": 8208598693430159375, "t": 264456692950778294064478964645038816420986575728}, "output": {"deltaL": 1, "next": 260716207742462198412180911468239724939813307140, "returned": 1, "used": 8208598693430159375}, "reference_output": {"deltaL": 1, "next": 260716207742462198412180911468239724939813307140, "returned": 0, "used": 8208598693430159375}}
```

### M038: survived, no observed difference

condition `currentSqrtP = targetSqrtP` replaced by `false` in `computeSwapStep` (line 120); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -119,3 +119,3 @@
 def computeSwapStep : StepFn := fun liquidity currentSqrtP targetSqrtP feeInFeeUnits specifiedAmount isExactInput => do
-  if currentSqrtP = targetSqrtP then return ⟨0, 0, 0, currentSqrtP⟩
+  if false then return ⟨0, 0, 0, currentSqrtP⟩
   let reach ← reachAmount liquidity currentSqrtP targetSqrtP feeInFeeUnits isExactInput
```

### M039: survived, behaviour differs

condition `notReached` replaced by `true` in `computeSwapStep` (line 124); outputs differ from the reference on 6066 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -123,3 +123,3 @@
     (!isExactInput && decide (reach ≤ specifiedAmount))
-  let usedAmount := if notReached then specifiedAmount else reach
+  let usedAmount := if true then specifiedAmount else reach
   let nextSqrtP : U256 := if notReached then 0 else targetSqrtP
```

First differing case:

```json
{"input": {"F": 40, "L": 108217392398391914380679, "c": 593096295975945169826734454010, "exact_input": false, "op": "step", "spec": -389171309622958030772848263925050973890866947489, "t": 593036986346347575309751780568}, "output": {"revert": true}, "reference_output": {"deltaL": 2164997347171989, "next": 593036986346347575309751780568, "returned": 1446044789256704914, "used": -80994552088830996549}}
```

### M041: survived, behaviour differs

condition `notReached` replaced by `false` in `computeSwapStep` (line 125); outputs differ from the reference on 5143 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -124,3 +124,3 @@
   let usedAmount := if notReached then specifiedAmount else reach
-  let nextSqrtP : U256 := if notReached then 0 else targetSqrtP
+  let nextSqrtP : U256 := if false then 0 else targetSqrtP
   let absDelta : U256 := BitVec.ofNat 256 usedAmount.natAbs
```

First differing case:

```json
{"input": {"F": 300, "L": 529700652, "c": 26908681593376338809905220921561871, "exact_input": true, "op": "step", "spec": 1816821696332, "t": 27180014754403994732126507336932861}, "output": {"deltaL": 8023, "next": 27180014754403994732126507336932861, "returned": -14, "used": 1816821696332}, "reference_output": {"deltaL": 8024, "next": 27180014703364498790021120733517497, "returned": -14, "used": 1816821696332}}
```

### M044: survived, behaviour differs

condition `nextSqrtP = 0` replaced by `false` in `computeSwapStep` (line 127); outputs differ from the reference on 4470 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -126,3 +126,3 @@
   let absDelta : U256 := BitVec.ofNat 256 usedAmount.natAbs
-  if nextSqrtP = 0 then
+  if false then
     let deltaL ← estimateDeltaL absDelta liquidity currentSqrtP feeInFeeUnits isExactInput
```

First differing case:

```json
{"input": {"F": 300, "L": 529700652, "c": 26908681593376338809905220921561871, "exact_input": true, "op": "step", "spec": 1816821696332, "t": 27180014754403994732126507336932861}, "output": {"revert": true}, "reference_output": {"deltaL": 8024, "next": 27180014703364498790021120733517497, "returned": -14, "used": 1816821696332}}
```

### M047: survived, behaviour differs

operands of `-` swapped in `reachAmount` (line 46); outputs differ from the reference on 5934 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -45,3 +45,3 @@
     if currentSqrtP.toNat ≥ targetSqrtP.toNat then currentSqrtP - targetSqrtP
-    else targetSqrtP - currentSqrtP
+    else currentSqrtP - targetSqrtP
   if isExactInput then
```

First differing case:

```json
{"input": {"F": 300, "L": 529700652, "c": 26908681593376338809905220921561871, "exact_input": true, "op": "step", "spec": 1816821696332, "t": 27180014754403994732126507336932861}, "output": {"revert": true}, "reference_output": {"deltaL": 8024, "next": 27180014703364498790021120733517497, "returned": -14, "used": 1816821696332}}
```

### M048: survived, behaviour differs

arguments `(← mul TWO_FEE_UNITS currentSqrtP)` and `(← mul feeInFeeUnits targetSqrtP)` of `sub` swapped in `reachAmount` (line 48); outputs differ from the reference on 5934 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -47,3 +47,3 @@
   if isExactInput then
-    let denominator ← sub (← mul TWO_FEE_UNITS currentSqrtP) (← mul feeInFeeUnits targetSqrtP)
+    let denominator ← sub (← mul feeInFeeUnits targetSqrtP) (← mul TWO_FEE_UNITS currentSqrtP)
     let numerator ← mulDivFloor liquidity (← mul TWO_FEE_UNITS absPriceDiff) denominator
```

First differing case:

```json
{"input": {"F": 300, "L": 529700652, "c": 26908681593376338809905220921561871, "exact_input": true, "op": "step", "spec": 1816821696332, "t": 27180014754403994732126507336932861}, "output": {"revert": true}, "reference_output": {"deltaL": 8024, "next": 27180014703364498790021120733517497, "returned": -14, "used": 1816821696332}}
```

### M049: survived, no observed difference

arguments `TWO_FEE_UNITS` and `currentSqrtP` of `mul` swapped in `reachAmount` (line 48); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -47,3 +47,3 @@
   if isExactInput then
-    let denominator ← sub (← mul TWO_FEE_UNITS currentSqrtP) (← mul feeInFeeUnits targetSqrtP)
+    let denominator ← sub (← mul currentSqrtP TWO_FEE_UNITS) (← mul feeInFeeUnits targetSqrtP)
     let numerator ← mulDivFloor liquidity (← mul TWO_FEE_UNITS absPriceDiff) denominator
```

### M050: survived, no observed difference

arguments `feeInFeeUnits` and `targetSqrtP` of `mul` swapped in `reachAmount` (line 48); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -47,3 +47,3 @@
   if isExactInput then
-    let denominator ← sub (← mul TWO_FEE_UNITS currentSqrtP) (← mul feeInFeeUnits targetSqrtP)
+    let denominator ← sub (← mul TWO_FEE_UNITS currentSqrtP) (← mul targetSqrtP feeInFeeUnits)
     let numerator ← mulDivFloor liquidity (← mul TWO_FEE_UNITS absPriceDiff) denominator
```

### M051: survived, no observed difference

arguments `liquidity` and `(← mul TWO_FEE_UNITS absPriceDiff)` of `mulDivFloor` swapped in `reachAmount` (line 49); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -48,3 +48,3 @@
     let denominator ← sub (← mul TWO_FEE_UNITS currentSqrtP) (← mul feeInFeeUnits targetSqrtP)
-    let numerator ← mulDivFloor liquidity (← mul TWO_FEE_UNITS absPriceDiff) denominator
+    let numerator ← mulDivFloor (← mul TWO_FEE_UNITS absPriceDiff) liquidity denominator
     toInt256 (← mulDivFloor numerator currentSqrtP TWO_POW_96)
```

### M053: survived, no observed difference

arguments `TWO_FEE_UNITS` and `absPriceDiff` of `mul` swapped in `reachAmount` (line 49); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -48,3 +48,3 @@
     let denominator ← sub (← mul TWO_FEE_UNITS currentSqrtP) (← mul feeInFeeUnits targetSqrtP)
-    let numerator ← mulDivFloor liquidity (← mul TWO_FEE_UNITS absPriceDiff) denominator
+    let numerator ← mulDivFloor liquidity (← mul absPriceDiff TWO_FEE_UNITS) denominator
     toInt256 (← mulDivFloor numerator currentSqrtP TWO_POW_96)
```

### M054: survived, no observed difference

arguments `numerator` and `currentSqrtP` of `mulDivFloor` swapped in `reachAmount` (line 50); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -49,3 +49,3 @@
     let numerator ← mulDivFloor liquidity (← mul TWO_FEE_UNITS absPriceDiff) denominator
-    toInt256 (← mulDivFloor numerator currentSqrtP TWO_POW_96)
+    toInt256 (← mulDivFloor currentSqrtP numerator TWO_POW_96)
   else
```

### M056: survived, behaviour differs

arguments `(← mul TWO_FEE_UNITS targetSqrtP)` and `(← mul feeInFeeUnits currentSqrtP)` of `sub` swapped in `reachAmount` (line 52); outputs differ from the reference on 5088 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -51,3 +51,3 @@
   else
-    let denominator ← sub (← mul TWO_FEE_UNITS targetSqrtP) (← mul feeInFeeUnits currentSqrtP)
+    let denominator ← sub (← mul feeInFeeUnits currentSqrtP) (← mul TWO_FEE_UNITS targetSqrtP)
     let numerator ← sub denominator (← mul feeInFeeUnits targetSqrtP)
```

First differing case:

```json
{"input": {"F": 40, "L": 108217392398391914380679, "c": 593096295975945169826734454010, "exact_input": false, "op": "step", "spec": -389171309622958030772848263925050973890866947489, "t": 593036986346347575309751780568}, "output": {"revert": true}, "reference_output": {"deltaL": 2164997347171989, "next": 593036986346347575309751780568, "returned": 1446044789256704914, "used": -80994552088830996549}}
```

### M057: survived, no observed difference

arguments `TWO_FEE_UNITS` and `targetSqrtP` of `mul` swapped in `reachAmount` (line 52); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -51,3 +51,3 @@
   else
-    let denominator ← sub (← mul TWO_FEE_UNITS targetSqrtP) (← mul feeInFeeUnits currentSqrtP)
+    let denominator ← sub (← mul targetSqrtP TWO_FEE_UNITS) (← mul feeInFeeUnits currentSqrtP)
     let numerator ← sub denominator (← mul feeInFeeUnits targetSqrtP)
```

### M058: survived, no observed difference

arguments `feeInFeeUnits` and `currentSqrtP` of `mul` swapped in `reachAmount` (line 52); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -51,3 +51,3 @@
   else
-    let denominator ← sub (← mul TWO_FEE_UNITS targetSqrtP) (← mul feeInFeeUnits currentSqrtP)
+    let denominator ← sub (← mul TWO_FEE_UNITS targetSqrtP) (← mul currentSqrtP feeInFeeUnits)
     let numerator ← sub denominator (← mul feeInFeeUnits targetSqrtP)
```

### M060: survived, no observed difference

arguments `feeInFeeUnits` and `targetSqrtP` of `mul` swapped in `reachAmount` (line 53); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -52,3 +52,3 @@
     let denominator ← sub (← mul TWO_FEE_UNITS targetSqrtP) (← mul feeInFeeUnits currentSqrtP)
-    let numerator ← sub denominator (← mul feeInFeeUnits targetSqrtP)
+    let numerator ← sub denominator (← mul targetSqrtP feeInFeeUnits)
     let numerator ← mulDivFloor liquidity numerator denominator
```

### M061: survived, no observed difference

arguments `liquidity` and `numerator` of `mulDivFloor` swapped in `reachAmount` (line 54); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -53,3 +53,3 @@
     let numerator ← sub denominator (← mul feeInFeeUnits targetSqrtP)
-    let numerator ← mulDivFloor liquidity numerator denominator
+    let numerator ← mulDivFloor numerator liquidity denominator
     revToInt256 (← mulDivFloor numerator absPriceDiff TWO_POW_96)
```

### M063: survived, no observed difference

arguments `numerator` and `absPriceDiff` of `mulDivFloor` swapped in `reachAmount` (line 55); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -54,3 +54,3 @@
     let numerator ← mulDivFloor liquidity numerator denominator
-    revToInt256 (← mulDivFloor numerator absPriceDiff TWO_POW_96)
+    revToInt256 (← mulDivFloor absPriceDiff numerator TWO_POW_96)
 
```

### M065: survived, behaviour differs

arguments `(← mul b b)` and `(← mul a c)` of `sub` swapped in `smallerRoot` (line 60); outputs differ from the reference on 2081 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -59,3 +59,3 @@
 def smallerRoot (a b c : U256) : Option U256 := do
-  let d ← sub (← mul b b) (← mul a c)
+  let d ← sub (← mul a c) (← mul b b)
   let s := sqrtUp d
```

First differing case:

```json
{"input": {"F": 8, "L": 488099447615, "c": 12702106732281905876958584314416, "exact_input": false, "op": "step", "spec": -76421257163, "t": 12689701559484189505314970178876}, "output": {"revert": true}, "reference_output": {"deltaL": 19086, "next": 12689701559509978602990516944905, "returned": 2976330, "used": -76421257163}}
```

### M066: survived, no observed difference

arguments `a` and `c` of `mul` swapped in `smallerRoot` (line 60); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -59,3 +59,3 @@
 def smallerRoot (a b c : U256) : Option U256 := do
-  let d ← sub (← mul b b) (← mul a c)
+  let d ← sub (← mul b b) (← mul c a)
   let s := sqrtUp d
```

### M068: survived, behaviour differs

arguments `b` and `s` of `sub` swapped in `smallerRoot` (line 62); outputs differ from the reference on 1601 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -61,3 +61,3 @@
   let s := sqrtUp d
-  divFloor (← sub b s) a
+  divFloor (← sub s b) a
 
```

First differing case:

```json
{"input": {"F": 8, "L": 488099447615, "c": 12702106732281905876958584314416, "exact_input": false, "op": "step", "spec": -76421257163, "t": 12689701559484189505314970178876}, "output": {"revert": true}, "reference_output": {"deltaL": 19086, "next": 12689701559509978602990516944905, "returned": 2976330, "used": -76421257163}}
```

### M069: survived, no observed difference

arguments `(← mulDivFloor absDelta TWO_POW_96 currentSqrtP)` and `feeInFeeUnits` of `mulDivCeiling` swapped in `estimateDeltaL` (line 84); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -83,3 +83,3 @@
   if isExactInput then
-    mulDivCeiling (← mulDivFloor absDelta TWO_POW_96 currentSqrtP) feeInFeeUnits TWO_FEE_UNITS
+    mulDivCeiling feeInFeeUnits (← mulDivFloor absDelta TWO_POW_96 currentSqrtP) TWO_FEE_UNITS
   else
```

### M070: survived, no observed difference

arguments `absDelta` and `TWO_POW_96` of `mulDivFloor` swapped in `estimateDeltaL` (line 84); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -83,3 +83,3 @@
   if isExactInput then
-    mulDivCeiling (← mulDivFloor absDelta TWO_POW_96 currentSqrtP) feeInFeeUnits TWO_FEE_UNITS
+    mulDivCeiling (← mulDivFloor TWO_POW_96 absDelta currentSqrtP) feeInFeeUnits TWO_FEE_UNITS
   else
```

### M073: survived, no observed difference

arguments `(← sub FEE_UNITS feeInFeeUnits)` and `liquidity` of `mul` swapped in `estimateDeltaL` (line 86); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -85,3 +85,3 @@
   else
-    let b ← mul (← sub FEE_UNITS feeInFeeUnits) liquidity
+    let b ← mul liquidity (← sub FEE_UNITS feeInFeeUnits)
     let c ← mul (← mul feeInFeeUnits liquidity) absDelta
```

### M074: survived, behaviour differs

arguments `FEE_UNITS` and `feeInFeeUnits` of `sub` swapped in `estimateDeltaL` (line 86); outputs differ from the reference on 2081 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -85,3 +85,3 @@
   else
-    let b ← mul (← sub FEE_UNITS feeInFeeUnits) liquidity
+    let b ← mul (← sub feeInFeeUnits FEE_UNITS) liquidity
     let c ← mul (← mul feeInFeeUnits liquidity) absDelta
```

First differing case:

```json
{"input": {"F": 8, "L": 488099447615, "c": 12702106732281905876958584314416, "exact_input": false, "op": "step", "spec": -76421257163, "t": 12689701559484189505314970178876}, "output": {"revert": true}, "reference_output": {"deltaL": 19086, "next": 12689701559509978602990516944905, "returned": 2976330, "used": -76421257163}}
```

### M075: survived, no observed difference

arguments `(← mul feeInFeeUnits liquidity)` and `absDelta` of `mul` swapped in `estimateDeltaL` (line 87); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -86,3 +86,3 @@
     let b ← mul (← sub FEE_UNITS feeInFeeUnits) liquidity
-    let c ← mul (← mul feeInFeeUnits liquidity) absDelta
+    let c ← mul absDelta (← mul feeInFeeUnits liquidity)
     let b ← sub b (← mulDivFloor (← mul FEE_UNITS absDelta) TWO_POW_96 currentSqrtP)
```

### M076: survived, no observed difference

arguments `feeInFeeUnits` and `liquidity` of `mul` swapped in `estimateDeltaL` (line 87); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -86,3 +86,3 @@
     let b ← mul (← sub FEE_UNITS feeInFeeUnits) liquidity
-    let c ← mul (← mul feeInFeeUnits liquidity) absDelta
+    let c ← mul (← mul liquidity feeInFeeUnits) absDelta
     let b ← sub b (← mulDivFloor (← mul FEE_UNITS absDelta) TWO_POW_96 currentSqrtP)
```

### M077: survived, behaviour differs

arguments `b` and `(← mulDivFloor (← mul FEE_UNITS absDelta) TWO_POW_96 curr...` of `sub` swapped in `estimateDeltaL` (line 88); outputs differ from the reference on 2081 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -87,3 +87,3 @@
     let c ← mul (← mul feeInFeeUnits liquidity) absDelta
-    let b ← sub b (← mulDivFloor (← mul FEE_UNITS absDelta) TWO_POW_96 currentSqrtP)
+    let b ← sub (← mulDivFloor (← mul FEE_UNITS absDelta) TWO_POW_96 currentSqrtP) b
     let c ← mulDivFloor c TWO_POW_96 currentSqrtP
```

First differing case:

```json
{"input": {"F": 8, "L": 488099447615, "c": 12702106732281905876958584314416, "exact_input": false, "op": "step", "spec": -76421257163, "t": 12689701559484189505314970178876}, "output": {"revert": true}, "reference_output": {"deltaL": 19086, "next": 12689701559509978602990516944905, "returned": 2976330, "used": -76421257163}}
```

### M078: survived, no observed difference

arguments `(← mul FEE_UNITS absDelta)` and `TWO_POW_96` of `mulDivFloor` swapped in `estimateDeltaL` (line 88); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -87,3 +87,3 @@
     let c ← mul (← mul feeInFeeUnits liquidity) absDelta
-    let b ← sub b (← mulDivFloor (← mul FEE_UNITS absDelta) TWO_POW_96 currentSqrtP)
+    let b ← sub b (← mulDivFloor TWO_POW_96 (← mul FEE_UNITS absDelta) currentSqrtP)
     let c ← mulDivFloor c TWO_POW_96 currentSqrtP
```

### M079: survived, no observed difference

arguments `FEE_UNITS` and `absDelta` of `mul` swapped in `estimateDeltaL` (line 88); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -87,3 +87,3 @@
     let c ← mul (← mul feeInFeeUnits liquidity) absDelta
-    let b ← sub b (← mulDivFloor (← mul FEE_UNITS absDelta) TWO_POW_96 currentSqrtP)
+    let b ← sub b (← mulDivFloor (← mul absDelta FEE_UNITS) TWO_POW_96 currentSqrtP)
     let c ← mulDivFloor c TWO_POW_96 currentSqrtP
```

### M081: survived, no observed difference

arguments `c` and `TWO_POW_96` of `mulDivFloor` swapped in `estimateDeltaL` (line 89); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -88,3 +88,3 @@
     let b ← sub b (← mulDivFloor (← mul FEE_UNITS absDelta) TWO_POW_96 currentSqrtP)
-    let c ← mulDivFloor c TWO_POW_96 currentSqrtP
+    let c ← mulDivFloor TWO_POW_96 c currentSqrtP
     smallerRoot feeInFeeUnits b c
```

### M083: survived, behaviour differs

arguments `feeInFeeUnits` and `b` of `smallerRoot` swapped in `estimateDeltaL` (line 90); outputs differ from the reference on 1978 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -89,3 +89,3 @@
     let c ← mulDivFloor c TWO_POW_96 currentSqrtP
-    smallerRoot feeInFeeUnits b c
+    smallerRoot b feeInFeeUnits c
 
```

First differing case:

```json
{"input": {"F": 8, "L": 488099447615, "c": 12702106732281905876958584314416, "exact_input": false, "op": "step", "spec": -76421257163, "t": 12689701559484189505314970178876}, "output": {"revert": true}, "reference_output": {"deltaL": 19086, "next": 12689701559509978602990516944905, "returned": 2976330, "used": -76421257163}}
```

### M085: survived, no observed difference

arguments `absDelta` and `TWO_POW_96` of `mulDivFloor` swapped in `finalPrice` (line 95); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -94,3 +94,3 @@
 def finalPrice (absDelta liquidity deltaL currentSqrtP : U256) (isExactInput : Bool) : Option U256 := do
-  let tmp ← mulDivFloor absDelta TWO_POW_96 currentSqrtP
+  let tmp ← mulDivFloor TWO_POW_96 absDelta currentSqrtP
   if isExactInput then
```

### M087: survived, no observed difference

arguments `(← add liquidity tmp)` and `currentSqrtP` of `mulDivFloor` swapped in `finalPrice` (line 97); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -96,3 +96,3 @@
   if isExactInput then
-    mulDivFloor (← add liquidity tmp) currentSqrtP (← add liquidity deltaL)
+    mulDivFloor currentSqrtP (← add liquidity tmp) (← add liquidity deltaL)
   else
```

### M088: survived, no observed difference

arguments `liquidity` and `tmp` of `add` swapped in `finalPrice` (line 97); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -96,3 +96,3 @@
   if isExactInput then
-    mulDivFloor (← add liquidity tmp) currentSqrtP (← add liquidity deltaL)
+    mulDivFloor (← add tmp liquidity) currentSqrtP (← add liquidity deltaL)
   else
```

### M090: survived, no observed difference

arguments `liquidity` and `deltaL` of `add` swapped in `finalPrice` (line 97); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -96,3 +96,3 @@
   if isExactInput then
-    mulDivFloor (← add liquidity tmp) currentSqrtP (← add liquidity deltaL)
+    mulDivFloor (← add liquidity tmp) currentSqrtP (← add deltaL liquidity)
   else
```

### M091: survived, no observed difference

arguments `(← sub liquidity tmp)` and `currentSqrtP` of `mulDivCeiling` swapped in `finalPrice` (line 99); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -98,3 +98,3 @@
   else
-    mulDivCeiling (← sub liquidity tmp) currentSqrtP (← add liquidity deltaL)
+    mulDivCeiling currentSqrtP (← sub liquidity tmp) (← add liquidity deltaL)
 
```

### M092: survived, behaviour differs

arguments `liquidity` and `tmp` of `sub` swapped in `finalPrice` (line 99); outputs differ from the reference on 2081 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -98,3 +98,3 @@
   else
-    mulDivCeiling (← sub liquidity tmp) currentSqrtP (← add liquidity deltaL)
+    mulDivCeiling (← sub tmp liquidity) currentSqrtP (← add liquidity deltaL)
 
```

First differing case:

```json
{"input": {"F": 8, "L": 488099447615, "c": 12702106732281905876958584314416, "exact_input": false, "op": "step", "spec": -76421257163, "t": 12689701559484189505314970178876}, "output": {"revert": true}, "reference_output": {"deltaL": 19086, "next": 12689701559509978602990516944905, "returned": 2976330, "used": -76421257163}}
```

### M094: survived, no observed difference

arguments `liquidity` and `deltaL` of `add` swapped in `finalPrice` (line 99); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -98,3 +98,3 @@
   else
-    mulDivCeiling (← sub liquidity tmp) currentSqrtP (← add liquidity deltaL)
+    mulDivCeiling (← sub liquidity tmp) currentSqrtP (← add deltaL liquidity)
 
```

### M095: survived, no observed difference

arguments `liquidity` and `currentSqrtP` of `mulDivFloor` swapped in `incrementalDeltaL` (line 105); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -104,3 +104,3 @@
     Option U256 := do
-  let tmp1 ← mulDivFloor liquidity currentSqrtP TWO_POW_96
+  let tmp1 ← mulDivFloor currentSqrtP liquidity TWO_POW_96
   let tmp2 ← if isExactInput then add tmp1 absDelta else sub tmp1 absDelta
```

### M097: survived, no observed difference

arguments `tmp1` and `absDelta` of `add` swapped in `incrementalDeltaL` (line 106); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -105,3 +105,3 @@
   let tmp1 ← mulDivFloor liquidity currentSqrtP TWO_POW_96
-  let tmp2 ← if isExactInput then add tmp1 absDelta else sub tmp1 absDelta
+  let tmp2 ← if isExactInput then add absDelta tmp1 else sub tmp1 absDelta
   let tmp3 ← mulDivFloor tmp2 TWO_POW_96 nextSqrtP
```

### M098: survived, behaviour differs

arguments `tmp1` and `absDelta` of `sub` swapped in `incrementalDeltaL` (line 106); outputs differ from the reference on 2139 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -105,3 +105,3 @@
   let tmp1 ← mulDivFloor liquidity currentSqrtP TWO_POW_96
-  let tmp2 ← if isExactInput then add tmp1 absDelta else sub tmp1 absDelta
+  let tmp2 ← if isExactInput then add tmp1 absDelta else sub absDelta tmp1
   let tmp3 ← mulDivFloor tmp2 TWO_POW_96 nextSqrtP
```

First differing case:

```json
{"input": {"F": 40, "L": 108217392398391914380679, "c": 593096295975945169826734454010, "exact_input": false, "op": "step", "spec": -389171309622958030772848263925050973890866947489, "t": 593036986346347575309751780568}, "output": {"revert": true}, "reference_output": {"deltaL": 2164997347171989, "next": 593036986346347575309751780568, "returned": 1446044789256704914, "used": -80994552088830996549}}
```

### M099: survived, no observed difference

arguments `tmp2` and `TWO_POW_96` of `mulDivFloor` swapped in `incrementalDeltaL` (line 107); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -106,3 +106,3 @@
   let tmp2 ← if isExactInput then add tmp1 absDelta else sub tmp1 absDelta
-  let tmp3 ← mulDivFloor tmp2 TWO_POW_96 nextSqrtP
+  let tmp3 ← mulDivFloor TWO_POW_96 tmp2 nextSqrtP
   pure (if tmp3.toNat > liquidity.toNat then tmp3 - liquidity else 0)
```

### M101: survived, behaviour differs

operands of `>` swapped in `incrementalDeltaL` (line 108); outputs differ from the reference on 6188 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -107,3 +107,3 @@
   let tmp3 ← mulDivFloor tmp2 TWO_POW_96 nextSqrtP
-  pure (if tmp3.toNat > liquidity.toNat then tmp3 - liquidity else 0)
+  pure (if liquidity.toNat > tmp3.toNat then tmp3 - liquidity else 0)
 
```

First differing case:

```json
{"input": {"F": 40, "L": 108217392398391914380679, "c": 593096295975945169826734454010, "exact_input": false, "op": "step", "spec": -389171309622958030772848263925050973890866947489, "t": 593036986346347575309751780568}, "output": {"deltaL": 0, "next": 593036986346347575309751780568, "returned": 1445755551375065409, "used": -80994552088830996549}, "reference_output": {"deltaL": 2164997347171989, "next": 593036986346347575309751780568, "returned": 1446044789256704914, "used": -80994552088830996549}}
```

### M102: survived, behaviour differs

operands of `-` swapped in `incrementalDeltaL` (line 108); outputs differ from the reference on 2181 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -107,3 +107,3 @@
   let tmp3 ← mulDivFloor tmp2 TWO_POW_96 nextSqrtP
-  pure (if tmp3.toNat > liquidity.toNat then tmp3 - liquidity else 0)
+  pure (if tmp3.toNat > liquidity.toNat then liquidity - tmp3 else 0)
 
```

First differing case:

```json
{"input": {"F": 40, "L": 108217392398391914380679, "c": 593096295975945169826734454010, "exact_input": false, "op": "step", "spec": -389171309622958030772848263925050973890866947489, "t": 593036986346347575309751780568}, "output": {"revert": true}, "reference_output": {"deltaL": 2164997347171989, "next": 593036986346347575309751780568, "returned": 1446044789256704914, "used": -80994552088830996549}}
```

### M103: survived, no observed difference

arguments `(← add liquidity deltaL)` and `TWO_POW_96` of `mulDivCeiling` swapped in `returnedAmount` (line 113); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -112,3 +112,3 @@
 def returnedAmount (liquidity currentSqrtP nextSqrtP deltaL : U256) (isExactInput : Bool) : Option Int := do
-  let x ← toInt256 (← mulDivCeiling (← add liquidity deltaL) TWO_POW_96 nextSqrtP)
+  let x ← toInt256 (← mulDivCeiling TWO_POW_96 (← add liquidity deltaL) nextSqrtP)
   let y ← revToInt256 (← mulDivFloor liquidity TWO_POW_96 currentSqrtP)
```

### M104: survived, no observed difference

arguments `liquidity` and `deltaL` of `add` swapped in `returnedAmount` (line 113); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -112,3 +112,3 @@
 def returnedAmount (liquidity currentSqrtP nextSqrtP deltaL : U256) (isExactInput : Bool) : Option Int := do
-  let x ← toInt256 (← mulDivCeiling (← add liquidity deltaL) TWO_POW_96 nextSqrtP)
+  let x ← toInt256 (← mulDivCeiling (← add deltaL liquidity) TWO_POW_96 nextSqrtP)
   let y ← revToInt256 (← mulDivFloor liquidity TWO_POW_96 currentSqrtP)
```

### M106: survived, no observed difference

arguments `liquidity` and `TWO_POW_96` of `mulDivFloor` swapped in `returnedAmount` (line 114); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -113,3 +113,3 @@
   let x ← toInt256 (← mulDivCeiling (← add liquidity deltaL) TWO_POW_96 nextSqrtP)
-  let y ← revToInt256 (← mulDivFloor liquidity TWO_POW_96 currentSqrtP)
+  let y ← revToInt256 (← mulDivFloor TWO_POW_96 liquidity currentSqrtP)
   pure (if isExactInput && x + y == 1 then 0 else x + y)
```

### M140: survived, behaviour differs

constant `1` replaced by `2` in `returnedAmount` (line 115); outputs differ from the reference on 1838 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -114,3 +114,3 @@
   let y ← revToInt256 (← mulDivFloor liquidity TWO_POW_96 currentSqrtP)
-  pure (if isExactInput && x + y == 1 then 0 else x + y)
+  pure (if isExactInput && x + y == 2 then 0 else x + y)
 
```

First differing case:

```json
{"input": {"F": 70816, "L": 100, "c": 258160166490085118035590902532276590381579843345, "exact_input": true, "op": "step", "spec": 8208598693430159375, "t": 264456692950778294064478964645038816420986575728}, "output": {"deltaL": 1, "next": 260716207742462198412180911468239724939813307140, "returned": 1, "used": 8208598693430159375}, "reference_output": {"deltaL": 1, "next": 260716207742462198412180911468239724939813307140, "returned": 0, "used": 8208598693430159375}}
```

### M141: survived, behaviour differs

constant `1` replaced by `0` in `returnedAmount` (line 115); outputs differ from the reference on 1815 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -114,3 +114,3 @@
   let y ← revToInt256 (← mulDivFloor liquidity TWO_POW_96 currentSqrtP)
-  pure (if isExactInput && x + y == 1 then 0 else x + y)
+  pure (if isExactInput && x + y == 0 then 0 else x + y)
 
```

First differing case:

```json
{"input": {"F": 70816, "L": 100, "c": 258160166490085118035590902532276590381579843345, "exact_input": true, "op": "step", "spec": 8208598693430159375, "t": 264456692950778294064478964645038816420986575728}, "output": {"deltaL": 1, "next": 260716207742462198412180911468239724939813307140, "returned": 1, "used": 8208598693430159375}, "reference_output": {"deltaL": 1, "next": 260716207742462198412180911468239724939813307140, "returned": 0, "used": 8208598693430159375}}
```

### M142: survived, behaviour differs

constant `0` replaced by `1` in `returnedAmount` (line 115); outputs differ from the reference on 1815 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -114,3 +114,3 @@
   let y ← revToInt256 (← mulDivFloor liquidity TWO_POW_96 currentSqrtP)
-  pure (if isExactInput && x + y == 1 then 0 else x + y)
+  pure (if isExactInput && x + y == 1 then 1 else x + y)
 
```

First differing case:

```json
{"input": {"F": 70816, "L": 100, "c": 258160166490085118035590902532276590381579843345, "exact_input": true, "op": "step", "spec": 8208598693430159375, "t": 264456692950778294064478964645038816420986575728}, "output": {"deltaL": 1, "next": 260716207742462198412180911468239724939813307140, "returned": 1, "used": 8208598693430159375}, "reference_output": {"deltaL": 1, "next": 260716207742462198412180911468239724939813307140, "returned": 0, "used": 8208598693430159375}}
```

### M143: survived, no observed difference

constant `0` replaced by `1` in `computeSwapStep` (line 120); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -119,3 +119,3 @@
 def computeSwapStep : StepFn := fun liquidity currentSqrtP targetSqrtP feeInFeeUnits specifiedAmount isExactInput => do
-  if currentSqrtP = targetSqrtP then return ⟨0, 0, 0, currentSqrtP⟩
+  if currentSqrtP = targetSqrtP then return ⟨1, 0, 0, currentSqrtP⟩
   let reach ← reachAmount liquidity currentSqrtP targetSqrtP feeInFeeUnits isExactInput
```

### M144: survived, no observed difference

constant `0` replaced by `1` in `computeSwapStep` (line 120); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -119,3 +119,3 @@
 def computeSwapStep : StepFn := fun liquidity currentSqrtP targetSqrtP feeInFeeUnits specifiedAmount isExactInput => do
-  if currentSqrtP = targetSqrtP then return ⟨0, 0, 0, currentSqrtP⟩
+  if currentSqrtP = targetSqrtP then return ⟨0, 1, 0, currentSqrtP⟩
   let reach ← reachAmount liquidity currentSqrtP targetSqrtP feeInFeeUnits isExactInput
```

### M145: survived, no observed difference

constant `0` replaced by `1` in `computeSwapStep` (line 120); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -119,3 +119,3 @@
 def computeSwapStep : StepFn := fun liquidity currentSqrtP targetSqrtP feeInFeeUnits specifiedAmount isExactInput => do
-  if currentSqrtP = targetSqrtP then return ⟨0, 0, 0, currentSqrtP⟩
+  if currentSqrtP = targetSqrtP then return ⟨0, 0, 1, currentSqrtP⟩
   let reach ← reachAmount liquidity currentSqrtP targetSqrtP feeInFeeUnits isExactInput
```

### M151: survived, behaviour differs

constant `0` replaced by `1` in `computeSwapStep` (line 127); outputs differ from the reference on 4470 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -126,3 +126,3 @@
   let absDelta : U256 := BitVec.ofNat 256 usedAmount.natAbs
-  if nextSqrtP = 0 then
+  if nextSqrtP = 1 then
     let deltaL ← estimateDeltaL absDelta liquidity currentSqrtP feeInFeeUnits isExactInput
```

First differing case:

```json
{"input": {"F": 300, "L": 529700652, "c": 26908681593376338809905220921561871, "exact_input": true, "op": "step", "spec": 1816821696332, "t": 27180014754403994732126507336932861}, "output": {"revert": true}, "reference_output": {"deltaL": 8024, "next": 27180014703364498790021120733517497, "returned": -14, "used": 1816821696332}}
```

