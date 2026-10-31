# Specification strength: rw-balancer-upscale

Reference `realworld/tasks/rw-balancer-upscale/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `57787df38ed76a28`; report `61efe5a5cb1cdd3e`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 134 | 134 | 119 | 0 | 104 | 0 | 0 | 103 | 5 | 10 | 104 of 119 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-GIVEN-IN-SUCCEEDS | 20 | 17 | kernel-checked |
| REQ-GIVEN-OUT-SUCCEEDS | 23 | 18 | kernel-checked |
| REQ-GIVEN-IN-PAYS-AT-MOST | 27 | 15 | kernel-checked |
| REQ-GIVEN-IN-PAYS-AT-LEAST | 25 | 14 | kernel-checked |
| REQ-GIVEN-OUT-CHARGES-AT-LEAST | 43 | 29 | kernel-checked |
| REQ-GIVEN-OUT-CHARGES-AT-MOST | 31 | 6 | kernel-checked |
| REQ-SWAP-KEEPS-VALUE | 64 | 3 | kernel-checked |
| REQ-BATCH-KEEPS-VALUE | 59 | 1 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | rounding | `mulDown` | floor division `/` replaced by ceiling division | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M002 | rounding | `mulUp` | ceiling division idiom `(a - 1) / b + 1` replaced by floor division | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M003 | rounding | `mulUp` | floor division `/` replaced by ceiling division | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST, REQ-GIVEN-IN-SUCCEEDS, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-GIVEN-OUT-SUCCEEDS | REQ-GIVEN-IN-SUCCEEDS |
| M004 | rounding | `divDown` | floor division `/` replaced by ceiling division | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-SWAP-KEEPS-VALUE |
| M005 | rounding | `divUp` | ceiling division idiom `(a - 1) / b + 1` replaced by floor division | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-BATCH-KEEPS-VALUE |
| M006 | rounding | `divUp` | floor division `/` replaced by ceiling division | killed by property tests | REQ-GIVEN-OUT-CHARGES-AT-MOST | REQ-GIVEN-OUT-CHARGES-AT-MOST |
| M007 | rounding | `upscale` | `mulDown` replaced by `mulUp` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M008 | rounding | `upscaleUp` | `mulUp` replaced by `mulDown` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M009 | rounding | `downscaleDown` | `divDown` replaced by `divUp` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M010 | rounding | `downscaleUp` | `divUp` replaced by `divDown` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M011 | rounding | `subtractSwapFeeAmount` | `mulUp` replaced by `mulDown` | survived, behaviour differs |  |  |
| M012 | rounding | `subtractSwapFeeAmount` | `mulUp` replaced by `mulDown` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-MOST | REQ-GIVEN-IN-PAYS-AT-MOST |
| M013 | rounding | `addSwapFeeAmount` | `divUp` replaced by `divDown` | killed by property tests | REQ-GIVEN-OUT-CHARGES-AT-LEAST | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M014 | rounding | `swapGivenIn` | `downscaleDown` replaced by `downscaleUp` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M015 | rounding | `swapGivenOut` | `downscaleUp` replaced by `downscaleDown` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M016 | boundary | `complement` | `<` replaced by `≤` | survived, no observed difference |  |  |
| M017 | boundary | `subtractSwapFeeAmount` | `≤` replaced by `<` | killed by property tests | REQ-GIVEN-IN-SUCCEEDS | REQ-GIVEN-IN-SUCCEEDS |
| M018 | boundary | `swapGivenOut` | `≤` replaced by `<` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-SWAP-KEEPS-VALUE | REQ-SWAP-KEEPS-VALUE |
| M019 | equality | `mulUp` | `=` replaced by `≠` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-IN-SUCCEEDS, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-GIVEN-OUT-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-SUCCEEDS |
| M020 | equality | `divDown` | `=` replaced by `≠` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST, REQ-GIVEN-IN-SUCCEEDS | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M021 | equality | `divDown` | `=` replaced by `≠` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M022 | equality | `divUp` | `=` replaced by `≠` | killed by property tests | REQ-GIVEN-OUT-SUCCEEDS | REQ-GIVEN-OUT-SUCCEEDS |
| M023 | equality | `divUp` | `=` replaced by `≠` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M024 | arith | `mulDown` | `*` replaced by `/` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M025 | arith | `mulUp` | `*` replaced by `/` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M026 | arith | `mulUp` | `*` replaced by `/` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M027 | arith | `mulUp` | `-` replaced by `+` | killed by property tests | REQ-GIVEN-OUT-CHARGES-AT-MOST | REQ-GIVEN-OUT-CHARGES-AT-MOST |
| M028 | arith | `mulUp` | `+` replaced by `-` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M029 | arith | `divDown` | `*` replaced by `/` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M030 | arith | `divUp` | `*` replaced by `/` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M031 | arith | `divUp` | `-` replaced by `+` | killed by property tests | REQ-GIVEN-OUT-CHARGES-AT-MOST | REQ-GIVEN-OUT-CHARGES-AT-MOST |
| M032 | arith | `divUp` | `+` replaced by `-` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M033 | arith | `complement` | `-` replaced by `+` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M034 | arith | `subtractSwapFeeAmount` | `-` replaced by `+` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M035 | guard | `mulUp` | condition `a * b = 0` replaced by `true` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M036 | guard | `mulUp` | condition `a * b = 0` replaced by `false` | killed by property tests | REQ-GIVEN-IN-SUCCEEDS, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-GIVEN-OUT-SUCCEEDS | REQ-GIVEN-IN-SUCCEEDS |
| M037 | guard | `divDown` | condition `b = 0` replaced by `true` | killed by property tests | REQ-GIVEN-IN-SUCCEEDS |  |
| M038 | guard | `divDown` | condition `b = 0` replaced by `false` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M039 | guard | `divDown` | condition `a = 0` replaced by `false` | survived, no observed difference |  |  |
| M040 | guard | `divDown` | condition `a = 0` replaced by `true` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M041 | guard | `divUp` | condition `b = 0` replaced by `true` | killed by property tests | REQ-GIVEN-OUT-SUCCEEDS | REQ-GIVEN-OUT-SUCCEEDS |
| M042 | guard | `divUp` | condition `b = 0` replaced by `false` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M043 | guard | `divUp` | condition `a = 0` replaced by `true` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M044 | guard | `divUp` | condition `a = 0` replaced by `false` | survived, behaviour differs |  |  |
| M045 | guard | `complement` | condition `x < ONE` replaced by `false` | killed by property tests | REQ-GIVEN-OUT-SUCCEEDS | REQ-GIVEN-OUT-SUCCEEDS |
| M046 | guard | `complement` | condition `x < ONE` replaced by `true` | survived, no observed difference |  |  |
| M047 | guard | `subtractSwapFeeAmount` | condition `mulUp amount fee ≤ amount` replaced by `false` | killed by property tests | REQ-GIVEN-IN-SUCCEEDS | REQ-GIVEN-IN-SUCCEEDS |
| M048 | guard | `subtractSwapFeeAmount` | condition `mulUp amount fee ≤ amount` replaced by `true` | survived, behaviour differs |  |  |
| M049 | guard | `swapGivenOut` | condition `scaledBalances p s.tokenOut ≤ upscaleUp s.amount (p.rate ...` replaced by `true` | killed by property tests | REQ-GIVEN-OUT-SUCCEEDS | REQ-GIVEN-OUT-SUCCEEDS |
| M050 | guard | `swapGivenOut` | condition `scaledBalances p s.tokenOut ≤ upscaleUp s.amount (p.rate ...` replaced by `false` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-SWAP-KEEPS-VALUE | REQ-SWAP-KEEPS-VALUE |
| M051 | field | `swapGivenIn` | field read `s.amount` replaced by `s.tokenOut` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M052 | field | `swapGivenIn` | field read `s.amount` replaced by `s.tokenIn` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M053 | field | `swapGivenIn` | field read `p.fee` replaced by `p.rate` | does not compile |  |  |
| M054 | field | `swapGivenIn` | field read `s.tokenIn` replaced by `s.tokenOut` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-LEAST, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M055 | field | `swapGivenIn` | field read `s.tokenIn` replaced by `s.amount` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M056 | field | `swapGivenIn` | field read `s.tokenOut` replaced by `s.amount` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M057 | field | `swapGivenIn` | field read `s.tokenOut` replaced by `s.tokenIn` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-LEAST, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-IN-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-SUCCEEDS |
| M058 | field | `swapGivenIn` | field read `p.rate` replaced by `p.fee` | does not compile |  |  |
| M059 | field | `swapGivenIn` | field read `s.tokenIn` replaced by `s.amount` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M060 | field | `swapGivenIn` | field read `s.tokenIn` replaced by `s.tokenOut` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-LEAST, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M061 | field | `swapGivenIn` | field read `p.rate` replaced by `p.fee` | does not compile |  |  |
| M062 | field | `swapGivenIn` | field read `s.tokenOut` replaced by `s.tokenIn` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-LEAST, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-IN-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-SUCCEEDS |
| M063 | field | `swapGivenIn` | field read `s.tokenOut` replaced by `s.amount` | killed by property tests | REQ-GIVEN-IN-SUCCEEDS | REQ-GIVEN-IN-SUCCEEDS |
| M064 | field | `swapGivenOut` | field read `s.tokenOut` replaced by `s.tokenIn` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-SUCCEEDS |
| M065 | field | `swapGivenOut` | field read `s.tokenOut` replaced by `s.amount` | killed by property tests | REQ-GIVEN-OUT-SUCCEEDS | REQ-GIVEN-OUT-SUCCEEDS |
| M066 | field | `swapGivenOut` | field read `s.amount` replaced by `s.tokenIn` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-SUCCEEDS |
| M067 | field | `swapGivenOut` | field read `s.amount` replaced by `s.tokenOut` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-SUCCEEDS |
| M068 | field | `swapGivenOut` | field read `p.rate` replaced by `p.fee` | does not compile |  |  |
| M069 | field | `swapGivenOut` | field read `s.tokenOut` replaced by `s.amount` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-SUCCEEDS |
| M070 | field | `swapGivenOut` | field read `s.tokenOut` replaced by `s.tokenIn` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-SUCCEEDS |
| M071 | field | `swapGivenOut` | field read `s.tokenIn` replaced by `s.tokenOut` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M072 | field | `swapGivenOut` | field read `s.tokenIn` replaced by `s.amount` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M073 | field | `swapGivenOut` | field read `s.tokenOut` replaced by `s.amount` | killed by property tests | REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M074 | field | `swapGivenOut` | field read `s.tokenOut` replaced by `s.tokenIn` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M075 | field | `swapGivenOut` | field read `s.amount` replaced by `s.tokenIn` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M076 | field | `swapGivenOut` | field read `s.amount` replaced by `s.tokenOut` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M077 | field | `swapGivenOut` | field read `p.rate` replaced by `p.fee` | does not compile |  |  |
| M078 | field | `swapGivenOut` | field read `s.tokenOut` replaced by `s.amount` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M079 | field | `swapGivenOut` | field read `s.tokenOut` replaced by `s.tokenIn` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M080 | field | `swapGivenOut` | field read `p.rate` replaced by `p.fee` | does not compile |  |  |
| M081 | field | `swapGivenOut` | field read `s.tokenIn` replaced by `s.tokenOut` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M082 | field | `swapGivenOut` | field read `s.tokenIn` replaced by `s.amount` | killed by property tests | REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-GIVEN-OUT-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-SUCCEEDS |
| M083 | field | `swapGivenOut` | field read `p.fee` replaced by `p.rate` | does not compile |  |  |
| M084 | swap | `mulDown` | operands of `/` swapped | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M085 | swap | `mulUp` | operands of `/` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-LEAST, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-IN-SUCCEEDS, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-SUCCEEDS |
| M086 | swap | `mulUp` | operands of `-` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M087 | swap | `divDown` | operands of `/` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-IN-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-SUCCEEDS |
| M088 | swap | `divUp` | operands of `/` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M089 | swap | `divUp` | operands of `-` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M090 | swap | `complement` | operands of `<` swapped | killed by property tests | REQ-GIVEN-OUT-SUCCEEDS | REQ-GIVEN-OUT-SUCCEEDS |
| M091 | swap | `complement` | operands of `-` swapped | killed by property tests | REQ-GIVEN-OUT-SUCCEEDS | REQ-GIVEN-OUT-SUCCEEDS |
| M092 | swap | `upscale` | arguments `amount` and `scalingFactor` of `mulDown` swapped | survived, no observed difference |  |  |
| M093 | swap | `upscaleUp` | arguments `amount` and `scalingFactor` of `mulUp` swapped | survived, no observed difference |  |  |
| M094 | swap | `downscaleDown` | arguments `amount` and `scalingFactor` of `divDown` swapped | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-IN-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-SUCCEEDS |
| M095 | swap | `downscaleUp` | arguments `amount` and `scalingFactor` of `divUp` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-GIVEN-OUT-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-SUCCEEDS |
| M096 | swap | `subtractSwapFeeAmount` | arguments `amount` and `fee` of `mulUp` swapped | survived, no observed difference |  |  |
| M097 | swap | `subtractSwapFeeAmount` | arguments `amount` and `fee` of `mulUp` swapped | survived, no observed difference |  |  |
| M098 | swap | `addSwapFeeAmount` | arguments `amount` and `(complement fee)` of `divUp` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-GIVEN-OUT-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-SUCCEEDS |
| M099 | swap | `swapGivenIn` | arguments `s.amount` and `p.fee` of `subtractSwapFeeAmount` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-LEAST, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-IN-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-SUCCEEDS |
| M100 | swap | `swapGivenIn` | arguments `(m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (up...` and `(p.rate s.tokenOut)` of `downscaleDown` swapped | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-IN-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-SUCCEEDS |
| M101 | swap | `swapGivenIn` | arguments `(scaledBalances p)` and `s.tokenIn` of `m.outGivenIn` swapped | does not compile |  |  |
| M102 | swap | `swapGivenIn` | arguments `s.tokenIn` and `s.tokenOut` of `m.outGivenIn` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-LEAST, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-IN-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-SUCCEEDS |
| M103 | swap | `swapGivenIn` | arguments `s.tokenOut` and `(upscale a (p.rate s.tokenIn))` of `m.outGivenIn` swapped | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M104 | swap | `swapGivenIn` | arguments `a` and `(p.rate s.tokenIn)` of `upscale` swapped | survived, no observed difference |  |  |
| M105 | swap | `swapGivenOut` | arguments `p` and `s.tokenOut` of `scaledBalances` swapped | does not compile |  |  |
| M106 | swap | `swapGivenOut` | arguments `s.amount` and `(p.rate s.tokenOut)` of `upscaleUp` swapped | survived, no observed difference |  |  |
| M107 | swap | `swapGivenOut` | arguments `(m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (up...` and `(p.rate s.tokenIn)` of `downscaleUp` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-GIVEN-OUT-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-SUCCEEDS |
| M108 | swap | `swapGivenOut` | arguments `(scaledBalances p)` and `s.tokenIn` of `m.inGivenOut` swapped | does not compile |  |  |
| M109 | swap | `swapGivenOut` | arguments `s.tokenIn` and `s.tokenOut` of `m.inGivenOut` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M110 | swap | `swapGivenOut` | arguments `s.tokenOut` and `(upscaleUp s.amount (p.rate s.tokenOut))` of `m.inGivenOut` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M111 | swap | `swapGivenOut` | arguments `s.amount` and `(p.rate s.tokenOut)` of `upscaleUp` swapped | survived, no observed difference |  |  |
| M112 | swap | `swapGivenOut` | arguments `a` and `p.fee` of `addSwapFeeAmount` swapped | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-GIVEN-OUT-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-SUCCEEDS |
| M113 | swap | `onSwap` | arguments `p` and `s` of `m` swapped | does not compile |  |  |
| M114 | swap | `onSwap` | arguments `m` and `p` of `swapGivenIn` swapped | does not compile |  |  |
| M115 | swap | `onSwap` | arguments `p` and `s` of `swapGivenIn` swapped | does not compile |  |  |
| M116 | swap | `onSwap` | arguments `m` and `p` of `swapGivenOut` swapped | does not compile |  |  |
| M117 | swap | `onSwap` | arguments `p` and `s` of `swapGivenOut` swapped | does not compile |  |  |
| M118 | constant | `mulUp` | constant `0` replaced by `1` | killed by property tests | REQ-GIVEN-IN-SUCCEEDS, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-GIVEN-OUT-SUCCEEDS | REQ-GIVEN-IN-SUCCEEDS |
| M119 | constant | `mulUp` | constant `0` replaced by `1` | killed by property tests | REQ-GIVEN-IN-SUCCEEDS, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-GIVEN-OUT-SUCCEEDS | REQ-GIVEN-IN-SUCCEEDS |
| M120 | constant | `mulUp` | constant `1` replaced by `0` | killed by property tests | REQ-GIVEN-OUT-CHARGES-AT-MOST | REQ-GIVEN-OUT-CHARGES-AT-MOST |
| M121 | constant | `mulUp` | constant `1` replaced by `2` | killed by property tests | REQ-GIVEN-OUT-CHARGES-AT-LEAST | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M122 | constant | `mulUp` | constant `1` replaced by `2` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST, REQ-GIVEN-IN-SUCCEEDS, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-GIVEN-OUT-SUCCEEDS | REQ-GIVEN-IN-SUCCEEDS |
| M123 | constant | `mulUp` | constant `1` replaced by `0` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-PAYS-AT-MOST |
| M124 | constant | `divDown` | constant `0` replaced by `1` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M125 | constant | `divDown` | constant `0` replaced by `1` | killed by property tests | REQ-GIVEN-IN-PAYS-AT-LEAST | REQ-GIVEN-IN-PAYS-AT-LEAST |
| M126 | constant | `divDown` | constant `0` replaced by `1` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-IN-SUCCEEDS, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-IN-SUCCEEDS |
| M127 | constant | `divUp` | constant `0` replaced by `1` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-GIVEN-OUT-CHARGES-AT-MOST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M128 | constant | `divUp` | constant `0` replaced by `1` | killed by property tests | REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M129 | constant | `divUp` | constant `0` replaced by `1` | survived, behaviour differs |  |  |
| M130 | constant | `divUp` | constant `1` replaced by `2` | survived, behaviour differs |  |  |
| M131 | constant | `divUp` | constant `1` replaced by `0` | killed by property tests | REQ-GIVEN-OUT-CHARGES-AT-MOST | REQ-GIVEN-OUT-CHARGES-AT-MOST |
| M132 | constant | `divUp` | constant `1` replaced by `0` | killed by property tests | REQ-BATCH-KEEPS-VALUE, REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE | REQ-GIVEN-OUT-CHARGES-AT-LEAST |
| M133 | constant | `divUp` | constant `1` replaced by `2` | killed by property tests | REQ-GIVEN-OUT-CHARGES-AT-MOST | REQ-GIVEN-OUT-CHARGES-AT-MOST |
| M134 | constant | `complement` | constant `0` replaced by `1` | killed by property tests | REQ-GIVEN-OUT-CHARGES-AT-LEAST | REQ-GIVEN-OUT-CHARGES-AT-LEAST |

## Survivors

### M011: survived, behaviour differs

`mulUp` replaced by `mulDown` in `subtractSwapFeeAmount` (line 39); outputs differ from the reference on 64 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -38,3 +38,3 @@
 def subtractSwapFeeAmount (amount fee : Nat) : Option Nat :=
-  if mulUp amount fee ≤ amount then some (amount - mulUp amount fee) else none
+  if mulDown amount fee ≤ amount then some (amount - mulUp amount fee) else none
 
```

First differing case:

```json
{"input": {"math": "product", "pool": {"balances": [434312381500305329691818, 1], "fee": 1000000000000000001, "rates": [1776791408642453381, 1100000000000000000]}, "swaps": [{"amount": 1, "in": 0, "kind": "in", "out": 1}, {"amount": 13, "in": 1, "kind": "out", "out": 0}, {"amount": 35, "in": 1, "kind": "out", "out": 0}, {"amount": 37, "in": 1, "kind": "in", "out": 0}, {"amount": 5962408591845732681178, "in": 1, "kind": "in", "out": 0}]}, "output": {"balances_after": [434312381500305329691818, 1], "ok": false, "steps": [{"balances": [434312381500305329691819, 1], "ok": true, "quote": 0, "value": 771682508116786117078064}, {"balances": [434312381500305329691819, 1], "ok": false, "quote": null, "value": 771682508116786117078064}], "value_after": 771682508116786117078062, "value_before": 771682508116786117078062}, "reference_output": {"balances_after": [434312381500305329691818, 1], "ok": false, "steps": [{"balances": [434312381500305329691818, 1], "ok": false, "quote": null, "value": 771682508116786117078062}], "value_after": 771682508116786117078062, "value_before": 771682508116786117078062}}
```

### M016: survived, no observed difference

`<` replaced by `≤` in `complement` (line 22); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -21,3 +21,3 @@
 
-def complement (x : Nat) : Nat := if x < ONE then ONE - x else 0
+def complement (x : Nat) : Nat := if x ≤ ONE then ONE - x else 0
 
```

### M039: survived, no observed difference

condition `a = 0` replaced by `false` in `divDown` (line 17); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -16,3 +16,3 @@
 def divDown (a b : Nat) : Option Nat :=
-  if b = 0 then none else if a = 0 then some 0 else some (a * ONE / b)
+  if b = 0 then none else if false then some 0 else some (a * ONE / b)
 
```

### M044: survived, behaviour differs

condition `a = 0` replaced by `false` in `divUp` (line 20); outputs differ from the reference on 126 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -19,3 +19,3 @@
 def divUp (a b : Nat) : Option Nat :=
-  if b = 0 then none else if a = 0 then some 0 else some ((a * ONE - 1) / b + 1)
+  if b = 0 then none else if false then some 0 else some ((a * ONE - 1) / b + 1)
 
```

First differing case:

```json
{"input": {"math": "product", "pool": {"balances": [27419, 87191], "fee": 50000000000000000, "rates": [1000000000000000000, 1058132408689971699]}, "swaps": [{"amount": 0, "in": 1, "kind": "out", "out": 0}, {"amount": 2, "in": 1, "kind": "out", "out": 0}, {"amount": 24, "in": 0, "kind": "in", "out": 1}, {"amount": 1, "in": 1, "kind": "in", "out": 0}, {"amount": 16, "in": 0, "kind": "in", "out": 1}, {"amount": 1144028517434505608816, "in": 0, "kind": "in", "out": 1}]}, "output": {"balances_after": [1144028517434505636273, 2], "ok": true, "steps": [{"balances": [27419, 87193], "ok": true, "quote": 2, "value": 2529704359}, {"balances": [27417, 87201], "ok": true, "quote": 8, "value": 2529766590}, {"balances": [27441, 87133], "ok": true, "quote": 68, "value": 2530005318}, {"balances": [27441, 87134], "ok": true, "quote": 0, "value": 2530032759}, {"balances": [27457, 87087], "ok": true, "quote": 47, "value": 2530135093}, {"balances": [1144028517434505636273, 2], "ok": true, "quote": 87085, "value": 2288057034869011272546}], "value_after": 2288057034869011272546, "value_before": 2529649521}, "reference_output": {"balances_after": [1144028517434505636273, 2], "ok": true, "steps": [{"balances": [27419, 87191], "ok": true, "quote": 0, "value": 2529649521}, {"balances": [27417, 87199], "ok": true, "quote": 8, "value": 2529711756}, {"balances": [27441, 87131], "ok": true, "quote": 68, "value": 2529950436}, {"balances": [27441, 87132], "ok": true, "quote": 0, "value": 2529977877}, {"balances": [27457, 87085], "ok": true, "quote": 47, "value": 2530080179}, {"balances": [1144028517434505636273, 2], "ok": true, "quote": 87083, "value": 2288057034869011272546}], "value_after": 2288057034869011272546, "value_before": 2529649521}}
```

### M046: survived, no observed difference

condition `x < ONE` replaced by `true` in `complement` (line 22); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -21,3 +21,3 @@
 
-def complement (x : Nat) : Nat := if x < ONE then ONE - x else 0
+def complement (x : Nat) : Nat := if true then ONE - x else 0
 
```

### M048: survived, behaviour differs

condition `mulUp amount fee ≤ amount` replaced by `true` in `subtractSwapFeeAmount` (line 39); outputs differ from the reference on 92 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -38,3 +38,3 @@
 def subtractSwapFeeAmount (amount fee : Nat) : Option Nat :=
-  if mulUp amount fee ≤ amount then some (amount - mulUp amount fee) else none
+  if true then some (amount - mulUp amount fee) else none
 
```

First differing case:

```json
{"input": {"math": "product", "pool": {"balances": [434312381500305329691818, 1], "fee": 1000000000000000001, "rates": [1776791408642453381, 1100000000000000000]}, "swaps": [{"amount": 1, "in": 0, "kind": "in", "out": 1}, {"amount": 13, "in": 1, "kind": "out", "out": 0}, {"amount": 35, "in": 1, "kind": "out", "out": 0}, {"amount": 37, "in": 1, "kind": "in", "out": 0}, {"amount": 5962408591845732681178, "in": 1, "kind": "in", "out": 0}]}, "output": {"balances_after": [434312381500305329691818, 1], "ok": false, "steps": [{"balances": [434312381500305329691819, 1], "ok": true, "quote": 0, "value": 771682508116786117078064}, {"balances": [434312381500305329691819, 1], "ok": false, "quote": null, "value": 771682508116786117078064}], "value_after": 771682508116786117078062, "value_before": 771682508116786117078062}, "reference_output": {"balances_after": [434312381500305329691818, 1], "ok": false, "steps": [{"balances": [434312381500305329691818, 1], "ok": false, "quote": null, "value": 771682508116786117078062}], "value_after": 771682508116786117078062, "value_before": 771682508116786117078062}}
```

### M092: survived, no observed difference

arguments `amount` and `scalingFactor` of `mulDown` swapped in `upscale` (line 27); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -26,3 +26,3 @@
 /-- `_upscale`, used for the given-in amount (rounding down favours the pool there). -/
-def upscale (amount scalingFactor : Nat) : Nat := mulDown amount scalingFactor
+def upscale (amount scalingFactor : Nat) : Nat := mulDown scalingFactor amount
 
```

### M093: survived, no observed difference

arguments `amount` and `scalingFactor` of `mulUp` swapped in `upscaleUp` (line 30); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -29,3 +29,3 @@
 /-- The fix: the given-out amount is upscaled rounding up, `FixedPoint.mulUp`. -/
-def upscaleUp (amount scalingFactor : Nat) : Nat := mulUp amount scalingFactor
+def upscaleUp (amount scalingFactor : Nat) : Nat := mulUp scalingFactor amount
 
```

### M096: survived, no observed difference

arguments `amount` and `fee` of `mulUp` swapped in `subtractSwapFeeAmount` (line 39); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -38,3 +38,3 @@
 def subtractSwapFeeAmount (amount fee : Nat) : Option Nat :=
-  if mulUp amount fee ≤ amount then some (amount - mulUp amount fee) else none
+  if mulUp fee amount ≤ amount then some (amount - mulUp amount fee) else none
 
```

### M097: survived, no observed difference

arguments `amount` and `fee` of `mulUp` swapped in `subtractSwapFeeAmount` (line 39); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -38,3 +38,3 @@
 def subtractSwapFeeAmount (amount fee : Nat) : Option Nat :=
-  if mulUp amount fee ≤ amount then some (amount - mulUp amount fee) else none
+  if mulUp amount fee ≤ amount then some (amount - mulUp fee amount) else none
 
```

### M104: survived, no observed difference

arguments `a` and `(p.rate s.tokenIn)` of `upscale` swapped in `swapGivenIn` (line 47); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -46,3 +46,3 @@
   | some a =>
-    downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale a (p.rate s.tokenIn)))
+    downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale (p.rate s.tokenIn) a))
       (p.rate s.tokenOut)
```

### M106: survived, no observed difference

arguments `s.amount` and `(p.rate s.tokenOut)` of `upscaleUp` swapped in `swapGivenOut` (line 53); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -52,3 +52,3 @@
 def swapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
-  if scaledBalances p s.tokenOut ≤ upscaleUp s.amount (p.rate s.tokenOut) then none
+  if scaledBalances p s.tokenOut ≤ upscaleUp (p.rate s.tokenOut) s.amount then none
   else
```

### M111: survived, no observed difference

arguments `s.amount` and `(p.rate s.tokenOut)` of `upscaleUp` swapped in `swapGivenOut` (line 56); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -55,3 +55,3 @@
     match downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
-        (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
+        (upscaleUp (p.rate s.tokenOut) s.amount)) (p.rate s.tokenIn) with
     | none => none
```

### M129: survived, behaviour differs

constant `0` replaced by `1` in `divUp` (line 20); outputs differ from the reference on 126 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -19,3 +19,3 @@
 def divUp (a b : Nat) : Option Nat :=
-  if b = 0 then none else if a = 0 then some 0 else some ((a * ONE - 1) / b + 1)
+  if b = 0 then none else if a = 0 then some 1 else some ((a * ONE - 1) / b + 1)
 
```

First differing case:

```json
{"input": {"math": "product", "pool": {"balances": [27419, 87191], "fee": 50000000000000000, "rates": [1000000000000000000, 1058132408689971699]}, "swaps": [{"amount": 0, "in": 1, "kind": "out", "out": 0}, {"amount": 2, "in": 1, "kind": "out", "out": 0}, {"amount": 24, "in": 0, "kind": "in", "out": 1}, {"amount": 1, "in": 1, "kind": "in", "out": 0}, {"amount": 16, "in": 0, "kind": "in", "out": 1}, {"amount": 1144028517434505608816, "in": 0, "kind": "in", "out": 1}]}, "output": {"balances_after": [1144028517434505636273, 2], "ok": true, "steps": [{"balances": [27419, 87193], "ok": true, "quote": 2, "value": 2529704359}, {"balances": [27417, 87201], "ok": true, "quote": 8, "value": 2529766590}, {"balances": [27441, 87133], "ok": true, "quote": 68, "value": 2530005318}, {"balances": [27441, 87134], "ok": true, "quote": 0, "value": 2530032759}, {"balances": [27457, 87087], "ok": true, "quote": 47, "value": 2530135093}, {"balances": [1144028517434505636273, 2], "ok": true, "quote": 87085, "value": 2288057034869011272546}], "value_after": 2288057034869011272546, "value_before": 2529649521}, "reference_output": {"balances_after": [1144028517434505636273, 2], "ok": true, "steps": [{"balances": [27419, 87191], "ok": true, "quote": 0, "value": 2529649521}, {"balances": [27417, 87199], "ok": true, "quote": 8, "value": 2529711756}, {"balances": [27441, 87131], "ok": true, "quote": 68, "value": 2529950436}, {"balances": [27441, 87132], "ok": true, "quote": 0, "value": 2529977877}, {"balances": [27457, 87085], "ok": true, "quote": 47, "value": 2530080179}, {"balances": [1144028517434505636273, 2], "ok": true, "quote": 87083, "value": 2288057034869011272546}], "value_after": 2288057034869011272546, "value_before": 2529649521}}
```

### M130: survived, behaviour differs

constant `1` replaced by `2` in `divUp` (line 20); outputs differ from the reference on 4 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -19,3 +19,3 @@
 def divUp (a b : Nat) : Option Nat :=
-  if b = 0 then none else if a = 0 then some 0 else some ((a * ONE - 1) / b + 1)
+  if b = 0 then none else if a = 0 then some 0 else some ((a * ONE - 2) / b + 1)
 
```

First differing case:

```json
{"input": {"math": "product", "pool": {"balances": [1, 580380105682104817724422], "fee": 1000000000000, "rates": [1999999999999999999, 1058132408689971699]}, "swaps": [{"amount": 1, "in": 1, "kind": "in", "out": 0}, {"amount": 367471907244511917204360, "in": 0, "kind": "out", "out": 1}, {"amount": 1, "in": 1, "kind": "in", "out": 0}, {"amount": 1, "in": 1, "kind": "in", "out": 0}, {"amount": 101875, "in": 1, "kind": "in", "out": 0}]}, "output": {"balances_after": [3, 212908198437592900621940], "ok": true, "steps": [{"balances": [1, 580380105682104817724423], "ok": true, "quote": 0, "value": 614118999181145900870426}, {"balances": [3, 212908198437592900520063], "ok": true, "quote": 2, "value": 1126425324213063224790065}, {"balances": [3, 212908198437592900520064], "ok": true, "quote": 0, "value": 1126425324213063224790070}, {"balances": [3, 212908198437592900520065], "ok": true, "quote": 0, "value": 1126425324213063224790075}, {"balances": [3, 212908198437592900621940], "ok": true, "quote": 0, "value": 1126425324213063225329065}], "value_after": 1126425324213063225329065, "value_before": 614118999181145900870425}, "reference_output": {"balances_after": [4, 212908198437592900621940], "ok": true, "steps": [{"balances": [1, 580380105682104817724423], "ok": true, "quote": 0, "value": 614118999181145900870426}, {"balances": [4, 212908198437592900520063], "ok": true, "quote": 3, "value": 1576995453898288514706091}, {"balances": [4, 212908198437592900520064], "ok": true, "quote": 0, "value": 1576995453898288514706098}, {"balances": [4, 212908198437592900520065], "ok": true, "quote": 0, "value": 1576995453898288514706105}, {"balances": [4, 212908198437592900621940], "ok": true, "quote": 0, "value": 1576995453898288515460691}], "value_after": 1576995453898288515460691, "value_before": 614118999181145900870425}}
```

