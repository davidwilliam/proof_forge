# Specification strength: rw-compound-comp

Reference `realworld/tasks/rw-compound-comp/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `1490fbf459091f4e`; report `3901c41299bdeee8`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 184 | 184 | 154 | 0 | 125 | 1 | 0 | 123 | 0 | 28 | 126 of 154 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-CALLS-SUCCEED | 25 | 22 | kernel-checked |
| REQ-SUPPLY-HOOK | 47 | 39 | kernel-checked |
| REQ-BORROW-HOOK | 47 | 28 | kernel-checked |
| REQ-CLAIM | 101 | 19 | kernel-checked |
| REQ-SET-SPEEDS | 67 | 11 | kernel-checked |
| REQ-REWARDS-BOUNDED | 64 | 2 | kernel-checked |
| REQ-ACCOUNT-BOUNDED | 66 | 1 | kernel-checked |
| REQ-NO-BACKDATED-REWARDS | 33 | 1 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | rounding | `fraction` | floor division `/` replaced by ceiling division | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M002 | rounding | `mulDouble` | floor division `/` replaced by ceiling division | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-BORROW-HOOK |
| M003 | boundary | `subChecked` | `≤` replaced by `<` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CALLS-SUCCEED, REQ-REWARDS-BOUNDED | REQ-CALLS-SUCCEED |
| M004 | boundary | `updateCompSupplyIndex` | `>` replaced by `≥` | survived, no observed difference |  |  |
| M005 | boundary | `updateCompSupplyIndex` | `>` replaced by `≥` | survived, no observed difference |  |  |
| M006 | boundary | `updateCompSupplyIndex` | `>` replaced by `≥` | survived, no observed difference |  |  |
| M007 | boundary | `updateCompSupplyIndex` | `>` replaced by `≥` | survived, no observed difference |  |  |
| M008 | boundary | `updateCompBorrowIndex` | `>` replaced by `≥` | survived, no observed difference |  |  |
| M009 | boundary | `updateCompBorrowIndex` | `>` replaced by `≥` | survived, no observed difference |  |  |
| M010 | boundary | `updateCompBorrowIndex` | `>` replaced by `≥` | survived, no observed difference |  |  |
| M011 | boundary | `updateCompBorrowIndex` | `>` replaced by `≥` | survived, no observed difference |  |  |
| M012 | boundary | `distributeSupplierComp` | `≥` replaced by `>` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-CLAIM |
| M013 | boundary | `distributeBorrowerComp` | `≥` replaced by `>` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-REWARDS-BOUNDED | REQ-REWARDS-BOUNDED |
| M014 | boundary | `grantCompInternal` | `>` replaced by `≥` | survived, no observed difference |  |  |
| M015 | boundary | `grantCompInternal` | `≤` replaced by `<` | survived, no observed difference |  |  |
| M016 | equality | `distributeSupplierComp` | `=` replaced by `≠` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-ACCOUNT-BOUNDED |
| M017 | equality | `distributeBorrowerComp` | `=` replaced by `≠` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED | REQ-NO-BACKDATED-REWARDS |
| M018 | equality | `setSupplySpeed` | `≠` replaced by `=` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-SET-SPEEDS |
| M019 | equality | `setBorrowSpeed` | `≠` replaced by `=` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-SET-SPEEDS |
| M020 | arith | `fraction` | `*` replaced by `/` | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M021 | arith | `mulDouble` | `*` replaced by `/` | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M022 | arith | `subChecked` | `-` replaced by `+` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M023 | arith | `updateCompSupplyIndex` | `*` replaced by `/` | killed by property tests | REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M024 | arith | `updateCompSupplyIndex` | `+` replaced by `-` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-CALLS-SUCCEED |
| M025 | arith | `updateCompBorrowIndex` | `*` replaced by `/` | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M026 | arith | `updateCompBorrowIndex` | `+` replaced by `-` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-CALLS-SUCCEED |
| M027 | arith | `distributeSupplierComp` | `+` replaced by `-` | killed by property tests | REQ-CLAIM, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M028 | arith | `distributeBorrowerComp` | `+` replaced by `-` | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM | REQ-BORROW-HOOK |
| M029 | arith | `grantCompInternal` | `-` replaced by `+` | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M030 | arith | `grantCompInternal` | `+` replaced by `-` | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M031 | logic | `updateCompSupplyIndex` | `∧` replaced by `∨` | survived, no observed difference |  |  |
| M032 | logic | `updateCompBorrowIndex` | `∧` replaced by `∨` | survived, no observed difference |  |  |
| M033 | logic | `distributeSupplierComp` | `∧` replaced by `∨` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M034 | logic | `distributeBorrowerComp` | `∧` replaced by `∨` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED | REQ-CALLS-SUCCEED |
| M035 | logic | `grantCompInternal` | `∧` replaced by `∨` | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M036 | drop-conjunct | `updateCompSupplyIndex` | conjunct `deltaBlocks > 0` replaced by `True` | survived, no observed difference |  |  |
| M037 | drop-conjunct | `updateCompSupplyIndex` | conjunct `s.supplyState.speed > 0` replaced by `True` | survived, no observed difference |  |  |
| M038 | drop-conjunct | `updateCompBorrowIndex` | conjunct `deltaBlocks > 0` replaced by `True` | survived, no observed difference |  |  |
| M039 | drop-conjunct | `updateCompBorrowIndex` | conjunct `s.borrowState.speed > 0` replaced by `True` | survived, no observed difference |  |  |
| M040 | drop-conjunct | `distributeSupplierComp` | conjunct `(s.acct supplier).supplierIndex = 0` replaced by `True` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M041 | drop-conjunct | `distributeSupplierComp` | conjunct `supplyIndex ≥ compInitialIndex` replaced by `True` | killed by property tests | REQ-CALLS-SUCCEED |  |
| M042 | drop-conjunct | `distributeBorrowerComp` | conjunct `(s.acct borrower).borrowerIndex = 0` replaced by `True` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED | REQ-BORROW-HOOK |
| M043 | drop-conjunct | `distributeBorrowerComp` | conjunct `borrowIndex ≥ compInitialIndex` replaced by `True` | killed by property tests | REQ-CALLS-SUCCEED | REQ-CALLS-SUCCEED |
| M044 | drop-conjunct | `grantCompInternal` | conjunct `amount > 0` replaced by `True` | survived, no observed difference |  |  |
| M045 | drop-conjunct | `grantCompInternal` | conjunct `amount ≤ s.reserve` replaced by `True` | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M046 | guard | `subChecked` | condition `b ≤ a` replaced by `false` | killed by property tests | REQ-CALLS-SUCCEED | REQ-CALLS-SUCCEED |
| M047 | guard | `subChecked` | condition `b ≤ a` replaced by `true` | survived, no observed difference |  |  |
| M048 | guard | `updateCompSupplyIndex` | condition `deltaBlocks > 0 ∧ s.supplyState.speed > 0` replaced by `false` | killed by property tests | REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M049 | guard | `updateCompSupplyIndex` | condition `deltaBlocks > 0 ∧ s.supplyState.speed > 0` replaced by `true` | survived, no observed difference |  |  |
| M050 | guard | `updateCompSupplyIndex` | condition `supplyTokens > 0` replaced by `false` | killed by property tests | REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M051 | guard | `updateCompSupplyIndex` | condition `supplyTokens > 0` replaced by `true` | survived, no observed difference |  |  |
| M052 | guard | `updateCompSupplyIndex` | condition `deltaBlocks > 0` replaced by `false` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M053 | guard | `updateCompSupplyIndex` | condition `deltaBlocks > 0` replaced by `true` | survived, no observed difference |  |  |
| M054 | guard | `updateCompBorrowIndex` | condition `deltaBlocks > 0 ∧ s.borrowState.speed > 0` replaced by `false` | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M055 | guard | `updateCompBorrowIndex` | condition `deltaBlocks > 0 ∧ s.borrowState.speed > 0` replaced by `true` | survived, no observed difference |  |  |
| M056 | guard | `updateCompBorrowIndex` | condition `borrowAmount > 0` replaced by `false` | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | REQ-CLAIM |
| M057 | guard | `updateCompBorrowIndex` | condition `borrowAmount > 0` replaced by `true` | survived, no observed difference |  |  |
| M058 | guard | `updateCompBorrowIndex` | condition `deltaBlocks > 0` replaced by `true` | killed by extended property tests | WRAPPER |  |
| M059 | guard | `updateCompBorrowIndex` | condition `deltaBlocks > 0` replaced by `false` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M060 | guard | `distributeSupplierComp` | condition `(s.acct supplier).supplierIndex = 0 ∧ supplyIndex ≥ compI...` replaced by `true` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-CALLS-SUCCEED |
| M061 | guard | `distributeSupplierComp` | condition `(s.acct supplier).supplierIndex = 0 ∧ supplyIndex ≥ compI...` replaced by `false` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M062 | guard | `distributeBorrowerComp` | condition `(s.acct borrower).borrowerIndex = 0 ∧ borrowIndex ≥ compI...` replaced by `false` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-REWARDS-BOUNDED | REQ-BORROW-HOOK |
| M063 | guard | `distributeBorrowerComp` | condition `(s.acct borrower).borrowerIndex = 0 ∧ borrowIndex ≥ compI...` replaced by `true` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED | REQ-CALLS-SUCCEED |
| M064 | guard | `grantCompInternal` | condition `amount > 0 ∧ amount ≤ s.reserve` replaced by `true` | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M065 | guard | `grantCompInternal` | condition `amount > 0 ∧ amount ≤ s.reserve` replaced by `false` | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M066 | guard | `setSupplySpeed` | condition `s.supplyState.speed ≠ supplySpeed` replaced by `false` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-SET-SPEEDS |
| M067 | guard | `setSupplySpeed` | condition `s.supplyState.speed ≠ supplySpeed` replaced by `true` | killed by property tests | REQ-SET-SPEEDS | REQ-SET-SPEEDS |
| M068 | guard | `setBorrowSpeed` | condition `s.borrowState.speed ≠ borrowSpeed` replaced by `false` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-SET-SPEEDS |
| M069 | guard | `setBorrowSpeed` | condition `s.borrowState.speed ≠ borrowSpeed` replaced by `true` | killed by property tests | REQ-SET-SPEEDS | REQ-SET-SPEEDS |
| M070 | field | `updateCompSupplyIndex` | field read `s.blockNumber` replaced by `s.supplyState` | does not compile |  |  |
| M071 | field | `updateCompSupplyIndex` | field read `s.supplyState.block` replaced by `s.supplyState.speed` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-CALLS-SUCCEED |
| M072 | field | `updateCompSupplyIndex` | field read `s.supplyState.block` replaced by `s.supplyState.index` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CALLS-SUCCEED, REQ-REWARDS-BOUNDED | REQ-CALLS-SUCCEED |
| M073 | field | `updateCompSupplyIndex` | field read `s.supplyState.speed` replaced by `s.supplyState.block` | survived, no observed difference |  |  |
| M074 | field | `updateCompSupplyIndex` | field read `s.supplyState.speed` replaced by `s.supplyState.index` | survived, no observed difference |  |  |
| M075 | field | `updateCompSupplyIndex` | field read `s.supplyState.speed` replaced by `s.supplyState.block` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M076 | field | `updateCompSupplyIndex` | field read `s.supplyState.speed` replaced by `s.supplyState.index` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M077 | field | `updateCompSupplyIndex` | update of field `supplyState` dropped | killed by property tests | REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M078 | field | `updateCompSupplyIndex` | field read `s.supplyState` replaced by `s.blockNumber` | does not compile |  |  |
| M079 | field | `updateCompSupplyIndex` | update of field `index` dropped | killed by property tests | REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M080 | field | `updateCompSupplyIndex` | field read `s.supplyState.index` replaced by `s.supplyState.block` | killed by property tests | REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-CALLS-SUCCEED |
| M081 | field | `updateCompSupplyIndex` | field read `s.supplyState.index` replaced by `s.supplyState.speed` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-CALLS-SUCCEED |
| M082 | field | `updateCompSupplyIndex` | update of field `block` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M083 | field | `updateCompSupplyIndex` | field read `s.blockNumber` replaced by `s.supplyState` | does not compile |  |  |
| M084 | field | `updateCompSupplyIndex` | update of field `supplyState` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M085 | field | `updateCompSupplyIndex` | field read `s.supplyState` replaced by `s.blockNumber` | does not compile |  |  |
| M086 | field | `updateCompSupplyIndex` | update of field `block` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M087 | field | `updateCompSupplyIndex` | field read `s.blockNumber` replaced by `s.supplyState` | does not compile |  |  |
| M088 | field | `updateCompBorrowIndex` | field read `s.blockNumber` replaced by `s.borrowState` | does not compile |  |  |
| M089 | field | `updateCompBorrowIndex` | field read `s.borrowState.block` replaced by `s.borrowState.index` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CALLS-SUCCEED | REQ-CALLS-SUCCEED |
| M090 | field | `updateCompBorrowIndex` | field read `s.borrowState.block` replaced by `s.borrowState.speed` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-CALLS-SUCCEED |
| M091 | field | `updateCompBorrowIndex` | field read `s.borrowState.speed` replaced by `s.borrowState.block` | killed by property tests | WRAPPER |  |
| M092 | field | `updateCompBorrowIndex` | field read `s.borrowState.speed` replaced by `s.borrowState.index` | survived, no observed difference |  |  |
| M093 | field | `updateCompBorrowIndex` | field read `s.borrowState.speed` replaced by `s.borrowState.index` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M094 | field | `updateCompBorrowIndex` | field read `s.borrowState.speed` replaced by `s.borrowState.block` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M095 | field | `updateCompBorrowIndex` | update of field `borrowState` dropped | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M096 | field | `updateCompBorrowIndex` | field read `s.borrowState` replaced by `s.blockNumber` | does not compile |  |  |
| M097 | field | `updateCompBorrowIndex` | update of field `index` dropped | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M098 | field | `updateCompBorrowIndex` | field read `s.borrowState.index` replaced by `s.borrowState.speed` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-CALLS-SUCCEED |
| M099 | field | `updateCompBorrowIndex` | field read `s.borrowState.index` replaced by `s.borrowState.block` | killed by property tests | REQ-BORROW-HOOK, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-SET-SPEEDS | REQ-CALLS-SUCCEED |
| M100 | field | `updateCompBorrowIndex` | update of field `block` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M101 | field | `updateCompBorrowIndex` | field read `s.blockNumber` replaced by `s.borrowState` | does not compile |  |  |
| M102 | field | `updateCompBorrowIndex` | update of field `borrowState` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M103 | field | `updateCompBorrowIndex` | field read `s.borrowState` replaced by `s.blockNumber` | does not compile |  |  |
| M104 | field | `updateCompBorrowIndex` | update of field `block` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M105 | field | `updateCompBorrowIndex` | field read `s.blockNumber` replaced by `s.borrowState` | does not compile |  |  |
| M106 | field | `distributeSupplierComp` | field read `s.acct` replaced by `s.withAcct` | does not compile |  |  |
| M107 | field | `distributeSupplierComp` | projection `.supplierIndex` replaced by `.supply` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M108 | field | `distributeSupplierComp` | field read `s.acct` replaced by `s.withAcct` | does not compile |  |  |
| M109 | field | `distributeSupplierComp` | projection `.supplierIndex` replaced by `.supply` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M110 | field | `distributeSupplierComp` | field read `s.acct` replaced by `s.withAcct` | does not compile |  |  |
| M111 | field | `distributeSupplierComp` | projection `.supply` replaced by `.supplierIndex` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M112 | field | `distributeSupplierComp` | field read `s.withAcct` replaced by `s.acct` | does not compile |  |  |
| M113 | field | `distributeSupplierComp` | update of field `supplierIndex` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M114 | field | `distributeSupplierComp` | update of field `accrued` dropped | killed by property tests | REQ-CLAIM, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M115 | field | `distributeBorrowerComp` | field read `s.acct` replaced by `s.withAcct` | does not compile |  |  |
| M116 | field | `distributeBorrowerComp` | projection `.borrowerIndex` replaced by `.borrow` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-REWARDS-BOUNDED | REQ-BORROW-HOOK |
| M117 | field | `distributeBorrowerComp` | field read `s.acct` replaced by `s.withAcct` | does not compile |  |  |
| M118 | field | `distributeBorrowerComp` | projection `.borrowerIndex` replaced by `.borrow` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED | REQ-BORROW-HOOK |
| M119 | field | `distributeBorrowerComp` | field read `s.acct` replaced by `s.withAcct` | does not compile |  |  |
| M120 | field | `distributeBorrowerComp` | projection `.borrow` replaced by `.borrowerIndex` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED | REQ-CLAIM |
| M121 | field | `distributeBorrowerComp` | field read `s.withAcct` replaced by `s.acct` | does not compile |  |  |
| M122 | field | `distributeBorrowerComp` | update of field `borrowerIndex` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED | REQ-BORROW-HOOK |
| M123 | field | `distributeBorrowerComp` | update of field `accrued` dropped | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM | REQ-BORROW-HOOK |
| M124 | field | `grantCompInternal` | field read `s.acct` replaced by `s.reserve` | does not compile |  |  |
| M125 | field | `grantCompInternal` | field read `s.reserve` replaced by `s.acct` | does not compile |  |  |
| M126 | field | `grantCompInternal` | update of field `reserve` dropped | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M127 | field | `grantCompInternal` | field read `s.reserve` replaced by `s.acct` | does not compile |  |  |
| M128 | field | `grantCompInternal` | update of field `accts` dropped | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M129 | field | `grantCompInternal` | update of field `accrued` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED | REQ-CLAIM |
| M130 | field | `grantCompInternal` | update of field `wallet` dropped | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M131 | field | `setSupplySpeed` | update of field `supplyState` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-SET-SPEEDS |
| M132 | field | `setSupplySpeed` | update of field `speed` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-REWARDS-BOUNDED |
| M133 | field | `setBorrowSpeed` | update of field `borrowState` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-SET-SPEEDS |
| M134 | field | `setBorrowSpeed` | update of field `speed` dropped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-SET-SPEEDS |
| M135 | swap | `fraction` | operands of `/` swapped | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M136 | swap | `mulDouble` | operands of `/` swapped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M137 | swap | `subChecked` | operands of `≤` swapped | killed by property tests | REQ-CALLS-SUCCEED | REQ-CALLS-SUCCEED |
| M138 | swap | `subChecked` | operands of `-` swapped | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M139 | swap | `updateCompSupplyIndex` | arguments `s.blockNumber` and `s.supplyState.block` of `subChecked` swapped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CALLS-SUCCEED, REQ-REWARDS-BOUNDED | REQ-CALLS-SUCCEED |
| M140 | swap | `updateCompSupplyIndex` | operands of `>` swapped | killed by property tests | REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M141 | swap | `updateCompSupplyIndex` | operands of `>` swapped | killed by property tests | REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M142 | swap | `updateCompSupplyIndex` | operands of `>` swapped | killed by property tests | REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M143 | swap | `updateCompSupplyIndex` | arguments `compAccrued` and `supplyTokens` of `fraction` swapped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M144 | swap | `updateCompSupplyIndex` | operands of `>` swapped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M145 | swap | `updateCompBorrowIndex` | arguments `s.blockNumber` and `s.borrowState.block` of `subChecked` swapped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CALLS-SUCCEED | REQ-CALLS-SUCCEED |
| M146 | swap | `updateCompBorrowIndex` | operands of `>` swapped | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M147 | swap | `updateCompBorrowIndex` | operands of `>` swapped | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M148 | swap | `updateCompBorrowIndex` | operands of `>` swapped | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M149 | swap | `updateCompBorrowIndex` | arguments `compAccrued` and `borrowAmount` of `fraction` swapped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M150 | swap | `updateCompBorrowIndex` | operands of `>` swapped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M151 | swap | `distributeSupplierComp` | operands of `≥` swapped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M152 | swap | `distributeSupplierComp` | arguments `supplyIndex` and `supplierIndex` of `subChecked` swapped | killed by property tests | REQ-CALLS-SUCCEED | REQ-CALLS-SUCCEED |
| M153 | swap | `distributeSupplierComp` | arguments `(s.acct supplier).supply` and `deltaIndex` of `mulDouble` swapped | survived, no observed difference |  |  |
| M154 | swap | `distributeBorrowerComp` | operands of `≥` swapped | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CALLS-SUCCEED, REQ-CLAIM, REQ-REWARDS-BOUNDED | REQ-CALLS-SUCCEED |
| M155 | swap | `distributeBorrowerComp` | arguments `borrowIndex` and `borrowerIndex` of `subChecked` swapped | killed by property tests | REQ-CALLS-SUCCEED | REQ-CALLS-SUCCEED |
| M156 | swap | `distributeBorrowerComp` | arguments `(s.acct borrower).borrow` and `deltaIndex` of `mulDouble` swapped | survived, no observed difference |  |  |
| M157 | swap | `grantCompInternal` | operands of `>` swapped | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M158 | swap | `grantCompInternal` | operands of `≤` swapped | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M159 | swap | `grantCompInternal` | operands of `-` swapped | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M160 | swap | `claimComp` | arguments `s` and `holder` of `distributeBorrowerComp` swapped | does not compile |  |  |
| M161 | swap | `claimComp` | arguments `s` and `holder` of `distributeSupplierComp` swapped | does not compile |  |  |
| M162 | swap | `claimComp` | arguments `s` and `holder` of `grantCompInternal` swapped | does not compile |  |  |
| M163 | swap | `setCompSpeedInternal` | arguments `s` and `supplySpeed` of `setSupplySpeed` swapped | does not compile |  |  |
| M164 | swap | `setCompSpeedInternal` | arguments `s` and `borrowSpeed` of `setBorrowSpeed` swapped | does not compile |  |  |
| M165 | swap | `comptroller` | arguments `s` and `who` of `distributeSupplierComp` swapped | does not compile |  |  |
| M166 | swap | `comptroller` | arguments `s` and `who` of `distributeBorrowerComp` swapped | does not compile |  |  |
| M167 | swap | `comptroller` | arguments `s` and `who` of `claimComp` swapped | does not compile |  |  |
| M168 | swap | `comptroller` | arguments `a` and `b` of `setSpeeds` swapped | killed by property tests | REQ-SET-SPEEDS | REQ-SET-SPEEDS |
| M169 | swap | `comptroller` | arguments `s` and `a` of `setCompSpeedInternal` swapped | does not compile |  |  |
| M170 | swap | `comptroller` | arguments `a` and `b` of `setCompSpeedInternal` swapped | killed by property tests | REQ-SET-SPEEDS | REQ-SET-SPEEDS |
| M171 | constant | `updateCompSupplyIndex` | constant `0` replaced by `1` | killed by property tests | REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M172 | constant | `updateCompSupplyIndex` | constant `0` replaced by `1` | killed by property tests | REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M173 | constant | `updateCompSupplyIndex` | constant `0` replaced by `1` | killed by property tests | REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M174 | constant | `updateCompSupplyIndex` | constant `0` replaced by `1` | killed by property tests | REQ-CLAIM, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M175 | constant | `updateCompSupplyIndex` | constant `0` replaced by `1` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M176 | constant | `updateCompBorrowIndex` | constant `0` replaced by `1` | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | REQ-CLAIM |
| M177 | constant | `updateCompBorrowIndex` | constant `0` replaced by `1` | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M178 | constant | `updateCompBorrowIndex` | constant `0` replaced by `1` | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M179 | constant | `updateCompBorrowIndex` | constant `0` replaced by `1` | killed by property tests | REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M180 | constant | `updateCompBorrowIndex` | constant `0` replaced by `1` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SET-SPEEDS | REQ-BORROW-HOOK |
| M181 | constant | `distributeSupplierComp` | constant `0` replaced by `1` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-REWARDS-BOUNDED, REQ-SUPPLY-HOOK | REQ-SUPPLY-HOOK |
| M182 | constant | `distributeBorrowerComp` | constant `0` replaced by `1` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-BORROW-HOOK, REQ-CLAIM, REQ-REWARDS-BOUNDED | REQ-BORROW-HOOK |
| M183 | constant | `grantCompInternal` | constant `0` replaced by `1` | killed by property tests | REQ-CLAIM | REQ-CLAIM |
| M184 | constant | `grantCompInternal` | constant `0` replaced by `1` | killed by property tests | REQ-ACCOUNT-BOUNDED, REQ-CLAIM, REQ-NO-BACKDATED-REWARDS, REQ-REWARDS-BOUNDED | REQ-CLAIM |

## Survivors

### M004: survived, no observed difference

`>` replaced by `≥` in `updateCompSupplyIndex` (line 569); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -568,3 +568,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
+    if deltaBlocks ≥ 0 ∧ s.supplyState.speed > 0 then
       let supplyTokens := totalSupply s
```

### M005: survived, no observed difference

`>` replaced by `≥` in `updateCompSupplyIndex` (line 569); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -568,3 +568,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
+    if deltaBlocks > 0 ∧ s.supplyState.speed ≥ 0 then
       let supplyTokens := totalSupply s
```

### M006: survived, no observed difference

`>` replaced by `≥` in `updateCompSupplyIndex` (line 572); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -571,3 +571,3 @@
       let compAccrued := deltaBlocks * s.supplyState.speed
-      let ratio := if supplyTokens > 0 then fraction compAccrued supplyTokens else 0
+      let ratio := if supplyTokens ≥ 0 then fraction compAccrued supplyTokens else 0
       some { s with supplyState :=
```

### M007: survived, no observed difference

`>` replaced by `≥` in `updateCompSupplyIndex` (line 575); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -574,3 +574,3 @@
         { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } }
-    else if deltaBlocks > 0 then
+    else if deltaBlocks ≥ 0 then
       some { s with supplyState := { s.supplyState with block := s.blockNumber } }
```

### M008: survived, no observed difference

`>` replaced by `≥` in `updateCompBorrowIndex` (line 583); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -582,3 +582,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.borrowState.speed > 0 then
+    if deltaBlocks ≥ 0 ∧ s.borrowState.speed > 0 then
       let borrowAmount := totalBorrows s
```

### M009: survived, no observed difference

`>` replaced by `≥` in `updateCompBorrowIndex` (line 583); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -582,3 +582,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.borrowState.speed > 0 then
+    if deltaBlocks > 0 ∧ s.borrowState.speed ≥ 0 then
       let borrowAmount := totalBorrows s
```

### M010: survived, no observed difference

`>` replaced by `≥` in `updateCompBorrowIndex` (line 586); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -585,3 +585,3 @@
       let compAccrued := deltaBlocks * s.borrowState.speed
-      let ratio := if borrowAmount > 0 then fraction compAccrued borrowAmount else 0
+      let ratio := if borrowAmount ≥ 0 then fraction compAccrued borrowAmount else 0
       some { s with borrowState :=
```

### M011: survived, no observed difference

`>` replaced by `≥` in `updateCompBorrowIndex` (line 589); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -588,3 +588,3 @@
         { s.borrowState with index := s.borrowState.index + ratio, block := s.blockNumber } }
-    else if deltaBlocks > 0 then
+    else if deltaBlocks ≥ 0 then
       some { s with borrowState := { s.borrowState with block := s.blockNumber } }
```

### M014: survived, no observed difference

`>` replaced by `≥` in `grantCompInternal` (line 619); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -618,3 +618,3 @@
   let amount := (s.acct user).accrued
-  if amount > 0 ∧ amount ≤ s.reserve then
+  if amount ≥ 0 ∧ amount ≤ s.reserve then
     { s with reserve := s.reserve - amount,
```

### M015: survived, no observed difference

`≤` replaced by `<` in `grantCompInternal` (line 619); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -618,3 +618,3 @@
   let amount := (s.acct user).accrued
-  if amount > 0 ∧ amount ≤ s.reserve then
+  if amount > 0 ∧ amount < s.reserve then
     { s with reserve := s.reserve - amount,
```

### M031: survived, no observed difference

`∧` replaced by `∨` in `updateCompSupplyIndex` (line 569); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -568,3 +568,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
+    if deltaBlocks > 0 ∨ s.supplyState.speed > 0 then
       let supplyTokens := totalSupply s
```

### M032: survived, no observed difference

`∧` replaced by `∨` in `updateCompBorrowIndex` (line 583); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -582,3 +582,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.borrowState.speed > 0 then
+    if deltaBlocks > 0 ∨ s.borrowState.speed > 0 then
       let borrowAmount := totalBorrows s
```

### M036: survived, no observed difference

conjunct `deltaBlocks > 0` replaced by `True` in `updateCompSupplyIndex` (line 569); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -568,3 +568,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
+    if True ∧ s.supplyState.speed > 0 then
       let supplyTokens := totalSupply s
```

### M037: survived, no observed difference

conjunct `s.supplyState.speed > 0` replaced by `True` in `updateCompSupplyIndex` (line 569); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -568,3 +568,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
+    if deltaBlocks > 0 ∧ True then
       let supplyTokens := totalSupply s
```

### M038: survived, no observed difference

conjunct `deltaBlocks > 0` replaced by `True` in `updateCompBorrowIndex` (line 583); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -582,3 +582,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.borrowState.speed > 0 then
+    if True ∧ s.borrowState.speed > 0 then
       let borrowAmount := totalBorrows s
```

### M039: survived, no observed difference

conjunct `s.borrowState.speed > 0` replaced by `True` in `updateCompBorrowIndex` (line 583); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -582,3 +582,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.borrowState.speed > 0 then
+    if deltaBlocks > 0 ∧ True then
       let borrowAmount := totalBorrows s
```

### M044: survived, no observed difference

conjunct `amount > 0` replaced by `True` in `grantCompInternal` (line 619); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -618,3 +618,3 @@
   let amount := (s.acct user).accrued
-  if amount > 0 ∧ amount ≤ s.reserve then
+  if True ∧ amount ≤ s.reserve then
     { s with reserve := s.reserve - amount,
```

### M047: survived, no observed difference

condition `b ≤ a` replaced by `true` in `subChecked` (line 563); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -562,3 +562,3 @@
 
-def subChecked (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none
+def subChecked (a b : Nat) : Option Nat := if true then some (a - b) else none
 
```

### M049: survived, no observed difference

condition `deltaBlocks > 0 ∧ s.supplyState.speed > 0` replaced by `true` in `updateCompSupplyIndex` (line 569); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -568,3 +568,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
+    if true then
       let supplyTokens := totalSupply s
```

### M051: survived, no observed difference

condition `supplyTokens > 0` replaced by `true` in `updateCompSupplyIndex` (line 572); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -571,3 +571,3 @@
       let compAccrued := deltaBlocks * s.supplyState.speed
-      let ratio := if supplyTokens > 0 then fraction compAccrued supplyTokens else 0
+      let ratio := if true then fraction compAccrued supplyTokens else 0
       some { s with supplyState :=
```

### M053: survived, no observed difference

condition `deltaBlocks > 0` replaced by `true` in `updateCompSupplyIndex` (line 575); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -574,3 +574,3 @@
         { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } }
-    else if deltaBlocks > 0 then
+    else if true then
       some { s with supplyState := { s.supplyState with block := s.blockNumber } }
```

### M055: survived, no observed difference

condition `deltaBlocks > 0 ∧ s.borrowState.speed > 0` replaced by `true` in `updateCompBorrowIndex` (line 583); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -582,3 +582,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.borrowState.speed > 0 then
+    if true then
       let borrowAmount := totalBorrows s
```

### M057: survived, no observed difference

condition `borrowAmount > 0` replaced by `true` in `updateCompBorrowIndex` (line 586); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -585,3 +585,3 @@
       let compAccrued := deltaBlocks * s.borrowState.speed
-      let ratio := if borrowAmount > 0 then fraction compAccrued borrowAmount else 0
+      let ratio := if true then fraction compAccrued borrowAmount else 0
       some { s with borrowState :=
```

### M073: survived, no observed difference

field read `s.supplyState.speed` replaced by `s.supplyState.block` in `updateCompSupplyIndex` (line 569); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -568,3 +568,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
+    if deltaBlocks > 0 ∧ s.supplyState.block > 0 then
       let supplyTokens := totalSupply s
```

### M074: survived, no observed difference

field read `s.supplyState.speed` replaced by `s.supplyState.index` in `updateCompSupplyIndex` (line 569); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -568,3 +568,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
+    if deltaBlocks > 0 ∧ s.supplyState.index > 0 then
       let supplyTokens := totalSupply s
```

### M092: survived, no observed difference

field read `s.borrowState.speed` replaced by `s.borrowState.index` in `updateCompBorrowIndex` (line 583); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -582,3 +582,3 @@
   | some deltaBlocks =>
-    if deltaBlocks > 0 ∧ s.borrowState.speed > 0 then
+    if deltaBlocks > 0 ∧ s.borrowState.index > 0 then
       let borrowAmount := totalBorrows s
```

### M153: survived, no observed difference

arguments `(s.acct supplier).supply` and `deltaIndex` of `mulDouble` swapped in `distributeSupplierComp` (line 601); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -600,3 +600,3 @@
   | some deltaIndex =>
-    let supplierDelta := mulDouble (s.acct supplier).supply deltaIndex
+    let supplierDelta := mulDouble deltaIndex (s.acct supplier).supply
     some (s.withAcct supplier fun a =>
```

### M156: survived, no observed difference

arguments `(s.acct borrower).borrow` and `deltaIndex` of `mulDouble` swapped in `distributeBorrowerComp` (line 613); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -612,3 +612,3 @@
   | some deltaIndex =>
-    let borrowerDelta := mulDouble (s.acct borrower).borrow deltaIndex
+    let borrowerDelta := mulDouble deltaIndex (s.acct borrower).borrow
     some (s.withAcct borrower fun a =>
```

