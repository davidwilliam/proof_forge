# COMP reward distribution: Compound Proposal 62

This task holds a Lean specification of the COMP reward distribution in Compound's
Comptroller. It covers the supply and borrow reward indices of a market, the index recorded
for each account, the COMP accrued to each account, claims, speed changes, and the one-time
upgrade that Proposal 62 ran on mainnet. The task also holds a proved reference
implementation, which is the fix shipped by Proposal 64 and kept by Proposal 65, and a port of
the Proposal 62 code. The port is refuted in the Lean kernel by a claim made on mainnet 139
blocks after the upgrade. The deployed Solidity, compiled from the pinned commits, gives the
same results as the port and the reference on every sequence tested, and gives the same
result as the port on a fork of mainnet.

## What happened

Figures in this section come from the sources listed at the end or were read from mainnet;
the commands are in `eval/realworld_compound.py`.

- Proposal 62 took effect at block 13322798, 2021-09-29 20:24:08 UTC. In that block the
  Unitroller's implementation changed from `0x75442ac771a7243433e033f3f8eab2631e22938f`
  (Comptroller G6) to `0x374ABb8cE19A73f2c4EFAd642bda76c797f19233`. The proposal split each
  market's COMP speed into a supply speed and a borrow speed. Its `_become` ran
  `_upgradeSplitCompRewards`, which copied the old speed to both sides and set every reward
  index that was still 0 to `compInitialIndex` (1e36).
- At block 13322797, six markets had both reward indices at 0 and COMP speed 0: cTUSD, cMKR,
  cSUSHI, cAAVE, cYFI and cSAI (`0xF5DCe57282A584D2746FaF1593d3121Fcac444dC`, whose on-chain
  symbol is cDAI). These are the markets the Compound newsletter names as affected. Five other
  markets had a borrow index that had grown from 0 and was still below 1e36: cBAT, cDAI, cETH,
  cREP and cZRX. The specification therefore allows an index to start from 0 as well as from
  1e36.
- The Comptroller held 300514463598935139440340 COMP-wei (300,514.46 COMP) at block 13322797.
- The Block, the same night, quoting Robert Leshner: "the impact is bounded, at worst,
  280,000 COMP tokens," Leshner said. That is worth about $80 million as of press time. The
  same article reports that the bug "has mistakenly allowed some users to claim as much as
  about 168,000 COMP tokens already, worth around $50 million" and that "The Comptroller
  contract address now has 112,000 COMP tokens left."
- The Compound newsletter of 2021-10-14: "163k COMP were incorrectly claimed & returned to the
  community Timelock, 130k COMP remained in the Comptroller, which could have been incorrectly
  claimed, and ~200k misallocated COMP are currently outstanding."
- One claim, read from mainnet: transaction
  `0xc9244e5349f49f3b74a54a882e71f1ca11ba14ed74f73bf2cd091ed8be2b0001` (block 13322937, 139
  blocks after the upgrade) is `claimComp` for `0xf3f5C252e8ACd60671f92c7F72cf33661221Ef42` in
  cSUSHI and cETH. The account had no recorded borrower index in cSUSHI and a borrow balance of
  19192199818109949449525 at a cSUSHI borrow index of 1011323718759163337, which is
  18977306140567618322762 borrow units. The transaction emitted
  `DistributedBorrowerComp(cSUSHI, account, 18977306140567618322762, 1e36)` and paid the
  account 18,977.35 COMP. Nothing had been emitted to cSUSHI.
- Between the upgrade and Proposal 64 (blocks 13322798 to 13382884), the Comptroller emitted
  86 `DistributedBorrowerComp` and `DistributedSupplierComp` events that credit a positive
  amount at an index of exactly 1e36, the pattern of the bug
  (`results/compound-1/real-code/onchain-credits.jsonl`). They credit 74 accounts. The 46
  borrow-side credits total 70,514,337.98 COMP: cTUSD 32 credits and 70,458,160.18 COMP,
  cSUSHI 7 and 51,677.13, cAAVE 3 and 4,500.56, and cSAI, cMKR and cYFI together 0.11. The 40
  supply-side credits total 0.49 COMP. These are amounts added to `compAccrued`, not
  payments. The largest is 70,024,581.83 COMP, credited to a cTUSD borrower
  (`0xb3bd459e0598dde1fe84b1d0a1430be175b5d5be`) in transaction
  `0x6baaf785bf6a886c257a1add55cc5a3389bfcc48bd603426d3ba624e3d08c6b3` (block 13323929). It is
  far more than the Comptroller held, and that transaction transferred no COMP:
  `grantCompInternal` pays only when the Comptroller holds the whole amount.
- Proposal 64 took effect at block 13382885 (2021-10-09 06:16:06 UTC; the newsletter gives
  October 8th) with implementation `0x234b619b4f4e405665f7d94f2ce60c24256032b5`. It changed
  `>` to `>=` and added a temporary lock in `grantCompInternal`. Proposal 65 took effect at
  block 13449598 (2021-10-19 17:50:24 UTC) with implementation
  `0xbafe01ff935c7305907c33bf824352ee5979b526`. It removed the lock and added a one-off
  `fixBadAccruals` to correct balances.

## The vulnerable lines

Proposal 62's implementation is verified on Sourcify (exact match of runtime and creation
bytecode, solc 0.5.16, optimizer 200 runs). Its 15 source files are byte-identical to
compound-finance/compound-protocol at commit `f73b29373eb65cedf24896d7be46eed38435fc91`, the
head of pull request 161 ("The Comp Speeds Branch on Mainnet"). In `contracts/Comptroller.sol`
(SHA-256 `ec97bebc1c045bbbc2da36d42b079336e28d5f187524f88c29b3e00b10895e16`):

```solidity
1211        uint supplyIndex = supplyState.index;
1212        uint supplierIndex = compSupplierIndex[cToken][supplier];
1215        compSupplierIndex[cToken][supplier] = supplyIndex;
1217        if (supplierIndex == 0 && supplyIndex > compInitialIndex) {
1221            supplierIndex = compInitialIndex;
1222        }
1225        Double memory deltaIndex = Double({mantissa: sub_(supplyIndex, supplierIndex)});
1227        uint supplierTokens = CToken(cToken).balanceOf(supplier);
1230        uint supplierDelta = mul_(supplierTokens, deltaIndex);
```

Line 1256 in `distributeBorrowerComp` has the same condition with `borrowIndex >
compInitialIndex`. The upgrade set the indices of the six markets to exactly 1e36, so for an
account that held a position from before and had no recorded index, the condition was false.
Its start stayed at 0, and it was credited `units * (1e36 - 0) / 1e36`, which is one COMP-wei
per unit. For a cToken balance (8 decimals) that is small; for a borrow, measured in units of
the underlying, it is about one COMP per token borrowed.

The condition has a history in pull request 165. Commit
`2c7984fe3830daf99f3d2c9c6334b5d75a4e247a` (2021-09-13, "Fix subtraction underflow problem")
changed `borrowIndex > 0` to `borrowIndex > compInitialIndex`. The commit message says the
underflow "occurs when calling distributeBorrowerComp on markets whose borrowState.index
didn't start at 1e36". Commit `732887b937ad0dfdb96c09417534449e768a0065` (2021-09-17) made
`distributeSupplierComp` match. The fix, commit `ddde3ec0e749611474ca622081beb72deb2779af`
(2021-09-30, "Fix the bug introduced in proposal 62"), changes `>` to `>=` on both lines.

## The specification

`spec/CompRewards/Spec.lean` models one market. Each side (supply, borrow) has an index, a
block and a speed. Each account has a cToken balance, borrow units, a recorded supplier
index and a recorded borrower index (0 when none is recorded), accrued COMP and a wallet. The
Comptroller has its own COMP (`reserve`). The implementation `comptroller : Impl` handles
four calls: the supply hook (`mintAllowed`, `redeemAllowed`, `transferAllowed`,
`seizeAllowed`), the borrow hook (`borrowAllowed`, `repayBorrowAllowed`), `claimComp` and
`_setCompSpeeds`. Balance changes call the hook first and then change the balance, as a
cToken does. Blocks passing and COMP sent to the Comptroller are operations defined by the
specification. The pre-upgrade state (`Legacy`) and the upgrade (`upgrade`, a transcription
of `_upgradeSplitCompRewards`) are protected: the upgrade already ran on mainnet, so a repair
has to handle the states it produced.

Eight requirements are locked in `spec/CompRewards/Challenge.lean`:

| Requirement | Statement |
|---|---|
| REQ-CALLS-SUCCEED | in a consistent state (no side's block ahead of the current block, no recorded index above the market's), every call succeeds |
| REQ-SUPPLY-HOOK, REQ-BORROW-HOOK | the full next state: the index brought up to date (`blocks * speed * 1e36 / total`, rounded down), the account credited `units * (index - start) / 1e36`, rounded down, from its start (`accrualStart`: its recorded index; with none recorded, `compInitialIndex` once the index has reached it, else 0), its index recorded, nothing else changed |
| REQ-CLAIM | borrow side, then supply side, then payment of everything accrued when the Comptroller holds that much |
| REQ-SET-SPEEDS | a changed speed first accrues at the old speed |
| REQ-REWARDS-BOUNDED | the sequence-level bound below |
| REQ-ACCOUNT-BOUNDED | the same bound for every single account |
| REQ-NO-BACKDATED-REWARDS | an account with no position gains at most the COMP emitted from then on |

The main requirement, verbatim:

```lean
/-- REQ-REWARDS-BOUNDED: from the upgrade of any well-formed pre-upgrade state, after any
sequence of operations, the COMP paid out to accounts plus the COMP accrued to them never
exceeds what they held or had accrued before the upgrade, plus what they were owed at the
upgrade, plus the COMP emitted since. -/
def RewardsBounded (comptroller : Impl) : Prop :=
  ∀ (L : Legacy) (ops : List Op), L.WellFormed →
    (run comptroller (upgrade L) ops).credited ≤
      (upgrade L).credited + L.owed + emitted (L.compSpeed, L.compSpeed) ops

theorem req_rewards_bounded : RewardsBounded comptroller := sorry
```

Here `credited` is the sum of `accrued + wallet` over all accounts. `emitted` is computed from
the operations alone (blocks passed times the supply and borrow speeds last set), never from
the implementation's state. `L.owed` is the COMP the accounts were owed before the upgrade:
each account's units times the index gained since its start, scaled down by 1e36, plus the COMP
emitted since each index was last updated. For an account with no recorded index, the start
is the value the index started from. That value is not stored on chain. `Legacy` carries it as
`supplyStart` and `borrowStart`. `WellFormed` states the facts Comptroller G6 maintains: each
index started from 0 or 1e36 and never decreased, no side's block lies ahead of the current
block, and no recorded index exceeds the market's.

REQ-NO-BACKDATED-REWARDS is the per-account form of "an account never accrues for blocks
before it held a position":

```lean
def NoBackdatedRewards (comptroller : Impl) : Prop :=
  ∀ (L : Legacy) (history ops : List Op) (who : Account), L.WellFormed →
    NoPosition (run comptroller (upgrade L) history) who →
    (run comptroller (run comptroller (upgrade L) history) ops).creditedTo who ≤
      (run comptroller (upgrade L) history).creditedTo who +
        emitted (speedsAfter (L.compSpeed, L.compSpeed) history) ops
```

The requirements are not vacuous. `spec/CompRewards/Sanity.lean` proves `honest_rewards`.
Every implementation that meets REQ-CALLS-SUCCEED, REQ-CLAIM and REQ-SET-SPEEDS runs the
following sequence with exactly these results. The market never had rewards and holds 50
cTokens of account 0 and 20 borrow units of account 1 from before the upgrade, neither with a
recorded index. Speeds of 3 and 2 are set and 10 blocks pass, so 50 COMP is emitted. Both
accounts claim: account 0 receives 30, account 1 receives 20, and the Comptroller's COMP falls
from 1000 to 950. The same file proves that the upgrade changes no account.

## What was proved

- `reference/SolutionA.lean` defines `comptroller` as a transcription of the shipped fix:
  `updateCompSupplyIndex`, `updateCompBorrowIndex`, `distributeSupplierComp`,
  `distributeBorrowerComp`, `claimComp`, `grantCompInternal` and `setCompSpeedInternal` of
  Proposal 64 (commit `32f765957e05560cbbd977d7a49c86a09a81282b`), which Proposal 65 (commit
  `c05d7e09e57ff69582ddb621984e46099f1b4d4b`) left unchanged except for the claim lock. It
  proves all eight requirements. The judge accepts it: `lake comparator --paranoid` with the
  Lean default and paranoid kernels plus lean4lean, nanoda, con-leche and con-ron, then
  `leanchecker`, with axioms `propext`, `Classical.choice` and `Quot.sound` only. Its
  executable passes 1,001 generated property cases (`validation.json`). The proof goes
  through a potential, the scaled COMP credited to all accounts plus their pending rewards
  plus the unindexed emission, which never grows except when blocks pass, and then by at most
  the COMP emitted. The same argument for a single account gives the other two bounds.
- `spec/CompRewards/Sanity.lean` proves `honest_rewards` (above).
- Muse did not complete the task. Six runs of Muse Spark 1.3 on the Contributor tier, each
  capped at $10 list and 14,400 s, ended UNRESOLVED: two in repair mode without a planner (A1),
  two with Muse Wonder as planner (A2), and two in implement mode. The A2 runs proved the five
  per-call requirements, and the implement runs proved three and four of them. No run proved
  REQ-REWARDS-BOUNDED, REQ-ACCOUNT-BOUNDED or REQ-NO-BACKDATED-REWARDS. Total cost: $54.55 at
  list prices, $5.58 charged. Details and Passports are in `results/compound-1/README.md`.

## What the port corresponds to

`candidate/Solution.lean` (also `attacks/p62_port.lean`) transcribes the Proposal 62
functions listed above, with line numbers, from commit
`f73b29373eb65cedf24896d7be46eed38435fc91`, including `fraction`, `mul_` and the `sub_`
underflow reverts of `ExponentialNoError.sol`. It differs from the reference only in the two
`>` conditions. `attacks/p64_claim_lock.lean` is the Proposal 64 code as deployed: the `>=`
fix plus the lock in `grantCompInternal`. `attacks/supplier_only_fix.lean` changes only the
supply side; it is not a release.

Modelled and abstracted:

- One market. On chain, `claimComp(holder)` iterates over every market, `compAccrued` and the
  payment are shared across markets, and Proposal 64's lock checks every market.
- Borrow units are `borrowBalanceStored / borrowIndex` with the cToken's borrow index at 1e18.
  The market's total is the sum of the accounts' units; on chain it is `totalBorrows /
  borrowIndex`, which can differ by rounding and accrued interest.
- Only the reward part of the policy hooks is modelled. `borrowAllowed`'s membership, oracle,
  liquidity and cap checks and the pause guardians are not. An operation whose hook succeeds
  but whose balance change the cToken would refuse is refused as a whole.
- Arithmetic is unbounded, so the 224-bit index and 32-bit block checks never fail.
- Contributor rewards, `_grantComp`, claims for several holders at once, and Proposal 65's
  `fixBadAccruals` are not modelled.
- `emitted` counts blocks times speeds whether or not a side has holders. This makes the
  bound an upper bound: COMP for blocks in which a side has no units is never distributed.

## What refutes the port

- `witnesses/cSUSHI_claim.lean`, checked by the Lean kernel with `decide`. It uses the values
  of the cSUSHI claim read from mainnet: market indices 0, speed 0, one borrower with
  18977306140567618322762 units and no recorded index, and 300514463598935139440340 COMP-wei
  in the Comptroller. After the upgrade, 139 blocks pass and the account claims. Nothing was
  owed and nothing was emitted, and the port pays 18977306140567618322762.
  `port_refuted_rewards_bounded`, `port_refuted_account_bounded`,
  `port_refuted_borrow_hook` and `port_refuted_claim` hold.
- `witnesses/compound_regression.lean` runs the test Compound added after the incident
  (commit `4a0dcbcb5fab538ceee726ab8782df32de9e59f2`, "Zero COMP speed markets don't accrue
  rewards w/ uninitialized borrower/supplier state indices"), which expects every account to
  hold 0 COMP. The port pays Torrey 100e18 and Coburn 10e18. `tests/RegressionOnFix.lean`
  shows the same test passes on the reference.
- `harness/validate_task.py`: the judge rejects the port and its binary is REFUTED on the
  generated cases (REQ-ACCOUNT-BOUNDED, REQ-REWARDS-BOUNDED, REQ-CLAIM, REQ-SUPPLY-HOOK,
  REQ-BORROW-HOOK). The supplier-only fix is refuted on the borrow side. The Proposal 64 code is
  refuted on REQ-CLAIM only: its lock pays nothing to accounts with a recorded index in a
  market whose borrow speed is 0. REQ-NO-BACKDATED-REWARDS holds on all three.

The port passes the kind of unit tests Compound shipped. `tests/PortUnitTests.lean` restates
twelve tests of `tests/Flywheel/FlywheelTest.js` at the Proposal 62 commit: index updates,
distribution to first-time and repeat suppliers and borrowers, and claims. Two more tests
follow the Proposal 62 upgrade simulation on a fork of mainnet
(`spec/sim/0011-split-comp-rewards/hypothetical_mainnet_upgrade.scen`). The first is its mint
test: after the upgrade, an account mints into cMKR and its claim pays nothing. The second
takes the simulation's next steps (speeds of 1, blocks pass, a claim) with its own block
count. All fourteen pass on the port and on the reference. None of them has an account that
held a position before the upgrade, with no recorded index, in a market whose index the
upgrade initialized. The simulation's mint test uses
`0x05e793ce0c6027323ac150f6d45c2344d28b6019`, which held no cMKR and no cMKR borrow at the
simulation's fork block, 13057957 (read from mainnet), so it minted into cMKR only after the
upgrade. The repository's fuzz test of the reward flywheel,
`tests/Fuzz/CompWheelFuzzTest.js`, is marked `describe.skip` at that commit and starts every
run from freshly initialized indices.

## Real code

`eval/realworld_compound.py` (results in `results/compound-1/real-code/report.json`) fetches
compound-protocol at the three commits. It checks the SHA-256 of the 15 files each
Comptroller compiles from (`realworld/adapters/compound/sources.json`). These files are
byte-identical to the Sourcify-verified sources of the deployed implementations. The script
compiles them with solc 0.5.16, optimizer 200 runs, istanbul, and runs them in Foundry
(`realworld/adapters/compound`). Each sequence deploys a Unitroller, writes the pre-upgrade
state into its storage at the slots `forge inspect` reports, and installs the Proposal 62
implementation with `_setPendingImplementation` and `_become`, which runs
`_upgradeSplitCompRewards`. For Proposal 64 or 65 it then installs that implementation, as
those proposals did. The market is a mock cToken with a borrow index of 1e18, and COMP is a
mock token at the address the Comptroller has hard-coded. The borrow hook is called through
`repayBorrowAllowed`, whose reward code is the same as `borrowAllowed`'s.

| Check | Result |
|---|---|
| compiled Comptroller vs deployed runtime code, metadata hash excluded | identical for Proposal 62 (23,124 bytes), 64 (22,590) and 65 (23,339) |
| Proposal 62 build identical to the Lean port, every operation | 503 of 503 sequences |
| Proposal 64 build identical to the Lean port of Proposal 64 | 503 of 503 |
| Proposal 65 build identical to the proved component | 503 of 503 |
| sequences where the Proposal 62 build breaks a requirement | 279: REQ-ACCOUNT-BOUNDED 252, REQ-REWARDS-BOUNDED 229, REQ-CLAIM 182, REQ-SUPPLY-HOOK 99, REQ-BORROW-HOOK 74 |
| sequences where the Proposal 64 build breaks a requirement | 104, REQ-CLAIM only (its lock) |
| sequences where the Proposal 65 build breaks a requirement | 0 |
| real-code violations restated as `decide` goals over `Spec.lean`, checked in the kernel | 8 of 8 (`real-code/Confirm.lean`) |

The 503 sequences are the cSUSHI claim, Compound's regression scenario on the upgrade path,
the Sanity sequence, and 500 generated ones (seed 0). The generator (`oracle.py`) draws 30
percent of sequences in the incident's shape: a side whose index is 0, holders with no
recorded index, then a hook or a claim. The rest mix every kind of pre-upgrade index (0,
exactly 1e36, above 1e36, and grown from 0) with random operations by up to four accounts.

Fork replay. On a fork of mainnet at block 13322936 (RPC https://eth.drpc.org), the account of
the cSUSHI claim calls `claimComp(account, [cSUSHI])`. With the deployed Proposal 62
implementation, it is credited and paid 18977306140567618322762, the amount the Lean port gives
and the amount in the transaction's event. With the compiled Proposal 64 or Proposal 65 runtime
code placed at the implementation's address, it is credited 0, as the proved component gives.

## What was not proved

- The Solidity contracts are not proved. They were compiled from the pinned commits, run on the
  sequences above, and compared operation by operation with the port and with the proved
  component.
- That the port is faithful is tested, not proved, and only for the paths listed above.
- The specification states bounds and exact effects for one market. It does not cover several
  markets sharing `compAccrued`, the oracle and liquidity checks of the hooks, interest
  accrual, or the Proposal 65 corrections.
- `WellFormed` is an assumption about the pre-upgrade state, not checked against every
  account on chain. The market-level facts (indices 0 or at least 1e36, or grown from 0 below
  1e36; blocks not ahead) were read for all 18 markets at block 13322797.
- The JSON wrapper `app/Main.lean` is tested, not proved.

## Sources

- The Block, 2021-09-29: https://www.theblock.co/post/119086/compound-bug-comp-risk-misreward
- Compound newsletter, 2021-10-14: https://compound.substack.com/p/compound-treasury-updates-comp-bug
- Analysis of Proposal 64 by Geoffrey Hayes, Compound forum, 2021-10-04: https://www.comp.xyz/t/analysis-of-proposal-64/2384
- Pull request 165 and its commits: https://github.com/compound-finance/compound-protocol/pull/165
- Pull requests 161 and 166 (heads `f73b2937` and `c05d7e09`), and the sources of the three
  implementations on Sourcify (https://sourcify.dev, chain 1).
- Mainnet state and logs read through a public archive endpoint (https://eth.drpc.org).

## Reproduce

```sh
python3 harness/lock.py realworld/tasks/rw-compound-comp       # owner only, after review
python3 harness/validate_task.py realworld/tasks/rw-compound-comp
python3 eval/realworld_compound.py --cases 500 --out results/compound-1 --scan   # needs forge, cast, an archive RPC (PF_ETH_RPC)
```
