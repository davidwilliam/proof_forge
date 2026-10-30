import Solution
/-!
Unit tests of the kind Compound shipped with Proposal 62, run against the port
(`candidate/Solution.lean`). Each test is checked by the Lean kernel (`decide`).

Tests 1 to 12 restate tests in compound-finance/compound-protocol at commit
f73b29373eb65cedf24896d7be46eed38435fc91, `tests/Flywheel/FlywheelTest.js`
(`updateCompBorrowIndex()`, `updateCompSupplyIndex()`, `distributeBorrowerComp()`,
`distributeSupplierComp()`, `claimComp`, `transferComp`), with the same numbers. Compound's
harness sets indices, balances and block numbers directly; here a state with those values is
used. The cToken's borrow index is 1e18, so a borrow balance equals its borrow units; where a
test uses a borrow index of 1.1e18 the units are the balance divided by 1.1, as in its comments.

Tests 13 and 14 follow the Proposal 62 upgrade simulation on a fork of mainnet,
`spec/sim/0011-split-comp-rewards/hypothetical_mainnet_upgrade.scen` at the same commit. Test 13
is its mint test: after the upgrade, an account mints 1000e18 into cMKR, a market whose indices
were 0, and its claim pays nothing. Test 14 takes the simulation's next steps (governance sets
COMP speeds of 1, blocks pass, the account claims) with its own block count, so its amount is
not the simulation's.

All fourteen pass on the port. None of them has an account that held a position before the
upgrade, with no recorded index, in a market whose index the upgrade initialized: the state of
the cSUSHI claim (`witnesses/cSUSHI_claim.lean`).
-/
open CompRewards

def e18 : Nat := 10 ^ 18
def e36 : Nat := 10 ^ 36

def side (index block speed : Nat) : Side := ⟨index, block, speed⟩
def holder (supply borrow si bi : Nat) : Acct := ⟨supply, borrow, si, bi, 0, 0⟩

def market (now : Nat) (sup bor : Side) (reserve : Nat) (accts : List Acct) : St :=
  { blockNumber := now, supplyState := sup, borrowState := bor, reserve := reserve, accts := accts }

/-- 1. updateCompBorrowIndex: 100 blocks, 10e18 borrow units, speed 0.5e18: index 1e36 to 6e36. -/
example :
    (updateCompBorrowIndex (market 100 (side e36 0 0) (side e36 0 (e18 / 2)) 0
      [holder 0 (10 * e18) 0 0])).map (·.borrowState) = some (side (6 * e36) 100 (e18 / 2)) := by
  decide

/-- 2. updateCompBorrowIndex: no blocks passed since the last accrual, index unchanged. -/
example :
    (updateCompBorrowIndex (market 0 (side e36 0 0) (side e36 0 (e18 / 2)) 0
      [holder 0 (10 * e18) 0 0])).map (·.borrowState) = some (side e36 0 (e18 / 2)) := by
  decide

/-- 3. updateCompBorrowIndex: speed 0, index unchanged, block brought up to date. -/
example :
    (updateCompBorrowIndex (market 100 (side e36 0 0) (side e36 0 0) 0
      [holder 0 (10 * e18) 0 0])).map (·.borrowState) = some (side e36 100 0) := by
  decide

/-- 4. updateCompSupplyIndex: 100 blocks, 10e18 cTokens, speed 0.5e18: index 6e36. -/
example :
    (updateCompSupplyIndex (market 100 (side e36 0 (e18 / 2)) (side e36 0 0) 0
      [holder (10 * e18) 0 0 0])).map (·.supplyState) = some (side (6 * e36) 100 (e18 / 2)) := by
  decide

/-- 5. updateCompSupplyIndex: no blocks passed, index unchanged. -/
example :
    (updateCompSupplyIndex (market 0 (side e36 0 (e18 / 2)) (side e36 0 0) 0
      [holder (10 * e18) 0 0 0])).map (·.supplyState) = some (side e36 0 (e18 / 2)) := by
  decide

/-- 6. distributeBorrowerComp, first-time user (no borrow, no recorded index): nothing accrued,
index checkpoint set to the market's 6e36. -/
example :
    (distributeBorrowerComp (market 10 (side e36 10 0) (side (6 * e36) 10 0) 0 [holder 0 0 0 0]) 0).map
      (fun s => ((s.acct 0).accrued, (s.acct 0).borrowerIndex)) = some (0, 6 * e36) := by
  decide

/-- 7. distributeBorrowerComp, repeat user: 5e18 units (5.5e18 at index 1.1), index 6e36,
recorded 1e36: 25e18 accrued. -/
example :
    (distributeBorrowerComp (market 10 (side e36 10 0) (side (6 * e36) 10 0) 0
      [holder 0 (5 * e18) 0 e36]) 0).map (fun s => (s.acct 0).accrued) = some (25 * e18) := by
  decide

/-- 8. distributeBorrowerComp: 5e17 units, index 1.0019e36: 0.00095e18 accrued. -/
example :
    (distributeBorrowerComp (market 10 (side e36 10 0) (side (10019 * 10 ^ 32) 10 0) 0
      [holder 0 (5 * 10 ^ 17) 0 e36]) 0).map (fun s => (s.acct 0).accrued) = some (95 * 10 ^ 13) := by
  decide

/-- 9. distributeSupplierComp, first-time user: 5e18 cTokens, index 6e36, no recorded index:
25e18 accrued (from compInitialIndex). -/
example :
    (distributeSupplierComp (market 10 (side (6 * e36) 10 0) (side e36 10 0) 0
      [holder (5 * e18) 0 0 0]) 0).map (fun s => (s.acct 0).accrued) = some (25 * e18) := by
  decide

/-- 10. distributeSupplierComp, repeat user: recorded index 2e36: 20e18 accrued. -/
example :
    (distributeSupplierComp (market 10 (side (6 * e36) 10 0) (side e36 10 0) 0
      [holder (5 * e18) 0 (2 * e36) 0]) 0).map (fun s => (s.acct 0).accrued) = some (20 * e18) := by
  decide

/-- 11. claimComp with accrued below the old claim threshold: the whole amount is paid. -/
example :
    (claimComp (market 10 (side e36 10 0) (side e36 10 0) e18
      [{ holder 0 0 0 0 with accrued := 9 * 10 ^ 14 }]) 0).map
      (fun s => ((s.acct 0).accrued, (s.acct 0).wallet)) = some (0, 9 * 10 ^ 14) := by
  decide

/-- 12. transferComp: accrued above what the Comptroller holds, nothing is paid. -/
example :
    (claimComp (market 10 (side e36 10 0) (side e36 10 0) e18
      [{ holder 0 0 0 0 with accrued := 2 * e18 }]) 0).map
      (fun s => ((s.acct 0).accrued, (s.acct 0).wallet, s.reserve)) = some (2 * e18, 0, e18) := by
  decide

/-- cMKR before the upgrade, as the simulation reads it: both indices 0, speed 0. The minting
account has no position there. -/
def cMKR : Legacy :=
  { blockNumber := 13057957, compSpeed := 0, supplyIndex := 0, supplyBlock := 13057957,
    borrowIndex := 0, borrowBlock := 13057957, supplyStart := 0, borrowStart := 0,
    reserve := 10 ^ 24, accts := [holder 0 0 0 0] }

/-- 13. After the upgrade both cMKR indices are 1e36; the account mints and claims nothing. -/
example :
    let s := run comptroller (upgrade cMKR) [.mint 0 (1000 * e18), .claim 0]
    s.supplyState.index = e36 ∧ s.borrowState.index = e36 ∧ (s.acct 0).wallet = 0 := by
  decide

/-- 14. Speeds of 1 COMP-wei per block on each side, 10 blocks: the only supplier is paid 10. -/
example :
    let s := run comptroller (upgrade cMKR)
      [.mint 0 (1000 * e18), .claim 0, .setSpeeds 1 1, .advance 10, .claim 0]
    (s.acct 0).wallet = 10 := by
  decide
