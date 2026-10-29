import Solution
/-!
The regression test Compound added after the incident, run against the port. In
compound-finance/compound-protocol, commit 4a0dcbcb5fab538ceee726ab8782df32de9e59f2
(2021-09-30, "Add failing test case for the proposal 62 bug") adds to
`spec/scenario/Flywheel/Flywheel.scen` the test "Zero COMP speed markets don't accrue rewards
w/ uninitialized borrower/supplier state indices". In a new market cYFI with no rewards,
Torrey supplies 100e18 and Coburn borrows 10e18 with no recorded index, Jared and Geoff do the
same after the market is set up, 1000 blocks pass, everyone claims, and the test asserts that
all four hold 0 COMP. Commit ddde3ec0e749611474ca622081beb72deb2779af ("Fix the bug introduced
in proposal 62") makes it pass by changing `>` to `>=`.

Here cYFI's indices are 1e36 (set when the market is listed), its speeds are 0, Torrey and
Coburn have no recorded index, and Jared and Geoff are recorded at 1e36. The port pays Torrey
100e18 and Coburn 10e18 (100 and 10 COMP); the test expects 0 for both. The cToken amounts are
taken as units, which is what `distributeSupplierComp` multiplies.
-/
open CompRewards

def e18 : Nat := 10 ^ 18
def e36 : Nat := 10 ^ 36

/-- Accounts: 0 Torrey, 1 Jared, 2 Coburn, 3 Geoff. -/
def cYFI : St :=
  { blockNumber := 1000, supplyState := ⟨e36, 0, 0⟩, borrowState := ⟨e36, 0, 0⟩, reserve := 10 ^ 24,
    accts := [⟨100 * e18, 0, 0, 0, 0, 0⟩, ⟨100 * e18, 0, e36, 0, 0, 0⟩,
              ⟨0, 10 * e18, 0, 0, 0, 0⟩, ⟨0, 10 * e18, 0, e36, 0, 0⟩] }

def claims : List Op := [.claim 1, .claim 0, .claim 3, .claim 2]

/-- The test's assertions fail on the port: Torrey and Coburn are paid. -/
theorem regression_fails_on_port :
    let s := run comptroller cYFI claims
    (s.acct 0).wallet = 100 * e18 ∧ (s.acct 2).wallet = 10 * e18 ∧
      (s.acct 1).wallet = 0 ∧ (s.acct 3).wallet = 0 := by
  decide
