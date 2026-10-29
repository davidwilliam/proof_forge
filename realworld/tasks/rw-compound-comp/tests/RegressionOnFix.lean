import Solution
/-!
Compound's post-incident regression test (`witnesses/compound_regression.lean`), stated as it
expects: run against a candidate that meets the requirements (the reference, or an accepted
repair), all four accounts hold 0 COMP after their claims.
-/
open CompRewards

def e18 : Nat := 10 ^ 18
def e36 : Nat := 10 ^ 36

def cYFI : St :=
  { blockNumber := 1000, supplyState := ⟨e36, 0, 0⟩, borrowState := ⟨e36, 0, 0⟩, reserve := 10 ^ 24,
    accts := [⟨100 * e18, 0, 0, 0, 0, 0⟩, ⟨100 * e18, 0, e36, 0, 0, 0⟩,
              ⟨0, 10 * e18, 0, 0, 0, 0⟩, ⟨0, 10 * e18, 0, e36, 0, 0⟩] }

def claims : List Op := [.claim 1, .claim 0, .claim 3, .claim 2]

theorem regression_passes :
    let s := run comptroller cYFI claims
    (s.acct 0).wallet = 0 ∧ (s.acct 1).wallet = 0 ∧ (s.acct 2).wallet = 0 ∧ (s.acct 3).wallet = 0 := by
  decide
