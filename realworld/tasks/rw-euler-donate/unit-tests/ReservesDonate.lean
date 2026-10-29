import Solution
/-!
Euler's own unit tests for `donateToReserves`, ported to the model: `test/reservesDonate.js` at
commit b1ee3265853628d5a529081d7908c38404201b4e. Each `example` is checked in the Lean kernel
against whichever `Solution` it is built with; the port of the vulnerable code passes all of
them, and so does the reference.

The suite has four tests. Three are ported; "non-18 decimal places token" tests decimal scaling,
which the model does not have. Euler's `DefaultReserve` (the reserves a market starts with) is 0
here, and `et.eth(n)` is `n * 10^18`. Every test donates
from an account with no debt.
-/
open EulerLending

def eth (n : Nat) : Nat := n * 1000000000000000000

/-- "donate to reserves - basic": deposit 10, donate 1. The account keeps 9, the reserves hold
1, the pool still holds 10, and eTokens plus reserves (Euler's `totalSupply`) stay at 10. -/
example :
    (runAll step genesis [.deposit 0 (eth 10), .donate 0 (eth 1)]).map
      (fun s => (s.acct 0, s.reserves, s.cash, (s.acct 0).e + s.reserves))
      = some (⟨eth 9, 0⟩, eth 1, eth 10, eth 10) := by decide

/-- "donate to reserves - max uint": deposit 10, donate the whole balance. -/
example :
    (runAll step genesis [.deposit 0 (eth 10), .donate 0 (eth 10)]).map
      (fun s => (s.acct 0, s.reserves, s.cash))
      = some (⟨0, 0⟩, eth 10, eth 10) := by decide

/-- "donate to reserves - insufficient balance": deposit 10, donating 11 reverts. -/
example : (runAll step genesis [.deposit 0 (eth 10), .donate 0 (eth 11)]).isNone = true := by
  decide
