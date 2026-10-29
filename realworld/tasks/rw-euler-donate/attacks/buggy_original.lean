import EulerLending.Spec
/-!
Port of the market logic of Euler Finance v1 (euler-xyz/euler-contracts, commit
b1ee3265853628d5a529081d7908c38404201b4e), single asset, exchange rate 1, no interest.

* `deposit`: `EToken.deposit` (lines 139 to 175); checks liquidity when the account has debt.
* `withdraw`: `EToken.withdraw` (lines 180 to 200); `e/insufficient-pool-size`, then
  `checkLiquidity(account)`.
* `borrow`, `repay`: `DToken.borrow` (lines 98 to 121) and `DToken.repay` (lines 126 to 148);
  repay pays at most the amount owed.
* `mint`, `burn`: `EToken.mint` (lines 206 to 229) and `EToken.burn` (lines 234 to 264).
* `transfer`: `EToken.transferFrom` (lines 323 to 354); checks the sender, and the receiver
  when it has debt.
* `donate`: `EToken.donateToReserves` (lines 359 to 386): `e/insufficient-balance`, then the
  balance moves to the reserves.
* `liquidate`: `Liquidation.liquidate`, `computeLiqOpp` and `executeLiquidation` (lines 55 to
  283), same asset as debt and collateral.
-/
namespace EulerLending

/-- Replace the position of account `u`. -/
def setAcct (s : St) (u : Nat) (a : Acct) : St :=
  { s with acct := fun w => if w = u then a else s.acct w }

def step : Impl := fun s op =>
  match op with
  | .deposit u x =>
    let a : Acct := ⟨(s.acct u).e + x, (s.acct u).d⟩
    if (s.acct u).d = 0 ∨ Healthy a then some { setAcct s u a with cash := s.cash + x } else none
  | .withdraw u x =>
    let a : Acct := ⟨(s.acct u).e - x, (s.acct u).d⟩
    if x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy a then
      some { setAcct s u a with cash := s.cash - x } else none
  | .borrow u x =>
    let a : Acct := ⟨(s.acct u).e, (s.acct u).d + x⟩
    if x ≤ s.cash ∧ Healthy a then some { setAcct s u a with cash := s.cash - x } else none
  | .repay u x =>
    let y := min x (s.acct u).d
    some { setAcct s u ⟨(s.acct u).e, (s.acct u).d - y⟩ with cash := s.cash + y }
  | .mint u x =>
    let a : Acct := ⟨(s.acct u).e + x, (s.acct u).d + x⟩
    if Healthy a then some (setAcct s u a) else none
  | .burn u x =>
    let y := min x (s.acct u).d
    let a : Acct := ⟨(s.acct u).e - y, (s.acct u).d - y⟩
    if y ≤ (s.acct u).e ∧ Healthy a then some (setAcct s u a) else none
  | .transfer u v x =>
    let a : Acct := ⟨(s.acct u).e - x, (s.acct u).d⟩
    let b : Acct := ⟨(s.acct v).e + x, (s.acct v).d⟩
    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ ((s.acct v).d = 0 ∨ Healthy b) then
      some (setAcct (setAcct s u a) v b) else none
  | .donate u x =>
    if x ≤ (s.acct u).e then
      some { setAcct s u ⟨(s.acct u).e - x, (s.acct u).d⟩ with reserves := s.reserves + x }
    else none
  | .liquidate l v r =>
    let y := liqYield (s.acct v) r
    let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
      some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
        reserves := s.reserves + liqFee r } else none

theorem req_honest_flow      : HonestFlow step := sorry
theorem req_allowed_succeeds : AllowedSucceeds step := sorry
theorem req_effects          : Effects step := sorry
theorem req_actor_healthy    : ActorHealthy step := sorry
theorem req_stays_healthy    : StaysHealthy step := sorry
theorem req_no_bad_debt      : NoBadDebt step := sorry

end EulerLending
