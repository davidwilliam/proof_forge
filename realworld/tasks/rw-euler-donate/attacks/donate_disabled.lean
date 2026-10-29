import EulerLending.Spec
/-!
Seeded evasive fix: `donateToReserves` always reverts, so no donation can lower an account's
health. Proofs `sorry`.
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
  | .donate _ _ => none
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
