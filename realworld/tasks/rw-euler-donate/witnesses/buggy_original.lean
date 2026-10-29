import Solution
/-!
Kernel-checked refutation of the Euler v1 port (`attacks/buggy_original.lean`) by the shape of
the March 2023 attack, in whole DAI with the exchange rate at 1:

1. an honest lender (account 0) deposits 8,904,507;
2. the violator (account 1) deposits 20,000,000 (flash-loaned in the attack);
3. it mints 200,000,000 eTokens and dTokens (leverage within the 95% limit);
4. it repays 10,000,000 of the debt;
5. it mints 200,000,000 again (still within the limit: 390,000,000 owed against 420,000,000);
6. it donates 100,000,000 eTokens to the reserves: 390,000,000 owed against 320,000,000;
7. the liquidator (account 2, the attacker's second account) takes over the largest debt
   allowed, 256,000,000, at the maximum 20% discount, and receives all 320,000,000 of the
   violator's collateral; the violator keeps 134,000,000 of debt and no collateral;
8. the liquidator withdraws the whole pool, 38,904,507: 30,000,000 put in by the attacker and
   the lender's 8,904,507.
-/
open EulerLending

def attack : List Op :=
  [.deposit 0 8904507, .deposit 1 20000000, .mint 1 200000000, .repay 1 10000000,
   .mint 1 200000000, .donate 1 100000000, .liquidate 2 1 256000000, .withdraw 2 38904507]

/-- Every operation of the attack succeeds on the port. -/
theorem attack_succeeds : (runAll step genesis attack).isSome = true := by decide

/-- Before the donation the violator is healthy: 390,000,000 owed against 420,000,000. -/
theorem before_donation :
    (runAll step genesis (attack.take 5)).map (fun s => (s.acct 1, decide (Healthy (s.acct 1))))
      = some (⟨420000000, 390000000⟩, true) := by decide

/-- After the donation it holds more debt than collateral. -/
theorem after_donation :
    (runAll step genesis (attack.take 6)).map (fun s => (s.acct 1, decide (Healthy (s.acct 1))))
      = some (⟨320000000, 390000000⟩, false) := by decide

/-- The liquidation terms of the insolvent position: the discount is the 20% maximum and the
largest debt a liquidator may take over is 256,000,000. -/
theorem liquidation_terms :
    (runAll step genesis (attack.take 6)).map
      (fun s => (healthScore (s.acct 1) * 10000 / ONE, decide (discount (s.acct 1) = ONE / 5),
                 maxRepay (s.acct 1), liqYield (s.acct 1) 256000000))
      = some (7794, true, 256000000, 320000000) := by decide

/-- Final state: the violator has no collateral and 134,000,000 of debt, the liquidator holds
281,095,493 of collateral against 261,120,000 of debt (256,000,000 plus the 2% fee), and the
pool is empty. -/
theorem final_state :
    (runAll step genesis attack).map (fun s => (s.acct 0, s.acct 1, s.acct 2, s.cash, s.reserves))
      = some (⟨8904507, 0⟩, ⟨0, 134000000⟩, ⟨281095493, 261120000⟩, 0, 105120000) := by decide

theorem reachable_of_run :
    ∀ (ops : List Op) (s s' : St), Reachable step s → runAll step s ops = some s' →
      Reachable step s'
  | [], s, s', h, hr => by
    simp only [runAll, Option.some.injEq] at hr
    exact hr ▸ h
  | op :: ops, s, s', h, hr => by
    simp only [runAll] at hr
    split at hr
    · rename_i s1 h1
      exact reachable_of_run ops s1 s' (Reachable.step op h h1) hr
    · cases hr

/-- REQ-NO-BAD-DEBT fails: the state after the donation is reachable and account 1 is
unhealthy in it. -/
theorem port_refutes_no_bad_debt : ¬ NoBadDebt step := by
  intro h
  have hr := after_donation
  revert hr
  cases e : runAll step genesis (attack.take 6) with
  | none => intro hr; cases hr
  | some s =>
    intro hr
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
    have := h s (reachable_of_run _ _ _ Reachable.genesis e) 1
    simp [this] at hr

/-- The violator's position just before the donation (step 5 above). -/
def preDonation : St := ⟨fun _ => ⟨420000000, 390000000⟩, 38904507, 0⟩

/-- REQ-STAYS-HEALTHY and REQ-ACTOR-HEALTHY fail at the donation step: a healthy position
donates 100,000,000 eTokens and the donation succeeds, leaving it unhealthy. -/
theorem port_refutes_stays_healthy : ¬ StaysHealthy step ∧ ¬ ActorHealthy step := by
  have hd : (step preDonation (.donate 1 100000000)).map (fun s' => decide (Healthy (s'.acct 1)))
      = some false := by decide
  revert hd
  cases e : step preDonation (.donate 1 100000000) with
  | none => intro hd; cases hd
  | some s' =>
    intro hd
    simp only [Option.map_some, Option.some.injEq, decide_eq_false_iff_not] at hd
    exact ⟨fun h => hd (h preDonation _ s' 1 e (by decide)), fun h => hd (h preDonation _ s' 1 e rfl)⟩
