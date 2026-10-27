(1) Proof plan: SingleLeg follows from two facts about a successful step: the final balances are `applyLegs s.balance r.legs`, and the singleton leg was admissible, hence its source differs from its target. For one leg, `applyLegs` reduces to a single `shift`; evaluating `shift` at the source (using source ≠ target) gives the debit, and evaluating it at the target gives the credit. The helpers below isolate the singleton `applyLegs` computation, the two `shift` evaluations, extraction of `LegsOk` from success, the balance effect of success, and the source/target inequality for the singleton case.

(2)
```lean
theorem plan0_applyLegs_singleton (bal : AccountId → Int) (l : Leg) :
    applyLegs bal [l] = shift bal l := by sorry

theorem plan0_shift_source (bal : AccountId → Int) (l : Leg)
    (hne : l.source ≠ l.target) :
    shift bal l l.source = bal l.source - (l.amount : Int) := by sorry

theorem plan0_shift_target (bal : AccountId → Int) (l : Leg)
    (hne : l.source ≠ l.target) :
    shift bal l l.target = bal l.target + (l.amount : Int) := by sorry

theorem plan0_legsOk_of_step_ok (s : State) (r : Request)
    (hok : (step s r).1 = Outcome.ok) :
    LegsOk s s.balance r.legs := by sorry

theorem plan0_balance_of_step_ok (s : State) (r : Request) (a : AccountId)
    (hok : (step s r).1 = Outcome.ok) :
    (step s r).2.balance a = applyLegs s.balance r.legs a := by sorry

theorem plan0_source_ne_target_of_singleton_ok (s : State) (r : Request) (l : Leg)
    (hlegs : r.legs = [l]) (hok : (step s r).1 = Outcome.ok) :
    l.source ≠ l.target := by sorry
```