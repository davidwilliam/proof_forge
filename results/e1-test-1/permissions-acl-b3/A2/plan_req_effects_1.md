**Proof plan.** From `(step s r).1 ≠ .rejected`, the existing `eff_guard_true` gives the validity guard is `true`. With that guard, `step` unfolds to the granted/denied branch, whose state only updates `log` and whose first component is `granted` exactly when `decision s.entries r` is true. Hence `decide ((step s r).1 = .granted) = decision s.entries r`, and rewriting the state projections and this decision equality gives precisely the three conjuncts of `Effects`.

```lean
theorem plan1_effects_step_eq_of_guard (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    step s r = (if decision s.entries r then .granted else .denied,
      { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by sorry

theorem plan1_effects_decide_eq_of_guard (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    decide ((step s r).1 = .granted) = decision s.entries r := by sorry

theorem plan1_effects_state_parts_of_guard (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    (step s r).2.users = s.users ∧
    (step s r).2.entries = s.entries ∧
    (step s r).2.log = s.log ++ [⟨r.user, r.path, decision s.entries r⟩] := by sorry

theorem plan1_effects_holds (s : State) (r : Request)
    (hne : (step s r).1 ≠ .rejected) :
    (step s r).2.users = s.users ∧
    (step s r).2.entries = s.entries ∧
    (step s r).2.log = s.log ++ [⟨r.user, r.path, decide ((step s r).1 = .granted)⟩] := by sorry
```