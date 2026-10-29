Split on whether routing is active. If inactive, state and truth are unchanged; if active, exactly one child is appended, only the target parent's `sent` increases by the capped amount, and all order data stays fixed, giving `sent ≤ qty` by `omega`.

```lean
theorem plan1_advance_route (b : Build) (x : Sys) (id liq : Nat) :
    advance step b x (.route id liq) =
      ⟨(routeBySent x.st id liq).1, x.tr.record (routeBySent x.st id liq).2⟩ := by sorry

theorem plan1_route_inactive (s : State) (id liq : Nat)
    (h : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    routeBySent s id liq = (s, []) := by sorry

theorem plan1_route_active (s : State) (id liq : Nat)
    (h : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) :
    (routeBySent s id liq).2 = [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] ∧
    (routeBySent s id liq).1.nParents = s.nParents ∧
    ∀ j, ((routeBySent s id liq).1.parents j).qty = (s.parents j).qty ∧
      ((routeBySent s id liq).1.parents j).sent =
        if j = id then (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent)
        else (s.parents j).sent := by sorry

theorem plan1_record_nil (t : Truth) : t.record [] = t := by sorry

theorem plan1_record_single_sent (t : Truth) (id c j : Nat) :
    (t.record [⟨id, c⟩]).sent j = t.sent j + (if id = j then c else 0) := by sorry

theorem plan1_record_single_truth (t : Truth) (id c : Nat) (hid : id < t.nOrders)
    (hk : ∀ k ∈ t.kids, k.parent < t.nOrders) :
    (t.record [⟨id, c⟩]).nOrders = t.nOrders ∧
    (∀ j, (t.record [⟨id, c⟩]).qty j = t.qty j) ∧
    ∀ k ∈ (t.record [⟨id, c⟩]).kids, k.parent < (t.record [⟨id, c⟩]).nOrders := by sorry
```