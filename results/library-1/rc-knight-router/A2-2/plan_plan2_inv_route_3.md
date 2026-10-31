Split the route proof by the router's guard. In the negative case the state and truth are unchanged. In the positive case, describe the advanced system explicitly: one zero-executed kid is appended, `sent` increases only for the routed parent, `cum` and `qty` are unchanged, and a child record is inserted at the old child count. Separate the appended-list lookup and child-synchronisation arguments, then assemble the seven components of `Inv`.

```lean
theorem plan3_route_exec_append : ∀ (l : List Kid) (pid c j : Nat),
    execFor (l ++ [⟨pid, c, 0⟩]) j = execFor l j := by sorry

theorem plan3_route_get_cases : ∀ (l : List Kid) (y : Kid) (k : Nat) (c : Kid),
    (l ++ [y])[k]? = some c → l[k]? = some c ∨ (k = l.length ∧ c = y) := by sorry

theorem plan3_route_yes_desc : ∀ (b : Build) (x : Sys) (id liq : Nat),
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    (advance step b x (.route id liq)).tr.kids =
        x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] ∧
    (advance step b x (.route id liq)).st.nChildren = x.st.nChildren + 1 ∧
    (advance step b x (.route id liq)).st.children =
        upd x.st.children x.st.nChildren
          ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ ∧
    (advance step b x (.route id liq)).tr.nOrders = x.tr.nOrders ∧
    (advance step b x (.route id liq)).st.nParents = x.st.nParents ∧
    (∀ j, ((advance step b x (.route id liq)).st.parents j).qty = (x.st.parents j).qty) ∧
    (∀ j, ((advance step b x (.route id liq)).st.parents j).cum = (x.st.parents j).cum) ∧
    (∀ j, ((advance step b x (.route id liq)).st.parents j).sent =
        if j = id then
          (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent)
        else (x.st.parents j).sent) := by sorry

theorem plan3_route_yes_children_sync : ∀ (b : Build) (x : Sys) (id liq k : Nat) (c : Kid),
    Inv x →
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    (advance step b x (.route id liq)).tr.kids[k]? = some c →
    ((advance step b x (.route id liq)).st.children k).parent = c.parent ∧
    ((advance step b x (.route id liq)).st.children k).qty = c.qty ∧
    ((advance step b x (.route id liq)).st.children k).done = c.done := by sorry

theorem plan3_route_no_inv : ∀ (b : Build) (x : Sys) (id liq : Nat),
    Inv x →
    ¬ (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    Inv (advance step b x (.route id liq)) := by sorry

theorem plan3_route_yes_inv : ∀ (b : Build) (x : Sys) (id liq : Nat),
    Inv x →
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    Inv (advance step b x (.route id liq)) := by sorry
```