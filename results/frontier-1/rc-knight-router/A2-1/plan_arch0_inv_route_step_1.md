Split the route step into the already-banked no-op case and the successful case. For the successful case, compute separately how the truth-side sent/exec/quantity change, how the state-side parent and child records change, how old and new child entries are indexed, and why the sent bound is preserved using `c ≤ qty - sent`; these components then assemble directly into `arch0_Inv`.

```lean
theorem plan1_route_yes_sent (b : Build) (x : Sys) (rid liq j : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).tr.sent j =
      x.tr.sent j +
        (if rid = j then
          min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)
        else 0) := by sorry

theorem plan1_route_yes_exec_qty_orders (b : Build) (x : Sys) (rid liq j : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).tr.exec j = x.tr.exec j ∧
    (advance step b x (.route rid liq)).tr.qty j = x.tr.qty j ∧
    (advance step b x (.route rid liq)).tr.nOrders = x.tr.nOrders := by sorry

theorem plan1_route_yes_parents (b : Build) (x : Sys) (rid liq : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nParents = x.st.nParents ∧
    ∀ j : Nat,
      (advance step b x (.route rid liq)).st.parents j =
        if j = rid then
          { x.st.parents rid with
            sent := (x.st.parents rid).sent +
              min liq ((x.st.parents rid).qty - (x.st.parents rid).sent) }
        else x.st.parents j := by sorry

theorem plan1_route_yes_children (b : Build) (x : Sys) (rid liq : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nChildren = x.st.nChildren + 1 ∧
    (advance step b x (.route rid liq)).st.children x.st.nChildren =
      ⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ ∧
    ∀ k : Nat, k ≠ x.st.nChildren →
      (advance step b x (.route rid liq)).st.children k = x.st.children k := by sorry

theorem plan1_route_yes_kids_get (b : Build) (x : Sys) (rid liq : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (∀ k : Nat, k < x.tr.kids.length →
      (advance step b x (.route rid liq)).tr.kids[k]? = x.tr.kids[k]?) ∧
    (advance step b x (.route rid liq)).tr.kids[x.tr.kids.length]? =
      some (⟨rid,
        min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid) ∧
    (advance step b x (.route rid liq)).tr.kids.length =
      x.tr.kids.length + 1 := by sorry

theorem plan1_route_yes_sent_le_of_inv (b : Build) (x : Sys) (rid liq j : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).tr.sent j ≤
      (advance step b x (.route rid liq)).tr.qty j := by sorry
```