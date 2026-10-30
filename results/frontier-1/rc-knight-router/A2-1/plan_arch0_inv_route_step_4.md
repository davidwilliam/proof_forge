Split the route case by the `routeBySent` guard. The no-op branch is already handled by `route_nop_inv2`; for the sending branch, first establish that routing does not change the truth's order count, quantities, or executions, then prove the count, parent-record, and child-record components of `arch0_Inv` separately using the existing `plan1_route_yes_*` lemmas. Assembling those components gives preservation in the sending branch, and case analysis on the guard gives the full route step.

```lean
theorem plan4_route_tr_frame (b : Build) (x : Sys) (rid liq : Nat) :
    (advance step b x (.route rid liq)).tr.nOrders = x.tr.nOrders ∧
    (∀ j : Nat, (advance step b x (.route rid liq)).tr.qty j = x.tr.qty j) ∧
    (∀ j : Nat, (advance step b x (.route rid liq)).tr.exec j = x.tr.exec j) := by sorry

theorem plan4_route_yes_counts (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nParents =
      (advance step b x (.route rid liq)).tr.nOrders ∧
    (advance step b x (.route rid liq)).st.nChildren =
      (advance step b x (.route rid liq)).tr.kids.length := by sorry

theorem plan4_route_yes_parent_records (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent))
    (j : Nat) (hj : j < (advance step b x (.route rid liq)).tr.nOrders) :
    ((advance step b x (.route rid liq)).st.parents j).qty =
        (advance step b x (.route rid liq)).tr.qty j ∧
    ((advance step b x (.route rid liq)).st.parents j).sent =
        (advance step b x (.route rid liq)).tr.sent j ∧
    ((advance step b x (.route rid liq)).st.parents j).cum =
        (advance step b x (.route rid liq)).tr.exec j := by sorry

theorem plan4_route_yes_child_records (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent))
    (k : Nat) (hk : k < (advance step b x (.route rid liq)).tr.kids.length) :
    ∃ kid, (advance step b x (.route rid liq)).tr.kids[k]? = some kid ∧
      (advance step b x (.route rid liq)).st.children k =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.route rid liq)).tr.nOrders := by sorry

theorem plan4_route_yes_inv (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    arch0_Inv (advance step b x (.route rid liq)) := by sorry

theorem plan4_inv_route_step (b : Build) (x : Sys) (id liq : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.route id liq)) := by sorry
```