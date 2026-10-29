**Proof plan.** Split the route step on its issuing condition. In the negative case the whole system is unchanged. In the positive case, separately establish the equations for the advanced state and truth, preservation of the child-record correspondence for both old children and the newly appended child, preservation of the parent-count/child-count bounds, and preservation of cumulative execution; the target theorem then assembles these five components.

```lean
theorem plan6_route_neg_advance_eq (b : Build) (x : Sys) (rid liq : Nat)
    (hcond : ¬ (rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent))) :
    advance step b x (.route rid liq) = x := by sorry

theorem plan6_route_pos_advance_eq (b : Build) (x : Sys) (rid liq : Nat)
    (hcond : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st =
        (step b x.st (.route rid liq)).1 ∧
      (advance step b x (.route rid liq)).tr =
        x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩] := by sorry

theorem plan6_route_pos_children (b : Build) (x : Sys) (rid liq : Nat)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ k, k < x.tr.kids.length →
      ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩)
    (hcond : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    ∀ k, k < x.tr.kids.length + 1 →
      ∃ c, ((x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids)[k]? = some c ∧
        (step b x.st (.route rid liq)).1.children k = ⟨c.parent, c.qty, c.done⟩ := by sorry

theorem plan6_route_pos_lengths_bounds (b : Build) (x : Sys) (rid liq : Nat)
    (hnP : x.st.nParents = x.tr.nOrders)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hkb : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)
    (hcond : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nParents =
        (advance step b x (.route rid liq)).tr.nOrders ∧
      (advance step b x (.route rid liq)).st.nChildren =
        (advance step b x (.route rid liq)).tr.kids.length ∧
      ∀ k ∈ (advance step b x (.route rid liq)).tr.kids,
        k.parent < (advance step b x (.route rid liq)).tr.nOrders := by sorry

theorem plan6_route_pos_cum (b : Build) (x : Sys) (rid liq : Nat)
    (hcum : ∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id)
    (hcond : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    ∀ id, id < (advance step b x (.route rid liq)).tr.nOrders →
      ((advance step b x (.route rid liq)).st.parents id).cum =
        (advance step b x (.route rid liq)).tr.exec id := by sorry
```