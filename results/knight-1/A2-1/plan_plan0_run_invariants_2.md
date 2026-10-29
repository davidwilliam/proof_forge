Short plan: define the run invariant as the conjunction that `nParents` matches `nOrders`, every existing parent's stored `qty`/`sent` match the truth quantities, and every recorded kid belongs to an existing parent. Prove preservation separately for `parent`, `route`, `ack`, and `fill` events; each case unfolds `step`/`advance`, uses `upd` on the touched index, `sentFor_set_done`/`sentFor_append` for the truth, and `omega` for index bounds; then combine the four cases by `cases e` and close `plan0_run_invariants` by `run_induction` from the trivial start invariant.

```lean
theorem plan2_parent_preserves (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.parent q f)).st.nParents =
        (advance step b x (.parent q f)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.parent q f)).tr.nOrders →
        ((advance step b x (.parent q f)).st.parents id).qty =
          (advance step b x (.parent q f)).tr.qty id ∧
        ((advance step b x (.parent q f)).st.parents id).sent =
          (advance step b x (.parent q f)).tr.sent id) ∧
      ∀ k ∈ (advance step b x (.parent q f)).tr.kids,
        k.parent < (advance step b x (.parent q f)).tr.nOrders := by sorry

theorem plan2_route_preserves (b : Build) (x : Sys) (id liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ j, j < x.tr.nOrders →
        (x.st.parents j).qty = x.tr.qty j ∧
        (x.st.parents j).sent = x.tr.sent j) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.route id liq)).st.nParents =
        (advance step b x (.route id liq)).tr.nOrders ∧
      (∀ j, j < (advance step b x (.route id liq)).tr.nOrders →
        ((advance step b x (.route id liq)).st.parents j).qty =
          (advance step b x (.route id liq)).tr.qty j ∧
        ((advance step b x (.route id liq)).st.parents j).sent =
          (advance step b x (.route id liq)).tr.sent j) ∧
      ∀ k ∈ (advance step b x (.route id liq)).tr.kids,
        k.parent < (advance step b x (.route id liq)).tr.nOrders := by sorry

theorem plan2_ack_preserves (b : Build) (x : Sys) (k : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ j ∈ x.tr.kids, j.parent < x.tr.nOrders) :
    (advance step b x (.ack k)).st.nParents =
        (advance step b x (.ack k)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.ack k)).tr.nOrders →
        ((advance step b x (.ack k)).st.parents id).qty =
          (advance step b x (.ack k)).tr.qty id ∧
        ((advance step b x (.ack k)).st.parents id).sent =
          (advance step b x (.ack k)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.ack k)).tr.kids,
        j.parent < (advance step b x (.ack k)).tr.nOrders := by sorry

theorem plan2_fill_preserves (b : Build) (x : Sys) (k q : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ j ∈ x.tr.kids, j.parent < x.tr.nOrders) :
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents id).qty =
          (advance step b x (.fill k q)).tr.qty id ∧
        ((advance step b x (.fill k q)).st.parents id).sent =
          (advance step b x (.fill k q)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.fill k q)).tr.kids,
        j.parent < (advance step b x (.fill k q)).tr.nOrders := by sorry

theorem plan2_advance_preserves (b : Build) (x : Sys) (e : Event)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x e).st.nParents = (advance step b x e).tr.nOrders ∧
      (∀ id, id < (advance step b x e).tr.nOrders →
        ((advance step b x e).st.parents id).qty =
          (advance step b x e).tr.qty id ∧
        ((advance step b x e).st.parents id).sent =
          (advance step b x e).tr.sent id) ∧
      ∀ k ∈ (advance step b x e).tr.kids,
        k.parent < (advance step b x e).tr.nOrders := by sorry
```