**Proof plan.** Split the monolithic preservation statement by event. First isolate two reusable facts about the venue truth: a parent with no recorded kids has zero shares sent, and recording new kids preserves the bound on kid parents. The `parent` case then follows from `upd` at the fresh index, the `route` case by splitting on the routing condition and using the singleton-record sent formula, the `ack` case by rfl/simp, and the `fill` case because updating only `cum`/`done` leaves `qty`, `sent`, `nOrders`, and kid parents unchanged.

```lean
theorem plan1_sentFor_zero_of_all_parent_lt (l : List Kid) (n id : Nat)
    (h : ∀ k ∈ l, k.parent < n) (hid : n ≤ id) :
    sentFor l id = 0 := by sorry

theorem plan1_kids_bound_record (t : Truth) (out : List Child)
    (h1 : ∀ k ∈ t.kids, k.parent < t.nOrders)
    (h2 : ∀ c ∈ out, c.parent < t.nOrders) :
    ∀ k ∈ (t.record out).kids, k.parent < (t.record out).nOrders := by sorry

theorem plan1_advance_parent_preserves (b : Build) (x : Sys) (q : Nat) (f : Bool)
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

theorem plan1_advance_route_preserves (b : Build) (x : Sys) (id liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
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

theorem plan1_advance_ack_preserves (b : Build) (x : Sys) (k : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.ack k)).st.nParents =
        (advance step b x (.ack k)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.ack k)).tr.nOrders →
        ((advance step b x (.ack k)).st.parents id).qty =
          (advance step b x (.ack k)).tr.qty id ∧
        ((advance step b x (.ack k)).st.parents id).sent =
          (advance step b x (.ack k)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.ack k)).tr.kids,
        j.parent < (advance step b x (.ack k)).tr.nOrders := by sorry

theorem plan1_advance_fill_preserves (b : Build) (x : Sys) (k q : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents id).qty =
          (advance step b x (.fill k q)).tr.qty id ∧
        ((advance step b x (.fill k q)).st.parents id).sent =
          (advance step b x (.fill k q)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.fill k q)).tr.kids,
        j.parent < (advance step b x (.fill k q)).tr.nOrders := by sorry
```