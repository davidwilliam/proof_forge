**Proof plan**

The route output is determined entirely by the router state (`nParents`, the parent's `qty`, and `sent`), while `expectedRoute` is determined by the corresponding truth values (`nOrders`, `qty`, and `Truth.sent`). Therefore the proof has three parts:

1. Prove the routing output of `step` explicitly in terms of the state.
2. Prove by induction over the event sequence that the state remains synchronized with the truth: the numbers of parents agree, and for every existing parent the state quantity and sent quantity equal the truth quantity and sent quantity. The invariant must also track that all existing child orders belong to existing parents; this handles the arrival of a new parent, whose previously sent quantity is zero.
3. Combine these facts: once the state and truth quantities are equal, the two side conditions and the two `min` expressions in `step` and `expectedRoute` coincide, so their outputs are equal.

```lean
theorem plan0_step_route_out (b : Build) (s : State) (id liq : Nat) :
    (step b s (.route id liq)).2 =
      if id < s.nParents ∧
          0 < min liq ((s.parents id).qty - (s.parents id).sent) then
        [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩]
      else [] := by sorry

theorem plan0_advance_preserves (b : Build) (x : Sys) (e : Event)
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

theorem plan0_run_invariants (b : Build) (evs : List Event) :
    (run step b evs).st.nParents = (run step b evs).tr.nOrders ∧
      (∀ id, id < (run step b evs).tr.nOrders →
        ((run step b evs).st.parents id).qty =
          (run step b evs).tr.qty id ∧
        ((run step b evs).st.parents id).sent =
          (run step b evs).tr.sent id) ∧
      ∀ k ∈ (run step b evs).tr.kids,
        k.parent < (run step b evs).tr.nOrders := by sorry

theorem plan0_route_eq_expected_of_invariants (b : Build) (x : Sys)
    (id liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (step b x.st (.route id liq)).2 = expectedRoute x.tr id liq := by sorry
```