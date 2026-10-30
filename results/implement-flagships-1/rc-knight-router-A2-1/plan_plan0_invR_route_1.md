**Proof plan:** Split `route id liq` into three cases. If `id` is not an existing parent, or if the capped amount `min liq (qty - sent)` is zero, the router returns `(st, [])`, the venue model is unchanged, and `advance` is literally the identity, so `InvR` is preserved trivially. In the positive case, prove the `sent` component separately: the state adds `amt` to parent `id`'s `sent` via `upd`, while `Truth.sent` gains exactly the same `amt` from the single appended kid `[⟨id, amt⟩]` (via `adv_route_trkids`, `sentFor_append`, and `sentFor_out_single2`), with all other parents unchanged on both sides. Prove the remaining components (`nParents = nOrders`, `qty`, and the parent-bound on all kids) as a separate conjunction: `nParents` and quantities are unchanged by a successful route, old kids keep their bound, and the new kid's parent is `id < nParents`. Combining the `sent` lemma with that conjunction yields `InvR` for the successful case, and the main theorem follows by case analysis on `id < nParents` and `0 < amt`.

```lean
theorem plan1_adv_route_eq_of_not_lt (b : Build) (x : Sys) (id liq : Nat)
    (h : ¬ id < x.st.nParents) :
    advance step b x (Event.route id liq) = x := by sorry

theorem plan1_adv_route_eq_of_zero_amt (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : ¬ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    advance step b x (Event.route id liq) = x := by sorry

theorem plan1_adv_route_sent_of_succ (b : Build) (x : Sys) (id liq j : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent))
    (hSent : ∀ ide, (x.st.parents ide).sent = x.tr.sent ide) :
    ((advance step b x (Event.route id liq)).st.parents j).sent =
      (advance step b x (Event.route id liq)).tr.sent j := by sorry

theorem plan1_adv_route_core_of_succ (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    InvR x →
      (advance step b x (Event.route id liq)).st.nParents =
          (advance step b x (Event.route id liq)).tr.nOrders ∧
        (∀ j, j < (advance step b x (Event.route id liq)).st.nParents →
          ((advance step b x (Event.route id liq)).st.parents j).qty =
            (advance step b x (Event.route id liq)).tr.qty j) ∧
        (∀ k ∈ (advance step b x (Event.route id liq)).tr.kids,
          k.parent < (advance step b x (Event.route id liq)).st.nParents) := by sorry

theorem plan1_invR_route_succ (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    InvR x → InvR (advance step b x (Event.route id liq)) := by sorry
```