**Proof plan.** Split the route case of `Inv` into its five independent components, mirroring the parent case. In each component, case split on the `routeBySent` guard `id < s.nParents ∧ 0 < min liq (qty - sent)`: on failure both state and truth are unchanged (`route_nil_st`, `route_nil_tr`), and on success both gain exactly the same child/statistic (`routeBySent_snd2`, `route_adv_len_cons`, `route_rec_sent_single`), so counts, `qty`, `sent`, the bound on kid parents, and `sent ≤ qty` (the last by `min liq (qty - sent) ≤ qty - sent` via `omega`) are preserved separately. Destructuring `hx : Inv x` and applying these five lemmas then closes `plan0_inv_advance_route` by `refine ⟨counts.1, qty, sent, counts.2, kids_lt, sent_le⟩`.

```lean
theorem plan2_route_counts (b : Build) (x : Sys) (id liq : Nat)
    (hNp : x.st.nParents = x.tr.nOrders)
    (hNc : x.st.nChildren = x.tr.kids.length) :
    (advance step b x (.route id liq)).st.nParents = (advance step b x (.route id liq)).tr.nOrders
      ∧ (advance step b x (.route id liq)).st.nChildren = (advance step b x (.route id liq)).tr.kids.length := by sorry

theorem plan2_route_qty (b : Build) (x : Sys) (id liq : Nat)
    (hQty : ∀ j, (x.st.parents j).qty = x.tr.qty j) :
    ∀ j, ((advance step b x (.route id liq)).st.parents j).qty
      = (advance step b x (.route id liq)).tr.qty j := by sorry

theorem plan2_route_sent (b : Build) (x : Sys) (id liq : Nat)
    (hSent : ∀ j, (x.st.parents j).sent = x.tr.sent j) :
    ∀ j, ((advance step b x (.route id liq)).st.parents j).sent
      = (advance step b x (.route id liq)).tr.sent j := by sorry

theorem plan2_route_kids_lt (b : Build) (x : Sys) (id liq : Nat)
    (hNp : x.st.nParents = x.tr.nOrders)
    (hKids : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    ∀ k ∈ (advance step b x (.route id liq)).tr.kids,
      k.parent < (advance step b x (.route id liq)).tr.nOrders := by sorry

theorem plan2_route_sent_le_qty (b : Build) (x : Sys) (id liq : Nat)
    (hLe : ∀ j, (x.st.parents j).sent ≤ (x.st.parents j).qty) :
    ∀ j, ((advance step b x (.route id liq)).st.parents j).sent
      ≤ ((advance step b x (.route id liq)).st.parents j).qty := by sorry
```