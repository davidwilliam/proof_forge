**Proof plan.** For a `fill k q`, split on whether `k` is in range. By the invariant, the state's child count equals the truth's kid length, so the state and venue are in range together; in that case they describe the same child and use the same increment `min q (qty - done)`. The venue adds this increment only to that child's parent's executed total and never changes shares sent; the state adds it only to that parent's `cum` and updates only child `k`. Out of range, both sides are unchanged. The first three lemmas isolate the venue calculation and the state/truth child match; the last three transport the parent-quantity/sent, parent-`cum`, and child-correspondence parts of `arch0_Inv` across the step, leaving only counts, lengths, and the sent bound; which are unchanged; for the final assembly of `arch0_inv_fill_step`.

```lean
theorem plan2_fill_truth_sent (t : Truth) (k q id : Nat) :
    (t.observe (.fill k q)).sent id = t.sent id := by sorry

theorem plan2_fill_truth_exec_some (t : Truth) (k q id : Nat) (kid : Kid)
    (h : t.kids[k]? = some kid) :
    (t.observe (.fill k q)).exec id =
      t.exec id + (if kid.parent = id then min q (kid.qty - kid.done) else 0) := by sorry

theorem plan2_fill_child_match_of_inv {x : Sys} (h : arch0_Inv x) {k : Nat}
    (hk : k < x.tr.kids.length) :
    ∃ kid, x.tr.kids[k]? = some kid ∧
      x.st.children k = ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < x.tr.nOrders ∧ k < x.st.nChildren := by sorry

theorem plan2_fill_adv_qty_sent_of_inv (b : Build) {x : Sys} (h : arch0_Inv x)
    (k q id : Nat) (hid : id < (advance step b x (.fill k q)).tr.nOrders) :
    ((advance step b x (.fill k q)).st.parents id).qty =
        (advance step b x (.fill k q)).tr.qty id ∧
      ((advance step b x (.fill k q)).st.parents id).sent =
        (advance step b x (.fill k q)).tr.sent id := by sorry

theorem plan2_fill_adv_cum_of_inv (b : Build) {x : Sys} (h : arch0_Inv x)
    (k q id : Nat) (hid : id < (advance step b x (.fill k q)).tr.nOrders) :
    ((advance step b x (.fill k q)).st.parents id).cum =
      (advance step b x (.fill k q)).tr.exec id := by sorry

theorem plan2_fill_adv_child_of_inv (b : Build) {x : Sys} (h : arch0_Inv x)
    (k q k' : Nat) (hk' : k' < (advance step b x (.fill k q)).tr.kids.length) :
    ∃ kid, (advance step b x (.fill k q)).tr.kids[k']? = some kid ∧
      (advance step b x (.fill k q)).st.children k' =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.fill k q)).tr.nOrders := by sorry
```