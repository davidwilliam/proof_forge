(1) **Proof plan.** For a `fill k q` step, align the router and venue updates using `arch0_Inv`: the invariant gives `nChildren = kids.length`, so `k` is valid for the router exactly when it is valid for `Truth.observe`, and the router's child record matches the venue's `Kid`. Counts, parent quantities, and sent totals are unchanged; the only changed quantities are the filled child's `done` and its parent's `cum`, already covered by `plan2_fill_adv_qty_sent_of_inv` and `plan2_fill_adv_cum_of_inv`. The remaining work is split below into frame/count lemmas, the unchanged sent bound, the filled-child case, the other-child case, and their combination into the child-correspondence component. `arch0_inv_fill_step` then assembles these with the existing parent-record lemmas.

(2)
```lean
theorem plan5_fill_counts (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x) :
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
    (advance step b x (.fill k q)).st.nChildren =
        (advance step b x (.fill k q)).tr.kids.length := by sorry

theorem plan5_fill_sent_le_qty (b : Build) (x : Sys) (k q id : Nat) (h : arch0_Inv x) :
    (advance step b x (.fill k q)).tr.sent id ≤
      (advance step b x (.fill k q)).tr.qty id := by sorry

theorem plan5_fill_child_at (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x)
    (kid : Kid) (hkid : x.tr.kids[k]? = some kid) :
    (advance step b x (.fill k q)).tr.kids[k]? =
        some { kid with done := kid.done + min q (kid.qty - kid.done) } ∧
    (advance step b x (.fill k q)).st.children k =
        ⟨kid.parent, kid.qty, kid.done + min q (kid.qty - kid.done)⟩ ∧
    kid.parent < (advance step b x (.fill k q)).tr.nOrders := by sorry

theorem plan5_fill_child_ne (b : Build) (x : Sys) (k q k' : Nat) (h : arch0_Inv x)
    (hne : k' ≠ k) :
    (advance step b x (.fill k q)).tr.kids[k']? = x.tr.kids[k']? ∧
    (advance step b x (.fill k q)).st.children k' = x.st.children k' ∧
    (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders := by sorry

theorem plan5_fill_child_records (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x)
    (k' : Nat) (hk' : k' < (advance step b x (.fill k q)).tr.kids.length) :
    ∃ kid, (advance step b x (.fill k q)).tr.kids[k']? = some kid ∧
      (advance step b x (.fill k q)).st.children k' =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.fill k q)).tr.nOrders := by sorry
```