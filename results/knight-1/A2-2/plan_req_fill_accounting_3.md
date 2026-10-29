**Proof plan.** `FillAccounting` follows from the already-defined invariant `InvFillAcc`, whose last component is exactly cum-equals-exec for every parent. The only missing work is preservation of `InvFillAcc` under `route` and `fill`. Isolate the two hard components of those steps: (i) the child-record correspondence `children k = ⟨c.parent, c.qty, c.done⟩` after a route (new kid appended at index `nChildren`) and after a fill (child `k` updated via `List.set`), provable by case-splitting on the routing condition / on `kids[k]?` using `fa_get_append`, `fa_set_eq`, `fa_set_neq` and `upd_eq`/`upd_neq`; and (ii) cum-preservation under `fill`, where state and truth both add `min q (qty - done)` to exactly the filled child's parent (via `my_obs_fill_exec`). Packaging these with the easy count/bound facts (`my_route_nParents2`, `fa_fill_obs_len2`, `my_rec_exec`, `plan0_fill_kids_bound2`) gives full preservation for route and fill; combined with the existing `fa_parent_pres2`, `fa_ack_pres3` and `invFillAcc_base`, `run_induction` yields `InvFillAcc` after any run, and projecting its last component proves `req_fill_accounting`.

```lean
theorem plan3_route_children_corr (b : Build) (x : Sys) (rid liq : Nat)
    (hNC : x.st.nChildren = x.tr.kids.length)
    (hCorr : ∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c →
      x.st.children k = ⟨c.parent, c.qty, c.done⟩)
    (k : Nat) (c : Kid)
    (hk : ((advance step b x (.route rid liq)).tr.kids)[k]? = some c) :
    (advance step b x (.route rid liq)).st.children k = ⟨c.parent, c.qty, c.done⟩ := by sorry

theorem plan3_fill_children_corr (b : Build) (x : Sys) (k q : Nat)
    (hNC : x.st.nChildren = x.tr.kids.length)
    (hCorr : ∀ (j : Nat) (c : Kid), x.tr.kids[j]? = some c →
      x.st.children j = ⟨c.parent, c.qty, c.done⟩)
    (j : Nat) (c : Kid)
    (hj : ((advance step b x (.fill k q)).tr.kids)[j]? = some c) :
    (advance step b x (.fill k q)).st.children j = ⟨c.parent, c.qty, c.done⟩ := by sorry

theorem plan3_fill_cum_eq (b : Build) (x : Sys) (k q : Nat)
    (hNC : x.st.nChildren = x.tr.kids.length)
    (hCorr : ∀ (j : Nat) (c : Kid), x.tr.kids[j]? = some c →
      x.st.children j = ⟨c.parent, c.qty, c.done⟩)
    (hCum : ∀ id, (x.st.parents id).cum = x.tr.exec id)
    (id : Nat) :
    ((advance step b x (.fill k q)).st.parents id).cum =
      (advance step b x (.fill k q)).tr.exec id := by sorry

theorem plan3_invFillAcc_route (b : Build) (x : Sys) (rid liq : Nat) :
    InvFillAcc x → InvFillAcc (advance step b x (.route rid liq)) := by sorry

theorem plan3_invFillAcc_fill (b : Build) (x : Sys) (k q : Nat) :
    InvFillAcc x → InvFillAcc (advance step b x (.fill k q)) := by sorry

theorem plan3_invFillAcc_run (b : Build) (evs : List Event) :
    InvFillAcc (run step b evs) := by sorry
```