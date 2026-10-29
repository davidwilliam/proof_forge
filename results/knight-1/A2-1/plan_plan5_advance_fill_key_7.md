Short proof plan: split on `k < x.st.nChildren`. If false, the advanced system is just `x`. If true, the invariant gives a truth child `c` matching `x.st.children k`; the step only rewrites that child and the parent's `cum`, while `Truth.observe` only rewrites `kids[k]` by the same `min q (c.qty - c.done)` amount (via `execFor_set_done`/`plan5_exec_observe_fill`). Lengths and parent bounds are then unchanged, using the already-available `obs_fill_kids_len`, `nOrdersObsFill_aux2`, and `setParent_mem_aux`. The helpers below isolate the pointwise state update, the `List.set` lookup, and the two preserved components.

```lean
theorem plan7_fill_step_children (b : Build) (s : State) (k q j : Nat)
    (hk : k < s.nChildren) :
    (step b s (.fill k q)).1.children j =
      (if j = k then
        { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) }
       else s.children k) := by sorry

theorem plan7_set_get_of_lt (l : List Kid) (k j : Nat) (d : Kid)
    (hk : k < l.length) :
    (l.set k d)[j]? = (if j = k then some d else l[j]?) := by sorry

theorem plan7_fill_children_after (b : Build) (x : Sys) (k q : Nat)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ j, j < x.tr.kids.length →
      ∃ c, x.tr.kids[j]? = some c ∧ x.st.children j = ⟨c.parent, c.qty, c.done⟩)
    (hk : k < x.st.nChildren) :
    ∀ j, j < (advance step b x (.fill k q)).tr.kids.length →
      ∃ c, (advance step b x (.fill k q)).tr.kids[j]? = some c ∧
        (advance step b x (.fill k q)).st.children j = ⟨c.parent, c.qty, c.done⟩ := by sorry

theorem plan7_fill_cum_after (b : Build) (x : Sys) (k q : Nat)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ j, j < x.tr.kids.length →
      ∃ c, x.tr.kids[j]? = some c ∧ x.st.children j = ⟨c.parent, c.qty, c.done⟩)
    (hcum : ∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id)
    (hk : k < x.st.nChildren) :
    ∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
      ((advance step b x (.fill k q)).st.parents id).cum =
        (advance step b x (.fill k q)).tr.exec id := by sorry

theorem plan7_fill_advance_eq_of_not_lt (b : Build) (x : Sys) (k q : Nat)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hk : ¬ k < x.st.nChildren) :
    advance step b x (.fill k q) = x := by sorry
```