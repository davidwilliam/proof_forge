Split on whether child `k` exists in the router. If `k < nChildren`, the length invariant gives a corresponding executed child in `kids`, whose stored record determines the parent, quantity, and previously executed amount used by the fill update. If `k ≥ nChildren`, the same length invariant shows that `kids[k]?` is `none`, and the fill leaves the router state unchanged.

```lean
theorem plan3_getElem_ex_of_lt (l : List Kid) (k : Nat) (h : k < l.length) :
    ∃ c, l[k]? = some c := by sorry

theorem plan3_getElem_none_of_length_le (l : List Kid) (k : Nat)
    (h : l.length ≤ k) : l[k]? = none := by sorry

theorem plan3_fill_cum_of_some (b : Build) (x : Sys) (k q j : Nat) (c : Kid)
    (hk : k < x.st.nChildren)
    (hc : x.tr.kids[k]? = some c)
    (hchild : ∀ idx c', x.tr.kids[idx]? = some c' →
      x.st.children idx = ⟨c'.parent, c'.qty, c'.done⟩) :
    ((advance step b x (Event.fill k q)).st.parents j).cum =
      (x.st.parents j).cum +
        (if c.parent = j then min q (c.qty - c.done) else 0) := by sorry

theorem plan3_fill_adv_st_of_not_lt (b : Build) (x : Sys) (k q : Nat)
    (h : ¬ k < x.st.nChildren) :
    (advance step b x (Event.fill k q)).st = x.st := by sorry
```