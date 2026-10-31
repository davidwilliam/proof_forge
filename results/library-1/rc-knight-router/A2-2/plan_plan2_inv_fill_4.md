(1) Proof plan: Split the `fill k q` case according to whether `k < x.st.nChildren`. Under `Inv`, this bound equals `x.tr.kids.length`, so in the in-range case the truth has a kid `c` at index `k` and the router's child `k` agrees with `c` on parent, qty, and done; hence both sides add the same `x = min q (c.qty - c.done)`, which preserves cumulative execution via `execFor_set_done` and child synchronisation via list-set reasoning. In the out-of-range case both the router and `Truth.observe` are no-ops. The remaining components (parent/child counts, sent, qty, and the parent bound) are preserved by the existing `fill_adv_*` / `sentFor_set_done` facts.

(2)

```lean
theorem plan4_fill_get_of_lt : ∀ (b : Build) (x : Sys) (k : Nat),
    Inv x → k < x.st.nChildren →
    ∃ c, x.tr.kids[k]? = some c ∧
      (x.st.children k).parent = c.parent ∧
      (x.st.children k).qty = c.qty ∧
      (x.st.children k).done = c.done := by sorry

theorem plan4_fill_adv_of_not_lt : ∀ (b : Build) (x : Sys) (k q : Nat),
    Inv x → ¬ k < x.st.nChildren →
    advance step b x (.fill k q) = x := by sorry

theorem plan4_fill_adv_kids_of_some : ∀ (b : Build) (x : Sys) (k q : Nat) (c : Kid),
    x.tr.kids[k]? = some c →
    (advance step b x (.fill k q)).tr.kids =
      x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) } := by sorry

theorem plan4_fill_cum_of_lt : ∀ (b : Build) (x : Sys) (k q : Nat),
    Inv x → k < x.st.nChildren →
    ∀ j, ((advance step b x (.fill k q)).st.parents j).cum =
      execFor (advance step b x (.fill k q)).tr.kids j := by sorry

theorem plan4_fill_sync_of_lt : ∀ (b : Build) (x : Sys) (k q : Nat),
    Inv x → k < x.st.nChildren →
    ∀ (k2 : Nat) (c2 : Kid),
      (advance step b x (.fill k q)).tr.kids[k2]? = some c2 →
      ((advance step b x (.fill k q)).st.children k2).parent = c2.parent ∧
      ((advance step b x (.fill k q)).st.children k2).qty = c2.qty ∧
      ((advance step b x (.fill k q)).st.children k2).done = c2.done := by sorry

theorem plan4_fill_easy_of_lt : ∀ (b : Build) (x : Sys) (k q : Nat),
    Inv x → k < x.st.nChildren →
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
    (advance step b x (.fill k q)).st.nChildren =
        (advance step b x (.fill k q)).tr.kids.length ∧
    (∀ j, ((advance step b x (.fill k q)).st.parents j).sent =
        sentFor (advance step b x (.fill k q)).tr.kids j) ∧
    (∀ j, j < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents j).qty =
          (advance step b x (.fill k q)).tr.qty j) ∧
    (∀ (k2 : Nat) (c2 : Kid),
      (advance step b x (.fill k q)).tr.kids[k2]? = some c2 →
        c2.parent < (advance step b x (.fill k q)).tr.nOrders) := by sorry
```