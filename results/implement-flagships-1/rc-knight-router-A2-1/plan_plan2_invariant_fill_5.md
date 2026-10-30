A fill changes the truth only by updating `kids[k].done` by `min q (qty-done)`, and changes the router state in the matching way only when `k < nChildren`. Hence decompose the fill step into: a description of the resulting truth element, a description of the resulting child records, the combined child-record correspondence, the cumulative equality obtained from the already available fill formulas for `cum` and `exec`, and finally the unchanged length/parent-bound facts. With these five facts, the four components of `plan2_invariant_fill` follow directly.

```lean
theorem plan5_fill_kids_cases (t : Truth) (k q idx : Nat) (c : Kid)
    (h : ((t.observe (Event.fill k q)).kids)[idx]? = some c) :
    (t.kids[idx]? = some c ∧ idx ≠ k) ∨
      (∃ c0 : Kid, t.kids[k]? = some c0 ∧ idx = k ∧
        c = { c0 with done := c0.done + min q (c0.qty - c0.done) }) := by sorry

theorem plan5_fill_st_children (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (Event.fill k q)).st.children =
      if k < x.st.nChildren then
        upd x.st.children k
          { x.st.children k with
            done := (x.st.children k).done +
              min q ((x.st.children k).qty - (x.st.children k).done) }
      else x.st.children := by sorry

theorem plan5_fill_children_preserved (b : Build) (x : Sys) (k q : Nat)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hChild : ∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩) :
    ∀ idx c, (advance step b x (Event.fill k q)).tr.kids[idx]? = some c →
      (advance step b x (Event.fill k q)).st.children idx =
        ⟨c.parent, c.qty, c.done⟩ := by sorry

theorem plan5_fill_cum_preserved (b : Build) (x : Sys) (k q : Nat)
    (hCum : ∀ id, (x.st.parents id).cum = x.tr.exec id)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hChild : ∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩) :
    ∀ j, ((advance step b x (Event.fill k q)).st.parents j).cum =
      (advance step b x (Event.fill k q)).tr.exec j := by sorry

theorem plan5_fill_length_and_bound (b : Build) (x : Sys) (k q : Nat)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hBound : ∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents) :
    (advance step b x (Event.fill k q)).st.nChildren =
        (advance step b x (Event.fill k q)).tr.kids.length ∧
      (∀ kid ∈ (advance step b x (Event.fill k q)).tr.kids,
        kid.parent < (advance step b x (Event.fill k q)).st.nParents) := by sorry
```