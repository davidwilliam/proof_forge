**Proof plan:** Describe the filled run separately on the truth side (a `List.set` at `k`, or no change when `kids[k]?` is `none`) and on the state side (an `upd` at `k` guarded by `k < nChildren`). Then split on `idx = k` versus `idx ≠ k`: the off-diagonal case is preservation by `set`/`upd`, the diagonal case rewrites the state child via the `InvFull` correspondence `children k = ⟨c.parent, c.qty, c.done⟩` (using `nChildren = kids.length` to discharge the guard), and the `none` case is vacuous on the diagonal and pure preservation off it.

```lean
theorem plan4_fill_tr_kids_match (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr.kids =
      match x.tr.kids[k]? with
      | some c => x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) }
      | none => x.tr.kids := by sorry

theorem plan4_fill_st_children_apply (b : Build) (x : Sys) (k q : Nat) (idx : Nat) :
    (advance step b x (.fill k q)).st.children idx =
      if idx = k ∧ k < x.st.nChildren then
        { (x.st.children k) with
          done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }
      else x.st.children idx := by sorry

theorem plan4_getElem_set_same (l : List Kid) (k : Nat) (old : Kid) (d : Nat)
    (h : l[k]? = some old) :
    (l.set k { old with done := d })[k]? = some { old with done := d } := by sorry

theorem plan4_getElem_set_ne_idx (l : List Kid) (k idx : Nat) (v : Kid)
    (h : idx ≠ k) :
    (l.set k v)[idx]? = l[idx]? := by sorry

theorem plan4_fill_children_core (b : Build) (x : Sys) (k q : Nat)
    (hNch : x.st.nChildren = x.tr.kids.length)
    (hChild : ∀ k c, x.tr.kids[k]? = some c → x.st.children k = (⟨c.parent, c.qty, c.done⟩ : ChildRec)) :
    ∀ (idx : Nat) (c : Kid), (advance step b x (.fill k q)).tr.kids[idx]? = some c →
      (advance step b x (.fill k q)).st.children idx = (⟨c.parent, c.qty, c.done⟩ : ChildRec) := by sorry
```