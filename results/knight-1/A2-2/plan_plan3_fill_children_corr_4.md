(1) Proof plan: rewrite the truth-side kids after a `fill` as either a `List.set` update at `k` or unchanged. Split on whether the queried index `j` equals `k`. If `j ≠ k`, the router leaves child `j` unchanged and `hCorr` applies to the old kid. If `j = k` and there is an old kid `c0`, use `hCorr`, `hNC`, and the fact `k` is in bounds to compute the router's updated child directly. If there is no old kid at `k`, the router leaves all children unchanged.

(2)
```lean
theorem plan4_get_set_cases_of_lt (l : List Kid) (k j : Nat) (v c : Kid)
    (hk : k < l.length) (h : (l.set k v)[j]? = some c) :
    (j = k ∧ c = v) ∨ (j ≠ k ∧ l[j]? = some c) := by sorry

theorem plan4_fill_tr_kids_eq (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr.kids =
      match x.tr.kids[k]? with
      | some c => x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) }
      | none => x.tr.kids := by sorry

theorem plan4_fill_st_children_ne (b : Build) (x : Sys) (k q j : Nat)
    (hj : j ≠ k) :
    (advance step b x (.fill k q)).st.children j = x.st.children j := by sorry

theorem plan4_fill_st_children_kid (b : Build) (x : Sys) (k q : Nat)
    (hNC : x.st.nChildren = x.tr.kids.length)
    (hCorr : ∀ (j : Nat) (c : Kid), x.tr.kids[j]? = some c →
      x.st.children j = ⟨c.parent, c.qty, c.done⟩)
    (c0 : Kid) (hc0 : x.tr.kids[k]? = some c0) :
    (advance step b x (.fill k q)).st.children k =
      ⟨c0.parent, c0.qty, c0.done + min q (c0.qty - c0.done)⟩ := by sorry

theorem plan4_fill_st_children_of_no_kid (b : Build) (x : Sys) (k q : Nat)
    (hNC : x.st.nChildren = x.tr.kids.length)
    (h : x.tr.kids[k]? = none) :
    (advance step b x (.fill k q)).st.children = x.st.children := by sorry
```