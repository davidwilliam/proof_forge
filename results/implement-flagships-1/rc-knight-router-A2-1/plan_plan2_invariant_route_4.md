Split the route case by its output. If the output is empty the router does not move; if it routes, the whole successful step (new kid, updated `children`, incremented child count, unchanged parents/`cum`/`exec`) can be described once. The only genuinely new index after a successful route is the appended kid at position `kids.length = nChildren`, so a generic `getElem?` fact about appending a singleton isolates that case. With children preservation proved unconditionally and the remaining `cum`/length/bound components proved unconditionally, the route invariant is just assembling the pieces.

```lean
theorem plan4_adv_route_eq_of_out_nil (b : Build) (x : Sys) (id liq : Nat)
    (hout : (step b x.st (Event.route id liq)).2 = []) :
    advance step b x (Event.route id liq) = x := by sorry

theorem plan4_route_succ_desc (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (advance step b x (Event.route id liq)).tr.kids =
      x.tr.kids ++ [(⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ : Kid)] ∧
    (advance step b x (Event.route id liq)).st.children =
      upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ ∧
    (advance step b x (Event.route id liq)).st.nChildren = x.st.nChildren + 1 ∧
    (advance step b x (Event.route id liq)).st.nParents = x.st.nParents ∧
    (∀ j, ((advance step b x (Event.route id liq)).st.parents j).cum = (x.st.parents j).cum) ∧
    (∀ j, (advance step b x (Event.route id liq)).tr.exec j = x.tr.exec j) := by sorry

theorem plan4_getElem_append_singleton (l : List Kid) (kid : Kid) (idx : Nat) (c : Kid)
    (h : (l ++ [kid])[idx]? = some c) :
    (l[idx]? = some c) ∨ (idx = l.length ∧ c = kid) := by sorry

theorem plan4_route_children (b : Build) (x : Sys) (id liq : Nat)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hChild : ∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩) :
    ∀ idx c, (advance step b x (Event.route id liq)).tr.kids[idx]? = some c →
      (advance step b x (Event.route id liq)).st.children idx =
        ⟨c.parent, c.qty, c.done⟩ := by sorry

theorem plan4_route_cum_len_bound (b : Build) (x : Sys) (id liq : Nat)
    (hCum : ∀ j, (x.st.parents j).cum = x.tr.exec j)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hBound : ∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents) :
    (∀ j, ((advance step b x (Event.route id liq)).st.parents j).cum =
        (advance step b x (Event.route id liq)).tr.exec j) ∧
    (advance step b x (Event.route id liq)).st.nChildren =
        (advance step b x (Event.route id liq)).tr.kids.length ∧
    (∀ kid ∈ (advance step b x (Event.route id liq)).tr.kids,
       kid.parent < (advance step b x (Event.route id liq)).st.nParents) := by sorry
```