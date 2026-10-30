**Proof plan**

Maintain a strengthened invariant over every run: the router's cumulative quantity equals the true executed quantity for every parent; its child counter equals the number of true child orders; its child record at every valid index agrees with the true child (parent, quantity, executed shares); and every true child's parent already exists. The only nontrivial update is `fill`, where both sides increase the same parent's total by `min q (qty - done)`; handled by two formula lemmas. Parent/ack, route, and fill steps each preserve the invariant, so induction over the event list (`run_induction`) gives it for `run`, and `FillAccounting` is its first component.

```lean
theorem plan2_exec_fill_formula (b : Build) (x : Sys) (k q j : Nat) :
    (advance step b x (Event.fill k q)).tr.exec j =
      x.tr.exec j + (match x.tr.kids[k]? with
        | some c => if c.parent = j then min q (c.qty - c.done) else 0
        | none => 0) := by sorry

theorem plan2_cum_fill_formula (b : Build) (x : Sys) (k q j : Nat)
    (hlen : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩) :
    ((advance step b x (Event.fill k q)).st.parents j).cum =
      (x.st.parents j).cum + (match x.tr.kids[k]? with
        | some c => if c.parent = j then min q (c.qty - c.done) else 0
        | none => 0) := by sorry

theorem plan2_invariant_parent_ack (b : Build) (x : Sys) (q : Nat) (flag : Bool) (k : Nat)
    (h : (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
         x.st.nChildren = x.tr.kids.length ∧
         (∀ idx c, x.tr.kids[idx]? = some c →
           x.st.children idx = ⟨c.parent, c.qty, c.done⟩) ∧
         (∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents)) :
    ((∀ id, ((advance step b x (Event.parent q flag)).st.parents id).cum =
        (advance step b x (Event.parent q flag)).tr.exec id) ∧
     (advance step b x (Event.parent q flag)).st.nChildren =
        (advance step b x (Event.parent q flag)).tr.kids.length ∧
     (∀ idx c, (advance step b x (Event.parent q flag)).tr.kids[idx]? = some c →
       (advance step b x (Event.parent q flag)).st.children idx =
         ⟨c.parent, c.qty, c.done⟩) ∧
     (∀ kid ∈ (advance step b x (Event.parent q flag)).tr.kids,
        kid.parent < (advance step b x (Event.parent q flag)).st.nParents)) ∧
    ((∀ id, ((advance step b x (Event.ack k)).st.parents id).cum =
        (advance step b x (Event.ack k)).tr.exec id) ∧
     (advance step b x (Event.ack k)).st.nChildren =
        (advance step b x (Event.ack k)).tr.kids.length ∧
     (∀ idx c, (advance step b x (Event.ack k)).tr.kids[idx]? = some c →
       (advance step b x (Event.ack k)).st.children idx =
         ⟨c.parent, c.qty, c.done⟩) ∧
     (∀ kid ∈ (advance step b x (Event.ack k)).tr.kids,
        kid.parent < (advance step b x (Event.ack k)).st.nParents)) := by sorry

theorem plan2_invariant_route (b : Build) (x : Sys) (id liq : Nat)
    (h : (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
         x.st.nChildren = x.tr.kids.length ∧
         (∀ idx c, x.tr.kids[idx]? = some c →
           x.st.children idx = ⟨c.parent, c.qty, c.done⟩) ∧
         (∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents)) :
    (∀ j, ((advance step b x (Event.route id liq)).st.parents j).cum =
        (advance step b x (Event.route id liq)).tr.exec j) ∧
    (advance step b x (Event.route id liq)).st.nChildren =
        (advance step b x (Event.route id liq)).tr.kids.length ∧
    (∀ idx c, (advance step b x (Event.route id liq)).tr.kids[idx]? = some c →
      (advance step b x (Event.route id liq)).st.children idx =
        ⟨c.parent, c.qty, c.done⟩) ∧
    (∀ kid ∈ (advance step b x (Event.route id liq)).tr.kids,
       kid.parent < (advance step b x (Event.route id liq)).st.nParents) := by sorry

theorem plan2_invariant_fill (b : Build) (x : Sys) (k q : Nat)
    (h : (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
         x.st.nChildren = x.tr.kids.length ∧
         (∀ idx c, x.tr.kids[idx]? = some c →
           x.st.children idx = ⟨c.parent, c.qty, c.done⟩) ∧
         (∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents)) :
    (∀ j, ((advance step b x (Event.fill k q)).st.parents j).cum =
        (advance step b x (Event.fill k q)).tr.exec j) ∧
    (advance step b x (Event.fill k q)).st.nChildren =
        (advance step b x (Event.fill k q)).tr.kids.length ∧
    (∀ idx c, (advance step b x (Event.fill k q)).tr.kids[idx]? = some c →
      (advance step b x (Event.fill k q)).st.children idx =
        ⟨c.parent, c.qty, c.done⟩) ∧
    (∀ kid ∈ (advance step b x (Event.fill k q)).tr.kids,
       kid.parent < (advance step b x (Event.fill k q)).st.nParents) := by sorry

theorem plan2_run_invariant (b : Build) (evs : List Event) :
    (∀ id, ((run step b evs).st.parents id).cum = (run step b evs).tr.exec id) ∧
    (run step b evs).st.nChildren = (run step b evs).tr.kids.length ∧
    (∀ idx c, (run step b evs).tr.kids[idx]? = some c →
      (run step b evs).st.children idx = ⟨c.parent, c.qty, c.done⟩) ∧
    (∀ kid ∈ (run step b evs).tr.kids,
       kid.parent < (run step b evs).st.nParents) := by sorry
```