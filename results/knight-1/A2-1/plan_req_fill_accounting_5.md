Short proof plan: strengthen the induction to track the router's child table against the venue truth. Maintain, for every run: `nParents = nOrders`, `nChildren = kids.length`, every state child record equals the corresponding truth `Kid` (parent, quantity and executed shares), every existing parent's `cum` equals the truth executed total, and every truth kid belongs to an existing parent. The only nontrivial accounting update is a `fill`: by `execFor_set_done`, the venue adds `min q (qty - done)` exactly to the filled child's parent, which is precisely what `step` adds to that parent's `cum` once the child tables agree. Parent, route and ack steps leave `cum`/execution unchanged except for the new-parent and new-child boundary cases, which follow from the kid-parent bound. Induction over events via `run_induction` then gives `FillAccounting` by projection.

```lean
theorem plan5_exec_observe_fill (t : Truth) (k q : Nat) (c : Kid)
    (hc : t.kids[k]? = some c) (id : Nat) :
    (t.observe (.fill k q)).exec id =
      t.exec id + (if c.parent = id then min q (c.qty - c.done) else 0) := by sorry

theorem plan5_advance_parent_key (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.parent q f)).st.nParents =
        (advance step b x (.parent q f)).tr.nOrders ∧
      (advance step b x (.parent q f)).st.nChildren =
        (advance step b x (.parent q f)).tr.kids.length ∧
      (∀ k, k < (advance step b x (.parent q f)).tr.kids.length →
        ∃ c, (advance step b x (.parent q f)).tr.kids[k]? = some c ∧
          (advance step b x (.parent q f)).st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.parent q f)).tr.nOrders →
        ((advance step b x (.parent q f)).st.parents id).cum =
          (advance step b x (.parent q f)).tr.exec id) ∧
      ∀ k ∈ (advance step b x (.parent q f)).tr.kids,
        k.parent < (advance step b x (.parent q f)).tr.nOrders := by sorry

theorem plan5_advance_route_key (b : Build) (x : Sys) (rid liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.route rid liq)).st.nParents =
        (advance step b x (.route rid liq)).tr.nOrders ∧
      (advance step b x (.route rid liq)).st.nChildren =
        (advance step b x (.route rid liq)).tr.kids.length ∧
      (∀ k, k < (advance step b x (.route rid liq)).tr.kids.length →
        ∃ c, (advance step b x (.route rid liq)).tr.kids[k]? = some c ∧
          (advance step b x (.route rid liq)).st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.route rid liq)).tr.nOrders →
        ((advance step b x (.route rid liq)).st.parents id).cum =
          (advance step b x (.route rid liq)).tr.exec id) ∧
      ∀ k ∈ (advance step b x (.route rid liq)).tr.kids,
        k.parent < (advance step b x (.route rid liq)).tr.nOrders := by sorry

theorem plan5_advance_ack_key (b : Build) (x : Sys) (k : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.ack k)).st.nParents =
        (advance step b x (.ack k)).tr.nOrders ∧
      (advance step b x (.ack k)).st.nChildren =
        (advance step b x (.ack k)).tr.kids.length ∧
      (∀ j, j < (advance step b x (.ack k)).tr.kids.length →
        ∃ c, (advance step b x (.ack k)).tr.kids[j]? = some c ∧
          (advance step b x (.ack k)).st.children j = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.ack k)).tr.nOrders →
        ((advance step b x (.ack k)).st.parents id).cum =
          (advance step b x (.ack k)).tr.exec id) ∧
      ∀ j ∈ (advance step b x (.ack k)).tr.kids,
        j.parent < (advance step b x (.ack k)).tr.nOrders := by sorry

theorem plan5_advance_fill_key (b : Build) (x : Sys) (k q : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
      (advance step b x (.fill k q)).st.nChildren =
        (advance step b x (.fill k q)).tr.kids.length ∧
      (∀ j, j < (advance step b x (.fill k q)).tr.kids.length →
        ∃ c, (advance step b x (.fill k q)).tr.kids[j]? = some c ∧
          (advance step b x (.fill k q)).st.children j = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents id).cum =
          (advance step b x (.fill k q)).tr.exec id) ∧
      ∀ j ∈ (advance step b x (.fill k q)).tr.kids,
        j.parent < (advance step b x (.fill k q)).tr.nOrders := by sorry

theorem plan5_run_key (b : Build) (evs : List Event) :
    (run step b evs).st.nParents = (run step b evs).tr.nOrders ∧
      (run step b evs).st.nChildren = (run step b evs).tr.kids.length ∧
      (∀ k, k < (run step b evs).tr.kids.length →
        ∃ c, (run step b evs).tr.kids[k]? = some c ∧
          (run step b evs).st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (run step b evs).tr.nOrders →
        ((run step b evs).st.parents id).cum = (run step b evs).tr.exec id) ∧
      ∀ k ∈ (run step b evs).tr.kids, k.parent < (run step b evs).tr.nOrders := by sorry
```