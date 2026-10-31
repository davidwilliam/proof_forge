(1) **Proof plan.** Split `InvFull (advance step b x (.fill k q))` into its seven components. A fill changes neither parent/child counts, quantities, nor sent amounts, and does not create kids, giving the first helper. On the truth side, a fill adds exactly `min q (c.qty - c.done)` to the executed total of child `k`'s parent (or nothing if `k` is unknown); on the state side, `step` adds the same amount to that parent's `cum`. The invariant's child correspondence identifies the state's child `k` with the truth's child `k` (using `nChildren = kids.length`), so those two increments coincide, yielding the `cum` component. Finally, the truth updates `kids` by `List.set k` with the increased `done`, while the state updates `children` by `upd` at the same index with the same increase; case-splitting on `idx = k` versus `idx ≠ k`, and on `k` being in range, yields the child-correspondence component. Assembling these pieces gives `InvFull` after a fill.

(2)
```lean
theorem plan5_fill_easy_parts (b : Build) (x : Sys) (k q : Nat) (hx : InvFull x) :
    (advance step b x (.fill k q)).st.nParents = (advance step b x (.fill k q)).tr.nOrders
    ∧ (advance step b x (.fill k q)).st.nChildren = (advance step b x (.fill k q)).tr.kids.length
    ∧ (∀ j, ((advance step b x (.fill k q)).st.parents j).qty = (advance step b x (.fill k q)).tr.qty j)
    ∧ (∀ j, ((advance step b x (.fill k q)).st.parents j).sent = (advance step b x (.fill k q)).tr.sent j)
    ∧ (∀ kk ∈ (advance step b x (.fill k q)).tr.kids, kk.parent < (advance step b x (.fill k q)).tr.nOrders) := by sorry

theorem plan5_fill_tr_exec_match (b : Build) (x : Sys) (k q : Nat) (j : Nat) :
    (advance step b x (.fill k q)).tr.exec j =
      match x.tr.kids[k]? with
      | some c => x.tr.exec j + (if c.parent = j then min q (c.qty - c.done) else 0)
      | none => x.tr.exec j := by sorry

theorem plan5_fill_st_cum_match (b : Build) (x : Sys) (k q : Nat) (j : Nat) :
    ((advance step b x (.fill k q)).st.parents j).cum =
      if k < x.st.nChildren then
        (if j = (x.st.children k).parent
         then (x.st.parents j).cum + min q ((x.st.children k).qty - (x.st.children k).done)
         else (x.st.parents j).cum)
      else (x.st.parents j).cum := by sorry

theorem plan5_fill_cum (b : Build) (x : Sys) (k q : Nat) (hx : InvFull x) :
    ∀ j, ((advance step b x (.fill k q)).st.parents j).cum
      = (advance step b x (.fill k q)).tr.exec j := by sorry

theorem plan5_fill_kids_children_raw (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr.kids =
      (match x.tr.kids[k]? with
       | some c => x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) }
       | none => x.tr.kids)
    ∧ (advance step b x (.fill k q)).st.children =
      (if k < x.st.nChildren then
         upd x.st.children k { (x.st.children k) with
           done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }
       else x.st.children) := by sorry

theorem plan5_fill_children (b : Build) (x : Sys) (k q : Nat) (hx : InvFull x) :
    ∀ (idx : Nat) (c : Kid), (advance step b x (.fill k q)).tr.kids[idx]? = some c →
      (advance step b x (.fill k q)).st.children idx = (⟨c.parent, c.qty, c.done⟩ : ChildRec) := by sorry
```