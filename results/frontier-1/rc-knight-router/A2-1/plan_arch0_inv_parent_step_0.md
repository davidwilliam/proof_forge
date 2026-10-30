(1) **Proof plan.** For a `parent q f` event, the state adds the new record at index `nParents`, while the truth adds its quantity at index `nOrders` and leaves `kids` unchanged. Using `nParents = nOrders` from `arch0_Inv`, split every parent-index argument into the old case `id < nOrders`, where `upd` at a different index and the old invariant apply, and the new case `id = nOrders`, where `upd` at the same index applies. The new parent has sent and executed `0` because every existing kid belongs to an old parent. This also proves the preserved `sent ≤ qty` bound: at the new index `0 ≤ q`, and elsewhere both sides are unchanged.

(2)
```lean
theorem plan0_parent_kids_eq (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    (advance step b x (.parent q f)).tr.kids = x.tr.kids := by sorry

theorem plan0_parent_sent_exec_eq (b : Build) (x : Sys) (q : Nat) (f : Bool) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id = x.tr.sent id ∧
    (advance step b x (.parent q f)).tr.exec id = x.tr.exec id := by sorry

theorem plan0_kid_parent_lt_of_inv {x : Sys} (h : arch0_Inv x)
    {kid : Kid} (hkid : kid ∈ x.tr.kids) :
    kid.parent < x.tr.nOrders := by sorry

theorem plan0_sent_exec_new_parent_of_inv {x : Sys} (h : arch0_Inv x) :
    x.tr.sent x.tr.nOrders = 0 ∧ x.tr.exec x.tr.nOrders = 0 := by sorry

theorem plan0_parent_records_step (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat)
    (hid : id < (advance step b x (.parent q f)).tr.nOrders) :
    ((advance step b x (.parent q f)).st.parents id).qty =
        (advance step b x (.parent q f)).tr.qty id ∧
    ((advance step b x (.parent q f)).st.parents id).sent =
        (advance step b x (.parent q f)).tr.sent id ∧
    ((advance step b x (.parent q f)).st.parents id).cum =
        (advance step b x (.parent q f)).tr.exec id := by sorry

theorem plan0_parent_sent_le_qty_step (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id ≤
      (advance step b x (.parent q f)).tr.qty id := by sorry
```