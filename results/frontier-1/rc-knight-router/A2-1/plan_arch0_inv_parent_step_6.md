(1) **Proof plan.** For a `.parent q f` step, the truth appends one order while the router appends one parent record; kids, children, `sent`, and `exec` are unchanged, both counters increase by one, and `qty` is updated only at the old `nOrders`. Prove the parent-record equation separately for old indices (`id < nOrders`, via `upd` at a different index and the invariant) and for the new index (`id = nOrders`, via `upd` at the same index, `sentFor`/`execFor` over unchanged kids being `0` there by the kid-parent bound). Keep the child-record component by rewriting kids unchanged and weakening `kid.parent < nOrders` to `< nOrders+1`, and the `sent ≤ qty` component by casing on whether `id` is the new index. Assemble these five components into `arch0_Inv`.

(2)
```lean
theorem plan6_parent_old_records (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) (hid : id < x.tr.nOrders) :
    ((advance step b x (.parent q f)).st.parents id).qty =
        (advance step b x (.parent q f)).tr.qty id ∧
    ((advance step b x (.parent q f)).st.parents id).sent =
        (advance step b x (.parent q f)).tr.sent id ∧
    ((advance step b x (.parent q f)).st.parents id).cum =
        (advance step b x (.parent q f)).tr.exec id := by sorry

theorem plan6_parent_new_record (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) :
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).qty =
        (advance step b x (.parent q f)).tr.qty x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).sent =
        (advance step b x (.parent q f)).tr.sent x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).cum =
        (advance step b x (.parent q f)).tr.exec x.tr.nOrders := by sorry

theorem plan6_parent_children (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (k : Nat)
    (hk : k < (advance step b x (.parent q f)).tr.kids.length) :
    ∃ kid, (advance step b x (.parent q f)).tr.kids[k]? = some kid ∧
      (advance step b x (.parent q f)).st.children k =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.parent q f)).tr.nOrders := by sorry

theorem plan6_parent_sent_le_qty (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id ≤
      (advance step b x (.parent q f)).tr.qty id := by sorry

theorem plan6_inv_parent_step (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) :
    arch0_Inv (advance step b x (.parent q f)) := by sorry
```