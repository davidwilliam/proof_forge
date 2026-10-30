(1) Proof plan: Unfold `arch0_Inv` for the `parent` step into its five components. The frame lemma gives the parent/child counts and that the recorded kids do not change. For parent records, split into the previously existing parents, whose records and truth values are unchanged, and the newly added parent, whose record is `⟨q, f, 0, 0⟩` and whose sent/executed totals are zero because every existing kid belongs to an earlier parent. Existing child records remain valid, with their parent bound weakened from `< x.tr.nOrders` to `< x.tr.nOrders + 1`. Finally, `sent ≤ qty` follows by the same old/new split. Assembling these five facts gives `arch0_inv_parent_step` directly.

(2)
```lean
theorem plan3_parent_frame (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    (advance step b x (.parent q f)).st.nParents = x.st.nParents + 1 ∧
    (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 ∧
    (advance step b x (.parent q f)).st.nChildren = x.st.nChildren ∧
    (advance step b x (.parent q f)).tr.kids = x.tr.kids := by
  sorry

theorem plan3_parent_old_records (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) (hid : id < x.tr.nOrders) :
    ((advance step b x (.parent q f)).st.parents id).qty =
        (advance step b x (.parent q f)).tr.qty id ∧
    ((advance step b x (.parent q f)).st.parents id).sent =
        (advance step b x (.parent q f)).tr.sent id ∧
    ((advance step b x (.parent q f)).st.parents id).cum =
        (advance step b x (.parent q f)).tr.exec id := by
  sorry

theorem plan3_parent_new_record (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) :
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).qty =
        (advance step b x (.parent q f)).tr.qty x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).sent =
        (advance step b x (.parent q f)).tr.sent x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).cum =
        (advance step b x (.parent q f)).tr.exec x.tr.nOrders := by
  sorry

theorem plan3_parent_children (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (k : Nat)
    (hk : k < (advance step b x (.parent q f)).tr.kids.length) :
    ∃ kid, (advance step b x (.parent q f)).tr.kids[k]? = some kid ∧
      (advance step b x (.parent q f)).st.children k =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.parent q f)).tr.nOrders := by
  sorry

theorem plan3_parent_sent_le_qty (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id ≤
      (advance step b x (.parent q f)).tr.qty id := by
  sorry
```