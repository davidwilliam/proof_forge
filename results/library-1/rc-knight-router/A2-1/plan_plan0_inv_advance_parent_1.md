**Proof plan.** Unfold `Inv` at `x` and split the post-`parent` goal into its six components. The count fields both increase or stay fixed as required; parent-order quantities update simultaneously at the old `nParents = nOrders` index and are unchanged elsewhere. The new parent's sent total is `0` on the state side, and also `0` on the truth side because every existing kid belongs to a strictly earlier parent index (via `sentFor_all_lt_zero`); other indices keep their old values. Kid membership is unchanged while `nOrders` grows by one, and the `sent ≤ qty` invariant is preserved index-wise (the new index has `0 ≤ q`). Assembling these five facts with `⟨plan1_parent_counts …, plan1_parent_qty …, plan1_parent_sent …, plan1_parent_kids_lt …, plan1_parent_sent_le_qty …⟩` (splitting the count conjunction appropriately) proves `plan0_inv_advance_parent` by `refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩` after destructuring `hx`.

```lean
theorem plan1_parent_counts (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hNp : x.st.nParents = x.tr.nOrders)
    (hNc : x.st.nChildren = x.tr.kids.length) :
    (advance step b x (.parent q f)).st.nParents = (advance step b x (.parent q f)).tr.nOrders
      ∧ (advance step b x (.parent q f)).st.nChildren = (advance step b x (.parent q f)).tr.kids.length := by sorry

theorem plan1_parent_qty (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hNp : x.st.nParents = x.tr.nOrders)
    (hQty : ∀ id, (x.st.parents id).qty = x.tr.qty id) :
    ∀ j, ((advance step b x (.parent q f)).st.parents j).qty = (advance step b x (.parent q f)).tr.qty j := by sorry

theorem plan1_parent_sent (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hNp : x.st.nParents = x.tr.nOrders)
    (hSent : ∀ id, (x.st.parents id).sent = x.tr.sent id)
    (hKids : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    ∀ j, ((advance step b x (.parent q f)).st.parents j).sent = (advance step b x (.parent q f)).tr.sent j := by sorry

theorem plan1_parent_kids_lt (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hKids : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    ∀ k ∈ (advance step b x (.parent q f)).tr.kids, k.parent < (advance step b x (.parent q f)).tr.nOrders := by sorry

theorem plan1_parent_sent_le_qty (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hLe : ∀ id, (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ j, ((advance step b x (.parent q f)).st.parents j).sent ≤ ((advance step b x (.parent q f)).st.parents j).qty := by sorry
```