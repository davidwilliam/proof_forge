(1) Proof plan: Decompose `plan3_advance_sent_le_qty` by the event constructor. The parent case uses `0 ≤ q` for the new parent and the hypothesis for old parents; the route case is the only arithmetic step, since the added amount is `min liq (qty - sent)`, which is at most the remaining quantity when `sent ≤ qty`; ack and fill do not change any parent's `sent` or `qty` (fill only updates `cum`/child `done`). With the four event lemmas proved, the target follows by `cases e` and applying the matching lemma.

(2)
```lean
theorem plan4_sent_add_min_le (sent qty liq : Nat) (h : sent ≤ qty) :
    sent + min liq (qty - sent) ≤ qty := by sorry

theorem plan4_parent_sent_le_qty (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : ∀ id, id < x.st.nParents →
      (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ id, id < (advance step b x (.parent q f)).st.nParents →
      ((advance step b x (.parent q f)).st.parents id).sent ≤
        ((advance step b x (.parent q f)).st.parents id).qty := by sorry

theorem plan4_route_sent_le_qty (b : Build) (x : Sys) (rid liq : Nat)
    (h : ∀ id, id < x.st.nParents →
      (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ id, id < (advance step b x (.route rid liq)).st.nParents →
      ((advance step b x (.route rid liq)).st.parents id).sent ≤
        ((advance step b x (.route rid liq)).st.parents id).qty := by sorry

theorem plan4_ack_sent_le_qty (b : Build) (x : Sys) (k : Nat)
    (h : ∀ id, id < x.st.nParents →
      (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ id, id < (advance step b x (.ack k)).st.nParents →
      ((advance step b x (.ack k)).st.parents id).sent ≤
        ((advance step b x (.ack k)).st.parents id).qty := by sorry

theorem plan4_fill_sent_le_qty (b : Build) (x : Sys) (k q : Nat)
    (h : ∀ id, id < x.st.nParents →
      (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ id, id < (advance step b x (.fill k q)).st.nParents →
      ((advance step b x (.fill k q)).st.parents id).sent ≤
        ((advance step b x (.fill k q)).st.parents id).qty := by sorry
```