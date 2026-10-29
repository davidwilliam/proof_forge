(1) Proof plan: Show `prefers` is a strict total order: it is irreflexive, transitive, and total on distinct indices. Hence if `i ≠ j`, one of them is preferred to the other. Preference strictly increases `rankOf`, because every index preferring the less-preferred party also prefers the more-preferred party, while the preferred party itself is an extra witness. This contradicts equal ranks, so `i = j`. The filter-length lemmas formalize the strict counting step.

(2)
```lean
theorem plan3_prefers_self_false (keys : List Int) (i : Nat) :
    prefers keys i i = false := by sorry

theorem plan3_prefers_trans (keys : List Int) (a b c : Nat)
    (hab : prefers keys a b = true) (hbc : prefers keys b c = true) :
    prefers keys a c = true := by sorry

theorem plan3_prefers_total (keys : List Int) (i j : Nat) (hne : i ≠ j) :
    prefers keys i j = true ∨ prefers keys j i = true := by sorry

theorem plan3_filter_length_le (l : List Nat) (p q : Nat → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by sorry

theorem plan3_filter_length_lt (l : List Nat) (p q : Nat → Bool) (w : Nat)
    (h : ∀ x ∈ l, p x = true → q x = true)
    (hw : w ∈ l) (hqw : q w = true) (hpw : p w = false) :
    (l.filter p).length < (l.filter q).length := by sorry

theorem plan3_rankOf_lt_of_prefers (keys : List Int) (n i j : Nat)
    (hi : i < n) (hpref : prefers keys i j = true) :
    rankOf keys n i < rankOf keys n j := by sorry
```