(1) Proof plan: `rankOf keys n` maps indices below `n` to ranks below `n` and is injective there. Hence, by finiteness, every rank `k < n` is attained. Counting indices by `< L` then proceeds by induction on `L`: passing from `L` to `L+1` adds exactly the unique index whose rank equals `L`. Applying this general counting fact to `rankOf` gives `plan0_count_rankOf_lt`.

(2)
```lean
theorem plan4_rankOf_lt_n (keys : List Int) (n i : Nat) (hi : i < n) :
    rankOf keys n i < n := by sorry

theorem plan4_rankOf_injective (keys : List Int) (n i j : Nat)
    (hi : i < n) (hj : j < n)
    (h : rankOf keys n i = rankOf keys n j) : i = j := by sorry

theorem plan4_exists_rankOf_eq (keys : List Int) (n k : Nat) (hk : k < n) :
    ∃ i, i < n ∧ rankOf keys n i = k := by sorry

theorem plan4_filter_count_succ (f : Nat → Nat) (n L i0 : Nat)
    (hi0 : i0 < n) (hf0 : f i0 = L)
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j) :
    ((List.range n).filter (fun i => decide (f i < L + 1))).length =
      ((List.range n).filter (fun i => decide (f i < L))).length + 1 := by sorry

theorem plan4_count_filter_lt_eq_of_exists (f : Nat → Nat) (n L : Nat)
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j)
    (hex : ∀ k, k < n → ∃ i, i < n ∧ f i = k)
    (hL : L ≤ n) :
    ((List.range n).filter (fun i => decide (f i < L))).length = L := by sorry
```