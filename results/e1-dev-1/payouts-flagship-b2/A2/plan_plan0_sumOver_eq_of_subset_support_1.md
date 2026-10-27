Short proof plan: Prove the target by induction on `small`. If `small = []`, every value of `f` on `big` is zero, so both sums are zero. If `small = a :: small'`, use `a ∈ big` to split `sumOver big f` as `f a + sumOver (big.erase a) f`. Nodup gives `a ∉ small'` and `big.erase a` remains nodup; membership in an erase for elements different from `a`, and the inverse under nodup, show the subset and zero-support hypotheses are preserved for `small'` and `big.erase a`. The induction hypothesis then finishes the equality.

```lean
theorem plan1_sumOver_eq_zero (l : List Nat) (f : Nat → Int)
    (h : ∀ x ∈ l, f x = 0) :
    sumOver l f = 0 := by sorry

theorem plan1_nodup_erase (l : List Nat) (a : Nat) (h : l.Nodup) :
    (l.erase a).Nodup := by sorry

theorem plan1_mem_erase_of_mem_ne (l : List Nat) (x y : Nat)
    (hmem : x ∈ l) (hne : x ≠ y) :
    x ∈ l.erase y := by sorry

theorem plan1_mem_of_mem_erase_of_nodup (l : List Nat) (x y : Nat)
    (hl : l.Nodup) (h : x ∈ l.erase y) :
    x ∈ l ∧ x ≠ y := by sorry

theorem plan1_sumOver_erase_eq (l : List Nat) (f : Nat → Int) (a : Nat)
    (hl : l.Nodup) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f := by sorry

theorem plan1_erase_preserves_support (big small : List Nat) (f : Nat → Int)
    (a : Nat) (hbig : big.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hne : ∀ x ∈ small, x ≠ a)
    (hzero : ∀ x ∈ big, x ∉ a :: small → f x = 0) :
    (∀ x ∈ small, x ∈ big.erase a) ∧
      (∀ x ∈ big.erase a, x ∉ small → f x = 0) := by sorry
```