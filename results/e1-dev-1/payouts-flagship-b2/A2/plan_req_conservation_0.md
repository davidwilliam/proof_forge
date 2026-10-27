## Proof plan

For conservation, expand `expectedBalance` under `sumOver s.accounts` using `sumOver_add`/`sumOver_sub`. The source debit contributes exactly `r.amount` by the existing `sumOver_ite_eq`, since the source lies in the duplicate-free account list. The credits are handled in stages: first remove the first occurrence of a member from a sum, then show a sum over a list depends only on the sublist supporting the summand, allowing passage from `s.accounts` to `r.recipients`. A range-shift identity converts recipient-indexed `shareOf` sums (via `indexOf?`) into a sum over `List.range r.recipients.length` of `fairShare`. Finally, constant and initial-segment indicator sums over a range evaluate the `amount / n` and `amount % n` parts, whose total is `r.amount` by `Nat.div_add_mod`, cancelling the debit.

```lean
theorem plan0_sumOver_erase_eq (l : List Nat) (f : Nat → Int) (a : Nat)
    (hl : l.Nodup) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f := by sorry

theorem plan0_sumOver_eq_of_subset_support (big small : List Nat) (f : Nat → Int)
    (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hzero : ∀ x ∈ big, x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by sorry

theorem plan0_sum_range_shift_succ (f : Nat → Int) (n : Nat) :
    f 0 + sumOver (List.range n) (fun i => f (i + 1))
      = sumOver (List.range (n + 1)) f := by sorry

theorem plan0_sumOver_indexOf_fairShare_offset (l : List Nat)
    (amount n offset : Nat) (hl : l.Nodup) :
    sumOver l (fun a => match indexOf? l a with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0)
      = sumOver (List.range l.length)
          (fun i => (fairShare amount n (offset + i) : Int)) := by sorry

theorem plan0_sum_range_const (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by sorry

theorem plan0_sum_range_if_lt (n m : Nat) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0)
      = ((min m n : Nat) : Int) := by sorry
```