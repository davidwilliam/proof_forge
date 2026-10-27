Split `fairShare` into its constant quotient part and its one-cent indicator part. Summing the constant over `List.range n` gives `n * (amount / n)`, while summing the indicator counts exactly the first `amount % n` positions, i.e. `min n (amount % n) = amount % n` when `0 < n`. The usual division-modulo identity then recombines these into `amount`.

```lean
theorem plan1_sumOver_range_const (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by sorry

theorem plan1_sumOver_range_ite_min (n k : Nat) :
    sumOver (List.range n) (fun i => if i < k then (1 : Int) else 0) =
      ((Nat.min n k : Nat) : Int) := by sorry

theorem plan1_fairShare_cast (amount n i : Nat) :
    ((fairShare amount n i : Nat) : Int) =
      ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) := by sorry

theorem plan1_mul_div_add_mod_nat (amount n : Nat) :
    n * (amount / n) + amount % n = amount := by sorry

theorem plan1_mul_div_add_mod_int (amount n : Nat) :
    (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) =
      (amount : Int) := by sorry

theorem plan1_sumOver_range_fairShare_decomp (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int)) =
      (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) := by sorry
```