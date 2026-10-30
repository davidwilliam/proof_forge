(1) **Proof plan:** `ValidPayout` already contains the two facts needed for the indicator sum: `s.accounts.Nodup` and `r.source ∈ s.accounts`. Extract these separately. Then prove, for any duplicate-free list, that summing `if a = x then c else 0` over the list gives `c` when `x` is a member; this follows from `sumOver_ite_eq` by simplifying the membership case, or directly by induction. Specialising to `c = (r.amount : Int)` yields `arch0_sum_deduction` immediately.

(2)
```lean
theorem plan0_accounts_nodup_of_valid (s : State) (r : Request) :
    ValidPayout s r → s.accounts.Nodup := by sorry

theorem plan0_source_mem_of_valid (s : State) (r : Request) :
    ValidPayout s r → r.source ∈ s.accounts := by sorry

theorem plan0_sumOver_ite_eq_of_mem {l : List AccountId} (hl : l.Nodup)
    {x : AccountId} (hx : x ∈ l) (c : Int) :
    sumOver l (fun a => if a = x then c else 0) = c := by sorry

theorem plan0_sum_deduction_of_components {l : List AccountId}
    (hl : l.Nodup) {source : AccountId} (hsrc : source ∈ l) (amount : Nat) :
    sumOver l (fun a => if a = source then (amount : Int) else 0)
      = (amount : Int) := by sorry
```