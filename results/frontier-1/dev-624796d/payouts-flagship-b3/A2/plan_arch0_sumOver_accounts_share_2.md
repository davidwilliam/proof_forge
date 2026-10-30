(1) **Proof plan:** First prove that a sum over a duplicate-free list can be split using `List.erase`, then use induction with that split to transfer a sum from a large duplicate-free list to a duplicate-free sublist when the summand vanishes outside the sublist. Applied with the accounts as the large list and the recipients as the sublist, this reduces the goal to the recipient sum. Rewrite the recipient sum as a sum over `List.range` using the position of each recipient, evaluate the resulting `fairShare` range sum, and combine the equalities.

(2)
```lean
theorem plan2_sumOver_erase_add (l : List AccountId) (f : AccountId → Int)
    (hl : l.Nodup) (a : AccountId) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f := by sorry

theorem plan2_sumOver_subset_eq (big small : List AccountId) (f : AccountId → Int)
    (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hzero : ∀ x, x ∈ big → x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by sorry

theorem plan2_shareOf_int_eq_zero_of_not_mem (r : Request) (a : AccountId)
    (h : a ∉ r.recipients) :
    (shareOf r a : Int) = 0 := by sorry

theorem plan2_sumOver_recipients_eq_range (r : Request)
    (hnd : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by sorry

theorem plan2_fairShare_range_sum (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = (amount : Int) := by sorry

theorem plan2_sumOver_accounts_eq_recipients (s : State) (r : Request)
    (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => (shareOf r a : Int)) := by sorry
```