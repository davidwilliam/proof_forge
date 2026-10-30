(1) Proof plan: First prove that, for a duplicate-free list, removing a member splits its sum as that member's value plus the sum over the erased list; induction on the smaller list then gives equality of sums whenever one duplicate-free list is contained in another and the function vanishes outside the smaller list. Separately, convert a sum over recipients to a sum over `List.range` of their indices using `shareOf` on each element, and evaluate the resulting `fairShare` sum to `amount` (the division part contributes `n * (amount / n)` and the indicator part contributes `amount % n`). Applying the subset lemma with accounts as the large list and recipients as the small list; shares are zero off the recipients; reduces the account sum to the recipient sum, hence to `amount`.

(2)
```lean
theorem plan3_sumOver_erase_add (l : List AccountId) (f : AccountId → Int)
    (hl : l.Nodup) (a : AccountId) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f := by sorry

theorem plan3_sumOver_subset_eq (big small : List AccountId) (f : AccountId → Int)
    (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hzero : ∀ x, x ∈ big → x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by sorry

theorem plan3_sumOver_list_eq_range {α : Type} (l : List α) (f : α → Int)
    (g : Nat → Int)
    (h : ∀ (i : Nat) (hi : i < l.length), f l[i] = g i) :
    sumOver l f = sumOver (List.range l.length) g := by sorry

theorem plan3_fairShare_range_sum (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = (amount : Int) := by sorry

theorem plan3_sumOver_recipients_share (r : Request)
    (hnd : r.recipients.Nodup) (hpos : 0 < r.recipients.length) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem plan3_sumOver_accounts_eq_recipients (s : State) (r : Request)
    (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => (shareOf r a : Int)) := by sorry
```