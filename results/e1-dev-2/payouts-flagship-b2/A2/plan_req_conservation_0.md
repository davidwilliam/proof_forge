**Proof plan.** On a successful step the accounts are unchanged and every balance is `expectedBalance`, so conservation is a sum over `s.accounts`. Decompose that sum into the old balances, a single debit of `amount` at the source (using nodup and `sumOver_ite_eq`), and the credits `shareOf r a`. The credits over all accounts equal the credits over the recipients: erase/additivity lets one restrict a sum to a nodup sublist outside which the function vanishes. Over the recipients, `shareOf` is `fairShare` at the recipient's index, so reindex by `List.range` and use `n * (amount / n) + amount % n = amount` to show the credits total exactly `amount`. The debit and credit cancel by `omega`. If the payout is invalid the step is the identity, so the final theorem follows by case split on `ValidPayout s r`.

```lean
theorem plan0_sumOver_erase_add (l : List AccountId) (f : AccountId → Int)
    (a : AccountId) (hl : l.Nodup) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (List.erase l a) f := by sorry

theorem plan0_sumOver_eq_of_subset (L : List AccountId) (hL : L.Nodup) :
    ∀ (R : List AccountId), R.Nodup → (∀ x ∈ R, x ∈ L) →
      ∀ f : AccountId → Int, (∀ x ∈ L, x ∉ R → f x = 0) →
        sumOver L f = sumOver R f := by sorry

theorem plan0_sumOver_range_succ (g : Nat → Int) (n : Nat) :
    sumOver (List.range (n + 1)) g
      = g 0 + sumOver (List.range n) (fun i => g (i + 1)) := by sorry

theorem plan0_sumOver_indexOf_eq_range (l : List AccountId) (hl : l.Nodup) :
    ∀ g : Nat → Int,
      sumOver l (fun a => match indexOf? l a with
        | some i => g i
        | none => 0)
      = sumOver (List.range l.length) g := by sorry

theorem plan0_sumOver_range_fair (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int))
      = (amount : Int) := by sorry

theorem plan0_sumOver_expectedBalance_eq (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance := by sorry
```