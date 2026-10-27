**Proof plan.** In the valid case, `step` keeps `accounts` unchanged and replaces each balance by `expectedBalance`. Decompose that balance into the old balance, the source debit indicator, and `shareOf`. The key arithmetic fact is that the shares summed over the whole account universe equal `amount`: first rewrite one share as an indicator sum over recipients, swap the two `sumOver`s to pass from accounts to recipients, reindex recipients by `List.range` to obtain the `natSum` of `weightedShare`s, apply the already-established weighted-range sum to get `amount`, and finally cancel the source debit against the total shares in the summed `expectedBalance`.

```lean
theorem plan2_shareOf_eq_indicator_sum (r : Request) (hrec : r.recipients.Nodup)
    (a : AccountId) :
    (shareOf r a : Int) =
      sumOver r.recipients (fun x => if x = a then (shareOf r x : Int) else 0) := by sorry

theorem plan2_sumOver_accounts_share_eq_recipients (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) =
      sumOver r.recipients (fun a => (shareOf r a : Int)) := by sorry

theorem plan2_sumOver_recipients_share_eq_natSum (r : Request)
    (hrec : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) =
      ((natSum ((List.range r.recipients.length).map
        (weightedShare r.amount r.weights)) : Nat) : Int) := by sorry

theorem plan2_natSum_weighted_range_eq_amount (r : Request)
    (hne : r.recipients ≠ [])
    (hlen : r.weights.length = r.recipients.length)
    (hpos : ∀ w ∈ r.weights, 0 < w) :
    natSum ((List.range r.recipients.length).map
      (weightedShare r.amount r.weights)) = r.amount := by sorry

theorem plan2_sumOver_expectedBalance_eq (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hsrc : r.source ∈ s.accounts)
    (hshare : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int)) :
    sumOver s.accounts (fun a => expectedBalance s r a) =
      sumOver s.accounts s.balance := by sorry
```