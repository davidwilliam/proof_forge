## Proof plan

On a successful payout, rewrite every balance using `expectedBalance`. The account sum then splits into the original balance sum, a debit term, and the recipient-share term. The debit contributes exactly `r.amount` by `sumOver_ite_eq`, since the source belongs to the duplicate-free account list.

For the shares, first bound the sum of floor shares from both sides by multiplying by the total weight and cancelling that positive factor. This shows that the floor shares plus `leftover` equal the amount and that `leftover ≤ weights.length`. Consequently, summing `weightedShare` over all recipient positions gives exactly `r.amount`: the floor parts give the floor sum, and the first `leftover` positions contribute one additional cent each. Finally, reindex the share sum from recipient accounts to recipient positions using `indexOf?`, collapse the sum over all accounts to the sum over recipients, and combine the debit and credit sums by `omega`.

```lean
theorem plan0_floor_sum_mul_le (amount W : Nat) (ws : List Nat) :
    natSum (ws.map (floorShare amount W)) * W ≤ amount * natSum ws := by
  sorry

theorem plan0_amount_mul_le_floor_sum (amount W : Nat) (ws : List Nat)
    (hW : 0 < W) :
    amount * natSum ws ≤
      natSum (ws.map (floorShare amount W)) * W + ws.length * W := by
  sorry

theorem plan0_leftover_add_floor (amount : Nat) (ws : List Nat)
    (hW : 0 < natSum ws) :
    natSum (ws.map (floorShare amount (natSum ws))) + leftover amount ws = amount ∧
      leftover amount ws ≤ ws.length := by
  sorry

theorem plan0_weightedShare_range_sum (amount : Nat) (ws : List Nat)
    (hW : 0 < natSum ws) :
    natSum ((List.range ws.length).map (weightedShare amount ws)) = amount := by
  sorry

theorem plan0_sumOver_indexOf_offset (l : List AccountId) (amount : Nat)
    (ws : List Nat) (k : Nat) (hl : l.Nodup) :
    sumOver l
        (fun a => (weightedShare amount ws (k + (indexOf? l a).getD 0) : Int)) =
      ((natSum ((List.range l.length).map
        (fun i => weightedShare amount ws (k + i)))) : Int) := by
  sorry

theorem plan0_sumOver_eq_of_subset (big sub : List Nat) (f : Nat → Int)
    (hbig : big.Nodup) (hsubnd : sub.Nodup)
    (hsub : ∀ a ∈ sub, a ∈ big) (hzero : ∀ a, a ∉ sub → f a = 0) :
    sumOver big f = sumOver sub f := by
  sorry
```