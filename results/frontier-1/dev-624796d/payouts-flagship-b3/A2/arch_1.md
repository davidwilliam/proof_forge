## Plan

A successful step must first be valid, via the already-proved `valid_of_ok_aux`. For a valid payout, the already-proved effect lemmas `req_effects_aux1` and `req_effects_aux3` show that the account list is unchanged and every new balance is `expectedBalance s r a`. Hence the new total can be rewritten as the sum of the expected balances over the original accounts. The already-proved `arch0_sumOver_accounts_expected` identifies that sum with the original total, giving conservation. The one new helper isolates the total-rewriting step; it follows by unfolding `total`, rewriting the accounts, and applying `sumOver_congr` to the pointwise balance equation.

```lean
theorem arch1_total_step_eq_sum_expected (s : State) (r : Request)
    (hV : ValidPayout s r) :
    total (step s r).2 = sumOver s.accounts (expectedBalance s r) := by sorry

theorem req_conservation   : Conserves step := by
  intro s r hok
  have hV : ValidPayout s r := valid_of_ok_aux s r hok
  rw [arch1_total_step_eq_sum_expected s r hV]
  exact arch0_sumOver_accounts_expected s r hV
```