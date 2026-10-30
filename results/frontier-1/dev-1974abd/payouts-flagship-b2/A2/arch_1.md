(1) Plan: Conservation is a single-step property, so no list invariant is needed. Shared facts are: an `ok` outcome implies validity (`arch0_valid_of_ok`), effects fix the account universe and balances (`req_effects`), and the expected balances sum to the original total (`arch0_sum_expected_eq`, packaged as `arch1_sum_expected_eq`). For `req_conservation`, rewrite the next state's total using the unchanged accounts, replace its balances pointwise with `expectedBalance` via `sumOver_congr`, then apply the summed-expected-balance identity.

(2)

```lean
theorem arch1_accounts_eq_of_ok (s : State) (r : Request)
    (hok : (step s r).1 = .ok) :
    (step s r).2.accounts = s.accounts := by sorry

theorem arch1_balance_eq_of_ok (s : State) (r : Request)
    (hok : (step s r).1 = .ok) :
    ∀ a, (step s r).2.balance a = expectedBalance s r a := by sorry

theorem arch1_sum_expected_eq (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = total s := by sorry

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv : ValidPayout s r := arch0_valid_of_ok s r hok
  have hacc : (step s r).2.accounts = s.accounts :=
    arch1_accounts_eq_of_ok s r hok
  have hbal : ∀ a, (step s r).2.balance a = expectedBalance s r a :=
    arch1_balance_eq_of_ok s r hok
  calc total (step s r).2
      = sumOver s.accounts (fun a => expectedBalance s r a) := by
        unfold total
        rw [hacc]
        exact sumOver_congr s.accounts (step s r).2.balance
          (fun a => expectedBalance s r a) (fun a _ => hbal a)
    _ = total s := arch1_sum_expected_eq s r hv
```