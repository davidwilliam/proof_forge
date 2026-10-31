**Proof plan.** `grantCompInternal` captures `amount = (s.acct who).accrued`, whereas the specification's `grant` uses `a.accrued` inside the `List.modify` function. These functions agree on the account actually stored at `who`, since `St.acct` is definitionally `getD`; hence the modified account lists and the paid branches are equal. The conditions `amount > 0` and `0 < amount` are also definitionally the same, so unfolding both definitions and performing case analysis on that condition finishes the proof.

```lean
theorem plan8_modify_grant_wallet_eq (s : St) (who : Account) :
    s.accts.modify who
        (fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }) =
    s.accts.modify who
        (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by sorry

theorem plan8_grant_branch_eq (s : St) (who : Account) :
    { s with
      reserve := s.reserve - (s.acct who).accrued,
      accts := s.accts.modify who
        fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } } =
    { s with
      reserve := s.reserve - (s.acct who).accrued,
      accts := s.accts.modify who
        fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } } := by sorry

theorem plan8_grantCompInternal_eq_if (s : St) (who : Account) :
    grantCompInternal s who =
      if 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve then
        { s with
          reserve := s.reserve - (s.acct who).accrued,
          accts := s.accts.modify who
            fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } }
      else s := by sorry

theorem plan8_grant_eq_if (s : St) (who : Account) :
    grant s who =
      if 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve then
        { s with
          reserve := s.reserve - (s.acct who).accrued,
          accts := s.accts.modify who
            fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
      else s := by sorry
```