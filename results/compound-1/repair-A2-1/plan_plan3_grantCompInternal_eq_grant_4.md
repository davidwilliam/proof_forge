Short proof plan: split on whether the accrued amount is positive and covered by the reserve. In the positive case, unfold both definitions; they differ only inside `List.modify`, where the candidate adds the globally fetched `amount` and the specification adds the modified account's own `a.accrued`. At the modified position these coincide because `s.acct who = s.accts.getD who noAcct`, so a modify-congruence lemma identifies the two lists. In the negative case both definitions return the state unchanged. Case analysis then proves `grantCompInternal s who = grant s who`.

```lean
theorem plan4_modify_wallet_amount (xs : List Acct) (who amount : Nat)
    (h : amount = (xs.getD who noAcct).accrued) :
    xs.modify who (fun a => { a with accrued := 0, wallet := a.wallet + amount }) =
      xs.modify who (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by sorry

theorem plan4_grantCompInternal_pos (s : St) (who : Account)
    (h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) :
    grantCompInternal s who =
      { s with
        reserve := s.reserve - (s.acct who).accrued,
        accts := s.accts.modify who fun a =>
          { a with accrued := 0, wallet := a.wallet + a.accrued } } := by sorry

theorem plan4_grant_pos (s : St) (who : Account)
    (h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) :
    grant s who =
      { s with
        reserve := s.reserve - (s.acct who).accrued,
        accts := s.accts.modify who fun a =>
          { a with accrued := 0, wallet := a.wallet + a.accrued } } := by sorry

theorem plan4_grantCompInternal_neg_and_grant_neg (s : St) (who : Account)
    (h : ¬ (0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve)) :
    grantCompInternal s who = s ∧ grant s who = s := by sorry
```