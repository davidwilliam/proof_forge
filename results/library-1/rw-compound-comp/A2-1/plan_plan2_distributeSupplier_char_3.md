**Proof plan.** Unfold `distributeSupplierComp` and invert its `subChecked`: success gives `adjusted ≤ index` and `delta = index - adjusted`. The adjusted index is exactly `accrualStart` (the symmetric form of `plan2_accrualStart_adjusted`), giving the first conjunct. For the second, rewrite the successful branch via `withAcct = { … with accts := modify … }`, replace `mulDouble u (index - start)` by `creditFor u start index`, and finally replace the captured `(acct who).supply / .supplierIndex` inside the `modify` function by the fields of the modified element itself, using `snippet_modify_congr_test` since `St.acct who = accts.getD who noAcct` definitionally. This yields exactly the stated `modify` form.

```lean
theorem plan3_subChecked_some_inv (a b d : Nat) (h : subChecked a b = some d) :
    b ≤ a ∧ d = a - b := by sorry

theorem plan3_supplier_adjusted_eq_accrualStart (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by sorry

theorem plan3_mulDouble_eq_creditFor (units start index : Nat) :
    mulDouble units (index - start) = creditFor units start index := by sorry

theorem plan3_modify_supplier_credit (l : List Acct) (n idx : Nat) :
    l.modify n (fun a => { a with
        supplierIndex := idx,
        accrued := a.accrued + mulDouble (l.getD n noAcct).supply
          (idx - accrualStart (l.getD n noAcct).supplierIndex idx) }) =
    l.modify n (fun a => { a with
        supplierIndex := idx,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex idx) idx }) := by sorry

theorem plan3_withAcct_eq_modify (s : St) (who : Account) (f : Acct → Acct) :
    s.withAcct who f = { s with accts := s.accts.modify who f } := by sorry
```