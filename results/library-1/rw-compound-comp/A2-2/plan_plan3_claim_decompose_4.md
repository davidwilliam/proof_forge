(1) Proof plan: unfold `claimComp` as a chain of `Option.bind`s. Eliminate a successful bind to obtain its intermediate state, twice for the borrow update/distribution pair and twice for the supply update/distribution pair. The first pair is definitionally the `borrowHook` call and the second pair, starting from the intermediate state, is definitionally the `supplyHook` call. Reassociating these binds therefore rewrites a successful claim as a successful borrow hook, then a successful supply hook, ending with `grantCompInternal`.

(2)
```lean
theorem plan4_bind_some_elim (o : Option St) (f : St → Option St) (y : St)
    (h : o.bind f = some y) :
    ∃ t, o = some t ∧ f t = some y := by sorry

theorem plan4_borrowHook_eq_bind (s : St) (who : Account) :
    comptroller s (.borrowHook who) =
      (updateCompBorrowIndex s).bind (fun s1 => distributeBorrowerComp s1 who) := by sorry

theorem plan4_supplyHook_eq_bind (s : St) (who : Account) :
    comptroller s (.supplyHook who) =
      (updateCompSupplyIndex s).bind (fun s1 => distributeSupplierComp s1 who) := by sorry

theorem plan4_claim_eq_hook_binds (s : St) (who : Account) :
    comptroller s (.claim who) =
      (comptroller s (.borrowHook who)).bind
        (fun m1 => (comptroller m1 (.supplyHook who)).bind
          (fun m2 => some (grantCompInternal m2 who))) := by sorry
```