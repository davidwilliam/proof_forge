**Proof plan**

If a check is denied, it is not permitted, since denial means `permittedB` is false. If there is no matching allow entry, the first disjunct holds. Otherwise, take a matching allow entry of maximal depth. Because the check is not permitted, this maximal allow cannot strictly dominate every deny, so some matching deny has depth at least that of the maximal allow. That deny therefore dominates every matching allow and establishes `Overridden`.

```lean
theorem plan0_exists_deny_ge_of_allow_not_permitted (l : List Entry) (r : Request) (a : Entry) (haMem : a ∈ l) (haMatch : Matches a r) (haAllow : a.effect = .allow) (hNot : ¬ Permitted l r) : ∃ d ∈ l, Matches d r ∧ d.effect = .deny ∧ depth a ≤ depth d := by sorry

theorem plan0_not_permitted_of_denied (s : State) (r : Request) (h : (step s r).1 = .denied) : ¬ Permitted s.entries r := by sorry

theorem plan0_overridden_of_hasAllow_not_permitted (l : List Entry) (r : Request) (hHas : HasAllow l r) (hNot : ¬ Permitted l r) : Overridden l r := by sorry

theorem plan0_denial_explained_of_denied (s : State) (r : Request) (h : (step s r).1 = .denied) : ¬ HasAllow s.entries r ∨ Overridden s.entries r := by sorry
```