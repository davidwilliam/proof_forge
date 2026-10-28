If `step` grants, then `decision` is true, so the matching allows are nonempty and either there are no matching denies or the deepest deny is strictly shallower than the deepest allow. Taking an allow entry attaining the maximum allow depth gives a witness for `Permitted`: every matching deny lies in the filtered deny list, hence has depth at most the deny maximum, which is strictly below that witness.

```lean
theorem plan3_decision_true_parts (l : List Entry) (r : Request) (h : decision l r = true) :
    ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = false ∧
    (((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = true ∨
      maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) <
        maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow))) := by sorry

theorem plan3_exists_max_allow (l : List Entry) (r : Request) (h : decision l r = true) :
    ∃ a, a ∈ l ∧ Matches a r ∧ a.effect = .allow ∧
      a.path.length = maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) := by sorry

theorem plan3_deny_depth_lt_max_allow (l : List Entry) (r : Request) (h : decision l r = true)
    (a : Entry)
    (haMax : a.path.length = maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)))
    (d : Entry) (hdL : d ∈ l) (hdM : Matches d r) (hdE : d.effect = .deny) :
    depth d < depth a := by sorry

theorem plan3_permitted_of_decision_true (l : List Entry) (r : Request)
    (h : decision l r = true) : Permitted l r := by sorry

theorem plan3_permitted_of_granted (s : State) (r : Request)
    (h : (step s r).1 = .granted) : Permitted s.entries r := by sorry
```