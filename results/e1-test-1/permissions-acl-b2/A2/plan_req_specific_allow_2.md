If a permitted allow `a` exists, its filtered allow-list is nonempty, so the allow depth maximum is at least `depth a`. Every matching deny is shallower than `a`: either `depth a = 0`, forcing the deny list to be empty, or `depth a > 0`, forcing the deny depth maximum to be below the allow depth maximum. Hence `decision` returns `true`, and a valid query is then granted by `step`.

```lean
theorem plan2_allows_not_empty_of_permitted (l : List Entry) (r : Request)
    (h : Permitted l r) :
    ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = false := by sorry

theorem plan2_denies_empty_or_lt_of_permitted (l : List Entry) (r : Request)
    (h : Permitted l r) :
    ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = true ∨
      maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) <
        maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) := by sorry

theorem plan2_decision_true_of_permitted (l : List Entry) (r : Request)
    (h : Permitted l r) : decision l r = true := by sorry

theorem plan2_step_granted_of_permitted (s : State) (r : Request)
    (hv : ValidQuery s r) (h : Permitted s.entries r) :
    (step s r).1 = .granted := by sorry
```