**Proof plan**

Prove `plan2_run_invariant` by `run_induction` on the conjunction of cum-accounting, `nChildren = kids.length`, correctness of every stored child record, and the parent bound for every kid. The start case is by `simp`. Parent and ack steps are already handled by `plan2_invariant_parent_ack`. For a route step, the only new kid is appended as a singleton: old indices keep their old records, and the new index equals the old length, which matches the updated `children` at `nChildren` by the length invariant. For a fill step, cum/exec are already matched by `plan2_cum_fill_formula` and `plan2_exec_fill_formula`; the remaining work is purely list-level: a `List.set` either changes the filled index to the predictably updated record or leaves other indices unchanged, and it preserves length. The lemmas below isolate exactly those list facts, in dependency order, so the route/fill child-record cases become routine case splits.

```lean
theorem plan6_getElem_set_of_ne (l : List Kid) (k idx : Nat) (v : Kid)
    (h : idx ≠ k) : (l.set k v)[idx]? = l[idx]? := by sorry

theorem plan6_getElem_set_self (l : List Kid) (k : Nat) (v : Kid)
    (h : k < l.length) : (l.set k v)[k]? = some v := by sorry

theorem plan6_getElem_append_singleton_cases (l : List Kid) (kid : Kid)
    (idx : Nat) (c : Kid) (h : (l ++ [kid])[idx]? = some c) :
    (l[idx]? = some c) ∨ (idx = l.length ∧ c = kid) := by sorry

theorem plan6_observe_fill_length (t : Truth) (k q : Nat) :
    (t.observe (Event.fill k q)).kids.length = t.kids.length := by sorry

theorem plan6_fill_kids_cases (t : Truth) (k q idx : Nat) (c : Kid)
    (h : ((t.observe (Event.fill k q)).kids)[idx]? = some c) :
    (t.kids[idx]? = some c ∧ idx ≠ k) ∨
      (∃ c0 : Kid, t.kids[k]? = some c0 ∧ idx = k ∧
        c = { c0 with done := c0.done + min q (c0.qty - c0.done) }) := by sorry
```