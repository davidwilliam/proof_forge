(1) **Proof plan.** The obstruction is that, when peeling the head off `r.recipients`, every remaining recipient's `indexOf?` increases by one, while `fairShare` still uses the *original* list length. Direct induction on `recipients` therefore does not match. Generalize the induction with an offset `k`: prove that summing `g (k + i)` over a duplicate-free list, where `i` is taken from `indexOf?`, equals summing `g (k + i)` over `List.range l.length`. The head contributes `g k`, the tail is the same statement at `k+1`, and the range side is decomposed into its head plus a shifted tail. Finally specialize to `k = 0` and `g i = (fairShare r.amount r.recipients.length i : Int)`, and rewrite `shareOf` as exactly this match on `indexOf?`.

(2)
```lean
theorem plan2_indexOf_cons_head_apply (x : AccountId) (xs : List AccountId)
    (g : Nat → Int) (k : Nat) :
    (match indexOf? (x :: xs) x with
     | some i => g (k + i)
     | none => 0) = g k := by sorry

theorem plan2_indexOf_cons_tail_apply (x a : AccountId) (xs : List AccountId)
    (g : Nat → Int) (k : Nat) (h : x ≠ a) :
    (match indexOf? (x :: xs) a with
     | some i => g (k + i)
     | none => 0)
      = (match indexOf? xs a with
         | some i => g ((k + 1) + i)
         | none => 0) := by sorry

theorem plan2_sumOver_range_succ_head (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f
      = f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by sorry

theorem plan2_sumOver_indexOf_offset (l : List AccountId) (g : Nat → Int)
    (k : Nat) (hl : l.Nodup) :
    sumOver l (fun a => match indexOf? l a with
                          | some i => g (k + i)
                          | none => 0)
      = sumOver (List.range l.length) (fun i => g (k + i)) := by sorry

theorem plan2_shareOf_int_eq_match (r : Request) (a : AccountId) :
    (shareOf r a : Int)
      = (match indexOf? r.recipients a with
         | some i => (fairShare r.amount r.recipients.length i : Int)
         | none => 0) := by sorry
```