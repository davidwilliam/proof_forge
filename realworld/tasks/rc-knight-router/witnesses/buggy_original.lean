import Solution
/-!
Kernel-checked refutation of the reconstructed port (`attacks/buggy_original.lean`, the start
candidate), reconstructed from the SEC findings in Release No. 34-70694; not Knight's code.

The scenario: one parent order of 100 shares with the repurposed flag arrives at a server
that did not receive the new code (`Build.legacy`), followed by `n` rounds of a routing
opportunity for 100 shares and an execution report that fills the child order just sent.
On that server the port sends `n` child orders for the one parent, `100 * n` shares sent
and `100 * n` shares executed against an order for 100, for every `n`: the number of child
orders for a single parent order is unbounded. The same events on a server with the new
code send exactly one child order of 100 shares.
-/
open OrderRouter

/-- `n` rounds: a routing opportunity of 100 shares for parent 0, then an execution report
filling child order `k` (the one just sent) for 100 shares. -/
def rounds : Nat → List Event
  | 0 => []
  | n + 1 => rounds n ++ [.route 0 100, .fill n 100]

/-- One flagged 100-share parent order, then `n` rounds. -/
def flagged (n : Nat) : List Event := .parent 100 true :: rounds n

theorem flagged_succ (n : Nat) :
    flagged (n + 1) = (flagged n ++ [.route 0 100]) ++ [.fill n 100] := by
  simp [flagged, rounds]

theorem sentFor_replicate (n : Nat) (k : Kid) :
    sentFor (List.replicate n k) k.parent = k.qty * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih, Nat.mul_succ]; omega

theorem execFor_replicate (n : Nat) (k : Kid) :
    execFor (List.replicate n k) k.parent = k.done * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih, Nat.mul_succ]; omega

/-- What the run looks like after `n` rounds on the server without the new code. -/
structure Legacy (n : Nat) (x : Sys) : Prop where
  np    : x.st.nParents = 1
  p0    : x.st.parents 0 = ⟨100, true, 100 * n, 0⟩
  nc    : x.st.nChildren = n
  kids  : x.tr.kids = List.replicate n ⟨0, 100, 100⟩
  no    : x.tr.nOrders = 1
  q0    : x.tr.qty 0 = 100

theorem legacy_run (n : Nat) : Legacy n (run step .legacy (flagged n)) := by
  induction n with
  | zero =>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨np, p0, nc, kids, no, q0⟩ := ih
    rw [flagged_succ, run_snoc, run_snoc]
    generalize run step .legacy (flagged n) = x at *
    have hk : (x.tr.kids ++ [(⟨0, 100, 0⟩ : Kid)])[n]? = some ⟨0, 100, 0⟩ := by
      simp [kids]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [advance, step, powerPegPath, routePowerPeg, Truth.observe, Truth.record, upd, np, p0, nc, no,
        q0, hk, Nat.mul_succ]
    rw [kids, List.set_append_right _ _ (by simp)]
    simp [List.replicate_succ']

/-- On the server without the new code, `n` rounds send `n` child orders, `100 * n` shares,
and execute `100 * n` shares, for a 100-share parent order. -/
theorem legacy_unbounded (n : Nat) :
    (run step .legacy (flagged n)).tr.kids.length = n ∧
    (run step .legacy (flagged n)).tr.qty 0 = 100 ∧
    (run step .legacy (flagged n)).tr.sent 0 = 100 * n ∧
    (run step .legacy (flagged n)).tr.exec 0 = 100 * n := by
  obtain ⟨_, _, _, kids, _, q0⟩ := legacy_run n
  refine ⟨by simp [kids], q0, ?_, ?_⟩
  · simp only [Truth.sent, kids]; exact sentFor_replicate n ⟨0, 100, 100⟩
  · simp only [Truth.exec, kids]; exact execFor_replicate n ⟨0, 100, 100⟩

/-- For every bound there is an event sequence in which the router sends more child orders
than the bound for a single 100-share parent order. -/
theorem child_orders_unbounded (N : Nat) :
    ∃ evs, (run step .legacy evs).tr.qty 0 = 100 ∧
      N < (run step .legacy evs).tr.kids.length ∧
      (∀ k ∈ (run step .legacy evs).tr.kids, k.parent = 0) := by
  refine ⟨flagged (N + 1), (legacy_unbounded (N + 1)).2.1, by rw [(legacy_unbounded (N + 1)).1]; omega, ?_⟩
  rw [(legacy_run (N + 1)).kids]
  intro k hk
  rw [(List.mem_replicate.mp hk).2]

/-- What the run looks like after `n + 1` rounds on a server with the new code. -/
structure Rlp (x : Sys) : Prop where
  np    : x.st.nParents = 1
  p0    : x.st.parents 0 = ⟨100, true, 100, 100⟩
  nc    : x.st.nChildren = 1
  c0    : x.st.children 0 = ⟨0, 100, 100⟩
  kids  : x.tr.kids = [⟨0, 100, 100⟩]
  no    : x.tr.nOrders = 1
  q0    : x.tr.qty 0 = 100

theorem rlp_run (n : Nat) : Rlp (run step .rlp (flagged (n + 1))) := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨np, p0, nc, c0, kids, no, q0⟩ := ih
    rw [flagged_succ, run_snoc, run_snoc]
    generalize run step .rlp (flagged (n + 1)) = x at *
    have hn : ¬ n + 1 < 1 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [advance, step, powerPegPath, routeBySent, Truth.observe, Truth.record, np, p0, nc, c0,
        kids, no, q0]

/-- The same events on a server with the new code send exactly one child order of 100
shares. -/
theorem rlp_one_child (n : Nat) :
    (run step .rlp (flagged (n + 1))).tr.kids = [⟨0, 100, 100⟩] := (rlp_run n).kids

/-! ## The requirements the port breaks -/

theorem refutes_never_overroute : ¬ NeverOverroute step := by
  intro h
  have := h .legacy (flagged 2) 0
  rw [(legacy_unbounded 2).2.2.1, (legacy_unbounded 2).2.1] at this
  omega

theorem refutes_no_excess_execution : ¬ NoExcessExecution step := by
  intro h
  have := h .legacy (flagged 2) 0
  rw [(legacy_unbounded 2).2.2.2, (legacy_unbounded 2).2.1] at this
  omega

theorem refutes_stop_when_filled : ¬ StopWhenFilled step := by
  intro h
  have hfull : (run step .legacy (flagged 1)).tr.exec 0 = (run step .legacy (flagged 1)).tr.qty 0 := by
    rw [(legacy_unbounded 1).2.2.2, (legacy_unbounded 1).2.1]
  have := h .legacy (flagged 1) (.route 0 100) 0 hfull
  revert this
  decide

theorem refutes_fill_accounting : ¬ FillAccounting step := by
  intro h
  have := h .legacy (flagged 1) 0 (by decide)
  revert this
  decide

theorem refutes_normal_order_routed : ¬ NormalOrderRouted step := by
  intro h
  have := (h .legacy true).1
  revert this
  decide

theorem refutes_routes_available : ¬ RoutesAvailable step := by
  intro h
  have := h .legacy (flagged 1) 0 100
  revert this
  decide

/-! ## Eight servers, one without the new code (paragraphs 15 and 16) -/

/-- The deployment of August 1, 2012 as the order describes it: the new code on seven of the
eight servers, not on the eighth. -/
def aug1 (i : Fin 8) : Build := if i.val = 7 then .legacy else .rlp

theorem aug1_seven_servers (i : Fin 8) (hi : i.val < 7) (n : Nat) :
    (run step (aug1 i) (flagged (n + 1))).tr.kids = [⟨0, 100, 100⟩] := by
  have : aug1 i = .rlp := by simp [aug1]; omega
  rw [this]; exact rlp_one_child n

theorem aug1_eighth_server (n : Nat) :
    (run step (aug1 7) (flagged n)).tr.kids.length = n ∧
    (run step (aug1 7) (flagged n)).tr.sent 0 = 100 * n :=
  ⟨(legacy_unbounded n).1, (legacy_unbounded n).2.2.1⟩

/-- A concrete instance checked by evaluation (`decide`), independent of the induction above:
20 rounds on the eighth server send 20 child orders and 2,000 shares for a 100-share parent
order, and 2,000 shares are executed. -/
theorem eighth_server_20 :
    (run step (aug1 7) (flagged 20)).tr.kids.length = 20 ∧
    (run step (aug1 7) (flagged 20)).tr.sent 0 = 2000 ∧
    (run step (aug1 7) (flagged 20)).tr.exec 0 = 2000 := by
  decide
