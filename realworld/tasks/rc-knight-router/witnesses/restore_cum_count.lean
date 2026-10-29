import Solution
/-!
Kernel-checked refutation of `attacks/restore_cum_count.lean`, the obvious repair of the
reconstructed port: execution reports advance the cumulative quantity on every path again,
and the Power Peg path still decides from it whether to send another child order.
Reconstructed from the SEC findings in Release No. 34-70694; not Knight's code.

Two routing opportunities for a flagged 100-share parent order arrive on the legacy build
before any execution report. Nothing has executed, so the cumulative quantity is 0 both
times, and the router sends two child orders of 100 shares: 200 shares for a 100-share
order. Counting executions bounds the shares executed only after they are reported; the
shares sent are bounded only by counting what was sent.
-/
open OrderRouter

def twoRoutes : List Event := [.parent 100 true, .route 0 100, .route 0 100]

theorem two_child_orders :
    (run step .legacy twoRoutes).tr.kids = [⟨0, 100, 0⟩, ⟨0, 100, 0⟩] ∧
    (run step .legacy twoRoutes).tr.sent 0 = 200 ∧
    (run step .legacy twoRoutes).tr.qty 0 = 100 := by
  decide

theorem refutes_never_overroute : ¬ NeverOverroute step := by
  intro h
  have := h .legacy twoRoutes 0
  rw [two_child_orders.2.1, two_child_orders.2.2] at this
  omega

/-- When both child orders are then executed in full, 200 shares are executed for the
100-share order. -/
theorem refutes_no_excess_execution : ¬ NoExcessExecution step := by
  intro h
  have := h .legacy (twoRoutes ++ [.fill 0 100, .fill 1 100]) 0
  revert this
  decide

/-- The same events on the rlp build send one child order. -/
theorem rlp_one_child : (run step .rlp twoRoutes).tr.kids = [⟨0, 100, 0⟩] := by
  decide
