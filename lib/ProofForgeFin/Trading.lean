import ProofForgeFin.Trading.Basic
import ProofForgeFin.Trading.Orders
import ProofForgeFin.Trading.Router
import ProofForgeFin.Trading.RouterModel
import ProofForgeFin.Trading.Book
import ProofForgeFin.Trading.Risk
import ProofForgeFin.Trading.Position
import ProofForgeFin.Trading.Netting
/-!
# Trading systems

Proved models and lemmas for the software of traditional market infrastructure: order
management, routing, matching, pre-trade risk, position keeping and settlement. Prices and
quantities are natural numbers in the smallest unit; cash and profit and loss are integers.

* `ProofForgeFin.Trading.Basic`: sides, price comparisons from either side, the crossing
  condition.
* `ProofForgeFin.Trading.Orders`: one order's quantity, cumulative filled and leaves quantity
  under fill reports (duplicate and oversized included), cancels and cancel/replace; execution
  report identifiers and replayed report streams.
* `ProofForgeFin.Trading.Router`: per-key sums over records, function tables as lists, the
  venue model of child orders, routing arithmetic (never overroute, stop when filled) and the
  agreement of a router's counters with what the venues executed.
* `ProofForgeFin.Trading.RouterModel`: a parent and child order router with every requirement of
  `rc-knight-router` proved over every sequence of events.
* `ProofForgeFin.Trading.Book`: a limit order book with price-time priority, matching with
  partial fills over several levels and self-trade prevention, sortedness, uncrossing,
  conservation and priority; insertion with time priority and FIFO flow for queues.
* `ProofForgeFin.Trading.Risk`: a pre-trade risk gateway of the SEC Rule 15c3-5 kind (size,
  notional, price collar, duplicate, aggregate credit, kill switch).
* `ProofForgeFin.Trading.Position`: positions, average cost with rounding, realized and
  unrealized P&L and their conservation.
* `ProofForgeFin.Trading.Netting`: multilateral netting, settlement through a central
  counterparty, delivery versus payment.
-/
