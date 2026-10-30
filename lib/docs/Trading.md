# ProofForgeFin.Trading

`ProofForgeFin.Trading` covers the software of traditional market infrastructure: order
management, child-order routing, a limit order book, pre-trade risk controls, position keeping,
and settlement netting. Each part fixes a model in the shape task specifications use: a state, a
step, and facts computed from the events. It then proves the requirements a rulebook or a
supervisor states, over every sequence of events.

The area has 8 modules with 296 theorems and 139 definitions (structures, inductives and
instances included), plus 3 demonstrations with 40 theorems. Everything depends only on the
Lean core library and on `ProofForgeFin.Seq` and `ProofForgeFin.Ledger`. Every declaration has a
doc string, the build emits no warning with `linter.missingDocs`, and every theorem uses only
`propext`, `Classical.choice` and `Quot.sound`.

Prices and quantities are `Nat` in the smallest unit (ticks, lots, shares, cents). Cash and
profit and loss are `Int`. Every bound is exact: it uses cross-multiplication, never division.

Statements below are quoted from the sources. Implicit variables are elided where the module
fixes them in a `variable` line.

## Contents

### `ProofForgeFin.Trading.Basic`: sides and prices

`Side` is `buy | sell`, and `Side.opp` is the other side. `s.le p q` means price `p` is at least
as good as `q` for orders of side `s`: for bids `q ≤ p`, for asks `p ≤ q`. `s.lt` is the strict
form. `Crosses s limit px := s.le limit px` is the condition for an incoming order of side `s`
to trade at a resting price `px`. `Side.sign` is `+1` or `-1`. The module also has the order
lemmas: `le_trans`, `lt_of_lt_of_le`, `not_lt_iff_le`, `le_total`, `le_antisymm`, `le_opp`.

### `ProofForgeFin.Trading.Orders`: one order under fills, cancels and replaces

`Order` has fields `qty`, `filled` (FIX `CumQty`) and `canceled`, and `leaves = qty - filled`
(FIX `LeavesQty`). `fill o q` executes `fillAmt o q`, which is `min q leaves`, or nothing on a
canceled order. `cancel` cancels. `replace o q` sets the quantity to `max q filled` on an open
order and leaves a closed one unchanged. `Wf o` is `filled ≤ qty`. `Closed o` is
`canceled ∨ qty ≤ filled`.

* `run_wf : o.Wf → (run apply o es).Wf`: no sequence of fill reports, cancels and replaces
  (duplicate and oversized reports included) fills an order beyond its quantity.
  `leaves_add_filled : o.Wf → o.leaves + o.filled = o.qty`.
* `fill_of_closed : o.Closed → o.fill q = o` and
  `filled_run_of_closed : o.Closed → (run apply o es).filled = o.filled`: there is no fill
  after a full fill or a cancel, over any later sequence of events.
* `fillAmt_of_le`, `fillAmt_of_ge`, `leaves_fill`, `fill_full_iff`, `filled_le_run` (the
  filled quantity never decreases), `filled_run_le` (it is at most the start plus the reported
  quantities).
* Execution report identifiers (FIX `ExecID`): `Tracked.report` ignores a report whose
  identifier was already applied. `report_report` says applying a report twice is applying it
  once. `run_replay : run report (run report t rs) rs = run report t rs` says replaying a whole
  stream after a reconnect (FIX `PossDupFlag`) changes nothing. `run_append_dups` covers any
  suffix that repeats earlier reports.

### `ProofForgeFin.Trading.Router`: child orders and router accounting

* `sumFor key f l id`: the sum of `f` over the records of `l` whose key is `id`, for any record
  type. It has lemmas for `append`, `List.set` (`sumFor_set`, `sumFor_set_eq`,
  `sumFor_set_add`), `map`, pointwise bounds (`sumFor_le_sumFor`), and absent keys
  (`sumFor_eq_zero_of_forall_ne`). A specification with its own child-order structure
  identifies its sums with `sumFor` by a three-line induction.
* `table f n`: entries `0 .. n-1` of a function table, as a list.
  `table_upd_succ : table (upd f n v) (n + 1) = table f n ++ [v]` and
  `set_table : k < n → (table f n).set k v = table (upd f k v) n` cover the two ways a router
  that stores child records in a function changes them. `table_comp_upd_succ` and
  `set_table_comp` cover a table read through a projection.
* The venue model: `Child` has `parent`, `qty` and `done`. `sent l id` and `executed l id` sum
  per parent. `execute l k q` executes `min q (qty - done)` of child `k` and nothing for an
  unknown `k`. `send` appends fresh children.
  `run_executed_le_sent : executed (run venueStep [] es) id ≤ sent (run venueStep [] es) id`
  holds over every sequence of sends and reports.
* Routing arithmetic: `routeQty liq qty sent := min liq (qty - sent)`.
  `add_routeQty_le : sent ≤ qty → sent + routeQty liq qty sent ≤ qty` is never-overroute.
  `routeQty_eq_zero_of_filled : exec ≤ sent → sent ≤ qty → exec = qty → routeQty liq qty sent = 0`
  is stop-when-filled.
* Accounting: `Counts key f ctr l` says `∀ id, ctr id = sumFor key f l id`. A router's counter
  takes one of these steps: `Counts.append_one`, `Counts.append_zero`, `Counts.set_add`,
  `Counts.set_eq`, `Counts.upd_zero` (a new parent) or `Counts.congr`. `Counts.execute` is the
  cumulative quantity function kept right: the parent's counter advances by what the venue
  executed. `reported_count_overcounts` shows that adding the reported quantity instead reads
  200 after a duplicate report on a 100-share child.

### `ProofForgeFin.Trading.RouterModel`: a router with its requirements proved

This module states the model of `rc-knight-router` over the venue model above. Events are
`parent qty tag`, `route id liq`, `fill k q` and `other`. `Facts` are computed by
`Facts.observe` and `Facts.record` and never by the router. The router state is `RState`, with
function tables and counters. `step` is the router. For every tag type and every event sequence
`evs`, writing `x := run advance (start d) evs`:

* `route_out : (step x.st (.route id liq)).2 = expectedRoute x.tr id liq`
* `sent_le_qty : sent x.tr.kids id ≤ x.tr.qty id`
* `executed_le_qty' : executed x.tr.kids id ≤ x.tr.qty id`
* `stop_when_filled : executed x.tr.kids id = x.tr.qty id → ∀ o ∈ (step x.st e).2, o.1 ≠ id`
* `cum_eq_executed : (x.st.parents id).cum = executed x.tr.kids id`

A specification proves the same requirements for its own types by defining its router through
`step` and proving a per-event commutation of its run with `run advance`.

### `ProofForgeFin.Trading.Book`: limit order book

* Price-time priority on any element type with a price key. `Sorted s key l` is
  `l.Pairwise (fun a b => s.le (key a) (key b))`. `insertBy s key x l` inserts after every
  element at least as good as `x`.
  * `insertBy_split : Sorted s key l → ∃ l₁ l₂, l = l₁ ++ l₂ ∧ insertBy s key x l = l₁ ++ x :: l₂ ∧ (∀ y ∈ l₁, s.le (key y) (key x)) ∧ (∀ y ∈ l₂, s.lt (key x) (key y))`
  * `sorted_insertBy`, `perm_insertBy`, `length_insertBy`
  * `level_insertBy_self : Sorted s key l → level key (key x) (insertBy s key x l) = level key (key x) l ++ [x]`:
    at one price level the new order is served after every order already there.
  * `level_insert_at`, `level_remove_at`, `level_head`: the FIFO bookkeeping of one insert and
    one removal.
* `flow_runOut`: if `F (items s) ++ F (inflow of a step) = F (outflow of the step) ++ F (items after)`
  holds for every step, it holds for every run, for any `F` that distributes over `++`. This is
  the FIFO argument of a queue, and of a priority class with `F := level key p`.
* Matching. `matchOrder s stp owner limit q book` walks the opposite side from the best order
  with partial fills over several levels. Self-trade prevention `Stp` is `off`,
  `cancelResting` or `cancelIncoming`. The result has `trades`, `rest`, `book`, `canceled` and
  `killed`.
  * `matchOrder_traded_add_rest : traded m.trades + m.rest = q`
  * `matchOrder_traded_add_total : traded m.trades + total m.book + total m.canceled = total book`
  * `matchOrder_price : ∀ t ∈ m.trades, Crosses s limit t.px` (no trade worse than the limit);
    `matchOrder_maker` (each trade is at the maker's price, for at most its open quantity)
  * `matchOrder_no_self_trade : stp ≠ .off → ∀ t ∈ m.trades, t.makerOwner ≠ t.takerOwner`
  * `matchOrder_sorted`, `matchOrder_live`, and `matchOrder_stop`: with a rest left and no STP
    cancel, no remaining resting order crosses the limit.
  * `matchOrder_shape`: the book is `pre ++ post`, and the trades consume `pre` in order.
    `matchOrder_priority : (book.map Resting.id).Nodup → book = l₁ ++ r :: l₂ → (∃ t ∈ m.trades, t.maker = r.id) → ∀ y ∈ l₁, y ∈ m.canceled ∨ toTrade owner y y.qty ∈ m.trades`
    says an order trades only after every order ahead of it was filled in full or canceled by
    self-trade prevention.
* The book. `Book` has `bids` and `asks`. `submit` matches, then rests the remainder with
  `insertBy` unless the order is IOC or was canceled by self-trade prevention. `cancel` removes
  an order by id. `Wf` means both sides are sorted, quantities are positive, and the book is
  uncrossed (every bid below every ask).
  * `wf_run : Wf b → Wf (Seq.run (step stp) b ops)` holds over every sequence of submits and
    cancels.
  * `submit_conserves`, `submit_price`, `submit_no_self_trade`, `submit_traded_le`

### `ProofForgeFin.Trading.Risk`: pre-trade risk gateway

The gateway applies five checks: quantity (`QtyOk`), notional (`NotionalOk`), a price collar in
basis points around a reference price (`CollarOk`, cross-multiplied), duplicate client order id,
and aggregate credit (`CreditOk`). Exposure is the executed notional plus `leaves * px` over the
open orders. Events are submit, fill (capped at leaves, unknown id ignored), cancel, kill
(cancels every open order) and reset.

* `check_eq_none_iff : check L s o = none ↔ s.killed = false ∧ o.id ∉ s.seen ∧ QtyOk L o ∧ NotionalOk L o ∧ CollarOk L o ∧ CreditOk L s o`;
  `check_eq_some`: every reject reason names a check that failed.
* `exposure_fill : exposure (step L s (.fill id q)) = exposure s`; `exposure_cancel_le`.
* `run_exposure_le : exposure s ≤ L.credit → exposure (run (step L) s evs) ≤ L.credit` holds
  over every sequence of orders, fills, cancels, kills and resets.
* `run_sent_of_killed : (∀ e ∈ evs, e ≠ .reset) → (run (step L) (step L s .kill) evs).sent = s.sent ∧ (…).orders = [] ∧ (…).killed = true`:
  after the kill switch no order passes until a reset.
* `run_sent_checked`: every forwarded order passed the per-order checks, and no two forwarded
  orders share a client order id.
* `run_le_of_gate`: if operations that may raise a quantity are admitted only when the result
  is within the bound, and the other operations do not raise it, the bound holds over every
  run. `run_skip_le_of_gate` is the version for partial steps.

### `ProofForgeFin.Trading.Position`: positions and P&L

`Pos` has a side, a `Nat` quantity, a `Nat` cost basis, `Int` cash and `Int` realized P&L. A
fill opens, adds to, reduces or flips the position. On a reduce, the remaining cost is
`cost * (qty - k) / qty` rounded down.

* `signedQty_run : signedQty (run apply p fs) = signedQty p + sumOver fs Fill.signedQty`;
  `cash_run : (run apply p fs).cash = p.cash + sumOver fs Fill.cashFlow`.
* `pnl_conservation : pnl (run apply p fs) mark - ((run apply p fs).cash + signedQty (run apply p fs) * mark) = pnl p mark - (p.cash + signedQty p * mark)`
  and, from flat,
  `pnl_flat : (run apply Pos.flat fs).realized + unrealized (run apply Pos.flat fs) mark = (run apply Pos.flat fs).cash + signedQty (run apply Pos.flat fs) * mark`.
  Rounding the cost basis moves P&L between realized and unrealized and never creates or
  destroys it.
* `removedCost_spec : 0 < qty → k ≤ qty → cost * k ≤ removedCost cost qty k * qty ∧ removedCost cost qty k * qty < cost * k + qty`;
  `realized_reduce`; `avgDown_spec` and `avgUp_spec`.
* `run_inRange : InRange lo hi p → (∀ f ∈ fs, lo ≤ f.px ∧ f.px ≤ hi) → InRange lo hi (run apply p fs)`
  and `avg_mem_range : InRange lo hi p → 0 < p.qty → lo ≤ avgDown p ∧ avgDown p ≤ avgUp p ∧ avgUp p ≤ hi`:
  the average cost stays within the range of fill prices.
* `round_trip`; `round_trip_same : run apply Pos.flat [⟨.buy, q, px⟩, ⟨.sell, q, px⟩] = Pos.flat`.

### `ProofForgeFin.Trading.Netting`: settlement netting

`netOf ms k` is the net amount party `k` receives over the obligations `ms` (`Ledger.Move`).

* `applyMoves_eq_add_netOf : applyMoves bal ms k = bal k + netOf ms k`: gross settlement in
  any order equals net settlement, account by account, with no hypothesis.
* `sumOver_netOf : l.Nodup → (∀ m ∈ ms, m.src ∈ l ∧ m.dst ∈ l) → sumOver l (netOf ms) = 0`
* `sumOver_pos_netOf_le : l.Nodup → (∀ m ∈ ms, 0 ≤ m.amount) → sumOver l (fun k => pos (netOf ms k)) ≤ gross ms`;
  `sumOver_pos_eq_sumOver_neg`.
* Central counterparty: `applyMoves_ccpMoves` gives every party its gross-settlement balance
  with one instruction per party. `applyMoves_ccpMoves_ccp` leaves the counterparty flat.
* Delivery versus payment for trades (buyer, seller, qty, px): `netCash_eq`, `netSec_eq`,
  `sumOver_netCash`, `sumOver_netSec`, `applyMoves_cash`, `applyMoves_sec`.

## What each part models

| Part | Real systems and rules |
|---|---|
| `Orders` | FIX order state: `OrderQty`, `CumQty`, `LeavesQty`, `OrdStatus` filled or canceled, `OrderCancelReplaceRequest` (a quantity below `CumQty` leaves the order done), `ExecID` and `PossDupFlag` resend handling in OMS and EMS order books |
| `Router`, `RouterModel` | Smart order routers that slice a parent order into child orders as liquidity appears. The requirements are the ones the SEC order against Knight Capital (Release No. 34-70694, 2013) finds were missing: stop routing once the parent is filled, never send or execute more than the parent quantity, keep the cumulative executed quantity equal to the executions received |
| `Book` | Central limit order books with price-time priority (the matching rules of Nasdaq, NYSE Arca, Eurex, LSE and the FIFO products of CME Globex). Self-trade prevention modes in the style of CME (cancel oldest, cancel newest) and Nasdaq. IOC time in force |
| `Risk` | SEC Rule 15c3-5 (Market Access Rule) pre-trade controls: credit or capital thresholds in the aggregate, price and size parameters order by order, duplicative orders. FINRA and exchange kill switches |
| `Position` | Average cost position keeping and P&L in OMS, PMS and broker back offices: realized and unrealized P&L, mark to market |
| `Netting` | Multilateral netting at clearing houses and CSDs (NSCC CNS, LCH, DTC). CCP novation into one instruction per party. Delivery versus payment |

## Demonstrations

`ProofForgeFinDemo.Trading` re-proves the requirements of three tasks over definitions copied
verbatim, doc strings included, from their `Spec.lean`. No task file is imported or modified.
Sizes are non-blank lines from the implementation (`def step`, or the instance before it) to the
end of the file, for both the task's reference solution and the demonstration.

| Task | Requirements | Reference `SolutionA.lean` | Library-based demonstration |
|---|---|---|---|
| `realworld/tasks/rc-knight-router` | all 6 | 185 (24 router, 161 proof), using the task's 110-line `spec/OrderRouter/Lemmas.lean` | 96 (24 state and event maps and router, 72 proof), using no task lemma |
| `tasks/queues-prio-b3` (spec identical to `b1`) | all 8 | 195 | 103 |
| `tasks/queues-bounded-b3` | all 6 | 69 | 69 |

* `KnightRouter.lean` defines the router as `RouterModel.step` on the task's state. It maps the
  task's state, events and facts onto the library's (`toAbs`, `toEv`, `toFacts`) and proves
  `run_eq : toSys (run step b evs) = Seq.run RouterModel.advance (RouterModel.start false) (evs.map toEv)`
  by a per-event commutation (`advance_eq`). Each requirement is then one library theorem read
  through the maps: `route_out`, `sent_le_qty`, `stop_when_filled`, `executed_le_qty'`,
  `cum_eq_executed`. REQ-NORMAL-ORDER-ROUTED stays a `decide`. The reference proof's
  seven-field invariant and its event-by-event preservation proof are in the library once
  (`RouterModel.inv_advance`).
* `PrioQueue.lean`: the task's `Sorted` is `Book.Sorted .sell Entry.prio` and its `classOf p`
  is `Book.level Entry.prio p`, both by `rfl`. Insertion is `Book.insertBy`, and REQ-FIFO-TIES
  is `Book.flow_runOut` with `F := classOf p`. The library replaces the reference's `ins_split`,
  `length_ins`, `sorted_insert_at`, `class_insert_at`, `class_pop_at`, `ties_of_flow` and
  `flow_of_effects`.
* `BoundedQueue.lean`: REQ-FIFO is `Book.flow_runOut` with `F := id`. The proof is no shorter:
  the library replaces only a six-line induction, and the demonstration adds `run_eq` and a
  small helper.

## Audit

`lib/Audit.lean` covers every constant of the area through the `ProofForgeFin` and
`ProofForgeFinDemo` roots. In the pinned image, after this area was added:

```
axioms used: [Classical.choice, Quot.sound, propext]
audit: 3470 constants, 1073 theorems, 0 violations
```

`tests/test_fin_lib.py` passes (escape-hatch scan, build with no warning, clean audit, probe
detection).

## Limits

* Orders: one order at a time. Order types (stop, peg), time in force other than IOC, and
  amendments of price are not modeled. A fill report is capped at the leaves quantity, which is
  what an OMS records. A venue's overfill is not represented as a fact distinct from the
  order's state, except in the router's venue model.
* Router: one venue model with child orders addressed by position. There are no cancels of
  child orders, no venue rejects and no latency or in-flight quantity. `RouterModel.step` is one
  router: other routing policies satisfy `add_routeQty_le` and the `Counts` lemmas, but they get
  the requirement theorems only by their own invariant proof.
* Book: limit orders with optional IOC only. Market orders are limit orders at the worst price.
  Not modeled: hidden and iceberg quantity, minimum quantity, auctions, pro-rata or
  size-priority matching (some futures and options books), amend that keeps priority, and
  cancel-both self-trade prevention.
* Risk: exposure is gross. Executed notional never decreases, there is no settlement or
  intraday release, and buys and sells do not offset. Fills are capped at the gateway's leaves.
  Limits over a period of time (order rate, message throttles) are not modeled.
* Position: one instrument, no fees, commissions or currency conversion, and only the floor
  rounding of the remaining cost on a reduce. `Int` floor and ceiling rounding is not used.
* Netting: no net debit caps, no collateral, no settlement failure or partial settlement, no
  multi-currency netting.
* Candidates may import the library; the task projects are unchanged (see `lib/README.md`,
  Integration). The demonstrations are separate re-proofs, not accepted task
  solutions.
