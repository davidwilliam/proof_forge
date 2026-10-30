import ProofForgeFin.Seq
/-!
# Orders and fills

The state of one order as an order management system or an exchange keeps it: the order
quantity, the cumulative filled quantity (FIX `CumQty`), the leaves quantity (FIX `LeavesQty`,
`qty - filled`) and whether the order was canceled. Fill reports, cancels and cancel/replace
requests are applied to it in order.

* `Order.fill o q` applies a fill report of `q`: it executes at most the leaves quantity, so an
  oversized report executes only the rest, and a report against a canceled or completely filled
  order executes nothing. `Order.fillAmt o q` is the quantity it executes.
* `Order.cancel` cancels; `Order.replace o q` changes the order quantity to `q`, never below the
  filled quantity (a replace below `CumQty` leaves the order filled in full, as FIX specifies).
* `Order.Wf o`: `filled ≤ qty`. Every event preserves it, so it holds after any sequence.
* `Order.Closed o`: the order is canceled or filled in full. A closed order stays closed and no
  later event fills it.

Execution reports carry an identifier (FIX `ExecID`); `Tracked` keeps the identifiers already
applied and ignores a report whose identifier was seen. A report stream replayed after a
reconnect (FIX `PossDupFlag`) is then harmless: `Tracked.run_replay` states that replaying the
whole stream again changes nothing.
-/

namespace ProofForgeFin.Trading.Orders

open ProofForgeFin.Seq

/-- One order: its quantity, the quantity filled so far and whether it was canceled. -/
structure Order where
  /-- The order quantity (FIX `OrderQty`). -/
  qty : Nat
  /-- The cumulative filled quantity (FIX `CumQty`). -/
  filled : Nat
  /-- Whether the order was canceled. -/
  canceled : Bool
  deriving DecidableEq, Repr

namespace Order

/-- A new order of quantity `q`: nothing filled, not canceled. -/
def new (q : Nat) : Order := ⟨q, 0, false⟩

/-- The leaves quantity: the quantity still open for execution (FIX `LeavesQty`). -/
def leaves (o : Order) : Nat := o.qty - o.filled

/-- The order is well formed: it is not filled beyond its quantity. -/
def Wf (o : Order) : Prop := o.filled ≤ o.qty

/-- The order is closed: canceled, or filled in full. -/
def Closed (o : Order) : Prop := o.canceled = true ∨ o.qty ≤ o.filled

/-- Well-formedness of an order is decidable. -/
instance (o : Order) : Decidable o.Wf := by unfold Wf; infer_instance

/-- Whether an order is closed is decidable. -/
instance (o : Order) : Decidable o.Closed := by unfold Closed; infer_instance

/-- The quantity a fill report of `q` executes: the report capped at the leaves quantity, and
nothing on a canceled order. -/
def fillAmt (o : Order) (q : Nat) : Nat := if o.canceled then 0 else min q o.leaves

/-- Apply a fill report of `q`. -/
def fill (o : Order) (q : Nat) : Order := { o with filled := o.filled + o.fillAmt q }

/-- Cancel the order. The filled quantity stays; the leaves quantity no longer executes. -/
def cancel (o : Order) : Order := { o with canceled := true }

/-- A cancel/replace request changing the order quantity to `q`. The new quantity is never
below the filled quantity; a closed order (canceled or filled in full) is not changed. -/
def replace (o : Order) (q : Nat) : Order := if o.Closed then o else { o with qty := max q o.filled }

/-- A new order is well formed. -/
theorem new_wf (q : Nat) : (new q).Wf := Nat.zero_le q

/-- A new order has nothing filled. -/
@[simp] theorem filled_new (q : Nat) : (new q).filled = 0 := rfl

/-- A new order has its whole quantity open. -/
@[simp] theorem leaves_new (q : Nat) : (new q).leaves = q := by simp [new, leaves]

/-- For a well formed order, leaves plus filled is the order quantity. -/
theorem leaves_add_filled {o : Order} (h : o.Wf) : o.leaves + o.filled = o.qty := by
  unfold leaves; unfold Wf at h; omega

/-- For a well formed order, `leaves = qty - filled` with `filled ≤ qty`, as an equation
without truncated subtraction. -/
theorem qty_eq {o : Order} (h : o.Wf) : o.qty = o.filled + o.leaves := by
  unfold leaves; unfold Wf at h; omega

/-- The leaves quantity is zero exactly when the order is filled in full. -/
theorem leaves_eq_zero_iff (o : Order) : o.leaves = 0 ↔ o.qty ≤ o.filled := by
  unfold leaves; omega

/-- A fill executes at most the reported quantity. -/
theorem fillAmt_le (o : Order) (q : Nat) : o.fillAmt q ≤ q := by
  unfold fillAmt; split <;> omega

/-- A fill executes at most the leaves quantity. -/
theorem fillAmt_le_leaves (o : Order) (q : Nat) : o.fillAmt q ≤ o.leaves := by
  unfold fillAmt; split <;> omega

/-- On an open order a report within the leaves quantity executes exactly. -/
theorem fillAmt_of_le {o : Order} {q : Nat} (hc : o.canceled = false) (h : q ≤ o.leaves) :
    o.fillAmt q = q := by
  simp [fillAmt, hc]; omega

/-- On an open order an oversized report executes exactly the leaves quantity. -/
theorem fillAmt_of_ge {o : Order} {q : Nat} (hc : o.canceled = false) (h : o.leaves ≤ q) :
    o.fillAmt q = o.leaves := by
  simp [fillAmt, hc]; omega

/-- A closed order executes nothing. -/
theorem fillAmt_of_closed {o : Order} (h : o.Closed) (q : Nat) : o.fillAmt q = 0 := by
  unfold fillAmt leaves
  rcases h with h | h
  · simp [h]
  · split <;> omega

/-- The filled quantity after a fill. -/
@[simp] theorem filled_fill (o : Order) (q : Nat) : (o.fill q).filled = o.filled + o.fillAmt q := rfl

/-- A fill does not change the order quantity. -/
@[simp] theorem qty_fill (o : Order) (q : Nat) : (o.fill q).qty = o.qty := rfl

/-- A fill does not change whether the order is canceled. -/
@[simp] theorem canceled_fill (o : Order) (q : Nat) : (o.fill q).canceled = o.canceled := rfl

/-- The leaves quantity after a fill is the leaves quantity less what the fill executed. -/
theorem leaves_fill (o : Order) (q : Nat) : (o.fill q).leaves = o.leaves - o.fillAmt q := by
  have := fillAmt_le_leaves o q
  simp only [leaves, filled_fill, qty_fill] at *
  omega

/-- A fill keeps the order well formed, whatever the reported quantity. -/
theorem fill_wf {o : Order} (h : o.Wf) (q : Nat) : (o.fill q).Wf := by
  have := fillAmt_le_leaves o q
  unfold Wf leaves at *
  simp only [filled_fill, qty_fill]
  omega

/-- A fill report against a closed order changes nothing: no fill after a full fill or a
cancel. -/
theorem fill_of_closed {o : Order} (h : o.Closed) (q : Nat) : o.fill q = o := by
  simp [fill, fillAmt_of_closed h]

/-- The order is filled in full after a fill exactly when the fill covered the leaves
quantity (for a well formed order). -/
theorem fill_full_iff {o : Order} (h : o.Wf) (q : Nat) :
    o.qty ≤ (o.fill q).filled ↔ o.leaves ≤ o.fillAmt q := by
  unfold Wf at h; simp only [filled_fill, leaves]; omega

/-- The filled quantity after a cancel. -/
@[simp] theorem filled_cancel (o : Order) : o.cancel.filled = o.filled := rfl

/-- The order quantity after a cancel. -/
@[simp] theorem qty_cancel (o : Order) : o.cancel.qty = o.qty := rfl

/-- A canceled order is canceled. -/
@[simp] theorem canceled_cancel (o : Order) : o.cancel.canceled = true := rfl

/-- A canceled order is closed. -/
theorem cancel_closed (o : Order) : o.cancel.Closed := Or.inl rfl

/-- A cancel keeps the order well formed. -/
theorem cancel_wf {o : Order} (h : o.Wf) : o.cancel.Wf := h

/-- A replace does not change the filled quantity. -/
@[simp] theorem filled_replace (o : Order) (q : Nat) : (o.replace q).filled = o.filled := by
  unfold replace; split <;> rfl

/-- A replace does not change whether the order is canceled. -/
@[simp] theorem canceled_replace (o : Order) (q : Nat) : (o.replace q).canceled = o.canceled := by
  unfold replace; split <;> rfl

/-- The order quantity after a replace of an open order. -/
theorem qty_replace {o : Order} (hc : ¬ o.Closed) (q : Nat) :
    (o.replace q).qty = max q o.filled := by
  simp [replace, hc]

/-- A replace keeps the order well formed, whatever the requested quantity. -/
theorem replace_wf {o : Order} (h : o.Wf) (q : Nat) : (o.replace q).Wf := by
  unfold replace Wf at *; split
  · exact h
  · show o.filled ≤ max q o.filled
    omega

/-- A replace keeps a closed order closed. -/
theorem replace_closed {o : Order} (h : o.Closed) (q : Nat) : (o.replace q).Closed := by
  unfold replace
  split
  · exact h
  · rename_i hc; exact absurd h hc

/-- An event on an order. -/
inductive Event where
  /-- A fill report of the given quantity. -/
  | fill (q : Nat)
  /-- A cancel request. -/
  | cancel
  /-- A cancel/replace request with the given new order quantity. -/
  | replace (q : Nat)
  deriving DecidableEq, Repr

/-- Apply one event. -/
def apply (o : Order) : Event → Order
  | .fill q => o.fill q
  | .cancel => o.cancel
  | .replace q => o.replace q

/-- The quantity an event executes: a fill's `fillAmt`, nothing for the other events. -/
def execAmt (o : Order) : Event → Nat
  | .fill q => o.fillAmt q
  | _ => 0

/-- Every event keeps the order well formed. -/
theorem apply_wf : Preserves apply Wf := by
  intro o e h
  cases e with
  | fill q => exact fill_wf h q
  | cancel => exact cancel_wf h
  | replace q => exact replace_wf h q

/-- Every event keeps a closed order closed. -/
theorem apply_closed : Preserves apply Closed := by
  intro o e h
  cases e with
  | fill q => rw [apply, fill_of_closed h]; exact h
  | cancel => exact cancel_closed o
  | replace q => exact replace_closed h q

/-- Every event raises the filled quantity by exactly what it executes. -/
theorem filled_apply (o : Order) (e : Event) : (o.apply e).filled = o.filled + o.execAmt e := by
  cases e <;> simp [apply, execAmt]

/-- After any sequence of fills, cancels and replaces, a well formed order is still well
formed: `filled ≤ qty`, so `leaves = qty - filled` exactly. -/
theorem run_wf {o : Order} (h : o.Wf) (es : List Event) : (run apply o es).Wf :=
  run_invariant apply_wf h es

/-- The filled quantity never decreases. -/
theorem filled_le_run (o : Order) (es : List Event) : o.filled ≤ (run apply o es).filled :=
  run_ge filled (fun o e => by rw [filled_apply]; omega) o es

/-- The filled quantity after a sequence of events is at most the start plus the reported fill
quantities. -/
theorem filled_run_le (o : Order) (es : List Event) :
    (run apply o es).filled ≤ o.filled + (es.map fun | .fill q => q | _ => 0).sum := by
  apply run_le_add_sum filled
  intro s e
  rw [filled_apply]
  cases e <;> simp [execAmt, fillAmt_le]

/-- A closed order stays closed after any sequence of events. -/
theorem run_closed {o : Order} (h : o.Closed) (es : List Event) : (run apply o es).Closed :=
  run_invariant apply_closed h es

/-- No fill after a full fill or a cancel: once an order is closed, no sequence of events
changes its filled quantity. -/
theorem filled_run_of_closed {o : Order} (h : o.Closed) (es : List Event) :
    (run apply o es).filled = o.filled := by
  induction es generalizing o with
  | nil => rfl
  | cons e es ih =>
    rw [run_cons, ih (apply_closed o e h), filled_apply]
    cases e <;> simp [execAmt, fillAmt_of_closed h]

/-- No fill after a cancel, stated for the event: whatever follows a cancel, the filled
quantity stays the one at the cancel. -/
theorem filled_run_cancel (o : Order) (es : List Event) :
    (run apply o (.cancel :: es)).filled = o.filled :=
  filled_run_of_closed (cancel_closed o) es

/-- A new order of quantity `q` is never filled beyond `q` by any sequence of fill reports
alone, including duplicate and oversized ones. -/
theorem filled_run_new_le (q : Nat) (es : List Event) :
    (run apply (new q) es).filled ≤ (run apply (new q) es).qty :=
  run_wf (new_wf q) es

/-! ## Execution reports with identifiers -/

/-- An execution report: its identifier (FIX `ExecID`) and the reported quantity. -/
structure Report where
  /-- The report identifier. Two reports with the same identifier are the same execution. -/
  execId : Nat
  /-- The reported quantity. -/
  qty : Nat
  deriving DecidableEq, Repr

end Order

/-- An order with the identifiers of the execution reports already applied to it. -/
structure Tracked where
  /-- The order. -/
  order : Order
  /-- Identifiers of the execution reports applied so far. -/
  seen : List Nat
  deriving DecidableEq, Repr

namespace Tracked

open Order

/-- Apply an execution report unless its identifier was already applied. -/
def report (t : Tracked) (r : Report) : Tracked :=
  if r.execId ∈ t.seen then t else ⟨t.order.fill r.qty, r.execId :: t.seen⟩

/-- A report whose identifier was already applied changes nothing. -/
theorem report_of_mem {t : Tracked} {r : Report} (h : r.execId ∈ t.seen) : t.report r = t := by
  simp [report, h]

/-- A report with a new identifier applies its fill and records the identifier. -/
theorem report_of_not_mem {t : Tracked} {r : Report} (h : r.execId ∉ t.seen) :
    t.report r = ⟨t.order.fill r.qty, r.execId :: t.seen⟩ := by
  simp [report, h]

/-- After a report its identifier is recorded. -/
theorem mem_seen_report (t : Tracked) (r : Report) : r.execId ∈ (t.report r).seen := by
  unfold report; split
  · assumption
  · simp

/-- Identifiers once recorded stay recorded. -/
theorem seen_subset_report (t : Tracked) (r : Report) {i : Nat} (h : i ∈ t.seen) :
    i ∈ (t.report r).seen := by
  unfold report; split
  · exact h
  · exact List.mem_cons_of_mem _ h

/-- Applying the same report twice is applying it once. -/
theorem report_report (t : Tracked) (r : Report) : (t.report r).report r = t.report r :=
  report_of_mem (mem_seen_report t r)

/-- Identifiers once recorded stay recorded after any sequence of reports. -/
theorem seen_subset_run (t : Tracked) (rs : List Report) {i : Nat} (h : i ∈ t.seen) :
    i ∈ (run report t rs).seen := by
  induction rs generalizing t with
  | nil => exact h
  | cons r rs ih => exact ih (t.report r) (seen_subset_report t r h)

/-- After a sequence of reports every identifier of the sequence is recorded. -/
theorem mem_seen_run (t : Tracked) (rs : List Report) {r : Report} (h : r ∈ rs) :
    r.execId ∈ (run report t rs).seen := by
  induction rs generalizing t with
  | nil => simp at h
  | cons r' rs ih =>
    rcases List.mem_cons.mp h with h | h
    · subst h; exact seen_subset_run _ rs (mem_seen_report t r)
    · exact ih (t.report r') h

/-- A sequence of reports whose identifiers were all applied changes nothing. -/
theorem run_of_seen {t : Tracked} {rs : List Report} (h : ∀ r ∈ rs, r.execId ∈ t.seen) :
    run report t rs = t := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [run_cons, report_of_mem (h r (by simp))]
    exact ih (fun r' hr => h r' (List.mem_cons_of_mem _ hr))

/-- Replaying a report stream (after a reconnect, with possible duplicates) changes nothing:
running the same reports a second time leaves the order where the first run left it. -/
theorem run_replay (t : Tracked) (rs : List Report) :
    run report (run report t rs) rs = run report t rs :=
  run_of_seen (fun _ h => mem_seen_run t rs h)

/-- More generally, a run followed by any reports that repeat earlier ones is the run. -/
theorem run_append_dups (t : Tracked) (rs ds : List Report) (h : ∀ d ∈ ds, ∃ r ∈ rs, r.execId = d.execId) :
    run report t (rs ++ ds) = run report t rs := by
  rw [run_append]
  apply run_of_seen
  intro d hd
  obtain ⟨r, hr, e⟩ := h d hd
  rw [← e]; exact mem_seen_run t rs hr

/-- Every report keeps the order well formed. -/
theorem report_wf : Preserves report (fun t => t.order.Wf) := by
  intro t r h
  unfold report; split
  · exact h
  · exact fill_wf h r.qty

/-- With identifiers, the order is never filled beyond its quantity after any sequence of
reports, duplicates included. -/
theorem run_wf {t : Tracked} (h : t.order.Wf) (rs : List Report) : (run report t rs).order.Wf :=
  run_invariant report_wf h rs

/-- With identifiers, the filled quantity is at most the start plus the quantities of the
reports. -/
theorem filled_run_le (t : Tracked) (rs : List Report) :
    (run report t rs).order.filled ≤ t.order.filled + (rs.map Report.qty).sum := by
  refine run_le_add_sum (fun t : Tracked => t.order.filled) Report.qty ?_ t rs
  intro t r
  unfold report; split
  · omega
  · simp only [filled_fill]; have := fillAmt_le t.order r.qty; omega

end Tracked

end ProofForgeFin.Trading.Orders
