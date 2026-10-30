import ProofForgeFin.Ledger
import ProofForgeFin.Trading.Basic
/-!
# Positions and profit and loss

A position keeping system turns fills into a position per instrument, a cost basis, cash and
realized profit and loss, and marks the open position to market for the unrealized part. The
average cost method keeps the total cost of the open quantity: a fill on the side of the
position adds to it, a fill on the other side closes part of it at the average cost and realizes
the difference, and a fill larger than the position closes it and opens the rest on the other
side. Dividing the cost basis on a partial close is where rounding enters.

* `Pos`: the side and magnitude of the open position, its cost basis (`Nat`, in price units
  times quantity), cash and realized P&L (`Int`).
* `Fill`: side, quantity and price of an execution; `apply` books it.
* `remainingCost cost qty k`: the cost basis left after closing `k` of `qty` units,
  `cost * (qty - k) / qty`, rounded down; `removedCost` is the cost basis taken out.
* `signedQty`, `signedCost`, `unrealized p mark` (market value at `mark` minus cost basis),
  `avgDown` and `avgUp` (the average cost rounded down and up).

The theorems:

* `signedQty_run`, `cash_run`: the signed position is the start plus the sum of the signed fill
  quantities, cash is the start plus the sum of the cash flows (`-sign * qty * px`).
* `pnl_conservation`: realized plus unrealized P&L minus cash minus position value at the mark is
  the same after every sequence of fills, whatever the rounding of the cost basis; from a flat
  start, `realized + unrealized mark = cash + signedQty * mark` (`pnl_flat`). Rounding moves P&L
  between realized and unrealized and never creates or destroys it.
* `removedCost_spec`: the cost basis removed on a partial close is the exact pro-rata cost rounded
  up, within one unit; `realized_reduce` gives the realized amount of a closing fill.
* `run_inRange`: when every fill price is in `[lo, hi]`, the cost basis stays between
  `lo * qty` and `hi * qty`, so the average cost (rounded either way) stays in `[lo, hi]`
  (`avg_mem_range`).
* `round_trip`: from flat, buying `q` at `p₁` and selling `q` at `p₂` returns to flat with
  realized P&L `q * p₂ - q * p₁` and equal cash; at one price it realizes zero.
-/

namespace ProofForgeFin.Trading.Position

open ProofForgeFin ProofForgeFin.Seq ProofForgeFin.Ledger

/-! ## Positions and fills -/

/-- A position in one instrument. When `qty = 0` the side is irrelevant. -/
structure Pos where
  /-- The side of the open position: `buy` for long, `sell` for short. -/
  side : Side
  /-- The magnitude of the open position. -/
  qty : Nat
  /-- The cost basis of the open position: the total price paid (long) or received (short). -/
  cost : Nat
  /-- Cash: proceeds of sales minus the cost of purchases. -/
  cash : Int
  /-- Realized profit and loss. -/
  realized : Int
  deriving DecidableEq, Repr

/-- An execution: side, quantity and price per unit. -/
structure Fill where
  /-- `buy` or `sell`. -/
  side : Side
  /-- The quantity executed. -/
  qty : Nat
  /-- The price per unit. -/
  px : Nat
  deriving DecidableEq, Repr

/-- The flat position with no cash and no P&L. -/
def Pos.flat : Pos := ⟨.buy, 0, 0, 0, 0⟩

/-- The signed position: positive when long, negative when short. -/
def signedQty (p : Pos) : Int := p.side.sign * p.qty

/-- The signed cost basis. -/
def signedCost (p : Pos) : Int := p.side.sign * p.cost

/-- Unrealized P&L at the price `mark`: the market value of the position minus its cost basis. -/
def unrealized (p : Pos) (mark : Nat) : Int := signedQty p * mark - signedCost p

/-- The signed quantity of a fill. -/
def Fill.signedQty (f : Fill) : Int := f.side.sign * f.qty

/-- The cash flow of a fill: a buy pays `qty * px`, a sell receives it. -/
def Fill.cashFlow (f : Fill) : Int := -(f.side.sign * ((f.qty * f.px : Nat) : Int))

/-- The cost basis left after closing `k` of `qty` units at the average cost, rounded down. -/
def remainingCost (cost qty k : Nat) : Nat := cost * (qty - k) / qty

/-- The cost basis taken out when closing `k` of `qty` units. -/
def removedCost (cost qty k : Nat) : Nat := cost - remainingCost cost qty k

/-- A fill on the side of the position adds its quantity and its cost. -/
def addFill (p : Pos) (f : Fill) : Pos :=
  { p with qty := p.qty + f.qty, cost := p.cost + f.qty * f.px, cash := p.cash + f.cashFlow }

/-- A fill on the other side of at most the open quantity closes that quantity at the average
cost: the cost basis left is `remainingCost`, and the realized P&L is the fill's notional minus
the cost basis removed (for a long position; the opposite for a short one). -/
def reduceFill (p : Pos) (f : Fill) : Pos :=
  { p with
    qty := p.qty - f.qty
    cost := remainingCost p.cost p.qty f.qty
    cash := p.cash + f.cashFlow
    realized := p.realized + p.side.sign *
      (((f.qty * f.px : Nat) : Int) - p.cost + remainingCost p.cost p.qty f.qty) }

/-- A fill on the other side of more than the open quantity closes the whole position and opens
the rest on the fill's side at the fill price. -/
def flipFill (p : Pos) (f : Fill) : Pos :=
  { side := f.side
    qty := f.qty - p.qty
    cost := (f.qty - p.qty) * f.px
    cash := p.cash + f.cashFlow
    realized := p.realized + p.side.sign * (((p.qty * f.px : Nat) : Int) - p.cost) }

/-- Book a fill: on the side of the position it adds quantity and cost; on the other side it
closes up to the open quantity at the average cost and realizes the difference; beyond the open
quantity it opens the rest on the fill's side at the fill price. -/
def apply (p : Pos) (f : Fill) : Pos :=
  if f.side = p.side then addFill p f
  else if f.qty ≤ p.qty then reduceFill p f
  else flipFill p f

/-- A fill on the side of the position. -/
theorem apply_of_side_eq {p : Pos} {f : Fill} (h : f.side = p.side) : apply p f = addFill p f := by
  simp [apply, h]

/-- A fill on the other side of at most the open quantity. -/
theorem apply_of_reduce {p : Pos} {f : Fill} (h : f.side ≠ p.side) (hq : f.qty ≤ p.qty) :
    apply p f = reduceFill p f := by
  simp [apply, h, hq]

/-- A fill on the other side of more than the open quantity. -/
theorem apply_of_flip {p : Pos} {f : Fill} (h : f.side ≠ p.side) (hq : p.qty < f.qty) :
    apply p f = flipFill p f := by
  simp [apply, h, Nat.not_le.mpr hq]

/-- Two sides that differ are each other's other side. -/
theorem eq_opp_of_ne {s t : Side} (h : s ≠ t) : s = t.opp := by
  cases s <;> cases t <;> simp_all

/-! ## Position and cash -/

/-- A fill changes the signed position by its signed quantity. -/
theorem signedQty_apply (p : Pos) (f : Fill) : signedQty (apply p f) = signedQty p + f.signedQty := by
  by_cases hs : f.side = p.side
  · rw [apply_of_side_eq hs]; unfold addFill
    simp only [signedQty, Fill.signedQty, hs]
    push_cast; rw [Int.mul_add]
  · have ho := eq_opp_of_ne hs
    by_cases hq : f.qty ≤ p.qty
    · rw [apply_of_reduce hs hq]; unfold reduceFill
      simp only [signedQty, Fill.signedQty, ho]
      cases p.side <;> simp <;> omega
    · rw [apply_of_flip hs (Nat.lt_of_not_le hq)]; unfold flipFill
      simp only [signedQty, Fill.signedQty, ho]
      cases p.side <;> simp <;> omega

/-- A fill changes cash by its cash flow. -/
@[simp] theorem cash_apply (p : Pos) (f : Fill) : (apply p f).cash = p.cash + f.cashFlow := by
  unfold apply; split
  · rfl
  · split <;> rfl

/-- REQ-POSITION: the signed position after a sequence of fills is the start plus the sum of the
signed fill quantities. -/
theorem signedQty_run (p : Pos) (fs : List Fill) :
    signedQty (run apply p fs) = signedQty p + sumOver fs Fill.signedQty := by
  induction fs generalizing p with
  | nil => simp
  | cons f fs ih => rw [run_cons, ih, signedQty_apply, sumOver_cons]; omega

/-- REQ-CASH: cash after a sequence of fills is the start plus the sum of the cash flows. -/
theorem cash_run (p : Pos) (fs : List Fill) :
    (run apply p fs).cash = p.cash + sumOver fs Fill.cashFlow := by
  induction fs generalizing p with
  | nil => simp
  | cons f fs ih => rw [run_cons, ih, cash_apply, sumOver_cons]; omega

/-! ## Conservation of P&L -/

/-- Realized P&L minus cash minus the signed cost basis: the quantity every fill preserves. -/
def gap (p : Pos) : Int := p.realized - p.cash - signedCost p

/-- Every fill preserves `gap`, whatever the rounding of the remaining cost basis. -/
theorem gap_apply (p : Pos) (f : Fill) : gap (apply p f) = gap p := by
  by_cases hs : f.side = p.side
  · rw [apply_of_side_eq hs]; unfold addFill
    simp only [gap, signedCost, Fill.cashFlow, hs]
    generalize f.qty * f.px = n
    cases p.side <;> simp <;> omega
  · have ho := eq_opp_of_ne hs
    by_cases hq : f.qty ≤ p.qty
    · rw [apply_of_reduce hs hq]; unfold reduceFill
      simp only [gap, signedCost, Fill.cashFlow, ho]
      generalize f.qty * f.px = n
      generalize remainingCost p.cost p.qty f.qty = r
      cases p.side <;> simp <;> omega
    · have hlt := Nat.lt_of_not_le hq
      rw [apply_of_flip hs hlt]; unfold flipFill
      have e : (f.qty - p.qty) * f.px + p.qty * f.px = f.qty * f.px := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      simp only [gap, signedCost, Fill.cashFlow, ho, Side.sign_opp]
      generalize (f.qty - p.qty) * f.px = a at e ⊢
      generalize p.qty * f.px = b at e ⊢
      generalize f.qty * f.px = n at e ⊢
      cases p.side <;> simp <;> omega

/-- `gap` is unchanged by every sequence of fills. -/
theorem gap_run (p : Pos) (fs : List Fill) : gap (run apply p fs) = gap p :=
  run_eq_of_step_eq gap gap_apply p fs

/-- Total P&L at a mark: realized plus unrealized. -/
def pnl (p : Pos) (mark : Nat) : Int := p.realized + unrealized p mark

/-- Total P&L minus cash minus position value is `gap`, for every mark. -/
theorem pnl_sub_eq_gap (p : Pos) (mark : Nat) :
    pnl p mark - (p.cash + signedQty p * mark) = gap p := by
  simp only [pnl, unrealized, gap]; omega

/-- REQ-PNL-CONSERVATION: for every mark, total P&L minus cash minus position value at the mark is
the same after every sequence of fills as before. The rounding of the cost basis on partial
closes moves P&L between realized and unrealized and never creates or destroys it. -/
theorem pnl_conservation (p : Pos) (fs : List Fill) (mark : Nat) :
    pnl (run apply p fs) mark - ((run apply p fs).cash + signedQty (run apply p fs) * mark) =
      pnl p mark - (p.cash + signedQty p * mark) := by
  rw [pnl_sub_eq_gap, pnl_sub_eq_gap, gap_run]

/-- From a flat start, realized plus unrealized P&L is cash plus the position valued at the mark,
after every sequence of fills. -/
theorem pnl_flat (fs : List Fill) (mark : Nat) :
    (run apply Pos.flat fs).realized + unrealized (run apply Pos.flat fs) mark =
      (run apply Pos.flat fs).cash + signedQty (run apply Pos.flat fs) * mark := by
  have := pnl_conservation Pos.flat fs mark
  have h0 : pnl Pos.flat mark - (Pos.flat.cash + signedQty Pos.flat * mark) = 0 := by
    simp [pnl, unrealized, Pos.flat, signedQty, signedCost]
  simp only [pnl] at this h0
  omega

/-! ## Rounding of the cost basis -/

/-- The remaining cost basis is at most the cost basis. -/
theorem remainingCost_le (cost qty k : Nat) : remainingCost cost qty k ≤ cost := by
  unfold remainingCost
  rw [Nat.mul_comm]
  exact mul_div_le_of_le (Nat.sub_le _ _)

/-- Closing the whole position leaves no cost basis. -/
@[simp] theorem remainingCost_self (cost qty : Nat) : remainingCost cost qty qty = 0 := by
  simp [remainingCost]

/-- The cost basis removed on a partial close is the exact pro-rata cost `cost * k / qty`
rounded up: `cost * k ≤ removed * qty < cost * k + qty`. The remaining average cost rounds down,
so the realized P&L of a long position rounds down by less than one unit. -/
theorem removedCost_spec (cost : Nat) {qty k : Nat} (hq : 0 < qty) (hk : k ≤ qty) :
    cost * k ≤ removedCost cost qty k * qty ∧ removedCost cost qty k * qty < cost * k + qty := by
  have hr := floor_spec (cost * (qty - k)) qty hq
  have hle := remainingCost_le cost qty k
  unfold removedCost
  unfold remainingCost at hle ⊢
  generalize cost * (qty - k) / qty = c' at hr hle
  have e1 : cost * qty = cost * (qty - k) + cost * k := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hk]
  rw [Nat.sub_mul]
  rw [Nat.add_mul, Nat.one_mul] at hr
  have h2 : c' * qty ≤ cost * qty := Nat.mul_le_mul_right _ hle
  omega

/-- The realized P&L of a closing fill: `k * px` minus the removed cost basis for a long position,
the opposite for a short one. -/
theorem realized_reduce {p : Pos} {f : Fill} (h : f.side ≠ p.side) (hq : f.qty ≤ p.qty) :
    (apply p f).realized = p.realized + p.side.sign *
      (((f.qty * f.px : Nat) : Int) - (removedCost p.cost p.qty f.qty : Nat)) := by
  rw [apply_of_reduce h hq]
  have := remainingCost_le p.cost p.qty f.qty
  simp only [reduceFill, removedCost]
  rw [Int.ofNat_sub this]
  rw [show (((f.qty * f.px : Nat) : Int) - p.cost + remainingCost p.cost p.qty f.qty) =
    ((f.qty * f.px : Nat) : Int) - ((p.cost : Int) - remainingCost p.cost p.qty f.qty) by omega]

/-! ## Average cost -/

/-- The average cost rounded down. -/
def avgDown (p : Pos) : Nat := p.cost / p.qty

/-- The average cost rounded up. -/
def avgUp (p : Pos) : Nat := ceilDiv p.cost p.qty

/-- The average cost rounded down is within one unit below the exact average. -/
theorem avgDown_spec (p : Pos) (h : 0 < p.qty) :
    avgDown p * p.qty ≤ p.cost ∧ p.cost < (avgDown p + 1) * p.qty := floor_spec _ _ h

/-- The average cost rounded up is within one unit above the exact average. -/
theorem avgUp_spec (p : Pos) (h : 0 < p.qty) :
    p.cost ≤ avgUp p * p.qty ∧ avgUp p * p.qty < p.cost + p.qty := ceilDiv_spec _ _ h

/-- A flat position has no cost basis. -/
def Wf (p : Pos) : Prop := p.qty = 0 → p.cost = 0

/-- Every fill keeps a flat position free of cost basis. -/
theorem wf_apply {p : Pos} (h : Wf p) (f : Fill) : Wf (apply p f) := by
  by_cases hs : f.side = p.side
  · rw [apply_of_side_eq hs]; unfold addFill
    intro h0
    simp only at h0 ⊢
    have h1 : p.qty = 0 := by omega
    have h2 : f.qty = 0 := by omega
    rw [h h1, h2]; simp
  · by_cases hq : f.qty ≤ p.qty
    · rw [apply_of_reduce hs hq]; unfold reduceFill
      intro h0
      simp only at h0 ⊢
      have : f.qty = p.qty := by omega
      rw [this, remainingCost_self]
    · rw [apply_of_flip hs (Nat.lt_of_not_le hq)]; unfold flipFill
      intro h0; simp only at h0; omega

/-- The cost basis is between `lo` and `hi` per unit. -/
def InRange (lo hi : Nat) (p : Pos) : Prop := lo * p.qty ≤ p.cost ∧ p.cost ≤ hi * p.qty

/-- A fill at a price in `[lo, hi]` keeps the cost basis in range. -/
theorem inRange_apply {lo hi : Nat} {p : Pos} (h : InRange lo hi p) {f : Fill}
    (hlo : lo ≤ f.px) (hhi : f.px ≤ hi) : InRange lo hi (apply p f) := by
  by_cases hs : f.side = p.side
  · rw [apply_of_side_eq hs]; unfold addFill
    unfold InRange at h ⊢
    simp only
    have h1 : lo * f.qty ≤ f.qty * f.px := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hlo
    have h2 : f.qty * f.px ≤ hi * f.qty := by rw [Nat.mul_comm hi]; exact Nat.mul_le_mul_left _ hhi
    rw [Nat.mul_add, Nat.mul_add]
    omega
  · by_cases hq : f.qty ≤ p.qty
    · rw [apply_of_reduce hs hq]; unfold reduceFill
      unfold InRange at h ⊢
      simp only
      unfold remainingCost
      rcases Nat.eq_zero_or_pos p.qty with h0 | h0
      · simp [h0]
      · constructor
        · apply (le_div_iff h0).2
          rw [Nat.mul_right_comm]
          exact Nat.mul_le_mul_right _ h.1
        · apply div_le_of_le_mul'
          rw [Nat.mul_right_comm]
          exact Nat.mul_le_mul_right _ h.2
    · rw [apply_of_flip hs (Nat.lt_of_not_le hq)]; unfold flipFill
      unfold InRange
      simp only
      constructor
      · rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hlo
      · rw [Nat.mul_comm hi]; exact Nat.mul_le_mul_left _ hhi

/-- REQ-AVERAGE-IN-RANGE: when every fill price is in `[lo, hi]`, the cost basis stays between
`lo * qty` and `hi * qty` after every sequence of fills from a position in range (for example
the flat position). -/
theorem run_inRange {lo hi : Nat} {p : Pos} (h : InRange lo hi p) {fs : List Fill}
    (hf : ∀ f ∈ fs, lo ≤ f.px ∧ f.px ≤ hi) : InRange lo hi (run apply p fs) :=
  run_invariant_of_mem (I := InRange lo hi)
    (fun _ f hm ht => inRange_apply ht (hf f hm).1 (hf f hm).2) h

/-- The flat position is in every range. -/
theorem inRange_flat (lo hi : Nat) : InRange lo hi Pos.flat := by simp [InRange, Pos.flat]

/-- A position in range has its average cost, rounded down or up, in `[lo, hi]`. -/
theorem avg_mem_range {lo hi : Nat} {p : Pos} (h : InRange lo hi p) (hq : 0 < p.qty) :
    lo ≤ avgDown p ∧ avgDown p ≤ avgUp p ∧ avgUp p ≤ hi :=
  ⟨(le_div_iff hq).2 h.1, div_le_ceilDiv _ _, (ceilDiv_le_iff hq).2 h.2⟩

/-! ## Round trips -/

/-- From flat, buying `q` at `p₁` and then selling `q` at `p₂` returns to a flat position with
no cost basis, realized P&L `q * p₂ - q * p₁`, and the same amount in cash. -/
theorem round_trip (q p₁ p₂ : Nat) :
    run apply Pos.flat [⟨.buy, q, p₁⟩, ⟨.sell, q, p₂⟩] =
      ⟨.buy, 0, 0, ((q * p₂ : Nat) : Int) - ((q * p₁ : Nat) : Int),
        ((q * p₂ : Nat) : Int) - ((q * p₁ : Nat) : Int)⟩ := by
  have h1 : apply Pos.flat ⟨.buy, q, p₁⟩ = ⟨.buy, q, q * p₁, -((q * p₁ : Nat) : Int), 0⟩ := by
    simp [apply, addFill, Pos.flat, Fill.cashFlow]
  simp only [run_cons, run_nil, h1]
  rw [apply_of_reduce (p := ⟨.buy, q, q * p₁, -((q * p₁ : Nat) : Int), 0⟩)
    (f := ⟨.sell, q, p₂⟩) (by simp) (Nat.le_refl _)]
  simp [reduceFill, Fill.cashFlow]
  omega

/-- A round trip at one price realizes nothing and leaves no cash. -/
theorem round_trip_same (q px : Nat) :
    run apply Pos.flat [⟨.buy, q, px⟩, ⟨.sell, q, px⟩] = Pos.flat := by
  rw [round_trip]; simp [Pos.flat]

end ProofForgeFin.Trading.Position
