/-!
# Sides and price comparisons

Every part of a trading system compares prices from the point of view of one side of the market:
a bid is better when it is higher, an ask is better when it is lower, an incoming buy order can
trade against an ask at or below its limit and an incoming sell order against a bid at or above
its limit. This module fixes one vocabulary for those comparisons so that the order book, the
risk checks and the position code state them the same way.

* `Side`: `buy` or `sell`; `Side.opp` is the other side.
* `Side.le s p q`: price `p` is at least as good as `q` for orders of side `s` (for `buy`,
  `q ≤ p`; for `sell`, `p ≤ q`). `Side.lt` is the strict form.
* `Side.le s limit px` is also the crossing condition: an incoming order of side `s` with limit
  `limit` may trade at the resting price `px` exactly when `s.le limit px`.
* `Side.sign`: `+1` for `buy` and `-1` for `sell`, the sign of a fill's effect on a position.

Prices and quantities are natural numbers in the smallest unit (ticks, lots, cents).
-/

namespace ProofForgeFin.Trading

/-- The side of an order: `buy` (a bid) or `sell` (an ask or offer). -/
inductive Side where
  /-- A buy order; resting buy orders are bids. -/
  | buy
  /-- A sell order; resting sell orders are asks. -/
  | sell
  deriving DecidableEq, Repr

namespace Side

/-- The other side of the market: incoming orders of side `s` trade against resting orders of
side `s.opp`. -/
def opp : Side → Side
  | buy => sell
  | sell => buy

/-- The other side of the other side is the side. -/
@[simp] theorem opp_opp (s : Side) : s.opp.opp = s := by cases s <;> rfl

/-- The other side of `buy`. -/
@[simp] theorem opp_buy : buy.opp = sell := rfl

/-- The other side of `sell`. -/
@[simp] theorem opp_sell : sell.opp = buy := rfl

/-- A side differs from its other side. -/
theorem opp_ne (s : Side) : s.opp ≠ s := by cases s <;> decide

/-- `s.le p q`: price `p` is at least as good as price `q` for orders of side `s`. Bids are
better when higher, asks when lower. -/
def le : Side → Nat → Nat → Prop
  | buy, p, q => q ≤ p
  | sell, p, q => p ≤ q

/-- `s.lt p q`: price `p` is strictly better than price `q` for orders of side `s`. -/
def lt : Side → Nat → Nat → Prop
  | buy, p, q => q < p
  | sell, p, q => p < q

instance instDecidableLe (s : Side) (p q : Nat) : Decidable (s.le p q) := by
  cases s <;> unfold le <;> infer_instance

instance instDecidableLt (s : Side) (p q : Nat) : Decidable (s.lt p q) := by
  cases s <;> unfold lt <;> infer_instance

/-- For bids a price is at least as good when it is at least as high. -/
@[simp] theorem le_buy (p q : Nat) : buy.le p q ↔ q ≤ p := Iff.rfl

/-- For asks a price is at least as good when it is at most as high. -/
@[simp] theorem le_sell (p q : Nat) : sell.le p q ↔ p ≤ q := Iff.rfl

/-- For bids a price is strictly better when it is higher. -/
@[simp] theorem lt_buy (p q : Nat) : buy.lt p q ↔ q < p := Iff.rfl

/-- For asks a price is strictly better when it is lower. -/
@[simp] theorem lt_sell (p q : Nat) : sell.lt p q ↔ p < q := Iff.rfl

/-- Every price is as good as itself. -/
theorem le_refl (s : Side) (p : Nat) : s.le p p := by cases s <;> simp

/-- "At least as good" is transitive. -/
theorem le_trans {s : Side} {p q r : Nat} (h₁ : s.le p q) (h₂ : s.le q r) : s.le p r := by
  cases s <;> simp at * <;> omega

/-- "Strictly better" implies "at least as good". -/
theorem le_of_lt {s : Side} {p q : Nat} (h : s.lt p q) : s.le p q := by
  cases s <;> simp at * <;> omega

/-- Strictly better, then at least as good, is strictly better. -/
theorem lt_of_lt_of_le {s : Side} {p q r : Nat} (h₁ : s.lt p q) (h₂ : s.le q r) : s.lt p r := by
  cases s <;> simp at * <;> omega

/-- At least as good, then strictly better, is strictly better. -/
theorem lt_of_le_of_lt {s : Side} {p q r : Nat} (h₁ : s.le p q) (h₂ : s.lt q r) : s.lt p r := by
  cases s <;> simp at * <;> omega

/-- No price is strictly better than itself. -/
theorem lt_irrefl (s : Side) (p : Nat) : ¬ s.lt p p := by cases s <;> simp

/-- `p` is not strictly better than `q` exactly when `q` is at least as good as `p`. -/
theorem not_lt_iff_le {s : Side} {p q : Nat} : ¬ s.lt p q ↔ s.le q p := by
  cases s <;> simp <;> omega

/-- `p` is not at least as good as `q` exactly when `q` is strictly better than `p`. -/
theorem not_le_iff_lt {s : Side} {p q : Nat} : ¬ s.le p q ↔ s.lt q p := by
  cases s <;> simp <;> omega

/-- Any two prices compare. -/
theorem le_total (s : Side) (p q : Nat) : s.le p q ∨ s.le q p := by
  cases s <;> simp <;> omega

/-- Two prices each at least as good as the other are equal. -/
theorem le_antisymm {s : Side} {p q : Nat} (h₁ : s.le p q) (h₂ : s.le q p) : p = q := by
  cases s <;> simp at * <;> omega

/-- Comparing from the other side reverses the order. -/
theorem le_opp {s : Side} {p q : Nat} : s.opp.le p q ↔ s.le q p := by
  cases s <;> simp

/-- Comparing strictly from the other side reverses the order. -/
theorem lt_opp {s : Side} {p q : Nat} : s.opp.lt p q ↔ s.lt q p := by
  cases s <;> simp

/-- The sign of a fill of side `s` on a signed position: `+1` for a buy, `-1` for a sell. -/
def sign : Side → Int
  | buy => 1
  | sell => -1

/-- A buy adds to a position. -/
@[simp] theorem sign_buy : buy.sign = 1 := rfl

/-- A sell subtracts from a position. -/
@[simp] theorem sign_sell : sell.sign = -1 := rfl

/-- The two sides have opposite signs. -/
@[simp] theorem sign_opp (s : Side) : s.opp.sign = - s.sign := by cases s <;> rfl

end Side

/-- An incoming order of side `s` with limit price `limit` may trade at the resting price `px`
of the other side: a buy at or below its limit, a sell at or above it. -/
abbrev Crosses (s : Side) (limit px : Nat) : Prop := s.le limit px

end ProofForgeFin.Trading
