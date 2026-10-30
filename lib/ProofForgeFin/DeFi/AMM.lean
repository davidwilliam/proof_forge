import ProofForgeFin.Rounding
import ProofForgeFin.FixedPoint
import ProofForgeFin.Seq
/-!
# Automated market makers

Two parts.

**Constant product with a fee** (Uniswap V2 and its forks). A pool holds reserves `x` and `y` and
has issued `L` liquidity tokens. The fee is `fee / D` of the amount in (Uniswap V2: `3 / 1000`),
with `g = D - fee` the share that trades. The formulas are those of `UniswapV2Library`:

* `amountOut D g x y dx = dx * g * y / (x * D + dx * g)` (`getAmountOut`), rounded down;
* `amountIn D g x y dy = x * dy * D / ((y - dy) * g) + 1` (`getAmountIn`), rounded up by adding one.

The theorems: the pair's K check passes for both quotes (`k_check_amountOut`, `k_check_amountIn`),
so the product of the reserves never decreases on a swap (`k_le_swapOut`, `k_le_swapIn`); the
output is below the reserve and never better than the spot price, and the average price worsens
with the size of the trade (`amountOut_mul_le`, price impact); minting at the smaller of the two
ratios and burning pro rata, both rounded down, never lower the product of the reserves per
liquidity token squared (`mint_kPerL`, `burn_kPerL`). For the pool model `step` (swaps both ways,
adds, removes, refusals unchanged): the product of the reserves never decreases over swaps and adds
(`run_k_le`), and `k / L^2` never decreases over any sequence while liquidity is outstanding
(`run_kPerL`).

**Invariant pools** (Balancer's `WellBehaved` pool math, Curve's `D`). Balances are a function
`Nat → Nat` of the token index; `update2 b i x j y` replaces two entries. A swap keeps a monotone
invariant when the pool math says the priced trade keeps it and the settled balances dominate the
priced ones (`invariant_le_of_dominates`). `scaled_dominates` gives the domination for balances
measured in scaled units rounded down (Balancer's `_upscale`) from the two rounding directions:
the amount credited to the math rounded down, the amount debited rounded up. A batch keeps the
invariant when each swap does (`runAll_invariant_le`).
-/

namespace ProofForgeFin.DeFi.AMM

open ProofForgeFin

/-! ## Constant product: quotes -/

/-- `UniswapV2Library.getAmountOut` with fee `fee / D` (`g = D - fee`): the output for `dx` in,
rounded down. -/
def amountOut (D g x y dx : Nat) : Nat := dx * g * y / (x * D + dx * g)

/-- `UniswapV2Library.getAmountIn`: the input for `dy` out, `x * dy * D / ((y - dy) * g) + 1`. -/
def amountIn (D g x y dy : Nat) : Nat := x * dy * D / ((y - dy) * g) + 1

/-- The output, times the denominator, is at most the numerator. -/
theorem amountOut_mul_le (D g x y dx : Nat) :
    amountOut D g x y dx * (x * D + dx * g) ≤ dx * g * y :=
  Nat.div_mul_le_self _ _

/-- The pair's K check with the fee (`balance0Adjusted * balance1Adjusted >= reserve0 * reserve1 *
1000**2`, divided by `D`) passes for `getAmountOut`: `(x * D + dx * g) * (y - out) ≥ x * y * D`. -/
theorem k_check_amountOut (D g x y dx : Nat) :
    x * y * D ≤ (x * D + dx * g) * (y - amountOut D g x y dx) := by
  have h := amountOut_mul_le D g x y dx
  have e : (x * D + dx * g) * y = x * y * D + dx * g * y := by
    rw [Nat.add_mul, Nat.mul_right_comm x D y]
  rw [Nat.mul_sub, Nat.mul_comm (x * D + dx * g) (amountOut D g x y dx)]
  omega

/-- The output never reaches the reserve while the reserve in and the scale are positive. -/
theorem amountOut_lt {D g x y dx : Nat} (hx : 0 < x) (hD : 0 < D) (hy : 0 < y) :
    amountOut D g x y dx < y := by
  unfold amountOut
  apply Nat.div_lt_of_lt_mul
  have : dx * g * y < (x * D + dx * g) * y := by
    rw [Nat.add_mul]
    have : 0 < x * D * y := Nat.mul_pos (Nat.mul_pos hx hD) hy
    rw [Nat.mul_right_comm dx g y]; omega
  exact this

/-- The product of the reserves never decreases on a swap priced by `getAmountOut`, for a fee in
`[0, 1)` (`0 < g ≤ D`). -/
theorem k_le_swapOut {D g x y dx : Nat} (hg : 0 < g) (hgD : g ≤ D) :
    x * y ≤ (x + dx) * (y - amountOut D g x y dx) := by
  have h := amountOut_mul_le D g x y dx
  have h1 : amountOut D g x y dx * (x + dx) * g ≤ dx * y * g := by
    calc amountOut D g x y dx * (x + dx) * g
        = amountOut D g x y dx * (x * g + dx * g) := by rw [Nat.mul_assoc, Nat.add_mul]
      _ ≤ amountOut D g x y dx * (x * D + dx * g) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ hgD) _)
      _ ≤ dx * g * y := h
      _ = dx * y * g := Nat.mul_right_comm _ _ _
  have h2 := Nat.le_of_mul_le_mul_right h1 hg
  rw [Nat.mul_sub, Nat.add_mul, Nat.mul_comm (x + dx) (amountOut D g x y dx)]
  omega

/-- The pair's K check passes for `getAmountIn`: `((x + in) * D - in * fee) * (y - dy) ≥ x * y * D`,
written with `g = D - fee` as `(x * D + in * g) * (y - dy)`. -/
theorem k_check_amountIn {D g x y dy : Nat} (hg : 0 < g) (hdy : dy < y) :
    x * y * D ≤ (x * D + amountIn D g x y dy * g) * (y - dy) := by
  have hpos : 0 < (y - dy) * g := Nat.mul_pos (by omega) hg
  have h := lt_div_add_one_mul (x * dy * D) ((y - dy) * g) hpos
  have e : x * y * D = x * D * (y - dy) + x * dy * D := by
    have : y = (y - dy) + dy := by omega
    conv => lhs; rw [this]
    rw [Nat.mul_add, Nat.add_mul, Nat.mul_right_comm x (y - dy) D]
  have h' : x * dy * D ≤ amountIn D g x y dy * g * (y - dy) := by
    unfold amountIn
    calc x * dy * D ≤ (x * dy * D / ((y - dy) * g) + 1) * ((y - dy) * g) := Nat.le_of_lt h
      _ = (x * dy * D / ((y - dy) * g) + 1) * g * (y - dy) := by ac_rfl
  rw [e, Nat.add_mul (x * D) (amountIn D g x y dy * g) (y - dy)]
  omega

/-- The product of the reserves never decreases on a swap priced by `getAmountIn`, for a fee in
`[0, 1)`. -/
theorem k_le_swapIn {D g x y dy : Nat} (hg : 0 < g) (hgD : g ≤ D) (hdy : dy < y) :
    x * y ≤ (x + amountIn D g x y dy) * (y - dy) := by
  have hpos : 0 < (y - dy) * g := Nat.mul_pos (by omega) hg
  have h := lt_div_add_one_mul (x * dy * D) ((y - dy) * g) hpos
  have h1 : x * dy * g ≤ amountIn D g x y dy * (y - dy) * g := by
    unfold amountIn
    calc x * dy * g ≤ x * dy * D := Nat.mul_le_mul_left _ hgD
      _ ≤ (x * dy * D / ((y - dy) * g) + 1) * ((y - dy) * g) := Nat.le_of_lt h
      _ = (x * dy * D / ((y - dy) * g) + 1) * (y - dy) * g := by ac_rfl
  have h2 := Nat.le_of_mul_le_mul_right h1 hg
  have e : x * y = x * (y - dy) + x * dy := by
    rw [← Nat.mul_add]; congr 1; omega
  rw [Nat.add_mul, e]
  omega

/-- The output is never better than the spot price: `out * x ≤ dx * y`. -/
theorem amountOut_mul_le_spot {D g x y dx : Nat} (hD : 0 < D) (hgD : g ≤ D) :
    amountOut D g x y dx * x ≤ dx * y := by
  have h := amountOut_mul_le D g x y dx
  have h1 : amountOut D g x y dx * x * D ≤ dx * y * D :=
    calc amountOut D g x y dx * x * D = amountOut D g x y dx * (x * D) := Nat.mul_assoc _ _ _
      _ ≤ amountOut D g x y dx * (x * D + dx * g) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      _ ≤ dx * g * y := h
      _ = dx * y * g := Nat.mul_right_comm _ _ _
      _ ≤ dx * y * D := Nat.mul_le_mul_left _ hgD
  exact Nat.le_of_mul_le_mul_right h1 hD

/-- More in, more out. -/
theorem amountOut_mono {D g x y dx dx' : Nat} (h : dx ≤ dx') :
    amountOut D g x y dx ≤ amountOut D g x y dx' := by
  unfold amountOut
  rcases Nat.eq_zero_or_pos (x * D + dx * g) with h0 | h0
  · rw [h0, Nat.div_zero]; exact Nat.zero_le _
  have h0' : 0 < x * D + dx' * g :=
    Nat.lt_of_lt_of_le h0 (Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _)
  apply div_le_div_of_mul_le h0 h0'
  have : dx * (x * D + dx' * g) ≤ dx' * (x * D + dx * g) := by
    have e1 : dx * (x * D + dx' * g) = dx * (x * D) + dx * dx' * g := by
      rw [Nat.mul_add]; ac_rfl
    have e2 : dx' * (x * D + dx * g) = dx' * (x * D) + dx * dx' * g := by
      rw [Nat.mul_add]; ac_rfl
    rw [e1, e2]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _
  calc dx * g * y * (x * D + dx' * g) = g * y * (dx * (x * D + dx' * g)) := by ac_rfl
    _ ≤ g * y * (dx' * (x * D + dx * g)) := Nat.mul_le_mul_left _ this
    _ = dx' * g * y * (x * D + dx * g) := by ac_rfl

/-- Price impact: the average price of a larger trade is no better. For `dx ≤ dx'`, the output per
unit in of the larger trade does not exceed that of the smaller one by more than the rounding of the
smaller: `out(dx') * dx < (out(dx) + 1) * dx'`, that is `out(dx') / dx' < (out(dx) + 1) / dx`. -/
theorem amountOut_avg_le {D g x y dx dx' : Nat} (hx : 0 < x * D) (hd : 0 < dx') (h : dx ≤ dx') :
    amountOut D g x y dx' * dx < (amountOut D g x y dx + 1) * dx' := by
  rcases Nat.eq_zero_or_pos dx with h0 | hpos
  · subst h0; rw [Nat.mul_zero]; exact Nat.mul_pos (Nat.succ_pos _) hd
  have d1 : 0 < x * D + dx * g := Nat.lt_of_lt_of_le hx (Nat.le_add_right _ _)
  have d2 : 0 < x * D + dx' * g := Nat.lt_of_lt_of_le hx (Nat.le_add_right _ _)
  have h1 := Nat.div_mul_le_self (dx' * g * y) (x * D + dx' * g)
  have h2 := lt_div_add_one_mul (dx * g * y) (x * D + dx * g) d1
  unfold amountOut
  -- out' * dx * (xD + dx' g) * (xD + dx g) ≤ dx' g y dx (xD + dx g) ≤ dx' g y dx (xD + dx' g)
  -- < (out + 1)(xD + dx g) dx' (xD + dx' g)
  apply Nat.lt_of_mul_lt_mul_right (a := (x * D + dx' * g) * (x * D + dx * g))
  calc dx' * g * y / (x * D + dx' * g) * dx * ((x * D + dx' * g) * (x * D + dx * g))
      = (dx' * g * y / (x * D + dx' * g) * (x * D + dx' * g)) * (dx * (x * D + dx * g)) := by
        ac_rfl
    _ ≤ dx' * g * y * (dx * (x * D + dx * g)) := Nat.mul_le_mul_right _ h1
    _ = dx * g * y * (dx' * (x * D + dx * g)) := by
        ac_rfl
    _ ≤ dx * g * y * (dx' * (x * D + dx' * g)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _))
    _ < (dx * g * y / (x * D + dx * g) + 1) * (x * D + dx * g) * (dx' * (x * D + dx' * g)) :=
        Nat.mul_lt_mul_of_pos_right h2 (Nat.mul_pos (Nat.lt_of_lt_of_le hpos h) d2)
    _ = (dx * g * y / (x * D + dx * g) + 1) * dx' * ((x * D + dx' * g) * (x * D + dx * g)) := by
        ac_rfl

/-! ## Constant product: liquidity -/

/-- A constant-product pool: reserves and liquidity tokens issued. -/
structure CPool where
  /-- Reserve of the first token. -/
  x : Nat
  /-- Reserve of the second token. -/
  y : Nat
  /-- Liquidity tokens outstanding. -/
  L : Nat
  deriving DecidableEq, Repr

/-- The product of the reserves per liquidity token squared does not fall from `p` to `q`:
`p.x * p.y * q.L^2 ≤ q.x * q.y * p.L^2`. With `sqrt(x * y) / L` the value of a liquidity token
in the geometric mean of the two assets, this says a liquidity token is worth no less. -/
def KPerLNotBelow (p q : CPool) : Prop := p.x * p.y * (q.L * q.L) ≤ q.x * q.y * (p.L * p.L)

/-- Reflexivity. -/
theorem kPerL_refl (p : CPool) : KPerLNotBelow p p := Nat.le_refl _

/-- The comparison chains through a pool with liquidity outstanding. -/
theorem kPerL_trans {p q r : CPool} (h1 : KPerLNotBelow p q) (h2 : KPerLNotBelow q r) (hq : 0 < q.L) :
    KPerLNotBelow p r := by
  unfold KPerLNotBelow at *
  have hq2 : 0 < q.L * q.L := Nat.mul_pos hq hq
  apply Nat.le_of_mul_le_mul_right _ hq2
  calc p.x * p.y * (r.L * r.L) * (q.L * q.L) = p.x * p.y * (q.L * q.L) * (r.L * r.L) :=
        Nat.mul_right_comm _ _ _
    _ ≤ q.x * q.y * (p.L * p.L) * (r.L * r.L) := Nat.mul_le_mul_right _ h1
    _ = q.x * q.y * (r.L * r.L) * (p.L * p.L) := Nat.mul_right_comm _ _ _
    _ ≤ r.x * r.y * (q.L * q.L) * (p.L * p.L) := Nat.mul_le_mul_right _ h2
    _ = r.x * r.y * (p.L * p.L) * (q.L * q.L) := Nat.mul_right_comm _ _ _

/-- A change of reserves that does not lower their product, with the same liquidity, keeps the
comparison. -/
theorem kPerL_of_k_le {p q : CPool} (hL : q.L = p.L) (h : p.x * p.y ≤ q.x * q.y) :
    KPerLNotBelow p q := by
  unfold KPerLNotBelow; rw [hL]; exact Nat.mul_le_mul_right _ h

/-- Liquidity minted for depositing `dx` and `dy`: the smaller of the two ratios, rounded down
(`UniswapV2Pair.mint`, `Math.min(amount0 * totalSupply / reserve0, amount1 * totalSupply /
reserve1)`). -/
def mintAmount (p : CPool) (dx dy : Nat) : Nat := min (dx * p.L / p.x) (dy * p.L / p.y)

/-- Amounts paid out for burning `l` liquidity tokens, rounded down (`UniswapV2Pair.burn`). -/
def burnAmounts (p : CPool) (l : Nat) : Nat × Nat := (l * p.x / p.L, l * p.y / p.L)

/-- Two cross-multiplied ratios multiply. -/
theorem mul_le_mul_of_ratio {a b c d e f : Nat} (h1 : a * c ≤ b * e) (h2 : d * c ≤ f * e) :
    a * d * (c * c) ≤ b * f * (e * e) := by
  calc a * d * (c * c) = (a * c) * (d * c) := by
        ac_rfl
    _ ≤ (b * e) * (f * e) := Nat.mul_le_mul h1 h2
    _ = b * f * (e * e) := by ac_rfl

/-- Minting at most the smaller ratio never lowers the product of the reserves per liquidity token
squared. -/
theorem mint_kPerL (p : CPool) (dx dy l : Nat) (hl : l ≤ mintAmount p dx dy) :
    KPerLNotBelow p ⟨p.x + dx, p.y + dy, p.L + l⟩ := by
  unfold KPerLNotBelow mintAmount at *
  have h1 : l * p.x ≤ dx * p.L := by
    have := Nat.div_mul_le_self (dx * p.L) p.x
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_trans hl (Nat.min_le_left _ _))) this
  have h2 : l * p.y ≤ dy * p.L := by
    have := Nat.div_mul_le_self (dy * p.L) p.y
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_trans hl (Nat.min_le_right _ _))) this
  apply mul_le_mul_of_ratio
  · rw [Nat.mul_add, Nat.add_mul, Nat.mul_comm p.x l]; omega
  · rw [Nat.mul_add, Nat.add_mul, Nat.mul_comm p.y l]; omega

/-- Burning pro rata, rounded down, never lowers the product of the reserves per liquidity token
squared. -/
theorem burn_kPerL (p : CPool) (l : Nat) :
    KPerLNotBelow p ⟨p.x - (burnAmounts p l).1, p.y - (burnAmounts p l).2, p.L - l⟩ := by
  unfold KPerLNotBelow burnAmounts
  dsimp only
  have h1 : l * p.x / p.L * p.L ≤ l * p.x := Nat.div_mul_le_self _ _
  have h2 : l * p.y / p.L * p.L ≤ l * p.y := Nat.div_mul_le_self _ _
  apply mul_le_mul_of_ratio
  · rw [Nat.mul_sub, Nat.sub_mul, Nat.mul_comm p.x l]; omega
  · rw [Nat.mul_sub, Nat.sub_mul, Nat.mul_comm p.y l]; omega

/-! ## Constant product: a pool model -/

/-- Operations on a constant-product pool. -/
inductive CPOp where
  /-- `dx` of the first token in, priced by `getAmountOut`. -/
  | swapXY (dx : Nat)
  /-- `dy` of the second token in, priced by `getAmountOut`. -/
  | swapYX (dy : Nat)
  /-- `dx` and `dy` added for the liquidity `mintAmount` gives. -/
  | add (dx dy : Nat)
  /-- `l` liquidity tokens burned for their pro-rata reserves. -/
  | remove (l : Nat)
  deriving DecidableEq, Repr

/-- One operation with fee `fee / D` (`g = D - fee`). A swap against an empty reserve and a
removal above the supply are refused; a removal of every token is refused (Uniswap V2 locks the
minimum liquidity forever). -/
def step (D g : Nat) (p : CPool) : CPOp → CPool
  | .swapXY dx => if 0 < p.x ∧ 0 < p.y then
      ⟨p.x + dx, p.y - amountOut D g p.x p.y dx, p.L⟩ else p
  | .swapYX dy => if 0 < p.x ∧ 0 < p.y then
      ⟨p.x - amountOut D g p.y p.x dy, p.y + dy, p.L⟩ else p
  | .add dx dy => if 0 < p.x ∧ 0 < p.y then
      ⟨p.x + dx, p.y + dy, p.L + mintAmount p dx dy⟩ else p
  | .remove l => if l < p.L then
      ⟨p.x - (burnAmounts p l).1, p.y - (burnAmounts p l).2, p.L - l⟩ else p

/-- An operation that is not a removal. -/
def CPOp.NotRemove : CPOp → Prop
  | .remove _ => False
  | _ => True

/-- Swaps and adds never lower the product of the reserves. -/
theorem step_k_le {D g : Nat} (hg : 0 < g) (hgD : g ≤ D) (p : CPool) (o : CPOp) (ho : o.NotRemove) :
    p.x * p.y ≤ (step D g p o).x * (step D g p o).y := by
  cases o with
  | swapXY dx =>
    simp only [step]; split
    · exact k_le_swapOut hg hgD
    · exact Nat.le_refl _
  | swapYX dy =>
    simp only [step]; split
    · rw [Nat.mul_comm p.x, Nat.mul_comm (p.x - _)]; exact k_le_swapOut hg hgD
    · exact Nat.le_refl _
  | add dx dy =>
    simp only [step]; split
    · exact Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    · exact Nat.le_refl _
  | remove l => exact ho.elim

/-- The product of the reserves never decreases over any sequence of swaps and adds. -/
theorem run_k_le {D g : Nat} (hg : 0 < g) (hgD : g ≤ D) (p : CPool) {ops : List CPOp}
    (ho : ∀ o ∈ ops, o.NotRemove) :
    p.x * p.y ≤ (Seq.run (step D g) p ops).x * (Seq.run (step D g) p ops).y := by
  induction ops generalizing p with
  | nil => exact Nat.le_refl _
  | cons o ops ih =>
    exact Nat.le_trans (step_k_le hg hgD p o (ho o (by simp)))
      (ih _ (fun o' h => ho o' (by simp [h])))

/-- No operation lowers the product of the reserves per liquidity token squared. -/
theorem step_kPerL {D g : Nat} (hg : 0 < g) (hgD : g ≤ D) (p : CPool) (o : CPOp) :
    KPerLNotBelow p (step D g p o) := by
  cases o with
  | remove l =>
    simp only [step]; split
    · exact burn_kPerL p l
    · exact kPerL_refl p
  | add dx dy =>
    simp only [step]; split
    · exact mint_kPerL p dx dy _ (Nat.le_refl _)
    · exact kPerL_refl p
  | swapXY dx => exact kPerL_of_k_le (by simp only [step]; split <;> rfl) (step_k_le hg hgD p _ trivial)
  | swapYX dy => exact kPerL_of_k_le (by simp only [step]; split <;> rfl) (step_k_le hg hgD p _ trivial)

/-- The product of the reserves per liquidity token squared never decreases over any sequence of
swaps, adds and removes along which liquidity stays outstanding. -/
theorem run_kPerL {D g : Nat} (hg : 0 < g) (hgD : g ≤ D) (p : CPool) (ops : List CPOp)
    (h : ∀ q ∈ Seq.trace (step D g) p ops, 0 < q.L) :
    KPerLNotBelow p (Seq.run (step D g) p ops) :=
  Seq.run_rel_of_trace (C := fun q => 0 < q.L) kPerL_refl (fun _ _ _ h1 h2 hq => kPerL_trans h1 h2 hq)
    (fun q o _ => step_kPerL hg hgD q o) p ops h

/-- Liquidity never runs out once outstanding: removals of every token are refused. -/
theorem step_L_pos {D g : Nat} (p : CPool) (o : CPOp) (h : 0 < p.L) : 0 < (step D g p o).L := by
  cases o with
  | remove l => simp only [step]; split <;> (try dsimp only) <;> omega
  | add dx dy => simp only [step]; split <;> (try dsimp only) <;> omega
  | swapXY dx => simp only [step]; split <;> (try dsimp only) <;> omega
  | swapYX dy => simp only [step]; split <;> (try dsimp only) <;> omega

/-- So the comparison holds over every sequence from a pool with liquidity outstanding. -/
theorem run_kPerL_of_pos {D g : Nat} (hg : 0 < g) (hgD : g ≤ D) (p : CPool) (ops : List CPOp)
    (h : 0 < p.L) : KPerLNotBelow p (Seq.run (step D g) p ops) :=
  run_kPerL hg hgD p ops (Seq.trace_invariant (I := fun q => 0 < q.L)
    (fun q o hq => step_L_pos q o hq) h ops)

/-! ## Invariant pools -/

/-- `b` with entry `i` replaced by `x` and entry `j` replaced by `y` (for `i ≠ j`). -/
def update2 (b : Nat → Nat) (i x j y : Nat) : Nat → Nat :=
  fun k => if k = i then x else if k = j then y else b k

/-- Entry `i` of `update2`. -/
@[simp] theorem update2_left (b : Nat → Nat) (i x j y : Nat) : update2 b i x j y i = x := by
  simp [update2]

/-- Entry `j ≠ i` of `update2`. -/
theorem update2_right (b : Nat → Nat) {i j : Nat} (x y : Nat) (h : j ≠ i) :
    update2 b i x j y j = y := by
  simp [update2, h]

/-- Other entries of `update2`. -/
theorem update2_other (b : Nat → Nat) {i j k : Nat} (x y : Nat) (hi : k ≠ i) (hj : k ≠ j) :
    update2 b i x j y k = b k := by
  simp [update2, hi, hj]

/-- An invariant on the balances of the tokens `0 .. n - 1` that does not decrease when no balance
decreases (Balancer's `InvariantMonotone`). -/
def InvariantMonotone (inv : (Nat → Nat) → Nat) (n : Nat) : Prop :=
  ∀ b b' : Nat → Nat, (∀ k, k < n → b k ≤ b' k) → inv b ≤ inv b'

/-- A swap keeps a monotone invariant when the priced trade keeps it and the settled balances
dominate the priced ones. -/
theorem invariant_le_of_dominates {inv : (Nat → Nat) → Nat} {n : Nat} (hm : InvariantMonotone inv n)
    {b b' : Nat → Nat} {i j gain loss : Nat}
    (hsound : inv b ≤ inv (update2 b i (b i + gain) j (b j - loss)))
    (hdom : ∀ k, k < n → update2 b i (b i + gain) j (b j - loss) k ≤ b' k) : inv b ≤ inv b' :=
  Nat.le_trans hsound (hm _ _ hdom)

/-- A raw amount added to a balance adds at least its scaled value rounded down. -/
theorem scaleDown_add_ge (one a x r : Nat) :
    scaleDown one a r + scaleDown one x r ≤ scaleDown one (a + x) r := by
  unfold scaleDown mulDown mulDiv
  rw [Nat.add_mul]
  exact div_add_div_le _ _ _

/-- A raw amount taken from a balance takes at most its scaled value rounded up. -/
theorem scaleDown_sub_ge (one : Nat) {a x : Nat} (r : Nat) (hone : 0 < one) (h : x ≤ a) :
    scaleDown one a r ≤ scaleDown one (a - x) r + scaleUp one x r := by
  have h1 := lt_div_add_one_mul ((a - x) * r) one hone
  have h2 := le_mulUp_mul one x r hone
  have h3 := Nat.div_mul_le_self (a * r) one
  have e : a * r = (a - x) * r + x * r := by rw [← Nat.add_mul]; congr 1; omega
  unfold scaleDown scaleUp mulDown mulDiv
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hone).2
  rw [Nat.succ_mul, Nat.add_mul]
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

/-- The domination a swap needs, for balances measured in scaled units rounded down (Balancer's
`_upscaleArray`). The raw balances move by `ain` into token `i` and `aout` out of token `j`; the
math was credited `gain` scaled units in, at most the amount in rounded down
(`gain * one ≤ ain * rate i`), and debited `loss` scaled units out, at least the amount out
(`aout * rate j ≤ loss * one`). Then the scaled balances after settlement dominate the priced ones
on every token. -/
theorem scaled_dominates (one : Nat) (hone : 0 < one) (raw rate : Nat → Nat) {i j : Nat}
    (hij : i ≠ j) {ain aout gain loss : Nat} (haout : aout ≤ raw j)
    (hgain : gain * one ≤ ain * rate i) (hloss : aout * rate j ≤ loss * one) (k : Nat) :
    update2 (fun t => scaleDown one (raw t) (rate t)) i (scaleDown one (raw i) (rate i) + gain) j
        (scaleDown one (raw j) (rate j) - loss) k ≤
      scaleDown one (update2 raw i (raw i + ain) j (raw j - aout) k) (rate k) := by
  by_cases hi : k = i
  · subst hi
    simp only [update2_left]
    have h1 := scaleDown_add_ge one (raw k) ain (rate k)
    have h2 : gain ≤ scaleDown one ain (rate k) :=
      (Nat.le_div_iff_mul_le hone).2 hgain
    omega
  · by_cases hj : k = j
    · subst hj
      rw [update2_right _ _ _ hi, update2_right _ _ _ hi]
      have h1 := scaleDown_sub_ge one (rate k) hone haout
      have h2 : scaleUp one aout (rate k) ≤ loss := (ceilDiv_le_iff hone).2 hloss
      omega
    · rw [update2_other _ _ _ hi hj, update2_other _ _ _ hi hj]
      exact Nat.le_refl _

/-! ### A pool-math interface -/

/-- Pool math on balances `b`: an invariant (StableMath's `D`, the constant product) and the two
pricing functions (`_calcOutGivenIn`, `_calcInGivenOut`; token `i` in, token `j` out). -/
structure PoolMath where
  /-- The invariant of the balances. -/
  invariant : (Nat → Nat) → Nat
  /-- The amount of token `j` out for `x` of token `i` in. -/
  outGivenIn : (Nat → Nat) → Nat → Nat → Nat → Nat
  /-- The amount of token `i` in for `x` of token `j` out. -/
  inGivenOut : (Nat → Nat) → Nat → Nat → Nat → Nat

/-- A given-in trade priced by the math pays out at most the balance and keeps the invariant. -/
def OutGivenInSound (m : PoolMath) (n : Nat) : Prop :=
  ∀ (b : Nat → Nat) (i j x : Nat), i ≠ j → i < n → j < n →
    m.outGivenIn b i j x ≤ b j ∧
    m.invariant b ≤ m.invariant (update2 b i (b i + x) j (b j - m.outGivenIn b i j x))

/-- A given-out trade below the balance, priced by the math, keeps the invariant. -/
def InGivenOutSound (m : PoolMath) (n : Nat) : Prop :=
  ∀ (b : Nat → Nat) (i j x : Nat), i ≠ j → i < n → j < n → x < b j →
    m.invariant b ≤ m.invariant (update2 b i (b i + m.inGivenOut b i j x) j (b j - x))

/-- The contract of Balancer's swap specification for an `n`-token pool: a monotone invariant that
trades priced by the math keep. -/
structure WellBehaved (m : PoolMath) (n : Nat) : Prop where
  /-- The invariant does not decrease when no balance decreases. -/
  monotone : InvariantMonotone m.invariant n
  /-- Given-in trades keep it. -/
  outGivenIn : OutGivenInSound m n
  /-- Given-out trades keep it. -/
  inGivenOut : InGivenOutSound m n

/-- A given-in swap settled in raw units keeps the invariant of the scaled balances (rounded
down) when the math was credited at most the amount in, rounded down, and the amount out, in scaled
units, is at most what the math priced. -/
theorem WellBehaved.scaled_swapIn {m : PoolMath} {n : Nat} (hw : WellBehaved m n) {one : Nat}
    (hone : 0 < one) (raw rate : Nat → Nat) {i j x ain aout : Nat} (hij : i ≠ j) (hi : i < n)
    (hj : j < n) (hgain : x * one ≤ ain * rate i)
    (hloss : aout * rate j ≤
      m.outGivenIn (fun k => scaleDown one (raw k) (rate k)) i j x * one) (haout : aout ≤ raw j) :
    m.invariant (fun k => scaleDown one (raw k) (rate k)) ≤
      m.invariant (fun k => scaleDown one (update2 raw i (raw i + ain) j (raw j - aout) k) (rate k)) :=
  invariant_le_of_dominates hw.monotone (hw.outGivenIn _ i j x hij hi hj).2
    (fun k _ => scaled_dominates one hone raw rate hij haout hgain hloss k)

/-- A given-out swap settled in raw units keeps the invariant of the scaled balances when the
amount out, rounded up, is below the scaled balance and the amount in, in scaled units, covers
what the math priced. -/
theorem WellBehaved.scaled_swapOut {m : PoolMath} {n : Nat} (hw : WellBehaved m n) {one : Nat}
    (hone : 0 < one) (raw rate : Nat → Nat) {i j x ain aout : Nat} (hij : i ≠ j) (hi : i < n)
    (hj : j < n) (hx : x < scaleDown one (raw j) (rate j)) (hloss : aout * rate j ≤ x * one)
    (hgain : m.inGivenOut (fun k => scaleDown one (raw k) (rate k)) i j x * one ≤ ain * rate i)
    (haout : aout ≤ raw j) :
    m.invariant (fun k => scaleDown one (raw k) (rate k)) ≤
      m.invariant (fun k => scaleDown one (update2 raw i (raw i + ain) j (raw j - aout) k) (rate k)) :=
  invariant_le_of_dominates hw.monotone (hw.inGivenOut _ i j x hij hi hj hx)
    (fun k _ => scaled_dominates one hone raw rate hij haout hgain hloss k)

/-- The two-token constant product (tokens 0 and 1): invariant `b 0 * b 1`, given-in priced at
`b j * x / (b i + x)` rounded down, given-out at `b i * x / (b j - x)` rounded up (and `b i * x`
when `x` is not below the balance). -/
def constantProduct : PoolMath where
  invariant b := b 0 * b 1
  outGivenIn b i j x := b j * x / (b i + x)
  inGivenOut b i j x := if x < b j then ceilDiv (b i * x) (b j - x) else b i * x

/-- A given-in trade on a constant product keeps the product: `u * v ≤ (u + x) * (v - out)`. -/
theorem cp_out_le (u v x : Nat) : u * v ≤ (u + x) * (v - v * x / (u + x)) := by
  have := k_le_swapOut (D := 1) (g := 1) (x := u) (y := v) (dx := x) Nat.one_pos (Nat.le_refl _)
  simp only [amountOut, Nat.mul_one] at this
  rwa [Nat.mul_comm x v] at this

/-- A given-out trade on a constant product keeps the product: `u * v ≤ (u + c) * (v - x)` for the
cost `c` rounded up. -/
theorem cp_in_le {u v x : Nat} (h : x < v) : u * v ≤ (u + ceilDiv (u * x) (v - x)) * (v - x) := by
  have h1 := le_ceilDiv_mul (u * x) (v - x) (by omega)
  have e : u * v = u * (v - x) + u * x := by rw [← Nat.mul_add]; congr 1; omega
  rw [Nat.add_mul, e]
  omega

/-- The constant product is well behaved for two tokens. -/
theorem constantProduct_wellBehaved : WellBehaved constantProduct 2 where
  monotone b b' h := Nat.mul_le_mul (h 0 (by decide)) (h 1 (by decide))
  outGivenIn b i j x hij hi hj := by
    have hc : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
    refine ⟨Nat.div_le_of_le_mul (by
      rw [Nat.mul_comm (b i + x)]; exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)), ?_⟩
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [constantProduct, update2_left, update2_right _ _ _ (by decide : (1 : Nat) ≠ 0)]
      exact cp_out_le _ _ _
    · simp only [constantProduct, update2_left, update2_right _ _ _ (by decide : (0 : Nat) ≠ 1)]
      rw [Nat.mul_comm (b 0), Nat.mul_comm (b 0 - _)]
      exact cp_out_le _ _ _
  inGivenOut b i j x hij hi hj hx := by
    have hc : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [constantProduct, update2_left, update2_right _ _ _ (by decide : (1 : Nat) ≠ 0),
        hx, ↓reduceIte]
      exact cp_in_le hx
    · simp only [constantProduct, update2_left, update2_right _ _ _ (by decide : (0 : Nat) ≠ 1),
        hx, ↓reduceIte]
      rw [Nat.mul_comm (b 0), Nat.mul_comm (b 0 - x)]
      exact cp_in_le hx

/-- A batch keeps the invariant when every successful swap does (`batchSwap` reverts as a whole
when one swap reverts). -/
theorem runAll_invariant_le {σ α : Type} {step : σ → α → Option σ} (V : σ → Nat)
    (h : ∀ s a s', step s a = some s' → V s ≤ V s') {s s' : σ} {as : List α}
    (hr : Seq.runAll step s as = some s') : V s ≤ V s' :=
  Seq.runAll_rel (R := fun x y => V x ≤ V y) (fun _ => Nat.le_refl _)
    (fun _ _ _ h1 h2 => Nat.le_trans h1 h2) h hr

end ProofForgeFin.DeFi.AMM
