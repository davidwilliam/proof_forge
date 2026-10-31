import BalancerSwap.Spec
namespace BalancerSwap

theorem ONE_pos : 0 < ONE := by unfold ONE; decide

theorem ceil_ge (a r : Nat) (hr : 0 < r) : a ≤ (a + r - 1) / r * r := by
  have h1 : r * ((a + r - 1) / r) + (a + r - 1) % r = a + r - 1 := Nat.div_add_mod _ _
  have h2 : (a + r - 1) % r < r := Nat.mod_lt _ hr
  have hc : r * ((a + r - 1) / r) = (a + r - 1) / r * r := Nat.mul_comm _ _
  omega

theorem succ_mul_gt (n r : Nat) (hr : 0 < r) : n < (n / r + 1) * r := by
  have h1 : r * (n / r) + n % r = n := Nat.div_add_mod _ _
  have h2 : n % r < r := Nat.mod_lt _ hr
  have hexp : (n / r + 1) * r = r * (n / r) + r := by
    rw [Nat.add_mul, Nat.mul_comm (n / r) r, Nat.mul_comm 1 r, Nat.mul_one]
  rw [hexp]
  omega

def qi (m : PoolMath) (p : Pool) (s : Swap) : Nat :=
  m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
def qo (m : PoolMath) (p : Pool) (s : Swap) : Nat :=
  m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))
def mid (m : PoolMath) (p : Pool) (s : Swap) : Nat :=
  (qo m p s * ONE + p.rate s.tokenIn - 1) / p.rate s.tokenIn
def quo (m : PoolMath) (p : Pool) (s : Swap) : Nat :=
  (mid m p s * ONE + (ONE - p.fee) - 1) / (ONE - p.fee)
def yIn (m : PoolMath) (p : Pool) (s : Swap) : Nat :=
  qi m p s * ONE / p.rate s.tokenOut

def onSwap : Impl := fun m p s =>
  if s.kind = Kind.givenIn then
    if p.rate s.tokenOut = 0 then none else some (yIn m p s)
  else
    if scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut then
      if p.rate s.tokenIn = 0 then none
      else if p.fee < ONE then some (quo m p s) else none
    else none

theorem req_given_in_succeeds : GivenInSucceeds onSwap := sorry
theorem req_given_out_succeeds : GivenOutSucceeds onSwap := sorry
theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := sorry
theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := sorry
theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := sorry
theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := sorry
theorem req_swap_keeps_value : SwapKeepsValue onSwap := sorry
theorem req_batch_keeps_value : BatchKeepsValue onSwap := sorry

end BalancerSwap
