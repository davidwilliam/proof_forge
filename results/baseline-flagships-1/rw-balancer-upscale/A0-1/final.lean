import BalancerSwap.Spec
namespace BalancerSwap
def onSwapGivenIn (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  if p.rate s.tokenOut = 0 then none
  else some ((m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) / p.rate s.tokenOut)
def onSwapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  if p.rate s.tokenIn = 0 then none
  else if ONE <= p.fee then none
  else if scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) then
    some ((ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + (ONE - p.fee) * p.rate s.tokenIn - 1) / ((ONE - p.fee) * p.rate s.tokenIn))
  else none
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn => onSwapGivenIn m p s
  | .givenOut => onSwapGivenOut m p s
theorem req_given_in_succeeds : GivenInSucceeds onSwap := sorry
theorem req_given_out_succeeds : GivenOutSucceeds onSwap := sorry
theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := sorry
theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := sorry
theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := sorry
theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := sorry
theorem req_swap_keeps_value : SwapKeepsValue onSwap := sorry
theorem req_batch_keeps_value : BatchKeepsValue onSwap := sorry
end BalancerSwap
