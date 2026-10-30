import BalancerSwap.Spec
namespace BalancerSwap
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn =>
    if p.rate s.tokenOut = 0 then none
    else
      let x := netInDown p s
      let o := m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut x
      some (o * ONE / p.rate s.tokenOut)
  | .givenOut =>
    let D := (ONE - p.fee) * p.rate s.tokenIn
    if D = 0 then none
    else
      let xo := scaleUp s.amount (p.rate s.tokenOut)
      let b := scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut)
      if xo < b then
        let inp := m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut xo
        let N := ONE * ONE * inp
        some ((N + D - 1) / D)
      else none

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by sorry

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by sorry

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by sorry

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by sorry

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by sorry

theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := by sorry

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by sorry

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by sorry

end BalancerSwap
