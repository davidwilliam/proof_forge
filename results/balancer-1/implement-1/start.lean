import BalancerSwap.Spec

namespace BalancerSwap

-- Placeholder body; replace it with an implementation that meets the spec.
def onSwap : Impl := fun _ _ _ => none

theorem req_given_in_succeeds        : GivenInSucceeds onSwap := sorry
theorem req_given_out_succeeds       : GivenOutSucceeds onSwap := sorry
theorem req_given_in_pays_at_most    : GivenInPaysAtMost onSwap := sorry
theorem req_given_in_pays_at_least   : GivenInPaysAtLeast onSwap := sorry
theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := sorry
theorem req_given_out_charges_at_most  : GivenOutChargesAtMost onSwap := sorry
theorem req_swap_keeps_value         : SwapKeepsValue onSwap := sorry
theorem req_batch_keeps_value        : BatchKeepsValue onSwap := sorry

end BalancerSwap
