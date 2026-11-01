import KyberSwapStep.Spec
import KyberSwapStep.Lemmas
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`KyberSwapStep.computeSwapStep` is a Comparator definition hole. A solution must define it and
prove every theorem below with exactly these statements.
-/

namespace KyberSwapStep

def computeSwapStep : StepFn := sorry

theorem req_in_within_target  : InWithinTarget computeSwapStep := sorry
theorem req_out_within_target : OutWithinTarget computeSwapStep := sorry
theorem req_step_reach        : StepReach computeSwapStep := sorry
theorem req_step_paid         : StepPaid computeSwapStep := sorry
theorem req_in_fee_liquidity  : InFeeLiquidity computeSwapStep := sorry
theorem req_out_fee_liquidity : OutFeeLiquidity computeSwapStep := sorry
theorem req_pool_crosses      : PoolCrosses computeSwapStep := sorry
theorem req_deployed_step     : DeployedStep computeSwapStep := sorry

end KyberSwapStep
