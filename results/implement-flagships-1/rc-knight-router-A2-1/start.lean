import OrderRouter.Spec
import OrderRouter.Lemmas

namespace OrderRouter

-- Placeholder body; replace it with an implementation that meets the spec.
def step : Impl := fun _ _ _ => default

theorem req_normal_order_routed : NormalOrderRouted step := sorry
theorem req_routes_available    : RoutesAvailable step := sorry
theorem req_never_overroute     : NeverOverroute step := sorry
theorem req_stop_when_filled    : StopWhenFilled step := sorry
theorem req_no_excess_execution : NoExcessExecution step := sorry
theorem req_fill_accounting     : FillAccounting step := sorry

end OrderRouter
