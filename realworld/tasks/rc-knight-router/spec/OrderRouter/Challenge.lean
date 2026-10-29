import OrderRouter.Spec
import OrderRouter.Lemmas
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`OrderRouter.step` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace OrderRouter

def step : Impl := sorry

theorem req_normal_order_routed : NormalOrderRouted step := sorry
theorem req_routes_available    : RoutesAvailable step := sorry
theorem req_never_overroute     : NeverOverroute step := sorry
theorem req_stop_when_filled    : StopWhenFilled step := sorry
theorem req_no_excess_execution : NoExcessExecution step := sorry
theorem req_fill_accounting     : FillAccounting step := sorry

end OrderRouter
