import OrderRouter.Spec
import OrderRouter.Lemmas
/-!
Seeded attack, side effect: routing is correct on every path, but the cumulative executed
quantity adds the quantity an execution report states, not the shares it executes, so a
report larger than the child order's unexecuted shares inflates the count.
-/
namespace OrderRouter

def step : Impl := fun _ s e =>
  match e with
  | .parent q f =>
    ({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ }, [])
  | .route id liq =>
    if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
      ({ s with parents := upd s.parents id
                  { s.parents id with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) },
                nChildren := s.nChildren + 1,
                children := upd s.children s.nChildren
                  ⟨id, min liq ((s.parents id).qty - (s.parents id).sent), 0⟩ },
       [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩])
    else (s, [])
  | .ack _ => (s, [])
  | .fill k q =>
    if k < s.nChildren then
      ({ s with parents := upd s.parents (s.children k).parent
                  { s.parents (s.children k).parent with
                    cum := (s.parents (s.children k).parent).cum + q },
                children := upd s.children k
                  { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) } },
       [])
    else (s, [])

theorem req_normal_order_routed : NormalOrderRouted step := sorry
theorem req_routes_available    : RoutesAvailable step := sorry
theorem req_never_overroute     : NeverOverroute step := sorry
theorem req_stop_when_filled    : StopWhenFilled step := sorry
theorem req_no_excess_execution : NoExcessExecution step := sorry
theorem req_fill_accounting     : FillAccounting step := sorry

end OrderRouter
