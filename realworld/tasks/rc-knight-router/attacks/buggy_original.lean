import OrderRouter.Spec
import OrderRouter.Lemmas
/-!
Port of the router behavior described in the SEC order against Knight Capital Americas LLC
(Release No. 34-70694, October 16, 2013), reconstructed from the SEC findings. Knight's code
is not public; this is not Knight's code.

Paths, as the order describes them:
- A parent order without the flag takes the regular path.
- A parent order with the flag takes the new RLP path on a server that received the new
  code (paragraphs 13 and 16).
- On a server that did not receive the new code (`Build.legacy`, paragraph 15), a parent
  order with the flag takes the Power Peg path, which is still present and callable
  (paragraphs 13 and 16).

Power Peg stops routing child orders once its cumulative quantity reaches the parent's
quantity (paragraph 14). In 2005 the cumulative quantity function was moved to an earlier
point in the code sequence, and Power Peg was not retested (paragraph 14); on August 1,
2012 the server sent child orders without regard to the executions already received
(paragraph 16). The order does not describe the code. This port models that outcome:
execution reports advance the cumulative quantity only for parent orders that do not take
the Power Peg path, so the Power Peg stop check reads a count that execution reports never
advance.
-/
namespace OrderRouter

/-- Regular and RLP paths: send the available liquidity capped at the shares not yet sent. -/
def routeBySent (s : State) (id liq : Nat) : State × List Child :=
  let p := s.parents id
  let c := min liq (p.qty - p.sent)
  if id < s.nParents ∧ 0 < c then
    ({ s with parents := upd s.parents id { p with sent := p.sent + c },
              nChildren := s.nChildren + 1,
              children := upd s.children s.nChildren ⟨id, c, 0⟩ }, [⟨id, c⟩])
  else (s, [])

/-- Power Peg path: keep sending until the cumulative quantity reaches the parent quantity. -/
def routePowerPeg (s : State) (id liq : Nat) : State × List Child :=
  let p := s.parents id
  let c := min liq (p.qty - p.cum)
  if id < s.nParents ∧ p.cum < p.qty ∧ 0 < c then
    ({ s with parents := upd s.parents id { p with sent := p.sent + c },
              nChildren := s.nChildren + 1,
              children := upd s.children s.nChildren ⟨id, c, 0⟩ }, [⟨id, c⟩])
  else (s, [])

/-- The path a parent order takes on a server. -/
def powerPegPath (b : Build) (p : ParentRec) : Bool := p.flag && b == .legacy

def step : Impl := fun b s e =>
  match e with
  | .parent q f =>
    ({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ }, [])
  | .route id liq =>
    if powerPegPath b (s.parents id) then routePowerPeg s id liq else routeBySent s id liq
  | .ack _ => (s, [])
  | .fill k q =>
    if k < s.nChildren then
      let c := s.children k
      let x := min q (c.qty - c.done)
      let p := s.parents c.parent
      let p' := if powerPegPath b p then p else { p with cum := p.cum + x }
      ({ s with parents := upd s.parents c.parent p',
                children := upd s.children k { c with done := c.done + x } }, [])
    else (s, [])

theorem req_normal_order_routed : NormalOrderRouted step := sorry
theorem req_routes_available    : RoutesAvailable step := sorry
theorem req_never_overroute     : NeverOverroute step := sorry
theorem req_stop_when_filled    : StopWhenFilled step := sorry
theorem req_no_excess_execution : NoExcessExecution step := sorry
theorem req_fill_accounting     : FillAccounting step := sorry

end OrderRouter
