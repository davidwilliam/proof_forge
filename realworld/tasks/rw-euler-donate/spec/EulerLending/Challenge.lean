import EulerLending.Spec
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`EulerLending.step` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace EulerLending

def step : Impl := sorry

theorem req_honest_flow      : HonestFlow step := sorry
theorem req_allowed_succeeds : AllowedSucceeds step := sorry
theorem req_effects          : Effects step := sorry
theorem req_actor_healthy    : ActorHealthy step := sorry
theorem req_stays_healthy    : StaysHealthy step := sorry
theorem req_no_bad_debt      : NoBadDebt step := sorry

end EulerLending
