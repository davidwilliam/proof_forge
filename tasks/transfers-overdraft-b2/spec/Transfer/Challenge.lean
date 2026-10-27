import Transfer.Spec
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`Transfer.step` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace Transfer

def step : Impl := sorry

theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_authorization  : AuthorizedOnly step := sorry
theorem req_debit_credit   : DebitCredit step := sorry
theorem req_effects        : Effects step := sorry
theorem req_idempotency    : Idempotent step := sorry
theorem req_limit          : LimitRespected step := sorry
theorem req_conservation   : Conserves step := sorry

end Transfer
