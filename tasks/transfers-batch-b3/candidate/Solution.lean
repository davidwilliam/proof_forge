import Batch.Spec
import Batch.Lemmas
namespace Batch
/-- Admission check of one leg against the running balances. -/
def legAllowed (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && l.source != l.target &&
  s.accounts.contains l.source &&
  s.accounts.contains l.target &&
  decide (-(s.limit l.source : Int) ≤ bal l.source - l.amount)

/-- Move one leg's amount between the running balances. -/
def post (bal : AccountId → Int) (l : Leg) : AccountId → Int :=
  fun a => bal a - (if a = l.source then (l.amount : Int) else 0)
    + (if a = l.target then (l.amount : Int) else 0)

/-- Final balances after the legs, or `none` if a leg is not allowed. -/
def applyAll (s : State) : List Leg → Option (AccountId → Int)
  | [] => some s.balance
  | l :: ls =>
    match applyAll s ls with
    | some bal => if legAllowed s bal l then some (post bal l) else none
    | none => none

def step : Impl := fun s r =>
  if s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied then
    match applyAll s r.legs with
    | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
    | none => (.rejected, s)
  else (.rejected, s)

theorem req_valid_succeeds   : ValidSucceeds step := sorry
theorem req_atomicity        : Atomicity step := sorry
theorem req_single_leg       : SingleLeg step := sorry
theorem req_effects          : Effects step := sorry
theorem req_idempotency      : Idempotent step := sorry
theorem req_conservation     : Conserves step := sorry
theorem req_limit_every_step : LimitEveryStep step := sorry
end Batch
