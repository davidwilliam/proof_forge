import WeightedPayout.Spec
import WeightedPayout.Lemmas
namespace WeightedPayout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    let unit := r.amount / natSum r.weights
    let extra := r.amount - unit * natSum r.weights
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (match indexOf? r.recipients a with
                             | some i => ((unit * r.weights.getD i 0 + if i < extra then 1 else 0 : Nat) : Int)
                             | none => 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)
theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_authorization  : AuthorizedOnly step := sorry
theorem req_effects        : Effects step := sorry
theorem req_idempotency    : Idempotent step := sorry
theorem req_nonnegative    : NonNegative step := sorry
theorem req_pro_rata       : ProRataShares step := sorry
theorem req_rounding_bound : RoundingBound step := sorry
theorem req_conservation   : Conserves step := sorry
end WeightedPayout
