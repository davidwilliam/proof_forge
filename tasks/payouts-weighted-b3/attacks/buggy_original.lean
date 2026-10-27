import WeightedPayout.Spec
import WeightedPayout.Lemmas
namespace WeightedPayout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
/-- Preconditions checked before a payout is applied. -/
def CanPay (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧
  0 < r.amount ∧
  r.recipients ≠ [] ∧
  r.weights.length = r.recipients.length ∧
  (∀ w ∈ r.weights, 0 < w) ∧
  r.source ∉ r.recipients ∧
  r.source ∈ s.accounts ∧
  (∀ x ∈ r.recipients, x ∈ s.accounts) ∧
  s.auth r.requester r.source = true ∧
  (r.amount : Int) ≤ s.balance r.source ∧
  r.txId ∉ s.applied
instance instDecidableCanPay (s : State) (r : Request) : Decidable (CanPay s r) := by
  unfold CanPay; infer_instance
/-- Credit recipients in order: position `i` gets its floor share, plus one cent while
`i < extra`. -/
def payFrom (A W extra : Nat) : Nat → List AccountId → List Nat → (AccountId → Int) → (AccountId → Int)
  | _, [], _, bal => bal
  | i, x :: xs, ws, bal =>
      payFrom A W extra (i + 1) xs ws.tail
        (fun b => if b = x then bal b + ((A * ws.headD 0 / W + if i < extra then 1 else 0 : Nat) : Int)
                  else bal b)
def step : Impl := fun s r =>
  if CanPay s r then
    let debited := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
    (.ok, { s with
      balance := payFrom r.amount (natSum r.weights) (leftover r.amount r.weights) 0
                   r.recipients r.weights debited,
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
