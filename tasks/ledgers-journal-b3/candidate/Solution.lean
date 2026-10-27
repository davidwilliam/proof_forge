import Journal.Spec
import Journal.Lemmas
namespace Journal
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance
/-- Add `amt` to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b
def step : Impl := fun s e =>
  if ValidEntry s e then
    let bal := e.lines.foldl (fun b l => fun x => if x = l.1 then s.balance x + l.2 else b x) s.balance
    (.ok, { s with balance := bal, posted := e.id :: s.posted })
  else (.rejected, s)
theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_known_accounts : KnownAccounts step := sorry
theorem req_balanced       : Balanced step := sorry
theorem req_effects        : Effects step := sorry
theorem req_idempotency    : Idempotent step := sorry
theorem req_trial_balance  : TrialBalance step := sorry
end Journal
