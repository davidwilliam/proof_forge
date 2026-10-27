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
    let bal := (List.range (e.lines.length - 1)).foldl
      (fun b i => match e.lines[i]? with
        | some l => adjust b l.1 l.2
        | none => b) s.balance
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
