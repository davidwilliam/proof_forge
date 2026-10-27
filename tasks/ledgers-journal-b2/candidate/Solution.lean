import Journal.Spec
import Journal.Lemmas
namespace Journal
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance
/-- Add `amt` to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b
/-- Acceptance check for an entry. -/
def acceptable (s : State) (e : Entry) : Bool :=
  decide s.accounts.Nodup && !e.lines.isEmpty && e.lines.all (fun l => l.2 != 0) &&
  decide (lineSum e.lines = 0) && !s.posted.contains e.id
def step : Impl := fun s e =>
  if acceptable s e then
    let fresh := (e.lines.map (·.1)).eraseDups.filter (fun a => !s.accounts.contains a)
    (.ok, { accounts := s.accounts ++ fresh,
            balance := e.lines.foldl (fun b l => adjust b l.1 l.2) s.balance,
            posted := e.id :: s.posted })
  else (.rejected, s)
theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_known_accounts : KnownAccounts step := sorry
theorem req_balanced       : Balanced step := sorry
theorem req_effects        : Effects step := sorry
theorem req_idempotency    : Idempotent step := sorry
theorem req_trial_balance  : TrialBalance step := sorry
end Journal
