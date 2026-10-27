import Reversal.Spec
import Reversal.Lemmas
namespace Reversal
instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance
/-- Add `amt` to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b
/-- Post every line, first to last. -/
def postLines : List Line → (AccountId → Int) → (AccountId → Int)
  | [], bal => bal
  | l :: ls, bal => postLines ls (adjust bal l.1 l.2)
def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then
      (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] })
    else (.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | some e =>
      if i ∈ s.reversed then (.rejected, s)
      else (.ok, { s with balance := postLines e.lines s.balance,
                          reversed := i :: s.reversed })
    | none => (.rejected, s)
theorem req_post_succeeds    : PostSucceeds step := sorry
theorem req_reverse_succeeds : ReverseSucceeds step := sorry
theorem req_invalid_noop     : InvalidNoop step := sorry
theorem req_post_effects     : PostEffects step := sorry
theorem req_reverse_effects  : ReverseEffects step := sorry
theorem req_reverse_once     : ReverseOnce step := sorry
theorem req_roundtrip        : RoundTrip step := sorry
theorem req_trial_balance    : TrialBalance step := sorry
theorem req_well_formed      : StaysWellFormed step := sorry
theorem req_consistent       : StaysConsistent step := sorry
end Reversal
