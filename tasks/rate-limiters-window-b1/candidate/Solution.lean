import FixedWindow.Spec
import FixedWindow.Lemmas
namespace FixedWindow
instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if (s.clients.map Client.id).Nodup then
    match lookup s.clients r.client with
    | some c =>
      let fresh := decide (c.start + s.window < r.time)
      let used := if fresh then 0 else c.count
      if c.start ≤ r.time ∧ used < s.limit then
        (.ok, { s with clients := s.clients.map fun x =>
          if x.id = r.client then
            { x with start := if fresh then r.time else x.start, count := used + 1 }
          else x })
      else (.rejected, s)
    | none => (.rejected, s)
  else (.rejected, s)
theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_isolation      : Isolation step := sorry
theorem req_reset          : ResetRule step := sorry
theorem req_effects        : Effects step := sorry
theorem req_window_bound   : WindowBound step := sorry
end FixedWindow
