import FixedWindow.Spec
import FixedWindow.Lemmas
namespace FixedWindow
instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with clients := s.clients.map fun c =>
      if c.id = r.client then advance s c r.time
      else if c.start + s.window ≤ r.time then { c with start := r.time, count := 0 }
      else c })
  else (.rejected, s)
theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_isolation      : Isolation step := sorry
theorem req_reset          : ResetRule step := sorry
theorem req_effects        : Effects step := sorry
theorem req_window_bound   : WindowBound step := sorry
end FixedWindow
