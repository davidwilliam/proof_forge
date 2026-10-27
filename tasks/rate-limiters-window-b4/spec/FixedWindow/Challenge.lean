import FixedWindow.Spec
import FixedWindow.Lemmas
/-!
# Locked challenge (never imports candidate code)

`FixedWindow.step` is a Comparator definition hole. A solution must define it and prove
every theorem below with exactly these statements.
-/

namespace FixedWindow

def step : Impl := sorry

theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_isolation      : Isolation step := sorry
theorem req_reset          : ResetRule step := sorry
theorem req_effects        : Effects step := sorry
theorem req_window_bound   : WindowBound step := sorry

end FixedWindow
