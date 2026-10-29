import ClmmMath.Spec
import ClmmMath.Lemmas
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`ClmmMath.checkedShlw` is a Comparator definition hole. A solution must define it and prove
every theorem below with exactly these statements.
-/

namespace ClmmMath

def checkedShlw : Shlw := sorry

theorem req_shlw_exact      : ShlwExact checkedShlw := sorry
theorem req_shlw_complete   : ShlwComplete checkedShlw := sorry
theorem req_delta_a_covers  : DeltaACovers checkedShlw := sorry
theorem req_delta_a_tight   : DeltaATight checkedShlw := sorry
theorem req_delta_a_floor   : DeltaAFloor checkedShlw := sorry

end ClmmMath
