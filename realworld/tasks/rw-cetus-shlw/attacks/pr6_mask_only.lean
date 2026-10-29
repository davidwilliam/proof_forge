import ClmmMath.Spec
import ClmmMath.Lemmas
/-!
Port of `checked_shlw` after pull request 6 of CetusProtocol/integer-mate (merge commit
fc84a51c29fabfbfbdb8ed76506b61a07493d492, `sui/sources/math_u256.move` lines 18 to 25), the
first fix merged on 2025-05-22:

```
public fun checked_shlw(n: u256): (u256, bool) {
    let mask = 1 << 192;
    if (n > mask) {
        (0, true)
    } else {
        ((n << 64), false)
    }
}
```
-/
namespace ClmmMath

def checkedShlw : Shlw := fun n =>
  let mask : BitVec 256 := (1 : BitVec 256) <<< 192
  if n > mask then (0, true) else (n <<< 64, false)

theorem req_shlw_exact      : ShlwExact checkedShlw := sorry
theorem req_shlw_complete   : ShlwComplete checkedShlw := sorry
theorem req_delta_a_covers  : DeltaACovers checkedShlw := sorry
theorem req_delta_a_tight   : DeltaATight checkedShlw := sorry
theorem req_delta_a_floor   : DeltaAFloor checkedShlw := sorry

end ClmmMath
