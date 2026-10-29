import ClmmMath.Spec
import ClmmMath.Lemmas
/-!
Port of `checked_shlw` in CetusProtocol/integer-mate, `sui/sources/math_u256.move`, as of
commit 4d09c8ba0527274983c6664a5d5def2e784d4692 (lines 18 to 25; the same function is at lines
19 to 26 of commit 585f17eb3085c283e06ca229c6b6fc4fc2939e57):

```
public fun checked_shlw(n: u256): (u256, bool) {
    let mask = 0xffffffffffffffff << 192;
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
  let mask : BitVec 256 := (0xffffffffffffffff : BitVec 256) <<< 192
  if n > mask then (0, true) else (n <<< 64, false)

theorem req_shlw_exact      : ShlwExact checkedShlw := sorry
theorem req_shlw_complete   : ShlwComplete checkedShlw := sorry
theorem req_delta_a_covers  : DeltaACovers checkedShlw := sorry
theorem req_delta_a_tight   : DeltaATight checkedShlw := sorry
theorem req_delta_a_floor   : DeltaAFloor checkedShlw := sorry

end ClmmMath
