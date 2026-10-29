import EqualSplit.Spec
/-!
Port of `Money.Split` in Rhymond/go-money 1.0.3 (money.go): every share is `amount / n`
with Go's truncating division, and the remainder `amount % n` (which has the sign of
`amount`) is handed out one unit at a time to the first parties by a loop
`for p := 0; l != 0; p++ { ...; l-- }`. A negative remainder never reaches zero, so the loop
indexes past the last party and panics, modeled as `none`. `n <= 0` returns an error.
-/
namespace EqualSplit

def split : Impl := fun amount n =>
  if n = 0 then none
  else
    let q := amount.tdiv n
    let l := amount.tmod n
    if l < 0 then none
    else some ((List.range n).map fun p => q + if p < l.toNat then 1 else 0)

theorem req_valid_succeeds  : ValidSucceeds split := sorry
theorem req_invalid_fails   : InvalidFails split := sorry
theorem req_one_share_each  : OneShareEach split := sorry
theorem req_conservation    : Conserves split := sorry
theorem req_within_one_unit : WithinOneUnit split := sorry
theorem req_sign            : Sign split := sorry

end EqualSplit
