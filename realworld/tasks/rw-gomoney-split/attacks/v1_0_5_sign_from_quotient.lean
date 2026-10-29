import EqualSplit.Spec
/-!
Port of `Money.Split` in Rhymond/go-money 1.0.4 and 1.0.5 (pull request #94): the loop now
hands out `|amount % n|` units, each of `-1` if the quotient `amount / n` is negative and
`+1` otherwise. For a small negative amount the quotient is zero, so the units are positive
(issue #106).
-/
namespace EqualSplit

def split : Impl := fun amount n =>
  if n = 0 then none
  else
    let q := amount.tdiv n
    let l := (amount.tmod n).natAbs
    let v : Int := if q < 0 then -1 else 1
    some ((List.range n).map fun p => q + if p < l then v else 0)

theorem req_valid_succeeds  : ValidSucceeds split := sorry
theorem req_invalid_fails   : InvalidFails split := sorry
theorem req_one_share_each  : OneShareEach split := sorry
theorem req_conservation    : Conserves split := sorry
theorem req_within_one_unit : WithinOneUnit split := sorry
theorem req_sign            : Sign split := sorry

end EqualSplit
