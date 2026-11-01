/-!
# The `sqrt()` builtin of Vyper on decimals (protected)

Owner-reviewed definitions for the code the Vyper compiler v0.4.0 (commit
e9db8d9f7486eae38f5b86531629019ad28f514e) inlines for the builtin `sqrt(d: decimal) -> decimal`,
`vyper/builtins/functions.py`, class `Sqrt` (lines 2117 to 2172):

```
assert x >= 0.0
z: decimal = 0.0

if x == 0.0:
    z = 0.0
else:
    z = x / 2.0 + 0.5
    y: decimal = x

    for i: uint256 in range(256):
        if z == y:
            break
        y = z
        z = (x / z + z) / 2.0
```

The result is `z`. Pull request 4486 (merge commit 2ffc8b3db8b7e32257a72560fa89e7dcf81b5384,
released in v0.4.1) added, after the loop,

```
    if y < z:
        z = y
```

A Vyper `decimal` is a signed 168-bit integer `x` read as `x / 10^10` (`DIVISOR`). The arithmetic
is that of `vyper/codegen/arithmetic.py` at the same commit:

* `a + b` is `add(a, b)` followed by a range check (`clamp_basetype`): outside
  `[-2^167, 2^167 - 1]` it reverts (`dadd`);
* `a / b` is `sdiv(mul(a, DIVISOR), b)` after the check that `b` is not zero
  (`clamp("gt", b, 0)`, an unsigned comparison), followed by the range check (`ddiv`). For
  decimals `|a| < 2^167`, so `a * 10^10` is below `2^201` in absolute value and the 256-bit `mul`
  never wraps; `sdiv` rounds toward zero, which is `Int.tdiv`.

A revert is `none`. The literals `2.0` and `0.5` are `2 * 10^10` and `5 * 10^9`.

`sqrt` is the definition hole. `vyperSqrtWith fin` is the deployed loop followed by
`fin y z`, the value chosen from the last two iterates: the code of v0.4.0 is
`vyperSqrtWith (fun _ z => z)` and the fix of pull request 4486 is
`vyperSqrtWith (fun y z => if y < z then y else z)`.

Candidates may not edit this file. Every requirement is a predicate over an implementation
`sqrt : SqrtFn`; the locked challenge (`VyperSqrt/Challenge.lean`) applies each one to the
definition hole `VyperSqrt.sqrt`.
-/

namespace VyperSqrt

/-- A routine on Vyper decimals, as raw `int168` values; `none` is a revert. -/
abbrev SqrtFn := Int → Option Int

/-- `DIVISOR = 10 ** 10`: a decimal `x` stands for `x / 10^10`. -/
def DIVISOR : Int := 10000000000

/-- The largest decimal, `2^167 - 1` (raw). -/
def MAX_DECIMAL : Int := 187072209578355573530071658587684226515959365500927

/-- The smallest decimal, `-2^167` (raw). -/
def MIN_DECIMAL : Int := -187072209578355573530071658587684226515959365500928

/-- A raw value in the range of `decimal`. -/
def IsDecimal (x : Int) : Prop := MIN_DECIMAL ≤ x ∧ x ≤ MAX_DECIMAL

instance (x : Int) : Decidable (IsDecimal x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The range check after an operation: the value if it is a decimal, else a revert. -/
def clampDecimal (x : Int) : Option Int := if IsDecimal x then some x else none

/-- Decimal `a + b`. -/
def dadd (a b : Int) : Option Int := clampDecimal (a + b)

/-- Decimal `a / b`: reverts on a zero divisor, rounds toward zero, range check. -/
def ddiv (a b : Int) : Option Int :=
  if b = 0 then none else clampDecimal (Int.tdiv (a * DIVISOR) b)

/-- The loop `for i: uint256 in range(256)` with `n` iterations left, on `(y, z)`:
`if z == y: break; y = z; z = (x / z + z) / 2.0`. The result is the final `(y, z)`. -/
def loop (x : Int) : Nat → Int → Int → Option (Int × Int)
  | 0, y, z => some (y, z)
  | n + 1, y, z =>
    if z = y then some (y, z)
    else
      (ddiv x z).bind fun q =>
        (dadd q z).bind fun t =>
          (ddiv t (2 * DIVISOR)).bind fun z' => loop x n z z'

/-- The deployed routine followed by `fin y z`, the value chosen from the last two iterates:
`assert x >= 0.0`, `0.0` for `x == 0.0`, else the seed `z = x / 2.0 + 0.5` with `y = x`, the
loop, and the choice. -/
def vyperSqrtWith (fin : Int → Int → Int) (x : Int) : Option Int :=
  if x < 0 then none
  else if x = 0 then some 0
  else
    ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
      (loop x 256 x z0).map fun p => fin p.1 p.2

/-! ## Requirements -/

/-- REQ-SQRT-NOT-ABOVE: for a decimal input, the result squared never exceeds the input: the root
is rounded down to the nearest `10^-10`, never up (`r * r ≤ x * 10^10` on raw values). -/
def SqrtNotAbove (sqrt : SqrtFn) : Prop :=
  ∀ x r : Int, IsDecimal x → sqrt x = some r → r * r ≤ x * DIVISOR

/-- REQ-SQRT-NOT-BELOW: for a decimal input, the result is less than `10^-10` below the root:
`x * 10^10 < (r + 1) * (r + 1)` on raw values. -/
def SqrtNotBelow (sqrt : SqrtFn) : Prop :=
  ∀ x r : Int, IsDecimal x → sqrt x = some r → x * DIVISOR < (r + 1) * (r + 1)

/-- REQ-SQRT-TOTAL: a non-negative decimal input never reverts. -/
def SqrtTotal (sqrt : SqrtFn) : Prop :=
  ∀ x : Int, IsDecimal x → 0 ≤ x → (sqrt x).isSome

/-- REQ-SQRT-NEG-REVERTS: a negative input reverts (`assert x >= 0.0`). -/
def SqrtNegReverts (sqrt : SqrtFn) : Prop :=
  ∀ x : Int, x < 0 → sqrt x = none

/-- REQ-DEPLOYED-LOOP: the routine is the deployed loop (the seed `x / 2.0 + 0.5`, at most 256
iterations, stopping when two successive iterates are equal) followed by a choice from the last
two iterates. -/
def DeployedLoop (sqrt : SqrtFn) : Prop :=
  ∃ fin : Int → Int → Int, ∀ x : Int, sqrt x = vyperSqrtWith fin x

end VyperSqrt
