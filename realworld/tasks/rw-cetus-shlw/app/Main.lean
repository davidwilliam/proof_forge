import Lean.Data.Json
import Solution
/-!
# clmm-sidecar (executable wrapper; NOT proved)

Reads JSON lines and runs the proved definitions on each:

* `{"op": "shlw", "n": nat}` runs `ClmmMath.checkedShlw` and prints
  `{"value": nat, "overflow": bool}`;
* `{"op": "delta_a", "sqrt_price_0": nat, "sqrt_price_1": nat, "liquidity": nat, "round_up": bool}`
  runs `ClmmMath.getDeltaA ClmmMath.checkedShlw` and prints `{"amount": nat}`, or
  `{"amount": null}` when the Move routine would abort.

`n` must be below `2^256` and the prices and liquidity below `2^128`; any other input is
answered with `{"error":"bad input"}`. The parser and serializer here are TESTED_ONLY.
-/

open Lean ClmmMath

def bv (w : Nat) (j : Json) (key : String) : Except String (BitVec w) := do
  let x ← (j.getObjValD key).getNat?
  if x < 2 ^ w then return BitVec.ofNat w x else throw s!"{key} out of range"

def runOne (line : String) : Except String String := do
  let j ← Json.parse line
  let op ← (j.getObjValD "op").getStr?
  if op == "shlw" then
    let n ← bv 256 j "n"
    let (v, o) := checkedShlw n
    return (Json.mkObj [("value", toJson v.toNat), ("overflow", toJson o)]).compress
  else if op == "delta_a" then
    let sp0 ← bv 128 j "sqrt_price_0"
    let sp1 ← bv 128 j "sqrt_price_1"
    let l ← bv 128 j "liquidity"
    let up ← (j.getObjValD "round_up").getBool?
    let out : Json := match getDeltaA checkedShlw sp0 sp1 l up with
      | some a => toJson a.toNat
      | none => Json.null
    return (Json.mkObj [("amount", out)]).compress
  else throw s!"unknown op {op}"

/-- One JSON request per stdin line, one JSON result per stdout line. -/
partial def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop (code : UInt32) : IO UInt32 := do
    let line ← stdin.getLine
    if line.isEmpty then return code
    let line := line.trimAsciiEnd.toString
    if line.isEmpty then loop code
    else
      match runOne line with
      | .ok out => stdout.putStrLn out; stdout.flush; loop code
      | .error e => IO.eprintln s!"bad input: {e}"; stdout.putStrLn "{\"error\":\"bad input\"}"; loop 2
  loop 0
