import Lean.Data.Json
import Solution
/-!
# sqrt-sidecar (executable wrapper; NOT proved)

Reads JSON lines and runs the proved definitions on each:

* `{"op": "sqrt", "a": nat}` runs `OzSqrt.sqrt` and prints `{"result": nat}`;
* `{"op": "sqrt_up", "a": nat}` runs `OzSqrt.sqrtUp OzSqrt.sqrt` and prints `{"result": nat}`;
* `{"op": "first_mint", "amount0": nat, "amount1": nat}` runs `OzSqrt.firstMint OzSqrt.sqrt` and
  prints `{"liquidity": nat}`, or `{"liquidity": null}` when the Solidity code would revert.

Every number must be below `2^256`; any other input is answered with `{"error":"bad input"}`.
The parser and serializer here are TESTED_ONLY.
-/

open Lean OzSqrt

def word (j : Json) (key : String) : Except String U256 := do
  let x ← (j.getObjValD key).getNat?
  if x < 2 ^ 256 then return BitVec.ofNat 256 x else throw s!"{key} out of range"

def runOne (line : String) : Except String String := do
  let j ← Json.parse line
  let op ← (j.getObjValD "op").getStr?
  if op == "sqrt" then
    let a ← word j "a"
    return (Json.mkObj [("result", toJson (sqrt a).toNat)]).compress
  else if op == "sqrt_up" then
    let a ← word j "a"
    return (Json.mkObj [("result", toJson (sqrtUp sqrt a).toNat)]).compress
  else if op == "first_mint" then
    let a0 ← word j "amount0"
    let a1 ← word j "amount1"
    let out : Json := match firstMint sqrt a0 a1 with
      | some l => toJson l.toNat
      | none => Json.null
    return (Json.mkObj [("liquidity", out)]).compress
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
