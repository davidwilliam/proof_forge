import Lean.Data.Json
import Solution
/-!
# vyper-sqrt-sidecar (executable wrapper; NOT proved)

Reads JSON lines `{"op": "sqrt", "x": int}`, where `x` is a raw Vyper decimal (the decimal
`x / 10^10`), runs `VyperSqrt.sqrt` and prints `{"result": int}`, or `{"result": null}` when the
Vyper code would revert. `x` must be a decimal, between `-2^167` and `2^167 - 1`; any other input
is answered with `{"error":"bad input"}`. The parser and serializer here are TESTED_ONLY.
-/

open Lean VyperSqrt

def runOne (line : String) : Except String String := do
  let j ← Json.parse line
  let op ← (j.getObjValD "op").getStr?
  if op == "sqrt" then
    let x ← (j.getObjValD "x").getInt?
    if x < -2 ^ 167 || x > 2 ^ 167 - 1 then throw "x out of range"
    let out : Json := match sqrt x with
      | some r => toJson r
      | none => Json.null
    return (Json.mkObj [("result", out)]).compress
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
