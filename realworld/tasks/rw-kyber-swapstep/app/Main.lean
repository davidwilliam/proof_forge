import Lean.Data.Json
import Solution
/-!
# swapstep-sidecar (executable wrapper; NOT proved)

Reads JSON lines and runs the proved definitions on each:

* `{"op": "step", "L": nat, "c": nat, "t": nat, "F": nat, "spec": int, "exact_input": bool}`
  runs `KyberSwapStep.computeSwapStep L c t F spec exact_input` and prints
  `{"used": int, "returned": int, "deltaL": nat, "next": nat}`, or `{"revert": true}` when the
  Solidity code would revert;
* `{"op": "loop", "L": nat, "p": nat, "tick": nat, "limit": nat, "F": nat, "spec": int,
  "exact_input": bool}` runs one iteration of the loop of `Pool.swap`,
  `KyberSwapStep.loopStep KyberSwapStep.computeSwapStep L p tick limit F spec exact_input`, and
  prints the step and `"crossed": bool`, or `{"revert": true}`.

Every natural number must be below `2^256`; any other input is answered with
`{"error":"bad input"}`. The parser and serializer here are TESTED_ONLY.
-/

open Lean KyberSwapStep

def word (j : Json) (key : String) : Except String U256 := do
  let x ← (j.getObjValD key).getNat?
  if x < 2 ^ 256 then return BitVec.ofNat 256 x else throw s!"{key} out of range"

def stepJson (s : Step) : List (String × Json) :=
  [("used", toJson s.usedAmount), ("returned", toJson s.returnedAmount),
   ("deltaL", toJson s.deltaL.toNat), ("next", toJson s.nextSqrtP.toNat)]

def runOne (line : String) : Except String String := do
  let j ← Json.parse line
  let op ← (j.getObjValD "op").getStr?
  let spec ← (j.getObjValD "spec").getInt?
  let ei ← (j.getObjValD "exact_input").getBool?
  let L ← word j "L"
  let F ← word j "F"
  if op == "step" then
    let c ← word j "c"
    let t ← word j "t"
    let out : Json := match computeSwapStep L c t F spec ei with
      | some s => Json.mkObj (stepJson s)
      | none => Json.mkObj [("revert", Json.bool true)]
    return out.compress
  else if op == "loop" then
    let p ← word j "p"
    let tick ← word j "tick"
    let limit ← word j "limit"
    let out : Json := match loopStep computeSwapStep L p tick limit F spec ei with
      | some (s, crossed) => Json.mkObj (stepJson s ++ [("crossed", Json.bool crossed)])
      | none => Json.mkObj [("revert", Json.bool true)]
    return out.compress
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
