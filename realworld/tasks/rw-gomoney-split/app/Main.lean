import Lean.Data.Json
import Solution
/-!
# split-sidecar (executable wrapper; NOT proved)

Reads JSON lines `{"amount": int, "n": nat}` from stdin, runs the proved
`EqualSplit.split` on each, and prints one `{"shares": [int, ...]}` line per input, or
`{"shares": null}` when the routine refuses the input. The parser and serializer here are
TESTED_ONLY.
-/

open Lean EqualSplit

structure Input where
  amount : Int
  n : Nat
  deriving FromJson

def runOne (line : String) : Except String String := do
  let inp ← Json.parse line >>= fromJson? (α := Input)
  let out : Json := match split inp.amount inp.n with
    | some s => toJson s
    | none => Json.null
  return (Json.mkObj [("shares", out)]).compress

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
