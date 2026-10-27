import Lean.Data.Json
import Solution
/-!
# bucket-sidecar (executable wrapper; NOT proved)

Reads JSON lines `{"state": ..., "request": ...}` from stdin, runs `TokenBucket.step` on
each, and prints one `{"outcome": ..., "state": ...}` line per input. The parser and
serializer here are TESTED_ONLY.

State JSON: {"capacity": n, "rate": n, "tokens": n, "last": n}
Request JSON: {"time": n, "cost": n}
-/

open Lean TokenBucket

structure StateJ where
  capacity : Nat
  rate     : Nat
  tokens   : Nat
  last     : Nat
  deriving FromJson, ToJson

structure RequestJ where
  time : Nat
  cost : Nat
  deriving FromJson, ToJson

structure Input where
  state   : StateJ
  request : RequestJ
  deriving FromJson

def toState (j : StateJ) : State :=
  { capacity := j.capacity, rate := j.rate, tokens := j.tokens, last := j.last }

def fromState (s : State) : StateJ :=
  { capacity := s.capacity, rate := s.rate, tokens := s.tokens, last := s.last }

def runOne (line : String) : Except String String := do
  let inp ← Json.parse line >>= fromJson? (α := Input)
  let r : Request := { time := inp.request.time, cost := inp.request.cost }
  let (o, s') := step (toState inp.state) r
  let outcome := match o with | .ok => "ok" | .rejected => "rejected"
  return (Json.mkObj [("outcome", toJson outcome),
                      ("state", toJson (fromState s'))]).compress

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
