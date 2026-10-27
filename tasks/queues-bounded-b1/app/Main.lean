import Lean.Data.Json
import Solution
/-!
# queue-sidecar (executable wrapper; not proved)

Reads JSON lines `{"state": ..., "op": ...}` from stdin, runs `BoundedQueue.step` on each,
and prints one `{"outcome": ..., "value": ..., "state": ...}` line per input. The parser
and serializer here are tested only.

State JSON: {"capacity": c, "items": [front, ..., back], "served": n}
Op JSON: {"kind": "enqueue", "value": x} or {"kind": "dequeue"}
Output: "outcome" is "ok", "got" or "rejected"; "value" is present only for "got".
-/

open Lean BoundedQueue

structure StateJ where
  capacity : Nat
  items    : List Nat
  served   : Nat
  deriving FromJson, ToJson

def toState (j : StateJ) : State :=
  { capacity := j.capacity, items := j.items, served := j.served }

def fromState (s : State) : StateJ :=
  { capacity := s.capacity, items := s.items, served := s.served }

def parseOp (j : Json) : Except String Op := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "enqueue" => return .enqueue (← j.getObjValAs? Nat "value")
  | "dequeue" => return .dequeue
  | k => throw s!"unknown op kind {k}"

def runOne (line : String) : Except String String := do
  let j ← Json.parse line
  let st ← j.getObjValAs? StateJ "state"
  let op ← parseOp (← j.getObjVal? "op")
  let (o, s') := step (toState st) op
  let fields := match o with
    | .ok => [("outcome", toJson "ok")]
    | .got x => [("outcome", toJson "got"), ("value", toJson x)]
    | .rejected => [("outcome", toJson "rejected")]
  return (Json.mkObj (fields ++ [("state", toJson (fromState s'))])).compress

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
