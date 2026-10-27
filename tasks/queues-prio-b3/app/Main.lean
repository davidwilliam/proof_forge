import Lean.Data.Json
import Solution
/-!
# prio-sidecar (executable wrapper; not proved)

Reads JSON lines `{"state": ..., "op": ...}` from stdin, runs `PrioQueue.step` on each,
and prints one `{"outcome": ..., "entry": ..., "state": ...}` line per input. The parser
and serializer here are tested only.

State JSON: {"capacity": c, "items": [[prio, value], ...]} in stored order.
Op JSON: {"kind": "insert", "prio": p, "value": v} or {"kind": "pop"}
Output: "outcome" is "ok", "got" or "rejected"; "entry" is present only for "got".
-/

open Lean PrioQueue

structure StateJ where
  capacity : Nat
  items    : List (Nat × Nat)
  deriving FromJson, ToJson

def toState (j : StateJ) : State :=
  { capacity := j.capacity, items := j.items.map (fun p => { prio := p.1, val := p.2 }) }

def fromState (s : State) : StateJ :=
  { capacity := s.capacity, items := s.items.map (fun e => (e.prio, e.val)) }

def parseOp (j : Json) : Except String Op := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "insert" => return .insert { prio := ← j.getObjValAs? Nat "prio", val := ← j.getObjValAs? Nat "value" }
  | "pop" => return .pop
  | k => throw s!"unknown op kind {k}"

def runOne (line : String) : Except String String := do
  let j ← Json.parse line
  let st ← j.getObjValAs? StateJ "state"
  let op ← parseOp (← j.getObjVal? "op")
  let (o, s') := step (toState st) op
  let fields := match o with
    | .ok => [("outcome", toJson "ok")]
    | .got e => [("outcome", toJson "got"), ("entry", toJson (e.prio, e.val))]
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
