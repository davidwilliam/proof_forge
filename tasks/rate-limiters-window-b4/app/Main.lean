import Lean.Data.Json
import Solution
/-!
# window-sidecar (executable wrapper; NOT proved)

Reads JSON lines `{"state": ..., "request": ...}` from stdin, runs `FixedWindow.step` on
each, and prints one `{"outcome": ..., "state": ...}` line per input. The parser and
serializer here are TESTED_ONLY.

State JSON: {"window": n, "limit": n, "clients": [{"id": n, "start": n, "count": n}, ...]}
Request JSON: {"client": n, "time": n}
The client list is serialized in order, so every field of every entry is visible.
-/

open Lean FixedWindow

structure ClientJ where
  id    : Nat
  start : Nat
  count : Nat
  deriving FromJson, ToJson

structure StateJ where
  window  : Nat
  limit   : Nat
  clients : List ClientJ
  deriving FromJson, ToJson

structure RequestJ where
  client : Nat
  time   : Nat
  deriving FromJson, ToJson

structure Input where
  state   : StateJ
  request : RequestJ
  deriving FromJson

def toState (j : StateJ) : State :=
  { window := j.window, limit := j.limit,
    clients := j.clients.map fun c => { id := c.id, start := c.start, count := c.count } }

def fromState (s : State) : StateJ :=
  { window := s.window, limit := s.limit,
    clients := s.clients.map fun c => { id := c.id, start := c.start, count := c.count } }

def runOne (line : String) : Except String String := do
  let inp ← Json.parse line >>= fromJson? (α := Input)
  let r : Request := { client := inp.request.client, time := inp.request.time }
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
