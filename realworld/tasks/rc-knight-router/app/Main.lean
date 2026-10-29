import Lean.Data.Json
import Solution
/-!
# router-sidecar (executable wrapper; not proved)

Reads JSON lines `{"build": "rlp" | "legacy", "events": [...]}` from stdin, runs
`OrderRouter.step` from `OrderRouter.init` over the events, and prints one line per input:
`{"steps": [{"children": [{"parent": p, "qty": q}, ...], "cum": [c0, c1, ...]}, ...]}` with
one entry per event: the child orders the router sent in response, and the router's
cumulative executed quantity for every parent order received so far. The parser and
serializer here are tested only.

Event JSON: {"kind": "parent", "qty": q, "flag": b}, {"kind": "route", "id": i, "liq": l},
{"kind": "ack", "child": k}, {"kind": "fill", "child": k, "qty": q}.
-/

open Lean OrderRouter

def parseBuild : String → Except String Build
  | "rlp" => .ok .rlp
  | "legacy" => .ok .legacy
  | b => .error s!"unknown build {b}"

def parseEvent (j : Json) : Except String Event := do
  match ← j.getObjValAs? String "kind" with
  | "parent" => return .parent (← j.getObjValAs? Nat "qty") (← j.getObjValAs? Bool "flag")
  | "route" => return .route (← j.getObjValAs? Nat "id") (← j.getObjValAs? Nat "liq")
  | "ack" => return .ack (← j.getObjValAs? Nat "child")
  | "fill" => return .fill (← j.getObjValAs? Nat "child") (← j.getObjValAs? Nat "qty")
  | k => throw s!"unknown event kind {k}"

def childJson (c : Child) : Json :=
  Json.mkObj [("parent", toJson c.parent), ("qty", toJson c.qty)]

def runOne (line : String) : Except String String := do
  let j ← Json.parse line
  let b ← parseBuild (← j.getObjValAs? String "build")
  let evs ← (← j.getObjValAs? (Array Json) "events").toList.mapM parseEvent
  let mut s := init
  let mut n := 0
  let mut steps : Array Json := #[]
  for e in evs do
    let r := step b s e
    s := r.1
    if let .parent _ _ := e then n := n + 1
    let cum := (List.range n).map (fun i => toJson (s.parents i).cum)
    steps := steps.push (Json.mkObj [("children", Json.arr (r.2.map childJson).toArray),
                                     ("cum", Json.arr cum.toArray)])
  return (Json.mkObj [("steps", Json.arr steps)]).compress

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
