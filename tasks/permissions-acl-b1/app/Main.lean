import Lean.Data.Json
import Solution
/-!
# acl-sidecar (executable wrapper; NOT proved)

Reads JSON lines `{"state": ..., "request": ...}` from stdin, runs the proved `Acl.step` on
each, prints one `{"outcome": ..., "state": ...}` line per input. The parser, serializer and
state mapping here are TESTED_ONLY.

State JSON: {"users": [ids], "entries": [[effect, subject, path], ...],
"log": [[user, path, granted], ...]} with effect "allow" or "deny", subject a user id (0 for
every user), path a list of numbers and granted a boolean. Request JSON:
{"user": id, "path": [numbers]}. Outcomes are "granted", "denied" and "rejected".
-/

open Lean Acl

def arr (j : Json) (n : Nat) : Except String (Array Json) := do
  let a ← j.getArr?
  if a.size != n then throw s!"expected an array of {n} elements"
  return a

def parsePath (j : Json) : Except String Path := do
  (← j.getArr?).toList.mapM (·.getNat?)

def parseEffect : String → Except String Effect
  | "allow" => pure .allow
  | "deny" => pure .deny
  | x => throw s!"unknown effect {x}"

def effectName : Effect → String
  | .allow => "allow"
  | .deny => "deny"

def parseState (j : Json) : Except String State := do
  let users ← (← (← j.getObjVal? "users").getArr?).toList.mapM (·.getNat?)
  let entries ← (← (← j.getObjVal? "entries").getArr?).toList.mapM fun e => do
    let a ← arr e 3
    return ({ effect := ← parseEffect (← a[0]!.getStr?), subject := ← a[1]!.getNat?,
              path := ← parsePath a[2]! } : Entry)
  let log ← (← (← j.getObjVal? "log").getArr?).toList.mapM fun x => do
    let a ← arr x 3
    return ({ user := ← a[0]!.getNat?, path := ← parsePath a[1]!, granted := ← a[2]!.getBool? } : Record)
  return { users, entries, log }

def fromState (s : State) : Json :=
  Json.mkObj [
    ("users", toJson s.users),
    ("entries", toJson (s.entries.map fun e =>
      Json.arr #[toJson (effectName e.effect), toJson e.subject, toJson e.path])),
    ("log", toJson (s.log.map fun x => Json.arr #[toJson x.user, toJson x.path, toJson x.granted]))]

def runOne (line : String) : Except String String := do
  let j ← Json.parse line
  let s ← parseState (← j.getObjVal? "state")
  let rq ← j.getObjVal? "request"
  let r : Request := { user := ← (← rq.getObjVal? "user").getNat?, path := ← parsePath (← rq.getObjVal? "path") }
  let (o, s') := step s r
  let outcome := match o with | .granted => "granted" | .denied => "denied" | .rejected => "rejected"
  return (Json.mkObj [("outcome", toJson outcome), ("state", fromState s')]).compress

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
