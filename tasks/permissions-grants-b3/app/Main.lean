import Lean.Data.Json
import Solution
/-!
# grants-sidecar (executable wrapper; NOT proved)

Reads JSON lines `{"state": ..., "request": ...}` from stdin, runs the proved
`Grants.step` on each, prints one `{"outcome": ..., "state": ...}` line per input. The parser,
serializer and state mapping here are TESTED_ONLY.

State JSON: {"users": [ids], "grants": [[user, role], ...]} with role one of "admin",
"editor", "viewer". Request JSON: {"op": "grant" | "revoke", "actor": id, "target": id,
"role": role}. The output lists every grant over the user universe, in universe order and
role order admin, editor, viewer.
-/

open Lean Grants

structure StateJ where
  users  : List Nat
  grants : List (Nat × String)
  deriving FromJson, ToJson

structure RequestJ where
  op     : String
  actor  : Nat
  target : Nat
  role   : String
  deriving FromJson

structure Input where
  state   : StateJ
  request : RequestJ
  deriving FromJson

def parseRole : String → Except String Role
  | "admin" => pure .admin
  | "editor" => pure .editor
  | "viewer" => pure .viewer
  | r => throw s!"unknown role {r}"

def roleName : Role → String
  | .admin => "admin"
  | .editor => "editor"
  | .viewer => "viewer"

def parseOp : String → Except String Op
  | "grant" => pure .grant
  | "revoke" => pure .revoke
  | o => throw s!"unknown op {o}"

def toState (j : StateJ) : Except String State := do
  let gs ← j.grants.mapM fun (u, q) => do return (u, ← parseRole q)
  return { users := j.users, has := fun u q => gs.any (fun p => p.1 == u && p.2 == q) }

def fromState (s : State) : StateJ where
  users  := s.users
  grants := s.users.flatMap fun u => [Role.admin, .editor, .viewer].filterMap fun q =>
              if s.has u q then some (u, roleName q) else none

def runOne (line : String) : Except String String := do
  let inp ← Json.parse line >>= fromJson? (α := Input)
  let s ← toState inp.state
  let r : Request := { op := ← parseOp inp.request.op, actor := inp.request.actor,
                       target := inp.request.target, role := ← parseRole inp.request.role }
  let (o, s') := step s r
  let outcome := match o with | .ok => "ok" | .rejected => "rejected"
  return (Json.mkObj [("outcome", toJson outcome), ("state", toJson (fromState s'))]).compress

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
