import Lean.Data.Json
import Solution
/-!
# workflow-sidecar (executable wrapper; NOT proved)

Reads JSON lines `{"state": ..., "request": ...}` from stdin, runs the proved
`Workflow.step` on each, prints one `{"outcome": ..., "state": ...}` line per input. The
parser, serializer and state mapping here are TESTED_ONLY.

State JSON: {"docs": [[doc, status, content], ...], "users": [[user, role], ...],
"audit": [[doc, actor, src, dst], ...]}. Statuses are "draft", "review", "approved",
"published", "archived"; roles are "guest", "author", "reviewer", "publisher". The document
and user universes are the ids listed, in order. Request JSON: {"actor": id, "doc": id,
"kind": "move" | "edit", "dst": status, "body": n}.
-/

open Lean Workflow

def parseStatus : String → Except String Status
  | "draft" => pure .draft
  | "review" => pure .review
  | "approved" => pure .approved
  | "published" => pure .published
  | "archived" => pure .archived
  | x => throw s!"unknown status {x}"

def statusName : Status → String
  | .draft => "draft"
  | .review => "review"
  | .approved => "approved"
  | .published => "published"
  | .archived => "archived"

def parseRole : String → Except String Role
  | "guest" => pure .guest
  | "author" => pure .author
  | "reviewer" => pure .reviewer
  | "publisher" => pure .publisher
  | x => throw s!"unknown role {x}"

def roleName : Role → String
  | .guest => "guest"
  | .author => "author"
  | .reviewer => "reviewer"
  | .publisher => "publisher"

def parseKind : String → Except String Kind
  | "move" => pure .move
  | "edit" => pure .edit
  | x => throw s!"unknown kind {x}"

def arr (j : Json) (n : Nat) : Except String (Array Json) := do
  let a ← j.getArr?
  if a.size != n then throw s!"expected an array of {n} elements"
  return a

def nat (j : Json) : Except String Nat := j.getNat?

def str (j : Json) : Except String String := j.getStr?

structure Parsed where
  docs  : List (Nat × Status × Nat)
  users : List (Nat × Role)
  audit : List Entry

def parseState (j : Json) : Except String Parsed := do
  let docs ← (← (← j.getObjVal? "docs").getArr?).toList.mapM fun d => do
    let a ← arr d 3
    return (← nat a[0]!, ← parseStatus (← str a[1]!), ← nat a[2]!)
  let users ← (← (← j.getObjVal? "users").getArr?).toList.mapM fun u => do
    let a ← arr u 2
    return (← nat a[0]!, ← parseRole (← str a[1]!))
  let audit ← (← (← j.getObjVal? "audit").getArr?).toList.mapM fun e => do
    let a ← arr e 4
    return ({ doc := ← nat a[0]!, actor := ← nat a[1]!, src := ← parseStatus (← str a[2]!),
              dst := ← parseStatus (← str a[3]!) } : Entry)
  return { docs, users, audit }

def toState (p : Parsed) : State where
  docs    := p.docs.map (·.1)
  users   := p.users.map (·.1)
  status  := fun d => match p.docs.find? (·.1 == d) with
    | some (_, st, _) => st
    | none => .draft
  content := fun d => match p.docs.find? (·.1 == d) with
    | some (_, _, c) => c
    | none => 0
  role    := fun u => match p.users.find? (·.1 == u) with
    | some (_, q) => q
    | none => .guest
  audit   := p.audit

def fromState (s : State) : Json :=
  Json.mkObj [
    ("docs", toJson (s.docs.map fun d =>
      Json.arr #[toJson d, toJson (statusName (s.status d)), toJson (s.content d)])),
    ("users", toJson (s.users.map fun u => Json.arr #[toJson u, toJson (roleName (s.role u))])),
    ("audit", toJson (s.audit.map fun e =>
      Json.arr #[toJson e.doc, toJson e.actor, toJson (statusName e.src), toJson (statusName e.dst)]))]

def runOne (line : String) : Except String String := do
  let j ← Json.parse line
  let s := toState (← parseState (← j.getObjVal? "state"))
  let rq ← j.getObjVal? "request"
  let r : Request := { actor := ← nat (← rq.getObjVal? "actor"), doc := ← nat (← rq.getObjVal? "doc"),
                       kind := ← parseKind (← str (← rq.getObjVal? "kind")),
                       dst := ← parseStatus (← str (← rq.getObjVal? "dst")),
                       body := ← nat (← rq.getObjVal? "body") }
  let (o, s') := step s r
  let outcome := match o with | .ok => "ok" | .rejected => "rejected"
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
