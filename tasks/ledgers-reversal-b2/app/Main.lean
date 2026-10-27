import Lean.Data.Json
import Solution
/-!
# reversal-sidecar (executable wrapper; not proved)

Reads JSON lines `{"state": ..., "command": ...}` from stdin, runs `Reversal.step` on each,
and prints one `{"outcome": ..., "state": ...}` line per input. The parser, serializer and
state mapping here are TESTED_ONLY.

State JSON: {"balances": [[account, cents], ...], "opening": [[account, cents], ...],
             "journal": [{"id": n, "lines": [[account, cents], ...]}, ...], "reversed": [ids]}
Command JSON: {"kind": "post" | "reverse", "id": n, "lines": [[account, cents], ...]}
(`lines` is ignored for a reversal). The account universe is the list of accounts in
`balances`, in order; `opening` is reported for the same accounts.
-/

open Lean Reversal

structure EntryJ where
  id    : Nat
  lines : List (Nat × Int)
  deriving FromJson, ToJson

structure StateJ where
  balances : List (Nat × Int)
  opening  : List (Nat × Int)
  journal  : List EntryJ
  reversed : List Nat
  deriving FromJson, ToJson

structure CommandJ where
  kind  : String
  id    : Nat
  lines : List (Nat × Int)
  deriving FromJson

structure Input where
  state   : StateJ
  command : CommandJ
  deriving FromJson

def lookupBal (bs : List (Nat × Int)) (a : Nat) : Int :=
  match bs.find? (·.1 == a) with
  | some (_, v) => v
  | none => 0

def toState (j : StateJ) : State where
  accounts := j.balances.map (·.1)
  opening  := lookupBal j.opening
  balance  := lookupBal j.balances
  journal  := j.journal.map (fun e => { id := e.id, lines := e.lines })
  reversed := j.reversed

def fromState (s : State) : StateJ where
  balances := s.accounts.map (fun a => (a, s.balance a))
  opening  := s.accounts.map (fun a => (a, s.opening a))
  journal  := s.journal.map (fun e => { id := e.id, lines := e.lines })
  reversed := s.reversed

def toCommand (c : CommandJ) : Except String Reversal.Command :=
  match c.kind with
  | "post" => .ok (.post { id := c.id, lines := c.lines })
  | "reverse" => .ok (.reverse c.id)
  | k => .error s!"unknown command kind {k}"

def runOne (line : String) : Except String String := do
  let inp ← Json.parse line >>= fromJson? (α := Input)
  let c ← toCommand inp.command
  let (o, s') := step (toState inp.state) c
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
