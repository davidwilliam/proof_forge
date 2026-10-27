import Lean.Data.Json
import Solution
/-!
# journal-sidecar (executable wrapper; not proved)

Reads JSON lines `{"state": ..., "entry": ...}` from stdin, runs `Journal.step` on each,
and prints one `{"outcome": ..., "state": ...}` line per input. The parser, serializer and
state mapping here are TESTED_ONLY.

State JSON: {"balances": [[account, cents], ...], "posted": [ids]}
Entry JSON: {"id": n, "lines": [[account, cents], ...]}
The account universe is the list of accounts in `balances`, in order.
-/

open Lean Journal

structure StateJ where
  balances : List (Nat × Int)
  posted   : List Nat
  deriving FromJson, ToJson

structure EntryJ where
  id    : Nat
  lines : List (Nat × Int)
  deriving FromJson, ToJson

structure Input where
  state : StateJ
  entry : EntryJ
  deriving FromJson

def lookupBal (bs : List (Nat × Int)) (a : Nat) : Int :=
  match bs.find? (·.1 == a) with
  | some (_, v) => v
  | none => 0

def toState (j : StateJ) : State where
  accounts := j.balances.map (·.1)
  balance  := lookupBal j.balances
  posted   := j.posted

def fromState (s : State) : StateJ where
  balances := s.accounts.map (fun a => (a, s.balance a))
  posted   := s.posted

def runOne (line : String) : Except String String := do
  let inp ← Json.parse line >>= fromJson? (α := Input)
  let (o, s') := step (toState inp.state) { id := inp.entry.id, lines := inp.entry.lines }
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
