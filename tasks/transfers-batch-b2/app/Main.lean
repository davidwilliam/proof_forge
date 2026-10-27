import Lean.Data.Json
import Solution
/-!
# batch-sidecar (executable wrapper; not proved)

Reads JSON lines `{"state": ..., "request": ...}` from stdin, runs `Batch.step` on each,
prints one `{"outcome": ..., "state": ...}` line per input. The parser, serializer and
state mapping here are TESTED_ONLY.

State JSON: {"balances": [[acct, cents], ...], "limits": [[acct, cents], ...], "applied": [ids]}
Request JSON: {"batchId": id, "legs": [{"source": a, "target": b, "amount": n}, ...]}
The account universe is the list of accounts in `balances`, in order. Accounts missing
from `limits` have limit 0.
-/

open Lean Batch

structure StateJ where
  balances : List (Nat × Int)
  limits   : List (Nat × Nat)
  applied  : List Nat
  deriving FromJson, ToJson

structure LegJ where
  source : Nat
  target : Nat
  amount : Nat
  deriving FromJson, ToJson

structure RequestJ where
  batchId : Nat
  legs    : List LegJ
  deriving FromJson, ToJson

structure Input where
  state   : StateJ
  request : RequestJ
  deriving FromJson

def lookupBal (bs : List (Nat × Int)) (a : Nat) : Int :=
  match bs.find? (·.1 == a) with
  | some (_, v) => v
  | none => 0

def lookupLim (ls : List (Nat × Nat)) (a : Nat) : Nat :=
  match ls.find? (·.1 == a) with
  | some (_, v) => v
  | none => 0

def toState (j : StateJ) : State where
  accounts := j.balances.map (·.1)
  balance  := lookupBal j.balances
  limit    := lookupLim j.limits
  applied  := j.applied

/-- Serialize back. Limits are reported for every account of the universe so that any
change is visible. -/
def fromState (s : State) : StateJ where
  balances := s.accounts.map (fun a => (a, s.balance a))
  limits   := s.accounts.map (fun a => (a, s.limit a))
  applied  := s.applied

def runOne (line : String) : Except String String := do
  let inp ← Json.parse line >>= fromJson? (α := Input)
  let s := toState inp.state
  let r : Request := { batchId := inp.request.batchId,
                       legs := inp.request.legs.map fun l =>
                         { source := l.source, target := l.target, amount := l.amount } }
  let (o, s') := step s r
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
