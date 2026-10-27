import Lean.Data.Json
import Solution
/-!
# log-sidecar (executable wrapper; not proved)

Reads JSON lines `{"state": ..., "entry": ...}` from stdin, runs `EntryLog.step` on each,
and prints one `{"outcome": ..., "receipt": ..., "state": ...}` line per input. The parser,
serializer and state mapping here are TESTED_ONLY.

State JSON: {"balances": [[account, cents], ...], "log": [{"id": n, "account": a, "amount": c}, ...]}
The account universe is the list of accounts in `balances`, in order.
-/

open Lean EntryLog

structure EntryJ where
  id      : Nat
  account : Nat
  amount  : Int
  deriving FromJson, ToJson

structure StateJ where
  balances : List (Nat × Int)
  log      : List EntryJ
  deriving FromJson, ToJson

structure Input where
  state : StateJ
  entry : EntryJ
  deriving FromJson

def lookupBal (bs : List (Nat × Int)) (a : Nat) : Int :=
  match bs.find? (·.1 == a) with
  | some (_, v) => v
  | none => 0

def toEntry (j : EntryJ) : Entry := { id := j.id, account := j.account, amount := j.amount }

def fromEntry (e : Entry) : EntryJ := { id := e.id, account := e.account, amount := e.amount }

def toState (j : StateJ) : State where
  accounts := j.balances.map (·.1)
  log      := j.log.map toEntry
  balance  := lookupBal j.balances

def fromState (s : State) : StateJ where
  balances := s.accounts.map (fun a => (a, s.balance a))
  log      := s.log.map fromEntry

def runOne (line : String) : Except String String := do
  let inp ← Json.parse line >>= fromJson? (α := Input)
  let (o, s') := step (toState inp.state) (toEntry inp.entry)
  let (outcome, receipt) := match o with
    | .ok n => ("ok", toJson n)
    | .rejected => ("rejected", Json.null)
  return (Json.mkObj [("outcome", toJson outcome), ("receipt", receipt),
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
