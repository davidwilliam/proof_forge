import Lean.Data.Json
import Solution
/-!
# fee-sidecar (executable wrapper; NOT proved)

Reads JSON lines `{"state": ..., "request": ...}` from stdin, runs the proved
`FeePayout.step` on each, prints one `{"outcome": ..., "state": ...}` line per input. The
parser, serializer and state mapping here are TESTED_ONLY.

State JSON: {"balances": [[acct, cents], ...], "auth": [[requester, source], ...],
"applied": [ids], "feeAccount": acct, "feeBps": bps}
The account universe is the list of accounts in `balances`, in order.
-/

open Lean FeePayout

structure StateJ where
  balances   : List (Nat × Int)
  auth       : List (Nat × Nat)
  applied    : List Nat
  feeAccount : Nat
  feeBps     : Nat
  deriving FromJson, ToJson

structure RequestJ where
  txId       : Nat
  requester  : Nat
  source     : Nat
  recipients : List Nat
  amount     : Nat
  deriving FromJson, ToJson

structure Input where
  state   : StateJ
  request : RequestJ
  deriving FromJson

def lookupBal (bs : List (Nat × Int)) (a : Nat) : Int :=
  match bs.find? (·.1 == a) with
  | some (_, v) => v
  | none => 0

def toState (j : StateJ) : State where
  accounts   := j.balances.map (·.1)
  balance    := lookupBal j.balances
  auth       := fun req src => j.auth.any (fun p => p.1 == req && p.2 == src)
  applied    := j.applied
  feeAccount := j.feeAccount
  feeBps     := j.feeBps

/-- Serialize back. Authorization is reported as a full check over the account universe so
that any change is visible. -/
def fromState (s : State) : StateJ where
  balances   := s.accounts.map (fun a => (a, s.balance a))
  auth       := (s.accounts.flatMap fun req => s.accounts.filterMap fun src =>
                   if s.auth req src then some (req, src) else none)
  applied    := s.applied
  feeAccount := s.feeAccount
  feeBps     := s.feeBps

def runOne (line : String) : Except String String := do
  let inp ← Json.parse line >>= fromJson? (α := Input)
  let s := toState inp.state
  let r : Request := { txId := inp.request.txId, requester := inp.request.requester,
                       source := inp.request.source, recipients := inp.request.recipients,
                       amount := inp.request.amount }
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
