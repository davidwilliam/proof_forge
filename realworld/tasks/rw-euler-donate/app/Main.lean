import Lean.Data.Json
import Solution
/-!
# market-sidecar (executable wrapper; NOT proved)

Reads JSON lines `{"n": accounts, "ops": [op, ...]}` from stdin. Each op is an array:
`["deposit", u, x]`, `["withdraw", u, x]`, `["borrow", u, x]`, `["repay", u, x]`,
`["mint", u, x]`, `["burn", u, x]`, `["transfer", u, v, x]`, `["donate", u, x]` or
`["liquidate", liq, viol, r]`, where `r` may be the string `"max"` for `maxRepay` of the
violator's position at that point. Starting from `genesis`, it applies the proved
`EulerLending.step` to each op in turn (a reverted op leaves the state unchanged) and prints one
line `{"steps": [{"ok": bool, "r": nat, "acct": [[e, d], ...], "cash": nat, "reserves": nat}, ...]}`
with the state after each op, for accounts `0` to `n - 1`. The parser and serializer here are
TESTED_ONLY.
-/

open Lean EulerLending

def natAt (a : Array Json) (i : Nat) : Except String Nat := do
  match a[i]? with
  | some j => j.getNat?
  | none => throw s!"missing field {i}"

/-- The op, given the current state (for a `"max"` liquidation amount). -/
def parseOp (s : St) (j : Json) : Except String Op := do
  let a ← j.getArr?
  let k ← (a[0]?.getD Json.null).getStr?
  match k with
  | "deposit" => return .deposit (← natAt a 1) (← natAt a 2)
  | "withdraw" => return .withdraw (← natAt a 1) (← natAt a 2)
  | "borrow" => return .borrow (← natAt a 1) (← natAt a 2)
  | "repay" => return .repay (← natAt a 1) (← natAt a 2)
  | "mint" => return .mint (← natAt a 1) (← natAt a 2)
  | "burn" => return .burn (← natAt a 1) (← natAt a 2)
  | "transfer" => return .transfer (← natAt a 1) (← natAt a 2) (← natAt a 3)
  | "donate" => return .donate (← natAt a 1) (← natAt a 2)
  | "liquidate" =>
    let l ← natAt a 1
    let v ← natAt a 2
    let r ← match a[3]? with
      | some (Json.str "max") => pure (maxRepay (s.acct v))
      | _ => natAt a 3
    return .liquidate l v r
  | _ => throw s!"unknown op {k}"

def opAmount : Op → Nat
  | .liquidate _ _ r => r
  | _ => 0

def stateJson (n : Nat) (s : St) : List (String × Json) :=
  [("acct", toJson ((List.range n).map fun u => [(s.acct u).e, (s.acct u).d])),
   ("cash", toJson s.cash), ("reserves", toJson s.reserves)]

def runOne (line : String) : Except String String := do
  let j ← Json.parse line
  let n ← j.getObjValAs? Nat "n"
  let ops ← (← j.getObjVal? "ops").getArr?
  let mut s := genesis
  let mut out : Array Json := #[]
  for oj in ops do
    let op ← parseOp s oj
    let (ok, s') := match step s op with
      | some s' => (true, s')
      | none => (false, s)
    s := s'
    out := out.push (Json.mkObj ([("ok", toJson ok), ("r", toJson (opAmount op))] ++ stateJson n s))
  return (Json.mkObj [("steps", Json.arr out)]).compress

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
