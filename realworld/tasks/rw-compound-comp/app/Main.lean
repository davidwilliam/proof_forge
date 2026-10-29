import Lean.Data.Json
import Solution
/-!
# comp-sidecar (executable wrapper; NOT proved)

Reads JSON lines, one run per line:

  {"legacy": {"blockNumber": n, "compSpeed": n, "supplyIndex": n, "supplyBlock": n,
              "borrowIndex": n, "borrowBlock": n, "supplyStart": n, "borrowStart": n,
              "reserve": n, "accts": [{"supply": n, "borrow": n, "supplierIndex": n,
                                       "borrowerIndex": n, "accrued": n, "wallet": n}, ...]},
   "ops": [{"op": "mint" | "redeem" | "borrow" | "repay", "who": n, "amount": n},
           {"op": "transfer", "src": n, "dst": n, "amount": n},
           {"op": "claim", "who": n},
           {"op": "setSpeeds", "supply": n, "borrow": n},
           {"op": "advance", "blocks": n},
           {"op": "drip", "amount": n}, ...]}

It applies `CompRewards.upgrade` to the legacy state and runs the operations through
`CompRewards.exec` with the proved `CompRewards.comptroller`. It prints the state after the
upgrade and, for each operation, whether it was applied and the state after it:

  {"start": state, "steps": [{"ok": bool, "state": state}, ...]}
  state = {"blockNumber": n, "supplyState": {"index": n, "block": n, "speed": n},
           "borrowState": {...}, "reserve": n, "accts": [{...}, ...]}

An operation that is refused has `"ok": false` and an unchanged state. The parser and
serializer here are TESTED_ONLY.
-/

open Lean CompRewards

def parseAcct (j : Json) : Except String Acct := do
  return { supply := ← j.getObjValAs? Nat "supply", borrow := ← j.getObjValAs? Nat "borrow",
           supplierIndex := ← j.getObjValAs? Nat "supplierIndex",
           borrowerIndex := ← j.getObjValAs? Nat "borrowerIndex",
           accrued := ← j.getObjValAs? Nat "accrued", wallet := ← j.getObjValAs? Nat "wallet" }

def parseLegacy (j : Json) : Except String Legacy := do
  let accts ← (← j.getObjValAs? (Array Json) "accts").mapM parseAcct
  return { blockNumber := ← j.getObjValAs? Nat "blockNumber", compSpeed := ← j.getObjValAs? Nat "compSpeed",
           supplyIndex := ← j.getObjValAs? Nat "supplyIndex", supplyBlock := ← j.getObjValAs? Nat "supplyBlock",
           borrowIndex := ← j.getObjValAs? Nat "borrowIndex", borrowBlock := ← j.getObjValAs? Nat "borrowBlock",
           supplyStart := ← j.getObjValAs? Nat "supplyStart", borrowStart := ← j.getObjValAs? Nat "borrowStart",
           reserve := ← j.getObjValAs? Nat "reserve", accts := accts.toList }

def parseOp (j : Json) : Except String Op := do
  let op ← j.getObjValAs? String "op"
  match op with
  | "mint" => return .mint (← j.getObjValAs? Nat "who") (← j.getObjValAs? Nat "amount")
  | "redeem" => return .redeem (← j.getObjValAs? Nat "who") (← j.getObjValAs? Nat "amount")
  | "borrow" => return .borrow (← j.getObjValAs? Nat "who") (← j.getObjValAs? Nat "amount")
  | "repay" => return .repay (← j.getObjValAs? Nat "who") (← j.getObjValAs? Nat "amount")
  | "transfer" =>
    return .transfer (← j.getObjValAs? Nat "src") (← j.getObjValAs? Nat "dst") (← j.getObjValAs? Nat "amount")
  | "claim" => return .claim (← j.getObjValAs? Nat "who")
  | "setSpeeds" => return .setSpeeds (← j.getObjValAs? Nat "supply") (← j.getObjValAs? Nat "borrow")
  | "advance" => return .advance (← j.getObjValAs? Nat "blocks")
  | "drip" => return .drip (← j.getObjValAs? Nat "amount")
  | _ => throw s!"unknown op {op}"

/-- Whether `exec comptroller s op` applies the operation (mirrors `exec`). -/
def applied (s : St) : Op → Bool
  | .mint who _ => who < s.accts.length && (comptroller s (.supplyHook who)).isSome
  | .redeem who x => who < s.accts.length &&
      match comptroller s (.supplyHook who) with
      | some s' => decide (x ≤ (s'.acct who).supply)
      | none => false
  | .transfer src dst x => src < s.accts.length && dst < s.accts.length && src != dst &&
      match comptroller s (.supplyHook src) with
      | some s₁ =>
        match comptroller s₁ (.supplyHook dst) with
        | some s₂ => decide (x ≤ (s₂.acct src).supply)
        | none => false
      | none => false
  | .borrow who _ => who < s.accts.length && (comptroller s (.borrowHook who)).isSome
  | .repay who x => who < s.accts.length &&
      match comptroller s (.borrowHook who) with
      | some s' => decide (x ≤ (s'.acct who).borrow)
      | none => false
  | .claim who => (comptroller s (.claim who)).isSome
  | .setSpeeds a b => (comptroller s (.setSpeeds a b)).isSome
  | .advance _ => true
  | .drip _ => true

def sideJson (sd : Side) : Json :=
  Json.mkObj [("index", toJson sd.index), ("block", toJson sd.block), ("speed", toJson sd.speed)]

def acctJson (a : Acct) : Json :=
  Json.mkObj [("supply", toJson a.supply), ("borrow", toJson a.borrow),
              ("supplierIndex", toJson a.supplierIndex), ("borrowerIndex", toJson a.borrowerIndex),
              ("accrued", toJson a.accrued), ("wallet", toJson a.wallet)]

def stateJson (s : St) : Json :=
  Json.mkObj [("blockNumber", toJson s.blockNumber), ("supplyState", sideJson s.supplyState),
              ("borrowState", sideJson s.borrowState), ("reserve", toJson s.reserve),
              ("accts", Json.arr (s.accts.map acctJson).toArray)]

def runOne (line : String) : Except String String := do
  let j ← Json.parse line
  let L ← parseLegacy (← j.getObjVal? "legacy")
  let ops ← (← j.getObjValAs? (Array Json) "ops").mapM parseOp
  let start := upgrade L
  let (_, steps) := ops.foldl (init := (start, (#[] : Array Json))) fun (s, acc) op =>
    let s' := exec comptroller s op
    (s', acc.push (Json.mkObj [("ok", toJson (applied s op)), ("state", stateJson s')]))
  return (Json.mkObj [("start", stateJson start), ("steps", toJson steps)]).compress

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
