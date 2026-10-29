import Lean.Data.Json
import Solution
/-!
# vault-sidecar (executable wrapper; NOT proved)

Reads JSON lines, one sequence of operations per line:

  {"start": {"assets": nat, "supply": nat, "balances": [nat, ...]},   (optional; default empty)
   "ops": [{"op": "deposit", "who": nat, "amount": nat},
           {"op": "redeem", "who": nat, "shares": nat},
           {"op": "withdraw", "who": nat, "amount": nat},
           {"op": "donate", "amount": nat}, ...]}

and runs them through `ShareVault.exec` with the proved `ShareVault.vault`. For each operation
it prints whether the call succeeded and the state after it:

  {"steps": [{"ok": bool, "assets": nat, "supply": nat, "balances": [nat, ...]}, ...]}

`balances` lists actors 0 to n - 1, where n covers every actor in the input. A refused call
has `"ok": false` and an unchanged state. The parser and serializer here are TESTED_ONLY.
-/

open Lean ShareVault

def parseOp (j : Json) : Except String (Op × Nat) := do
  let op ← j.getObjValAs? String "op"
  match op with
  | "deposit" =>
    let who ← j.getObjValAs? Nat "who"
    return (.call (.deposit who (← j.getObjValAs? Nat "amount")), who + 1)
  | "redeem" =>
    let who ← j.getObjValAs? Nat "who"
    return (.call (.redeem who (← j.getObjValAs? Nat "shares")), who + 1)
  | "withdraw" =>
    let who ← j.getObjValAs? Nat "who"
    return (.call (.withdraw who (← j.getObjValAs? Nat "amount")), who + 1)
  | "donate" => return (.donate (← j.getObjValAs? Nat "amount"), 0)
  | _ => throw s!"unknown op {op}"

def parseStart (j : Json) : Except String (Vault × Nat) :=
  match j.getObjVal? "start" with
  | .error _ => return (empty, 0)
  | .ok st => do
    let bs ← st.getObjValAs? (Array Nat) "balances"
    let s : Vault := { assets := ← st.getObjValAs? Nat "assets", supply := ← st.getObjValAs? Nat "supply",
                       balance := fun b => bs.getD b 0 }
    return (s, bs.size)

def stateJson (ok : Bool) (s : Vault) (n : Nat) : Json :=
  Json.mkObj [("ok", toJson ok), ("assets", toJson s.assets), ("supply", toJson s.supply),
              ("balances", toJson ((List.range n).map s.balance))]

def runOne (line : String) : Except String String := do
  let j ← Json.parse line
  let (start, n0) ← parseStart j
  let ops ← (← j.getObjValAs? (Array Json) "ops").mapM parseOp
  let n := ops.foldl (fun m p => max m p.2) n0
  let (_, steps) := ops.foldl (init := (start, (#[] : Array Json))) fun (s, acc) (op, _) =>
    let ok := match op with
      | .call c => (vault s c).isSome
      | .donate _ => true
    let s' := exec vault s op
    (s', acc.push (stateJson ok s' n))
  return (Json.mkObj [("steps", toJson steps)]).compress

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
