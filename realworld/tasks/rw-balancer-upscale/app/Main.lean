import Lean.Data.Json
import Solution
import BalancerSwap.StableMath
/-!
# swap-sidecar (executable wrapper; NOT proved)

Reads JSON lines, one batch of swaps per line:

  {"math": "product" | "stable", "amp": nat,                    ("amp" for "stable" only)
   "pool": {"balances": [nat, ...], "rates": [nat, ...], "fee": nat},
   "swaps": [{"kind": "in" | "out", "in": nat, "out": nat, "amount": nat}, ...]}

and runs the batch through `BalancerSwap.step` with the candidate's `BalancerSwap.onSwap`.
`"product"` is `BalancerSwap.constantProduct` (two tokens), `"stable"` is
`BalancerSwap.stableMath amp n` with `n` the number of balances. For `"stable"` a swap also
fails when a balance would reach 2^112 (the Vault's limit), which is how a StableMath revert
shows. It prints, for each swap until the first one that fails:

  {"steps": [{"quote": nat | null, "ok": bool, "balances": [nat, ...], "value": nat}, ...],
   "ok": bool, "value_before": nat, "balances_after": [nat, ...], "value_after": nat}

`quote` is the amount `onSwap` calculates (null when it refuses), `ok` whether the swap went
through, `balances` and `value` the pool after it (`value` is `BalancerSwap.value`; for
`"stable"` it is null when the StableMath port reverts on those balances). A batch with a failed swap reverts:
`balances_after` and `value_after` are then those of the starting pool. The parser and
serializer here are TESTED_ONLY.
-/

open Lean BalancerSwap

def LIMIT : Nat := 2 ^ 112

structure Req where
  math : PoolMath
  stable : Bool
  amp : Nat
  pool : Pool
  swaps : Array Swap

def parseSwap (j : Json) : Except String Swap := do
  let kind ← match ← j.getObjValAs? String "kind" with
    | "in" => pure Kind.givenIn
    | "out" => pure Kind.givenOut
    | k => throw s!"unknown kind {k}"
  return { kind, tokenIn := ← j.getObjValAs? Nat "in", tokenOut := ← j.getObjValAs? Nat "out",
           amount := ← j.getObjValAs? Nat "amount" }

def parseReq (j : Json) : Except String Req := do
  let pj ← j.getObjVal? "pool"
  let bs ← pj.getObjValAs? (Array Nat) "balances"
  let rs ← pj.getObjValAs? (Array Nat) "rates"
  if bs.size != rs.size then throw "balances and rates differ in length"
  let pool : Pool := { n := bs.size, balance := fun k => bs.getD k 0, rate := fun k => rs.getD k 0,
                       fee := ← pj.getObjValAs? Nat "fee" }
  let swaps ← (← j.getObjValAs? (Array Json) "swaps").mapM parseSwap
  match ← j.getObjValAs? String "math" with
  | "product" => return { math := constantProduct, stable := false, amp := 0, pool, swaps }
  | "stable" =>
    let amp ← j.getObjValAs? Nat "amp"
    return { math := stableMath amp bs.size, stable := true, amp, pool, swaps }
  | m => throw s!"unknown math {m}"

def balancesJson (p : Pool) : Json := toJson ((List.range p.n).map p.balance)

/-- The pool's value; for `"stable"`, null when the StableMath port reverts on it. -/
def valueJson (r : Req) (p : Pool) : Json :=
  if r.stable then toJson (StableMath.calculateInvariant r.amp (scaledBalances p) p.n)
  else toJson (value r.math p)

def runOne (line : String) : Except String String := do
  let r ← parseReq (← Json.parse line)
  let fits (p : Pool) : Bool := !r.stable || (List.range p.n).all (fun k => p.balance k < LIMIT)
  let mut p := r.pool
  let mut steps : Array Json := #[]
  let mut ok := true
  for s in r.swaps do
    let quote := if Valid p s then onSwap r.math p s else none
    let next := match step onSwap r.math p s with
      | some p' => if fits p' then some p' else none
      | none => none
    match next with
    | some p' =>
      p := p'
      steps := steps.push (Json.mkObj [("quote", toJson quote), ("ok", toJson true),
        ("balances", balancesJson p'), ("value", valueJson r p')])
    | none =>
      steps := steps.push (Json.mkObj [("quote", toJson quote), ("ok", toJson false),
        ("balances", balancesJson p), ("value", valueJson r p)])
      ok := false
      break
  let final := if ok then p else r.pool
  return (Json.mkObj [("steps", toJson steps), ("ok", toJson ok),
    ("value_before", valueJson r r.pool), ("balances_after", balancesJson final),
    ("value_after", valueJson r final)]).compress

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
