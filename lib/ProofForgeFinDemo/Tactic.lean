import ProofForgeFinDemo.Tactic.RoundBound
import ProofForgeFinDemo.Tactic.StructSimp
import ProofForgeFinDemo.Tactic.RunInduction
import ProofForgeFinDemo.Tactic.Router
/-!
# Tests of the proof automation

Every example and theorem in these files must be closed for the build to succeed.

* `RoundBound`: `fin_simp`, `div_norm` and `round_bound` on rounding facts, on the share-value
  arithmetic of `rw-hundred-vault`, and on goals copied from failed attempts on
  `rw-compound-comp`; a clean failure.
* `StructSimp`: `struct_simp` and `step_cases` on records, updates and conditions, on goals
  copied from failed attempts on `rw-compound-comp`, and on calls of its Comptroller model.
* `RunInduction`: `run_induction` in its four forms on the vault of `rw-hundred-vault`, an
  escrow and the Comptroller of `rw-compound-comp`.
* `Router`: goals copied from failed attempts on `rc-knight-router`, the two invariants of its
  accepted repair over every sequence of events, and two of its requirements.
-/
