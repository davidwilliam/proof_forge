import ProofForgeFinDemo.Machine.JournalPosting
import ProofForgeFinDemo.Machine.Reversal
import ProofForgeFinDemo.Machine.EntryLog
import ProofForgeFinDemo.Machine.KnightRouter
/-!
# Demonstrations of `ProofForgeFin.Machine`

Requirements of ledger and state machine tasks re-proved with `ProofForgeFin.Machine`, over
definitions copied from the task files (the task files are not imported or modified).

* `JournalPosting`: the seven requirements of `ledgers-journal-b3` for its reference
  implementation, with trial balance from `Journal.trial_balance_post`.
* `Reversal`: the ten requirements of `ledgers-reversal-b3` for its reference implementation,
  with exact reversal, trial balance and the reversal-mark sum from `Machine.Journal`.
* `EntryLog`: REQ-CONSISTENT of `ledgers-log-b4` as a cached field kept against an append-only
  log (`Machine.cache_log_invariant'`), and its extension to every run.
* `KnightRouter`: `rc-knight-router`: the task's lemma file from `Machine.keyTotal`, five
  requirements from an invariant for every router (`reqs_of_invariant`), and the six
  requirements of the reference router.
-/
