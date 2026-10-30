import ProofForgeFinDemo.Trading.KnightRouter
import ProofForgeFinDemo.Trading.PrioQueue
import ProofForgeFinDemo.Trading.BoundedQueue
/-!
# Trading demonstrations

Requirements of tasks re-proved with `ProofForgeFin.Trading`, over definitions copied from the
task files (the task files are not imported or modified).

* `KnightRouter`: the six requirements of `rc-knight-router`, by defining the router through
  `RouterModel.step` and mapping the task's run onto the library's.
* `PrioQueue`: the eight requirements of `queues-prio-b3` (insertion with time priority, FIFO
  within a priority).
* `BoundedQueue`: the six requirements of `queues-bounded-b3` (FIFO flow).
-/
