import PrioQueue.Spec
namespace PrioQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid Sorted <;> infer_instance

def ins (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs => if e.prio ≤ x.prio then e :: x :: xs else x :: ins e xs

def step : Impl := fun s op =>
  if Valid s op then
    match op, s.items with
    | .insert e, _ => (.ok, { s with items := ins e s.items })
    | .pop, x :: xs => (.got x, { s with items := xs })
    | .pop, [] => (.rejected, s)
  else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_capacity       : CapacityBound step := sorry
theorem req_pop_min        : PopMin step := sorry
theorem req_sorted         : KeepsSorted step := sorry
theorem req_insert_effects : InsertEffects step := sorry
theorem req_pop_effects    : PopEffects step := sorry
theorem req_fifo_ties      : FifoTies step := sorry

end PrioQueue
