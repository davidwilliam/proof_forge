import BoundedQueue.Spec
namespace BoundedQueue

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if s.items.length < s.capacity then (.ok, { s with items := s.items ++ [x] })
    else (.rejected, s)
  | .dequeue =>
    match s.items.getLast? with
    | none => (.rejected, s)
    | some x => (.got x, { s with items := s.items.dropLast, served := s.served + 1 })

theorem req_valid_succeeds  : ValidSucceeds step := sorry
theorem req_invalid_noop    : InvalidNoop step := sorry
theorem req_capacity        : CapacityBound step := sorry
theorem req_enqueue_effects : EnqueueEffects step := sorry
theorem req_dequeue_effects : DequeueEffects step := sorry
theorem req_fifo            : Fifo step := sorry

end BoundedQueue
