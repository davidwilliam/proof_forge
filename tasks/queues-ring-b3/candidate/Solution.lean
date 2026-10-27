import RingBuffer.Spec
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity then
      let tail := (s.head + s.count) % s.capacity
      (.ok, { s with buf := fun i => if i = tail then x else s.buf i, count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem req_valid_succeeds   : ValidSucceeds step := sorry
theorem req_invalid_noop     : InvalidNoop step := sorry
theorem req_well_formed      : KeepsWellFormed step := sorry
theorem req_enqueue_effects  : EnqueueEffects step := sorry
theorem req_dequeue_effects  : DequeueEffects step := sorry
theorem req_enqueue_contents : EnqueueContents step := sorry
theorem req_dequeue_contents : DequeueContents step := sorry
theorem req_fifo             : Fifo step := sorry

end RingBuffer
