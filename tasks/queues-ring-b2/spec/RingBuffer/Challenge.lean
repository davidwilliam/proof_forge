import RingBuffer.Spec
/-!
# Locked challenge (never imports candidate code)

`RingBuffer.step` is a Comparator definition hole. A solution must define it and prove
every theorem below with exactly these statements.
-/

namespace RingBuffer

def step : Impl := sorry

theorem req_valid_succeeds   : ValidSucceeds step := sorry
theorem req_invalid_noop     : InvalidNoop step := sorry
theorem req_well_formed      : KeepsWellFormed step := sorry
theorem req_enqueue_effects  : EnqueueEffects step := sorry
theorem req_dequeue_effects  : DequeueEffects step := sorry
theorem req_enqueue_contents : EnqueueContents step := sorry
theorem req_dequeue_contents : DequeueContents step := sorry
theorem req_fifo             : Fifo step := sorry

end RingBuffer
