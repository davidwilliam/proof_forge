import RingBuffer.Spec

namespace RingBuffer

-- Placeholder body; replace it with an implementation that meets the spec.
def step : Impl := fun s _ => (Outcome.rejected, s)

theorem req_valid_succeeds   : ValidSucceeds step := sorry
theorem req_invalid_noop     : InvalidNoop step := sorry
theorem req_well_formed      : KeepsWellFormed step := sorry
theorem req_enqueue_effects  : EnqueueEffects step := sorry
theorem req_dequeue_effects  : DequeueEffects step := sorry
theorem req_enqueue_contents : EnqueueContents step := sorry
theorem req_dequeue_contents : DequeueContents step := sorry
theorem req_fifo             : Fifo step := sorry

end RingBuffer
