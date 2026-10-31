import RingBuffer.Spec
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if _ : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if _ : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    unfold Valid at h
    obtain ⟨hw, hlt⟩ := h
    unfold WellFormed at hw
    obtain ⟨hc0, hh, hle⟩ := hw
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity :=
      ⟨hc0, hh, hlt⟩
    simp [step, hcond]
  | dequeue =>
    unfold Valid at h
    obtain ⟨hw, hlt⟩ := h
    unfold WellFormed at hw
    obtain ⟨hc0, hh, hle⟩ := hw
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count :=
      ⟨hc0, hh, hle, hlt⟩
    simp [step, hcond]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    unfold Valid at h
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro hc
      obtain ⟨hc0, hh, hlt⟩ := hc
      apply h
      constructor
      · unfold WellFormed
        exact ⟨hc0, hh, Nat.le_of_lt hlt⟩
      · exact hlt
    simp [step, hcond]
  | dequeue =>
    unfold Valid at h
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hc
      obtain ⟨hc0, hh, hle, hlt⟩ := hc
      apply h
      constructor
      · unfold WellFormed
        exact ⟨hc0, hh, hle⟩
      · exact hlt
    simp [step, hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hw
  cases op with
  | enqueue x =>
    simp only [step]
    split
    · next hc =>
      obtain ⟨hc0, hh, hlt⟩ := hc
      simp only [WellFormed] at hw ⊢
      obtain ⟨w0, wh, wle⟩ := hw
      exact ⟨w0, wh, Nat.succ_le_of_lt hlt⟩
    · exact hw
  | dequeue =>
    simp only [step]
    split
    · next hc =>
      obtain ⟨hc0, hh, hle, hlt⟩ := hc
      simp only at hw ⊢
      simp only [WellFormed] at hw ⊢
      obtain ⟨w0, wh, wle⟩ := hw
      refine ⟨hc0, Nat.mod_lt _ hc0, ?_⟩
      omega
    · exact hw

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hne
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · simp [step, hc]
  · simp [step, hc] at hne

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · simp [step, hc]
  · simp [step, hc] at hne

end RingBuffer
