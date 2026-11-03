import RingBuffer.Spec
import ProofForgeFin
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      let tail := (s.head + s.count) % s.capacity
      (.ok, { s with buf := fun i => if i = tail then x else s.buf i, count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hvalid
  cases op with
  | enqueue x =>
    unfold step
    simp only
    intro h
    have h1 : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
      obtain ⟨⟨hcap, hhead, hcount_le⟩, hcount_lt⟩ := hvalid
      exact ⟨hcap, hhead, hcount_lt⟩
    rw [if_pos h1] at h
    simp at h
  | dequeue =>
    unfold step
    simp only
    intro h
    obtain ⟨⟨hcap, hhead, hcount_le⟩, hpos⟩ := hvalid
    have h1 : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := ⟨hcap, hhead, hcount_le, hpos⟩
    rw [if_pos h1] at h
    simp at h

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  unfold step
  cases op with
  | enqueue x =>
    simp only
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exfalso; apply h
      obtain ⟨hcap, hhead, hcnt_lt⟩ := hc
      exact ⟨⟨hcap, hhead, Nat.le_of_lt hcnt_lt⟩, hcnt_lt⟩
    · simp [hc]
  | dequeue =>
    simp only
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · exfalso; apply h
      obtain ⟨hcap, hhead, hle, hpos⟩ := hc
      exact ⟨⟨hcap, hhead, hle⟩, hpos⟩
    · simp [hc]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hwf
  cases op with
  | enqueue x =>
    show WellFormed (step s (Op.enqueue x)).2
    unfold step
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · simp only [h]
      obtain ⟨hcap, hhead, hle⟩ := hwf
      obtain ⟨_, _, hlt⟩ := h
      simp
      exact ⟨hcap, hhead, Nat.succ_le_of_lt hlt⟩
    · simp only [h]
      exact hwf
  | dequeue =>
    show WellFormed (step s Op.dequeue).2
    unfold step
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · simp only [h]
      obtain ⟨hcap, hhead, hle⟩ := hwf
      simp
      refine ⟨hcap, Nat.mod_lt _ hcap, Nat.le_trans (Nat.sub_le _ _) hle⟩
    · simp only [h]
      exact hwf

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  simp only at h ⊢
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · simp [hc] at h ⊢
    -- need to show tail equals slot s.count
    have : (s.head + s.count) % s.capacity = slot s s.count := rfl
    simp [this]
  · simp [hc] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  unfold step at h ⊢
  simp only at h ⊢
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · simp [hc] at h ⊢
  · simp [hc] at h

theorem req_enqueue_contents : EnqueueContents step := sorry

theorem req_dequeue_contents : DequeueContents step := by
  intro s hrej
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · have hhead := hc.2.1
    have hpos : 0 < s.count := hc.2.2.2
    have step_eq : step s Op.dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
      unfold step
      simp [hc]
    have hfst : (step s Op.dequeue).1 = .got (s.buf s.head) := by rw [step_eq]
    have hsnd : (step s Op.dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by rw [step_eq]
    refine ⟨s.buf s.head, hfst, ?_⟩
    rw [hsnd]
    unfold contents slot
    obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hpos)
    rw [hn]
    simp only [Nat.add_sub_cancel]
    have hslot0 : (s.head + 0) % s.capacity = s.head := by
      simp [Nat.mod_eq_of_lt hhead]
    have h_range : List.range (n + 1) = 0 :: (List.range n).map (· + 1) := by
      simp [List.range_succ_eq_map]
    have h_map_head : (List.range (n + 1)).map (fun i => s.buf ((s.head + i) % s.capacity))
        = s.buf ((s.head + 0) % s.capacity) :: (List.range n).map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) := by
      rw [h_range]
      simp
    rw [h_map_head, hslot0]
    congr 1
    have hfun : (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) = (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) := by
      funext i
      have key : (s.head + (i + 1)) % s.capacity = ((s.head + 1) % s.capacity + i) % s.capacity := by
        have h1 : ((s.head + 1) % s.capacity + i) % s.capacity = (s.head + 1 + i) % s.capacity := Nat.mod_add_mod _ _ _
        have h3 : s.head + (i + 1) = s.head + 1 + i := by omega
        rw [h1, h3]
      rw [key]
    rw [hfun]
  · exfalso
    have : (step s Op.dequeue).1 = .rejected := by
      unfold step
      simp [hc]
    rw [this] at hrej
    simp at hrej

theorem req_fifo             : Fifo step := sorry

end RingBuffer
