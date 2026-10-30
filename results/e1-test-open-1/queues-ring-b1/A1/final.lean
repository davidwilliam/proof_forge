import RingBuffer.Spec
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

theorem dummy : True := trivial
#check RingBuffer.slot

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  simp [Valid, WellFormed] at h
  cases op with
  | enqueue x =>
    obtain ⟨⟨hcap, hhead, hcount_le⟩, hcount_lt⟩ := h
    simp only [step]
    simp [hcap, hhead, hcount_lt]
  | dequeue =>
    obtain ⟨⟨hcap, hhead, hcount_le⟩, hpos⟩ := h
    simp only [step]
    simp [hcap, hhead, hcount_le, hpos]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    simp only [step]
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro ⟨hcap, hhead, hlt⟩
      apply h
      refine ⟨⟨hcap, hhead, Nat.le_of_lt hlt⟩, hlt⟩
    simp [hcond]
  | dequeue =>
    simp only [Valid, WellFormed] at h
    simp only [step]
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro ⟨hcap, hhead, hle, hpos⟩
      apply h
      exact ⟨⟨hcap, hhead, hle⟩, hpos⟩
    simp [hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hwf
  obtain ⟨hcap, hhead, hcount⟩ := hwf
  cases op with
  | enqueue x =>
    simp only [step]
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · simp [hc]
      exact ⟨hcap, hhead, Nat.succ_le_of_lt hc.2.2⟩
    · simp [hc]
      exact ⟨hcap, hhead, hcount⟩
  | dequeue =>
    simp only [step]
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · simp [hc]
      refine ⟨hcap, Nat.mod_lt _ hcap, Nat.le_trans (Nat.sub_le _ _) hcount⟩
    · simp [hc]
      exact ⟨hcap, hhead, hcount⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  simp only [step, slot] at h ⊢
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · rw [if_pos hc] at h ⊢
    rfl
  · rw [if_neg hc] at h
    simp at h

theorem req_dequeue_effects  : DequeueEffects step := by
  intro s h
  simp only [step] at h ⊢
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · simp [hc]
  · simp [hc] at h

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · have step_eq : step s (.enqueue x) =
    (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
      simp [step, hc]
    have hcont : contents (step s (.enqueue x)).2 = contents s ++ [x] := by
      rw [step_eq]
      unfold contents slot
      simp only
      suffices hsuff : ∀ (c h n : Nat) (buf : Nat → Nat) (x : Nat),
          0 < c → h < c → n < c →
          (List.range (n + 1)).map (fun i => if (h + i) % c = (h + n) % c then x else buf ((h + i) % c))
          = (List.range n).map (fun i => buf ((h + i) % c)) ++ [x] by
          exact hsuff s.capacity s.head s.count s.buf x hc.1 hc.2.1 hc.2.2
      intro c h n buf x hc0 hh hn
      induction n with
      | zero => simp
      | succ n ih =>
        have hn1 : n < c := by omega
        have ih' := ih hn1
        have hrw : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by simp [List.range_succ]
        have lhs_rw : (List.range (n + 1 + 1)).map (fun i => if (h + i) % c = (h + (n + 1)) % c then x else buf ((h + i) % c))
          = (List.range (n + 1)).map (fun i => if (h + i) % c = (h + (n + 1)) % c then x else buf ((h + i) % c)) ++ [x] := by
          rw [hrw, List.map_append]; simp
        rw [lhs_rw]
        have hmap_eq : (List.range (n + 1)).map (fun i => if (h + i) % c = (h + (n + 1)) % c then x else buf ((h + i) % c))
          = (List.range (n + 1)).map (fun i => buf ((h + i) % c)) := by
          apply List.map_congr_left
          intro i hi
          have hi_lt : i < n + 1 := List.mem_range.mp hi
          have hne_mod : (h + i) % c ≠ (h + (n + 1)) % c := by
            intro heq
            have hrw1 : (h + i) % c = if h + i < c then h + i else h + i - c := by
              by_cases hi_c : h + i < c
              · simp [hi_c, Nat.mod_eq_of_lt hi_c]
              · have hle : c ≤ h + i := Nat.le_of_not_lt hi_c
                have hsub_lt : h + i - c < c := by omega
                have heq2 : h + i = c + (h + i - c) := by omega
                calc (h + i) % c = (c + (h + i - c)) % c := by rw [← heq2]
                  _ = (h + i - c) % c := by rw [Nat.add_mod_left]
                  _ = h + i - c := Nat.mod_eq_of_lt hsub_lt
                  _ = if h + i < c then h + i else h + i - c := by simp [hi_c]
            have hrw2 : (h + (n + 1)) % c = if h + (n + 1) < c then h + (n + 1) else h + (n + 1) - c := by
              by_cases hn_c : h + (n + 1) < c
              · simp [hn_c, Nat.mod_eq_of_lt hn_c]
              · have hle : c ≤ h + (n + 1) := Nat.le_of_not_lt hn_c
                have hsub_lt : h + (n + 1) - c < c := by omega
                have heq2 : h + (n + 1) = c + (h + (n + 1) - c) := by omega
                calc (h + (n + 1)) % c = (c + (h + (n + 1) - c)) % c := by rw [← heq2]
                  _ = (h + (n + 1) - c) % c := by rw [Nat.add_mod_left]
                  _ = h + (n + 1) - c := Nat.mod_eq_of_lt hsub_lt
                  _ = if h + (n + 1) < c then h + (n + 1) else h + (n + 1) - c := by simp [hn_c]
            rw [hrw1, hrw2] at heq
            by_cases hi_c : h + i < c <;> by_cases hn_c : h + (n + 1) < c <;> simp [hi_c, hn_c] at heq <;> omega
          simp [hne_mod]
        rw [hmap_eq]
    exact hcont
  · have step_rej : (step s (.enqueue x)).1 = .rejected := by simp [step, hc]
    exact absurd step_rej hne

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  simp only [step] at hne
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · have hstep2 : step s Op.dequeue = (Outcome.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by simp [step, hc]
    rw [hstep2]
    refine ⟨s.buf s.head, rfl, ?_⟩
    have hhead : s.head < s.capacity := hc.2.1
    have h0 : (s.head + 0) % s.capacity = s.head := by simp [Nat.mod_eq_of_lt hhead]
    unfold contents slot
    simp only
    obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
    rw [hn]
    have h_range : List.range (n + 1) = 0 :: (List.range n).map (fun x => x + 1) := by simp [List.range_succ_eq_map]
    rw [h_range]
    simp only [List.map_cons, List.map_map, Function.comp_def]
    rw [h0]
    congr 1
    apply List.map_congr_left
    intro i hi
    have h1 : s.head + (i + 1) = s.head + 1 + i := by omega
    show s.buf ((s.head + (i + 1)) % s.capacity) = s.buf (((s.head + 1) % s.capacity + i) % s.capacity)
    rw [h1, Nat.add_mod]
    have hi_lt : i < n := List.mem_range.mp hi
    -- need n+1 ≤ capacity, so n < capacity
    have hle : n + 1 ≤ s.capacity := by omega
    have hn_lt : n < s.capacity := by omega
    have hi_lt_cap : i < s.capacity := by omega
    have hi_mod : i % s.capacity = i := Nat.mod_eq_of_lt hi_lt_cap
    rw [hi_mod]
  · simp [hc] at hne

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    simp only [run]
    have ih_eq := ih (step s op).2
    cases op with
    | enqueue x =>
      by_cases hrej : (step s (Op.enqueue x)).1 = .rejected
      · have hstep : step s (Op.enqueue x) = (.rejected, s) := by
          have hvalid : ¬ Valid s (Op.enqueue x) := by
            intro hv
            have := req_valid_succeeds s (Op.enqueue x) hv
            exact this hrej
          exact req_invalid_noop s (Op.enqueue x) hvalid
        have h1 : (step s (Op.enqueue x)).1 = .rejected := by rw [hstep]
        have h2 : (step s (Op.enqueue x)).2 = s := by rw [hstep]
        rw [h2] at ih_eq ⊢
        simp [inflow, outflow, inflowOf, outflowOf, h1] at ⊢
        exact ih_eq
      · have h_not_rej : (step s (Op.enqueue x)).1 ≠ .rejected := hrej
        have h_succ_contents := req_enqueue_contents s x h_not_rej
        have h_ok : (step s (Op.enqueue x)).1 = .ok := by
          have heff := req_enqueue_effects s x h_not_rej
          have : (step s (Op.enqueue x)).1 = .ok := by rw [heff]
          exact this
        simp [inflow, outflow, inflowOf, outflowOf, h_ok]
        calc contents s ++ ([x] ++ inflow (run step (step s (Op.enqueue x)).2 ops).1)
            = (contents s ++ [x]) ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by rw [List.append_assoc]
          _ = contents (step s (Op.enqueue x)).2 ++ inflow (run step (step s (Op.enqueue x)).2 ops).1 := by rw [h_succ_contents]
          _ = outflow (run step (step s (Op.enqueue x)).2 ops).1 ++ contents (run step (step s (Op.enqueue x)).2 ops).2 := ih_eq
          _ = ([] ++ outflow (run step (step s (Op.enqueue x)).2 ops).1) ++ contents (run step (step s (Op.enqueue x)).2 ops).2 := by simp
    | dequeue =>
      by_cases hrej : (step s Op.dequeue).1 = .rejected
      · have hstep : step s Op.dequeue = (.rejected, s) := by
          have hvalid : ¬ Valid s Op.dequeue := by intro hv; have := req_valid_succeeds s Op.dequeue hv; exact this hrej
          exact req_invalid_noop s Op.dequeue hvalid
        have h1 : (step s Op.dequeue).1 = .rejected := by rw [hstep]
        have h2 : (step s Op.dequeue).2 = s := by rw [hstep]
        rw [h2] at ih_eq ⊢
        simp [inflow, outflow, inflowOf, outflowOf, h1] at ⊢
        exact ih_eq
      · have h_not_rej : (step s Op.dequeue).1 ≠ .rejected := hrej
        obtain ⟨x, hx_got, hx_cont⟩ := req_dequeue_contents s h_not_rej
        simp [inflow, outflow, inflowOf, outflowOf, hx_got]
        show contents s ++ inflow (run step (step s Op.dequeue).2 ops).1 =
          [x] ++ outflow (run step (step s Op.dequeue).2 ops).1 ++ contents (run step (step s Op.dequeue).2 ops).2
        have lhs_eq : contents s ++ inflow (run step (step s Op.dequeue).2 ops).1
            = [x] ++ (contents (step s Op.dequeue).2 ++ inflow (run step (step s Op.dequeue).2 ops).1) := by
          rw [hx_cont]; rfl
        rw [lhs_eq, ih_eq, List.append_assoc]

end RingBuffer
