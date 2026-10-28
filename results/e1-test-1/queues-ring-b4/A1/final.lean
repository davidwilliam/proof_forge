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

theorem helper_wf_proof2 : True := trivial

theorem helper_wf_b : KeepsWellFormed step := by
  intro s op hs
  have hc0 : 0 < s.capacity := hs.1
  have hh : s.head < s.capacity := hs.2.1
  have hle : s.count ≤ s.capacity := hs.2.2
  cases op with
  | enqueue x =>
    simp only [step]
    split
    · next hcond =>
      obtain ⟨h1, h2, hlt⟩ := hcond
      exact ⟨hc0, hh, Nat.succ_le_of_lt hlt⟩
    · exact hs
  | dequeue =>
    simp only [step]
    split
    · next hcond =>
      obtain ⟨h1, h2, h3, h4⟩ := hcond
      refine ⟨hc0, Nat.mod_lt _ hc0, ?_⟩
      exact Nat.le_trans (Nat.sub_le _ _) hle
    · exact hs

theorem tmp_enq_test5 (s : State) (x : Nat) (hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)) : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
  have h1 := hcond.1
  have h2 := hcond.2.1
  have h3 := hcond.2.2
  simp [step, h1, h2, h3, slot]
  rfl

theorem tmp_enq_neg (s : State) (x : Nat) (hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)) : step s (.enqueue x) = (.rejected, s) := by
  simp [step, hcond]

theorem tmp_deq_pos (s : State) (hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)) : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
  simp [step, hcond]

theorem tmp_deq_neg (s : State) (hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)) : step s .dequeue = (.rejected, s) := by
  simp [step, hcond]

theorem tmp_slot_unfold2 (h k cap : Nat) (hh : h < cap) (hk : k < cap) :
    (h + k) % cap = if h + k < cap then h + k else h + k - cap := by
  by_cases hlt : h + k < cap
  · simp [hlt, Nat.mod_eq_of_lt hlt]
  · simp [hlt]
    have hge : cap ≤ h + k := Nat.le_of_not_lt hlt
    have heq : (h + k) % cap = (h + k - cap) % cap := Nat.mod_eq_sub_mod hge
    have hlt2 : h + k - cap < cap := by omega
    rw [heq, Nat.mod_eq_of_lt hlt2]

theorem tmp_slot_neq (h i n cap : Nat) (hh : h < cap) (hi : i < n) (hn : n < cap) :
    (h + i) % cap ≠ (h + n) % cap := by
  have hi_lt : i < cap := Nat.lt_trans hi hn
  have e1 := tmp_slot_unfold2 h i cap hh hi_lt
  have e2 := tmp_slot_unfold2 h n cap hh hn
  by_cases h1 : h + i < cap <;> by_cases h2 : h + n < cap <;> simp [h1, h2] at e1 e2 <;> omega

theorem tmp_range_cons (n : Nat) : List.range (n+1) = 0 :: ((List.range n).map (· + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n+1) ++ [n+1] := by
      have := @List.range_succ (n+1)
      simpa using this
    have h2 : List.range (n+1) = List.range n ++ [n] := by
      have := @List.range_succ n
      simpa using this
    rw [h1]
    have hmap : ((List.range (n+1)).map (· + 1)) = ((List.range n).map (·+1)) ++ [n+1] := by
      rw [h2, List.map_append]
      rfl
    rw [hmap, ih]
    simp

theorem tmp_slot_succ_aux (h i cap : Nat) : (h + (i + 1)) % cap = (((h + 1) % cap + i) % cap) := by
  have h1 : h + (i + 1) = (h + 1) + i := by omega
  rw [h1]
  exact (Nat.mod_add_mod (h+1) cap i).symm

theorem tmp_slot_shift (s : State) (i : Nat) :
    slot s (i+1) = slot { s with head := (s.head + 1) % s.capacity } i := by
  unfold slot
  simp only
  exact tmp_slot_succ_aux s.head i s.capacity

theorem tmp_head_mod (s : State) (hh : s.head < s.capacity) : slot s 0 = s.head := by
  unfold slot
  simp only [Nat.add_zero]
  exact Nat.mod_eq_of_lt hh

theorem tmp_map_range_succ (f : Nat → Nat) (n : Nat) :
    ((List.range (n+1)).map f) = f 0 :: ((List.range n).map (fun i => f (i+1))) := by
  have hr := tmp_range_cons n
  rw [hr, List.map_cons]
  congr 1
  rw [List.map_map]
  rfl

theorem tmp_enq_contents_helper3 (s : State) (x : Nat) (hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) :
    contents { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } = contents s ++ [x] := by
  have hh : s.head < s.capacity := hcond.2.1
  have hlt : s.count < s.capacity := hcond.2.2
  unfold contents slot
  simp only
  have hrw : List.range (s.count + 1) = List.range s.count ++ [s.count] := by
    have := @List.range_succ s.count
    simpa using this
  rw [hrw, List.map_append]
  have h1 : List.map (fun i => (fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + i) % s.capacity)) (List.range s.count)
      = List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count) := by
    apply List.map_congr_left
    intro i hi
    have hi_lt : i < s.count := (List.mem_range.mp hi)
    have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity :=
      tmp_slot_neq s.head i s.count s.capacity hh hi_lt hlt
    simp [hne]
  have h2 : List.map (fun i => (fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + i) % s.capacity)) [s.count] = [x] := by
    simp
  rw [h1, h2]

theorem tmp_enqueue_contents_proved (s : State) (x : Nat) (hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) :
    contents (step s (.enqueue x)).2 = contents s ++ [x] := by
  have heq := tmp_enq_test5 s x hcond
  have h2 : (step s (.enqueue x)).2 = { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } := by rw [heq]
  rw [h2]
  exact tmp_enq_contents_helper3 s x hcond

theorem tmp_run_cons1 (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
  simp only [run]

theorem tmp_run_cons2 (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
  simp only [run]

theorem tmp_inflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (p :: t) = inflowOf p ++ inflow t := rfl

theorem tmp_outflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (p :: t) = outflowOf p ++ outflow t := rfl

theorem tmp_inflow_nil : inflow [] = [] := rfl

theorem tmp_outflow_nil : outflow [] = [] := rfl

theorem tmp_inflow_rej (op : Op) : inflowOf (op, .rejected) = [] := by
  cases op <;> rfl

theorem tmp_outflow_rej (op : Op) : outflowOf (op, .rejected) = [] := by
  cases op <;> rfl

theorem tmp_inflow_enq_ok (x : Nat) : inflowOf (.enqueue x, .ok) = [x] := rfl

theorem tmp_outflow_enq_ok (x : Nat) : outflowOf (.enqueue x, .ok) = ([] : List Nat) := rfl

theorem tmp_inflow_deq_got (y : Nat) : inflowOf (.dequeue, .got y) = ([] : List Nat) := rfl

theorem tmp_outflow_deq_got (y : Nat) : outflowOf (.dequeue, .got y) = [y] := rfl

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid, WellFormed] at h
    obtain ⟨⟨hc0, hh, hle⟩, hlt⟩ := h
    simp [step, hc0, hh, hlt]
  | dequeue =>
    simp [Valid, WellFormed] at h
    obtain ⟨⟨hc0, hh, hle⟩, hpos⟩ := h
    simp [step, hc0, hh, hle, hpos]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    have hc : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro ⟨hc0, hh, hlt⟩
      apply h
      exact ⟨⟨hc0, hh, Nat.le_of_lt hlt⟩, hlt⟩
    simp [step, hc]
  | dequeue =>
    simp only [Valid, WellFormed] at h
    have hc : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro ⟨hc0, hh, hle, hpos⟩
      apply h
      exact ⟨⟨hc0, hh, hle⟩, hpos⟩
    simp [step, hc]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hs
  have hc0 : 0 < s.capacity := hs.1
  have hh : s.head < s.capacity := hs.2.1
  have hle : s.count ≤ s.capacity := hs.2.2
  cases op with
  | enqueue x =>
    simp only [step]
    split
    · next hcond =>
      obtain ⟨h1, h2, hlt⟩ := hcond
      exact ⟨hc0, hh, Nat.succ_le_of_lt hlt⟩
    · exact hs
  | dequeue =>
    simp only [step]
    split
    · next hcond =>
      obtain ⟨h1, h2, h3, h4⟩ := hcond
      refine ⟨hc0, Nat.mod_lt _ hc0, ?_⟩
      exact Nat.le_trans (Nat.sub_le _ _) hle
    · exact hs

theorem req_enqueue_effects  : EnqueueEffects step := by
  intro s x hne
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · exact tmp_enq_test5 s x hcond
  · have heq := tmp_enq_neg s x hcond
    rw [heq] at hne
    simp at hne

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · exact tmp_deq_pos s hcond
  · have heq := tmp_deq_neg s hcond
    rw [heq] at hne
    simp at hne

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · exact tmp_enqueue_contents_proved s x hcond
  · have heq := tmp_enq_neg s x hcond
    rw [heq] at hne
    simp at hne

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · have heq := tmp_deq_pos s hcond
    obtain ⟨hc0, hh, hle, hpos⟩ := hcond
    refine ⟨s.buf s.head, ?_, ?_⟩
    · rw [heq]
    · have heq2 : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
        rw [heq]
      obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
      have hcount_sub : s.count - 1 = n := by omega
      have hL : contents s = s.buf s.head :: (List.range n).map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) := by
        unfold contents slot
        rw [hn, tmp_map_range_succ]
        simp only [Nat.add_zero, Nat.mod_eq_of_lt hh]
      have hR : contents ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State)
          = (List.range n).map (fun i => s.buf ((((s.head + 1) % s.capacity + i) % s.capacity))) := by
        unfold contents slot
        simp only [hcount_sub]
      rw [heq2, hL, hR]
      congr 1
      have hfun : (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) =
          (fun i => s.buf ((((s.head + 1) % s.capacity + i) % s.capacity))) := by
        funext i
        congr 1
        exact tmp_slot_succ_aux s.head i s.capacity
      rw [hfun]
  · have heq := tmp_deq_neg s hcond
    rw [heq] at hne
    simp at hne

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hsingle : contents s ++ inflowOf (op, (step s op).1)
        = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
      by_cases hrej : (step s op).1 = .rejected
      · have hstate : (step s op).2 = s := by
          have hnotvalid : ¬ Valid s op := by
            intro hv
            have hne : (step s op).1 ≠ .rejected := req_valid_succeeds s op hv
            exact hne hrej
          have h := req_invalid_noop s op hnotvalid
          exact congrArg Prod.snd h
        cases op with
        | enqueue x =>
          have hin : inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [] := by
            rw [hrej]; rfl
          have hout : outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [] := by
            rw [hrej]; rfl
          rw [hin, hout, hstate]
          simp
        | dequeue =>
          have hin : inflowOf (Op.dequeue, (step s Op.dequeue).1) = [] := by
            rw [hrej]; rfl
          have hout : outflowOf (Op.dequeue, (step s Op.dequeue).1) = [] := by
            rw [hrej]; rfl
          rw [hin, hout, hstate]
          simp
      · cases op with
        | enqueue x =>
          have hne : (step s (.enqueue x)).1 ≠ .rejected := hrej
          have heff := req_enqueue_effects s x hne
          have h1 : (step s (.enqueue x)).1 = .ok := by rw [heff]
          have h2 : contents (step s (.enqueue x)).2 = contents s ++ [x] :=
            req_enqueue_contents s x hne
          have hin : inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [x] := by
            rw [h1]; rfl
          have hout : outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = ([] : List Nat) := by
            rw [h1]; rfl
          rw [hin, hout, h2]
          simp
        | dequeue =>
          have hne : (step s .dequeue).1 ≠ .rejected := hrej
          obtain ⟨x, hxout, hxcont⟩ := req_dequeue_contents s hne
          have hin : inflowOf (Op.dequeue, (step s Op.dequeue).1) = ([] : List Nat) := by
            rw [hxout]; rfl
          have hout : outflowOf (Op.dequeue, (step s Op.dequeue).1) = [x] := by
            rw [hxout]; rfl
          rw [hin, hout]
          simp [hxcont]
    have hIH := ih (step s op).2
    have hrun1 : (run step s (op :: ops)).1
        = (op, (step s op).1) :: (run step (step s op).2 ops).1 := rfl
    have hrun2 : (run step s (op :: ops)).2
        = (run step (step s op).2 ops).2 := rfl
    rw [hrun1, hrun2]
    have hinf : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := rfl
    have hout : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := rfl
    rw [hinf, hout]
    calc contents s ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (contents s ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by
          rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ contents (step s op).2) ++ inflow (run step (step s op).2 ops).1 := by
          rw [hsingle]
      _ = outflowOf (op, (step s op).1) ++ (contents (step s op).2 ++ inflow (run step (step s op).2 ops).1) := by
          rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ contents (run step (step s op).2 ops).2) := by
          rw [hIH]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ contents (run step (step s op).2 ops).2 := by
          rw [List.append_assoc]

end RingBuffer
