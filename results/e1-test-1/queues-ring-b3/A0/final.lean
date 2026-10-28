import RingBuffer.Spec
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { s with buf := (fun i => if i = slot s s.count then x else s.buf i), count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at hV
    obtain ⟨⟨hcap, hhead, _⟩, hcount⟩ := hV
    have hC : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity :=
      ⟨hcap, hhead, hcount⟩
    simp [step, hC]
  | dequeue =>
    simp only [Valid, WellFormed] at hV
    obtain ⟨⟨hcap, hhead, hle⟩, hpos⟩ := hV
    have hC : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count :=
      ⟨hcap, hhead, hle, hpos⟩
    simp [step, hC]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at hInv
    have hC : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro h
      obtain ⟨hcap, hhead, hlt⟩ := h
      apply hInv
      exact ⟨⟨hcap, hhead, Nat.le_of_lt hlt⟩, hlt⟩
    simp [step, hC]
  | dequeue =>
    simp only [Valid, WellFormed] at hInv
    have hC : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro h
      obtain ⟨hcap, hhead, hle, hpos⟩ := h
      apply hInv
      exact ⟨⟨hcap, hhead, hle⟩, hpos⟩
    simp [step, hC]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hW
  cases op with
  | enqueue x =>
    simp only [WellFormed] at hW
    obtain ⟨hcap, hhead, hle⟩ := hW
    by_cases hC : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · simp [step, hC]
      simp only [WellFormed]
      obtain ⟨_, _, hlt⟩ := hC
      exact ⟨hcap, hhead, by omega⟩
    · simp [step, hC]
      exact ⟨hcap, hhead, hle⟩
  | dequeue =>
    simp only [WellFormed] at hW
    obtain ⟨hcap, hhead, hle⟩ := hW
    by_cases hC : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · simp [step, hC]
      simp only [WellFormed]
      obtain ⟨_, _, _, hpos⟩ := hC
      refine ⟨hcap, Nat.mod_lt _ hcap, by omega⟩
    · simp [step, hC]
      exact ⟨hcap, hhead, hle⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hNe
  have hC : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact h
    · exfalso
      apply hNe
      simp [step, h]
  simp [step, hC]

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hNe
  have hC : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
    by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · exact h
    · exfalso
      apply hNe
      simp [step, h]
  simp [step, hC]

private theorem enq_cond_of_ne {s : State} {x : Nat}
    (hNe : (step s (.enqueue x)).1 ≠ .rejected) :
    0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
  by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · exact h
  · exfalso
    apply hNe
    simp [step, h]

private theorem deq_cond_of_ne {s : State}
    (hNe : (step s .dequeue).1 ≠ .rejected) :
    0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
  by_cases h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · exact h
  · exfalso
    apply hNe
    simp [step, h]

private theorem mod_sub_eq {x cap : Nat} (_hcap : 0 < cap) (hle : cap ≤ x) (hlt : x < 2 * cap) :
    x % cap = x - cap := by
  have hlt2 : x - cap < cap := by omega
  have hk : cap + (x - cap) = x := Nat.add_sub_cancel' hle
  have h1 : (cap + (x - cap)) % cap = ((cap % cap) + ((x - cap) % cap)) % cap :=
    Nat.add_mod cap (x - cap) cap
  have h2 : cap % cap = 0 := Nat.mod_self cap
  have h3 : (x - cap) % cap = x - cap := Nat.mod_eq_of_lt hlt2
  have h4 : x % cap = (cap + (x - cap)) % cap := by rw [hk]
  rw [h4, h1, h2, h3, Nat.zero_add, h3]

private theorem enq_slot_ne {s : State}
    (hcap : 0 < s.capacity) (hhead : s.head < s.capacity) (hlt : s.count < s.capacity)
    {i : Nat} (hi : i < s.count) : slot s i ≠ slot s s.count := by
  simp only [slot]
  intro hEq
  have hb : s.head + s.count < 2 * s.capacity := by omega
  have ha : s.head + i < 2 * s.capacity := by omega
  by_cases h1 : s.head + i < s.capacity
  · by_cases h2 : s.head + s.count < s.capacity
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hEq
      omega
    · have h2p : s.capacity ≤ s.head + s.count := by omega
      rw [Nat.mod_eq_of_lt h1, mod_sub_eq hcap h2p hb] at hEq
      omega
  · have h1p : s.capacity ≤ s.head + i := by omega
    by_cases h2 : s.head + s.count < s.capacity
    · omega
    · have h2p : s.capacity ≤ s.head + s.count := by omega
      rw [mod_sub_eq hcap h1p ha, mod_sub_eq hcap h2p hb] at hEq
      omega

private theorem enq_map_aux (s : State) (x : Nat)
    (hcap : 0 < s.capacity) (hhead : s.head < s.capacity) (hlt : s.count < s.capacity)
    (n : Nat) (hle : n ≤ s.count) :
    (List.range n).map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i))
      = (List.range n).map (fun i => s.buf (slot s i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hle_n : n ≤ s.count := by omega
    have hlt_n : n < s.count := by omega
    have hne : slot s n ≠ slot s s.count := enq_slot_ne hcap hhead hlt hlt_n
    have ihr := ih hle_n
    have hrw : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [hrw, List.map_append, List.map_append, ihr]
    congr 1
    simp [hne]

private theorem my_range_cons (f : Nat → Nat) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := List.range_succ
    have h2 : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [h1, List.map_append, ih, h2, List.map_append]
    simp

private theorem slot_shift_eq (s : State) (i : Nat) :
    (s.head + (i + 1)) % s.capacity = ((s.head + 1) % s.capacity + i) % s.capacity := by
  have heq : s.head + (i + 1) = (s.head + 1) + i := by omega
  have h1 := Nat.add_mod (s.head + 1) i s.capacity
  have h2 := Nat.add_mod ((s.head + 1) % s.capacity) i s.capacity
  have hmm := Nat.mod_mod (s.head + 1) s.capacity
  rw [heq, h1, h2, hmm]

private theorem deq_map_eq (s : State) (n : Nat)
    (h : ∀ i, i < n → s.buf (slot s (i + 1)) = s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) :
    (List.range n).map (fun i => s.buf (slot s (i + 1)))
      = (List.range n).map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ihr : (List.range n).map (fun i => s.buf (slot s (i + 1)))
        = (List.range n).map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) := by
      apply ih
      intro i hi
      apply h
      omega
    have hlast : s.buf (slot s (n + 1)) = s.buf (((s.head + 1) % s.capacity + n) % s.capacity) :=
      h n (Nat.lt_succ_self n)
    have hrw : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [hrw, List.map_append, List.map_append, ihr]
    simp [hlast]

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hNe
  have hC := enq_cond_of_ne hNe
  obtain ⟨hcap, hhead, hlt⟩ := hC
  have hE := req_enqueue_effects s x hNe
  have hSnd : (step s (.enqueue x)).2
      = { s with buf := (fun i => if i = slot s s.count then x else s.buf i), count := s.count + 1 } := by
    rw [hE]
  rw [hSnd]
  have haux := enq_map_aux s x hcap hhead hlt s.count (Nat.le_refl s.count)
  have hgoal : contents ({ s with buf := (fun i => if i = slot s s.count then x else s.buf i), count := s.count + 1 } : State)
      = (List.range (s.count + 1)).map
        (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)) := rfl
  have hrange : List.range (s.count + 1) = List.range s.count ++ [s.count] := List.range_succ
  have hsing : (List.map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)) [s.count])
      = [x] := by simp
  have hc : contents s = (List.range s.count).map (fun i => s.buf (slot s i)) := rfl
  rw [hgoal, hrange, List.map_append, haux, hsing, hc]

theorem req_dequeue_contents : DequeueContents step := by
  intro s hNe
  have hC := deq_cond_of_ne hNe
  have hE := req_dequeue_effects s hNe
  obtain ⟨hcap, hhead, hle, hpos⟩ := hC
  have hSnd : (step s .dequeue).2
      = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
    rw [hE]
  have hout : (step s .dequeue).1 = .got (s.buf s.head) := by rw [hE]
  refine ⟨s.buf s.head, hout, ?_⟩
  have hcount : s.count = (s.count - 1) + 1 := by omega
  have h0 : slot s 0 = s.head := by
    simp only [slot, Nat.add_zero]
    exact Nat.mod_eq_of_lt hhead
  have htail : ∀ i, i < s.count - 1 →
      s.buf (slot s (i + 1)) = s.buf (((s.head + 1) % s.capacity + i) % s.capacity) := by
    intro i _
    congr 1
    simp only [slot]
    exact slot_shift_eq s i
  have hsplit : contents s
      = s.buf (slot s 0) :: (List.range (s.count - 1)).map (fun i => s.buf (slot s (i + 1))) := by
    simp only [contents]
    rw [hcount]
    exact my_range_cons (fun i => s.buf (slot s i)) (s.count - 1)
  have hcont : contents ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State)
      = (List.range (s.count - 1)).map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) := rfl
  have hmap := deq_map_eq s (s.count - 1) htail
  calc contents s
      = s.buf (slot s 0) :: (List.range (s.count - 1)).map (fun i => s.buf (slot s (i + 1))) := hsplit
    _ = s.buf s.head :: (List.range (s.count - 1)).map (fun i => s.buf (slot s (i + 1))) := by rw [h0]
    _ = s.buf s.head :: (List.range (s.count - 1)).map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) := by rw [hmap]
    _ = s.buf s.head :: contents ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) := by rw [hcont]
    _ = s.buf s.head :: contents (step s .dequeue).snd := by rw [hSnd]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hr1 : (run step s (op :: ops)).1
        = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by simp [run]
    have hr2 : (run step s (op :: ops)).2
        = (run step (step s op).2 ops).2 := by simp [run]
    have hIn : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      simp [inflow]
    have hOut : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      simp [outflow]
    have hstep : contents s ++ inflowOf (op, (step s op).1)
        = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
      cases op with
      | enqueue x =>
        by_cases hV : Valid s (.enqueue x)
        · have hNe : (step s (.enqueue x)).1 ≠ .rejected :=
            req_valid_succeeds s (.enqueue x) hV
          have hCc := req_enqueue_contents s x hNe
          have hE := req_enqueue_effects s x hNe
          have hOk : (step s (.enqueue x)).1 = .ok := by rw [hE]
          have hIn0 : inflowOf (.enqueue x, (step s (.enqueue x)).1) = [x] := by
            simp [hOk, inflowOf]
          have hOut0 : outflowOf (.enqueue x, (step s (.enqueue x)).1) = [] := by
            simp [hOk, outflowOf]
          rw [hIn0, hOut0, hCc]
          simp
        · have hEq : step s (.enqueue x) = (.rejected, s) :=
            req_invalid_noop s (.enqueue x) hV
          have h1 : (step s (.enqueue x)).1 = .rejected := by rw [hEq]
          have h2 : (step s (.enqueue x)).2 = s := by rw [hEq]
          have hIn0 : inflowOf (.enqueue x, (step s (.enqueue x)).1) = [] := by
            simp [h1, inflowOf]
          have hOut0 : outflowOf (.enqueue x, (step s (.enqueue x)).1) = [] := by
            simp [h1, outflowOf]
          rw [hIn0, hOut0, h2]
          simp
      | dequeue =>
        by_cases hV : Valid s .dequeue
        · have hNe : (step s .dequeue).1 ≠ .rejected :=
            req_valid_succeeds s .dequeue hV
          obtain ⟨y, hy1, hy2⟩ := req_dequeue_contents s hNe
          have hIn0 : inflowOf (.dequeue, (step s .dequeue).1) = [] := by
            simp [inflowOf]
          have hOut0 : outflowOf (.dequeue, (step s .dequeue).1) = [y] := by
            simp [hy1, outflowOf]
          rw [hIn0, hOut0, hy2]
          simp
        · have hEq : step s .dequeue = (.rejected, s) :=
            req_invalid_noop s .dequeue hV
          have h1 : (step s .dequeue).1 = .rejected := by rw [hEq]
          have h2 : (step s .dequeue).2 = s := by rw [hEq]
          have hIn0 : inflowOf (.dequeue, (step s .dequeue).1) = [] := by
            simp [inflowOf]
          have hOut0 : outflowOf (.dequeue, (step s .dequeue).1) = [] := by
            simp [h1, outflowOf]
          rw [hIn0, hOut0, h2]
          simp
    have iheq := ih (s := (step s op).2)
    rw [hr1, hr2, hIn, hOut]
    calc contents s ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (contents s ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by
          rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ contents (step s op).2)
          ++ inflow (run step (step s op).2 ops).1 := by rw [hstep]
      _ = outflowOf (op, (step s op).1)
          ++ (contents (step s op).2 ++ inflow (run step (step s op).2 ops).1) := by
          rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1)
          ++ (outflow (run step (step s op).2 ops).1
            ++ contents (run step (step s op).2 ops).2) := by rw [iheq]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1)
          ++ contents (run step (step s op).2 ops).2 := by rw [List.append_assoc]

end RingBuffer
