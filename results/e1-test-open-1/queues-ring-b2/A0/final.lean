import RingBuffer.Spec

namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem mod_small_aux {a c : Nat} (h : a < c) : a % c = a := Nat.mod_eq_of_lt h

theorem mod_big_aux {a c : Nat} (hle : c ≤ a) (hlt : a < 2 * c) : a % c = a - c := by
  have hsub_lt : a - c < c := by omega
  have heq : a = c + (a - c) := by omega
  have h1 : a % c = (c + (a - c)) % c := by rw [← heq]
  have h2 : (c + (a - c)) % c = (a - c) % c := by
    have : c + (a - c) = (a - c) + c := Nat.add_comm _ _
    rw [this, Nat.add_mod_right]
  have h3 : (a - c) % c = a - c := mod_small_aux hsub_lt
  rw [h1, h2, h3]

theorem mod_ne_aux {cap head i cnt : Nat} (hhead : head < cap) (hlt : cnt < cap) (hi : i < cnt) :
    (head + i) % cap ≠ (head + cnt) % cap := by
  intro heq
  have h_hi_lt2 : head + i < 2 * cap := by omega
  have h_hc_lt2 : head + cnt < 2 * cap := by omega
  by_cases h1 : cap ≤ head + i
  · have h2 : cap ≤ head + cnt := by omega
    rw [mod_big_aux h1 h_hi_lt2, mod_big_aux h2 h_hc_lt2] at heq
    omega
  · have h1' : head + i < cap := by omega
    by_cases h2 : cap ≤ head + cnt
    · rw [mod_small_aux h1', mod_big_aux h2 h_hc_lt2] at heq
      omega
    · have h2' : head + cnt < cap := by omega
      rw [mod_small_aux h1', mod_small_aux h2'] at heq
      omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
      obtain ⟨⟨hc, hh, _⟩, hlt⟩ := h
      exact ⟨hc, hh, hlt⟩
    show (step s (Op.enqueue x)).1 ≠ .rejected
    unfold step
    simp [hcond]
  | dequeue =>
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
      obtain ⟨⟨hc, hh, hle⟩, hpos⟩ := h
      exact ⟨hc, hh, hle, hpos⟩
    show (step s Op.dequeue).1 ≠ .rejected
    unfold step
    simp [hcond]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro ⟨hc, hh, hlt⟩
      apply h
      constructor
      · exact ⟨hc, hh, Nat.le_of_lt hlt⟩
      · exact hlt
    show step s (Op.enqueue x) = (.rejected, s)
    unfold step
    simp [hcond]
  | dequeue =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro ⟨hc, hh, hle, hpos⟩
      apply h
      exact ⟨⟨hc, hh, hle⟩, hpos⟩
    show step s Op.dequeue = (.rejected, s)
    unfold step
    simp [hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hw
  cases op with
  | enqueue x =>
    unfold step
    by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · simp only [if_pos hcond]
      obtain ⟨hc, hh, hle⟩ := hw
      show WellFormed { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }
      simp only [WellFormed]
      exact ⟨hc, hh, by omega⟩
    · simp only [if_neg hcond]
      exact hw
  | dequeue =>
    unfold step
    by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · simp only [if_pos hcond]
      obtain ⟨hc, hh, hle⟩ := hw
      show WellFormed { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }
      simp only [WellFormed]
      exact ⟨hc, Nat.mod_lt _ hc, by omega⟩
    · simp only [if_neg hcond]
      exact hw

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact hc
    · exfalso
      have heq : step s (Op.enqueue x) = (.rejected, s) := by unfold step; simp [hc]
      rw [heq] at h
      simp at h
  have : slot s s.count = (s.head + s.count) % s.capacity := by simp [slot]
  show step s (Op.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 })
  unfold step
  simp [hcond, this]

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · exact hc
    · exfalso
      have heq : step s Op.dequeue = (.rejected, s) := by unfold step; simp [hc]
      rw [heq] at h
      simp at h
  show step s Op.dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
  unfold step
  simp [hcond]

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x h
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · exact hc
    · exfalso
      have heq : step s (Op.enqueue x) = (.rejected, s) := by unfold step; simp [hc]
      rw [heq] at h
      simp at h
  have hlt : s.count < s.capacity := hcond.2.2
  have hheadLt : s.head < s.capacity := hcond.2.1
  have hstep : step s (Op.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
    unfold step; simp [hcond]
  rw [hstep]
  simp only [contents, slot]
  have hrange : List.range (s.count + 1) = List.range s.count ++ [s.count] := by
    simp [List.range_succ]
  have key : List.map (fun i => (fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + i) % s.capacity)) (List.range (s.count + 1)) =
      List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count) ++ [x] := by
    rw [hrange, List.map_append]
    have hmap_eq : List.map (fun i => (fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + i) % s.capacity)) (List.range s.count) =
        List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count) := by
      apply List.map_congr_left
      intro i hi
      have hi_lt : i < s.count := List.mem_range.mp hi
      have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity :=
        mod_ne_aux hheadLt hlt hi_lt
      simp [hne]
    have hlast : List.map (fun i => (fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + i) % s.capacity)) [s.count] = [x] := by
      simp
    rw [hmap_eq, hlast]
  exact key

theorem req_dequeue_contents : DequeueContents step := by
  intro s h
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · exact hc
    · exfalso
      have heq : step s Op.dequeue = (.rejected, s) := by unfold step; simp [hc]
      rw [heq] at h
      simp at h
  have hne : (step s Op.dequeue).1 ≠ .rejected := h
  have hstep_eq : step s Op.dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) :=
    req_dequeue_effects (s:=s) hne
  refine ⟨s.buf s.head, ?_, ?_⟩
  · rw [hstep_eq]
  · show contents s = s.buf s.head :: contents (step s Op.dequeue).2
    rw [hstep_eq]
    simp only [contents, slot]
    have hhead_lt : s.head < s.capacity := hcond.2.1
    have h0 : (s.head + 0) % s.capacity = s.head := Nat.mod_eq_of_lt hhead_lt
    have h_range : List.range s.count = 0 :: List.map (· + 1) (List.range (s.count - 1)) := by
      have h1 : s.count = s.count - 1 + 1 := by omega
      suffices hh : ∀ n, List.range (n + 1) = 0 :: List.map (· + 1) (List.range n) from by
        have := hh (s.count - 1)
        rwa [← h1] at this
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by simp [List.range_succ]
          _ = (0 :: List.map (· + 1) (List.range n)) ++ [n + 1] := by rw [ih]
          _ = 0 :: (List.map (· + 1) (List.range n) ++ [n + 1]) := rfl
          _ = 0 :: List.map (· + 1) (List.range n ++ [n]) := by simp
          _ = 0 :: List.map (· + 1) (List.range (n + 1)) := by rw [← List.range_succ]
    rw [h_range]
    simp only [List.map_cons, h0]
    congr 1
    have h_tail : List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.map (· + 1) (List.range (s.count - 1))) =
        List.map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) (List.range (s.count - 1)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp]
      have hi_lt_cap : i < s.capacity := by have := List.mem_range.mp hi; omega
      have hi_mod : i % s.capacity = i := Nat.mod_eq_of_lt hi_lt_cap
      have h1 : (s.head + 1 + i) % s.capacity = ((s.head + 1) % s.capacity + i % s.capacity) % s.capacity := Nat.add_mod _ _ _
      rw [hi_mod] at h1
      have h2 : (s.head + (i + 1)) % s.capacity = (s.head + 1 + i) % s.capacity := by congr 1; omega
      rw [h2, h1.symm]
    rw [h_tail]

theorem step_contents_fifo_aux (s : State) (op : Op) :
    contents s ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
  cases op with
  | enqueue x =>
    by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · have hne : (step s (Op.enqueue x)).1 ≠ .rejected := by unfold step; simp [hcond]
      have heq := req_enqueue_contents (s:=s) (x:=x) hne
      have hout : (step s (Op.enqueue x)).1 = .ok := by unfold step; simp [hcond]
      have hin : inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = [x] := by simp [inflowOf, hout]
      have hout2 : outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = ([] : List Nat) := by simp [outflowOf, hout]
      calc contents s ++ inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1)
          = contents s ++ [x] := by rw [hin]
        _ = ([] : List Nat) ++ (contents s ++ [x]) := by rw [List.nil_append]
        _ = outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) ++ contents (step s (Op.enqueue x)).2 := by rw [hout2, heq]
    · have heq : step s (Op.enqueue x) = (.rejected, s) := by unfold step; simp [hcond]
      have hout : (step s (Op.enqueue x)).1 = .rejected := by rw [heq]
      have hin : inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = ([] : List Nat) := by simp [inflowOf, hout]
      have hout2 : outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) = ([] : List Nat) := by simp [outflowOf, hout]
      have hsnd : (step s (Op.enqueue x)).2 = s := by rw [heq]
      calc contents s ++ inflowOf (Op.enqueue x, (step s (Op.enqueue x)).1)
          = contents s ++ [] := by rw [hin]
        _ = ([] : List Nat) ++ contents s := by rw [List.nil_append, List.append_nil]
        _ = outflowOf (Op.enqueue x, (step s (Op.enqueue x)).1) ++ contents (step s (Op.enqueue x)).2 := by rw [hout2, hsnd]
  | dequeue =>
    by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · have hne : (step s Op.dequeue).1 ≠ .rejected := by unfold step; simp [hcond]
      obtain ⟨y, hy1, hy2⟩ := req_dequeue_contents (s:=s) hne
      have hin : inflowOf (Op.dequeue, (step s Op.dequeue).1) = ([] : List Nat) := by simp [inflowOf, hy1]
      have hout : outflowOf (Op.dequeue, (step s Op.dequeue).1) = [y] := by simp [outflowOf, hy1]
      calc contents s ++ inflowOf (Op.dequeue, (step s Op.dequeue).1)
          = contents s ++ [] := by rw [hin]
        _ = contents s := by rw [List.append_nil]
        _ = y :: contents (step s Op.dequeue).2 := hy2
        _ = [y] ++ contents (step s Op.dequeue).2 := rfl
        _ = outflowOf (Op.dequeue, (step s Op.dequeue).1) ++ contents (step s Op.dequeue).2 := by rw [hout]
    · have heq : step s Op.dequeue = (.rejected, s) := by unfold step; simp [hcond]
      have hout : (step s Op.dequeue).1 = .rejected := by rw [heq]
      have hin : inflowOf (Op.dequeue, (step s Op.dequeue).1) = ([] : List Nat) := by simp [inflowOf, hout]
      have hout2 : outflowOf (Op.dequeue, (step s Op.dequeue).1) = ([] : List Nat) := by simp [outflowOf, hout]
      have hsnd : (step s Op.dequeue).2 = s := by rw [heq]
      calc contents s ++ inflowOf (Op.dequeue, (step s Op.dequeue).1)
          = contents s ++ [] := by rw [hin]
        _ = ([] : List Nat) ++ contents s := by rw [List.nil_append, List.append_nil]
        _ = outflowOf (Op.dequeue, (step s Op.dequeue).1) ++ contents (step s Op.dequeue).2 := by rw [hout2, hsnd]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have h1 : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) =
              inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      simp [inflow, List.flatMap_cons]
    have h2 : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) =
              outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      simp [outflow, List.flatMap_cons]
    have hstep := step_contents_fifo_aux s op
    have ih_eq := ih (s := (step s op).2)
    show contents s ++ inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) =
         outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) ++ contents (run step (step s op).2 ops).2
    rw [h1, h2]
    calc contents s ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (contents s ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ contents (step s op).2) ++ inflow (run step (step s op).2 ops).1 := by rw [hstep]
      _ = outflowOf (op, (step s op).1) ++ (contents (step s op).2 ++ inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ contents (run step (step s op).2 ops).2) := by rw [ih_eq]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ contents (run step (step s op).2 ops).2 := by rw [List.append_assoc]

end RingBuffer
