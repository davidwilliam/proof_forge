import RingBuffer.Spec
namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 })
    else (.rejected, s)
  | .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    obtain ⟨⟨hcap, hhead, _⟩, hlt⟩ := h
    simp [step, hcap, hhead, hlt]
  | dequeue =>
    obtain ⟨⟨hcap, hhead, hle⟩, hpos⟩ := h
    simp [step, hcap, hhead, hle, hpos]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [step]
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · exfalso; apply h; exact ⟨⟨hc.1, hc.2.1, Nat.le_of_lt hc.2.2⟩, hc.2.2⟩
    · simp [hc]
  | dequeue =>
    simp only [step]
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · exfalso; apply h; exact ⟨⟨hc.1, hc.2.1, hc.2.2.1⟩, hc.2.2.2⟩
    · simp [hc]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hwf
  obtain ⟨hcap, hhead, hle⟩ := hwf
  cases op with
  | enqueue x =>
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · have h2 : (step s (.enqueue x)).2 = { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } := by simp [step, hc]
      rw [h2]
      unfold WellFormed; simp; omega
    · have h2 : (step s (.enqueue x)).2 = s := by simp [step, hc]
      rw [h2]; exact ⟨hcap, hhead, hle⟩
  | dequeue =>
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · have h2 : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by simp [step, hc]
      rw [h2]
      unfold WellFormed; simp; exact ⟨hcap, Nat.mod_lt _ hcap, by omega⟩
    · have h2 : (step s .dequeue).2 = s := by simp [step, hc]
      rw [h2]; exact ⟨hcap, hhead, hle⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  simp only [step] at h ⊢
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · simp [hc]
  · simp [hc] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  simp only [step] at h ⊢
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · simp [hc]
  · simp [hc] at h

theorem mod_two_lt {a n : Nat} (ha : a < 2 * n) :
    0 < n → a % n = if a < n then a else a - n := by
  intro hn
  by_cases ha1 : a < n
  · simp [ha1, Nat.mod_eq_of_lt ha1]
  · have hle : n ≤ a := Nat.le_of_not_lt ha1
    have ha2 : a - n < n := by omega
    have h1 : (a - n) % n = a - n := Nat.mod_eq_of_lt ha2
    have h2 : a % n = (a - n) % n := Nat.mod_eq_sub_mod hle
    simp [ha1, h1, h2]

theorem slot_ne_of_lt {s : State} (hcap : 0 < s.capacity) (hhead : s.head < s.capacity)
    (hlt : s.count < s.capacity) {i : Nat} (hi : i < s.count) :
    (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := by
  intro heq
  have ha1 : s.head + i < 2 * s.capacity := by omega
  have ha2 : s.head + s.count < 2 * s.capacity := by omega
  have e1 := mod_two_lt ha1 hcap
  have e2 := mod_two_lt ha2 hcap
  rw [e1, e2] at heq
  by_cases hi1 : s.head + i < s.capacity <;> by_cases hc1 : s.head + s.count < s.capacity <;> simp [hi1, hc1] at heq <;> omega

theorem range_succ_map (k : Nat) : List.range (k + 1) = 0 :: List.map (· + 1) (List.range k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc List.range (k + 2) = List.range (k + 1) ++ [k+1] := by simp [List.range_succ]
      _ = (0 :: List.map (·+1) (List.range k)) ++ [k+1] := by rw [ih]
      _ = 0 :: (List.map (·+1) (List.range k) ++ [k+1]) := by simp
      _ = 0 :: List.map (·+1) (List.range (k+1)) := by simp [List.range_succ]

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x h
  have heff := req_enqueue_effects (s:=s) (x:=x) h
  simp only [step] at h
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · simp [hc] at h heff
    have hcap := hc.1
    have hhead := hc.2.1
    have hlt := hc.2.2
    have heff_snd : (step s (.enqueue x)).2 = { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } := by
      have : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := heff
      simp [this]
    have hcont_s' : contents { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } = contents s ++ [x] := by
      unfold contents slot
      simp only [List.range_succ, List.map_append, List.map_singleton]
      have hmap_eq : List.map (fun i => if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)) (List.range s.count) = List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count) := by
        apply List.map_congr_left
        intro i hi
        have hi' : i < s.count := List.mem_range.mp hi
        have hne := slot_ne_of_lt hcap hhead hlt hi'
        simp [hne]
      rw [hmap_eq]; simp
    rw [← heff_snd] at hcont_s'
    exact hcont_s'
  · simp [hc] at h

theorem req_dequeue_contents : DequeueContents step := by
  intro s h
  have heff := req_dequeue_effects (s:=s) h
  simp only [step] at h
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · simp [hc] at h heff
    obtain ⟨k, hk⟩ : ∃ k, s.count = k + 1 := ⟨s.count - 1, by omega⟩
    have hk1 : k + 1 - 1 = k := by omega
    have heff' : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := k }) := by
      have h1 : { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } = { s with head := (s.head + 1) % s.capacity, count := k } := by rw [hk, hk1]
      rw [heff, h1]
    have heff2 : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := k } := by simp [heff']
    have hk_lt_cap : k < s.capacity := by omega
    have hcont_eq : contents s = s.buf s.head :: contents (step s .dequeue).2 := by
      have hrw : contents (step s .dequeue).2 = contents { capacity := s.capacity, buf := s.buf, head := (s.head + 1) % s.capacity, count := k } := by rw [← heff2]
      rw [hrw]
      have hcount_eq : s.count = k + 1 := hk
      have lhs_eq : contents s = s.buf s.head :: List.map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) (List.range k) := by
        unfold contents slot
        have hr : List.range s.count = List.range (k+1) := by rw [hcount_eq]
        rw [hr, range_succ_map]
        simp [List.map_cons]
        simp [Nat.mod_eq_of_lt hc.2.1]
      have rhs_eq : contents { capacity := s.capacity, buf := s.buf, head := (s.head + 1) % s.capacity, count := k } = List.map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) (List.range k) := by
        unfold contents slot
        rfl
      rw [lhs_eq, rhs_eq]
      congr 1
      have hmap : List.map (fun i => s.buf (((s.head + 1) % s.capacity + i) % s.capacity)) (List.range k) = List.map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) (List.range k) := by
        apply List.map_congr_left
        intro i hi
        have hi_lt_k : i < k := List.mem_range.mp hi
        have hik2 : i < s.capacity := Nat.lt_of_lt_of_le hi_lt_k (Nat.le_of_lt hk_lt_cap)
        have himod : i % s.capacity = i := Nat.mod_eq_of_lt hik2
        congr 1
        have h1 : ((s.head + 1) % s.capacity + i) % s.capacity = ((s.head + 1) % s.capacity + i % s.capacity) % s.capacity := by rw [himod]
        have h2 : ((s.head + 1) % s.capacity + i % s.capacity) % s.capacity = (s.head + 1 + i) % s.capacity := by rw [← Nat.add_mod]
        have h3 : (s.head + 1 + i) % s.capacity = (s.head + (i + 1)) % s.capacity := by congr 1; omega
        exact h1.trans (h2.trans h3)
      exact hmap.symm
    exact ⟨s.buf s.head, by simp [heff'], hcont_eq⟩
  · simp [hc] at h

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | enqueue x =>
      by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
      · have hsucc : (step s (.enqueue x)).1 ≠ .rejected := by simp [step, hc]
        have hcont := req_enqueue_contents (s:=s) (x:=x) hsucc
        have heff := req_enqueue_effects (s:=s) (x:=x) hsucc
        have hrun : run step s (.enqueue x :: ops) = ((.enqueue x, (step s (.enqueue x)).1) :: (run step (step s (.enqueue x)).2 ops).1, (run step (step s (.enqueue x)).2 ops).2) := by simp [run]
        have hin : inflowOf (.enqueue x, (step s (.enqueue x)).1) = [x] := by simp [heff, inflowOf]
        have hout : outflowOf (.enqueue x, (step s (.enqueue x)).1) = ([] : List Nat) := by simp [heff, outflowOf]
        have hih := ih (step s (.enqueue x)).2
        have lhs : contents s ++ inflow (run step s (.enqueue x :: ops)).1 = contents s ++ ([x] ++ inflow (run step (step s (.enqueue x)).2 ops).1) := by simp [hrun, inflow, List.flatMap_cons, hin]
        have rhs : outflow (run step s (.enqueue x :: ops)).1 ++ contents (run step s (.enqueue x :: ops)).2 = outflow (run step (step s (.enqueue x)).2 ops).1 ++ contents (run step (step s (.enqueue x)).2 ops).2 := by simp [hrun, outflow, List.flatMap_cons, hout]
        rw [lhs, rhs]
        calc contents s ++ ([x] ++ inflow (run step (step s (.enqueue x)).2 ops).1)
            = (contents s ++ [x]) ++ inflow (run step (step s (.enqueue x)).2 ops).1 := by rw [List.append_assoc]
          _ = contents (step s (.enqueue x)).2 ++ inflow (run step (step s (.enqueue x)).2 ops).1 := by rw [hcont]
          _ = outflow (run step (step s (.enqueue x)).2 ops).1 ++ contents (run step (step s (.enqueue x)).2 ops).2 := hih
      · have hrej : (step s (.enqueue x)).1 = .rejected := by simp [step, hc]
        have hst : (step s (.enqueue x)).2 = s := by simp [step, hc]
        have hrun : run step s (.enqueue x :: ops) = ((.enqueue x, (step s (.enqueue x)).1) :: (run step (step s (.enqueue x)).2 ops).1, (run step (step s (.enqueue x)).2 ops).2) := by simp [run]
        have hin : inflowOf (.enqueue x, (step s (.enqueue x)).1) = ([] : List Nat) := by simp [hrej, inflowOf]
        have hout : outflowOf (.enqueue x, (step s (.enqueue x)).1) = ([] : List Nat) := by simp [hrej, outflowOf]
        have lhs : contents s ++ inflow (run step s (.enqueue x :: ops)).1 = contents s ++ inflow (run step s ops).1 := by simp [hrun, hst, inflow, List.flatMap_cons, hin]
        have rhs : outflow (run step s (.enqueue x :: ops)).1 ++ contents (run step s (.enqueue x :: ops)).2 = outflow (run step s ops).1 ++ contents (run step s ops).2 := by simp [hrun, hst, outflow, List.flatMap_cons, hout]
        rw [lhs, rhs]
        exact ih s
    | dequeue =>
      by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
      · have hsucc : (step s .dequeue).1 ≠ .rejected := by simp [step, hc]
        have hdeq := req_dequeue_contents (s:=s) hsucc
        obtain ⟨y, hyout, hycont⟩ := hdeq
        have hrun : run step s (.dequeue :: ops) = ((.dequeue, (step s .dequeue).1) :: (run step (step s .dequeue).2 ops).1, (run step (step s .dequeue).2 ops).2) := by simp [run]
        have hin : inflowOf (.dequeue, (step s .dequeue).1) = ([] : List Nat) := by simp [inflowOf]
        have hout : outflowOf (.dequeue, (step s .dequeue).1) = [y] := by simp [hyout, outflowOf]
        have hih := ih (step s .dequeue).2
        have lhs : contents s ++ inflow (run step s (.dequeue :: ops)).1 = contents s ++ inflow (run step (step s .dequeue).2 ops).1 := by simp [hrun, inflow, List.flatMap_cons, hin]
        have rhs : outflow (run step s (.dequeue :: ops)).1 ++ contents (run step s (.dequeue :: ops)).2 = (y :: outflow (run step (step s .dequeue).2 ops).1) ++ contents (run step (step s .dequeue).2 ops).2 := by simp [hrun, outflow, List.flatMap_cons, hout]
        rw [lhs, rhs]
        calc contents s ++ inflow (run step (step s .dequeue).2 ops).1
            = (y :: contents (step s .dequeue).2) ++ inflow (run step (step s .dequeue).2 ops).1 := by rw [hycont]
          _ = y :: (contents (step s .dequeue).2 ++ inflow (run step (step s .dequeue).2 ops).1) := by simp
          _ = y :: (outflow (run step (step s .dequeue).2 ops).1 ++ contents (run step (step s .dequeue).2 ops).2) := by rw [hih]
          _ = (y :: outflow (run step (step s .dequeue).2 ops).1) ++ contents (run step (step s .dequeue).2 ops).2 := by simp
      · have hrej : (step s .dequeue).1 = .rejected := by simp [step, hc]
        have hst : (step s .dequeue).2 = s := by simp [step, hc]
        have hrun : run step s (.dequeue :: ops) = ((.dequeue, (step s .dequeue).1) :: (run step (step s .dequeue).2 ops).1, (run step (step s .dequeue).2 ops).2) := by simp [run]
        have hin : inflowOf (.dequeue, (step s .dequeue).1) = ([] : List Nat) := by simp [inflowOf]
        have hout : outflowOf (.dequeue, (step s .dequeue).1) = ([] : List Nat) := by simp [hrej, outflowOf]
        have lhs : contents s ++ inflow (run step s (.dequeue :: ops)).1 = contents s ++ inflow (run step s ops).1 := by simp [hrun, hst, inflow, List.flatMap_cons, hin]
        have rhs : outflow (run step s (.dequeue :: ops)).1 ++ contents (run step s (.dequeue :: ops)).2 = outflow (run step s ops).1 ++ contents (run step s ops).2 := by simp [hrun, hst, outflow, List.flatMap_cons, hout]
        rw [lhs, rhs]
        exact ih s

end RingBuffer
