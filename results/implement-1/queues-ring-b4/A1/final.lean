import RingBuffer.Spec

namespace RingBuffer

def step : Impl
  | s, .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity then
      (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 })
    else
      (.rejected, s)
  | s, .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else
      (.rejected, s)

theorem deqSlotShiftLem (head cap i : Nat) :
    ((((head + 1) % cap) + i) % cap) = ((head + (i + 1)) % cap) := by
  have h : ((((head + 1) % cap) + i) % cap) = (((head + 1) + i) % cap) :=
    Nat.mod_add_mod (head + 1) cap i
  rw [h]
  congr 1
  omega

theorem mod_add_cap (cap t : Nat) : (cap + t) % cap = t % cap := by
  have h := Nat.mod_add_mod cap cap t
  have h0 : cap % cap = 0 := Nat.mod_self cap
  rw [h0] at h
  have h1 : (0 + t) % cap = t % cap := by simp
  rw [h1] at h
  exact h.symm

theorem mod_eq_sub_of_ge (cap k d : Nat) (_hcap : 0 < cap) (_hk : k < cap) (_hd : d < cap)
    (hge : cap ≤ k + d) : (k + d) % cap = k + d - cap := by
  have h1 : cap + (k + d - cap) = k + d := by omega
  have h2 : k + d - cap < cap := by omega
  calc (k + d) % cap = (cap + (k + d - cap)) % cap := by rw [h1]
    _ = (k + d - cap) % cap := mod_add_cap cap (k + d - cap)
    _ = k + d - cap := Nat.mod_eq_of_lt h2

theorem mod_add_ne_self (cap k d : Nat) (hcap : 0 < cap) (hk : k < cap)
    (h0 : 0 < d) (hd : d < cap) : (k + d) % cap ≠ k := by
  by_cases hge : cap ≤ k + d
  · rw [mod_eq_sub_of_ge cap k d hcap hk hd hge]
    omega
  · have hlt : k + d < cap := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

theorem slot_ne_of_lt (head cap count i : Nat) (hcap : 0 < cap)
    (_hhead : head < cap) (hcount : count < cap) (hi : i < count) :
    (head + i) % cap ≠ (head + count) % cap := by
  intro heq
  have hk : (head + i) % cap < cap := Nat.mod_lt _ hcap
  have hd0 : 0 < count - i := by omega
  have hdlt : count - i < cap := by omega
  have h_eq : (head + i) + (count - i) = head + count := by omega
  have hbase := Nat.mod_add_mod (head + i) cap (count - i)
  rw [h_eq] at hbase
  have heq2 : (((head + i) % cap) + (count - i)) % cap = (head + i) % cap := by
    rw [hbase]
    rw [heq]
  exact mod_add_ne_self cap ((head + i) % cap) (count - i) hcap hk hd0 hdlt heq2

theorem range_succ_eq (n : Nat) : List.range (n + 1) = List.range n ++ [n] :=
  List.range_succ

theorem map_eq_of_mem_eq (f g : Nat → Nat) (l : List Nat)
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : f hd = g hd := h hd (by simp)
    have htl : ∀ x ∈ tl, f x = g x := fun x hx => h x (by simp [hx])
    have iht := ih htl
    simp [hhd, iht]

theorem map_range_cons (f : Nat → Nat) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  induction n generalizing f with
  | zero =>
    rw [range_succ_eq 0]
    simp
  | succ n ih =>
    rw [range_succ_eq (n + 1)]
    rw [List.map_append]
    rw [ih f]
    simp only [List.cons_append]
    congr 1
    rw [range_succ_eq n, List.map_append]
    simp

theorem enqueue_contents_aux (s : State) (x : Nat)
    (hcap : 0 < s.capacity) (hhead : s.head < s.capacity)
    (_hle : s.count ≤ s.capacity) (hlt : s.count < s.capacity) :
    contents (State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1)) = contents s ++ [x] := by
  have hshow : contents (State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1))
    = ((List.range (s.count + 1)).map (fun i => if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity))) := rfl
  have hshow2 : contents s
    = ((List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity))) := rfl
  rw [hshow, hshow2]
  rw [range_succ_eq s.count, List.map_append]
  have hmap : ((List.range s.count).map (fun i => if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)))
    = ((List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity))) := by
    apply map_eq_of_mem_eq
    intro i hi
    have hi_lt : i < s.count := List.mem_range.mp hi
    have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity :=
      slot_ne_of_lt s.head s.capacity s.count i hcap hhead hlt hi_lt
    simp [hne]
  rw [hmap]
  simp

theorem dequeue_contents_aux (s : State)
    (_hcap : 0 < s.capacity) (hhead : s.head < s.capacity)
    (_hle : s.count ≤ s.capacity) (hpos : 0 < s.count) :
    contents s = s.buf s.head :: contents (State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1)) := by
  obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
  have hshow : contents s
    = ((List.range (n + 1)).map (fun i => s.buf ((s.head + i) % s.capacity))) := by
    simp only [contents, slot, hn]
  have hshow2 : contents (State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1))
    = ((List.range n).map (fun i => s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity))) := by
    simp only [contents, slot, hn, Nat.add_sub_cancel]
  rw [hshow, hshow2]
  rw [map_range_cons]
  have hf0 : s.buf ((s.head + 0) % s.capacity) = s.buf s.head := by
    have h1 : s.head + 0 = s.head := by omega
    have h2 : s.head % s.capacity = s.head := Nat.mod_eq_of_lt hhead
    rw [h1, h2]
  have htail : (List.range n).map (fun i => s.buf ((s.head + (i + 1)) % s.capacity))
    = (List.range n).map (fun i => s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity)) := by
    apply map_eq_of_mem_eq
    intro i _
    exact congrArg s.buf (deqSlotShiftLem s.head s.capacity i).symm
  rw [hf0, htail]

theorem single_step_fifo (s : State) (op : Op) :
    contents s ++ inflowOf (op, (step s op).1)
      = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
  cases op with
  | enqueue x =>
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity)
    · have e1 : (step s (.enqueue x)).1 = Outcome.ok := by
        unfold step
        simp [hc]
      have e2 : (step s (.enqueue x)).2 =
        State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1) := by
        unfold step
        simp [hc]
      have hin : inflowOf (Op.enqueue x, Outcome.ok) = [x] := rfl
      have hout : outflowOf (Op.enqueue x, Outcome.ok) = ([] : List Nat) := rfl
      rw [e1, e2, hin, hout, List.nil_append]
      exact (enqueue_contents_aux s x hc.1 hc.2.1 hc.2.2.1 hc.2.2.2).symm
    · have e1 : (step s (.enqueue x)).1 = Outcome.rejected := by
        unfold step
        simp [hc]
      have e2 : (step s (.enqueue x)).2 = s := by
        unfold step
        simp [hc]
      have hin : inflowOf (Op.enqueue x, Outcome.rejected) = ([] : List Nat) := rfl
      have hout : outflowOf (Op.enqueue x, Outcome.rejected) = ([] : List Nat) := rfl
      rw [e1, e2, hin, hout, List.append_nil, List.nil_append]
  | dequeue =>
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · have e1 : (step s .dequeue).1 = Outcome.got (s.buf s.head) := by
        unfold step
        simp [hc]
      have e2 : (step s .dequeue).2 =
        State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1) := by
        unfold step
        simp [hc]
      have hin : inflowOf (Op.dequeue, Outcome.got (s.buf s.head)) = ([] : List Nat) := rfl
      have hout : outflowOf (Op.dequeue, Outcome.got (s.buf s.head)) = [s.buf s.head] := rfl
      rw [e1, e2, hin, hout, List.append_nil]
      exact dequeue_contents_aux s hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    · have e1 : (step s .dequeue).1 = Outcome.rejected := by
        unfold step
        simp [hc]
      have e2 : (step s .dequeue).2 = s := by
        unfold step
        simp [hc]
      have hin : inflowOf (Op.dequeue, Outcome.rejected) = ([] : List Nat) := rfl
      have hout : outflowOf (Op.dequeue, Outcome.rejected) = ([] : List Nat) := rfl
      rw [e1, e2, hin, hout, List.append_nil, List.nil_append]

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    obtain ⟨⟨hcap, hhead, hle⟩, hlt⟩ := h
    have hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity) :=
      ⟨hcap, hhead, hle, hlt⟩
    show (step s (Op.enqueue x)).1 ≠ .rejected
    unfold step
    simp [hc]
  | dequeue =>
    simp only [Valid, WellFormed] at h
    obtain ⟨⟨hcap, hhead, hle⟩, hlt⟩ := h
    have hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) :=
      ⟨hcap, hhead, hle, hlt⟩
    show (step s Op.dequeue).1 ≠ .rejected
    unfold step
    simp [hc]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    have hc : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity) := by
      intro hc
      apply h
      obtain ⟨hcap, hhead, hle, hlt⟩ := hc
      exact ⟨⟨hcap, hhead, hle⟩, hlt⟩
    show step s (Op.enqueue x) = _
    unfold step
    simp [hc]
  | dequeue =>
    simp only [Valid, WellFormed] at h
    have hc : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hc
      apply h
      obtain ⟨hcap, hhead, hle, hlt⟩ := hc
      exact ⟨⟨hcap, hhead, hle⟩, hlt⟩
    show step s Op.dequeue = _
    unfold step
    simp [hc]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hWf
  obtain ⟨hcap, hhead, hle⟩ := hWf
  cases op with
  | enqueue x =>
    show WellFormed (step s (Op.enqueue x)).2
    unfold step
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity)
    · simp only [hc]
      exact ⟨hcap, hhead, Nat.succ_le_of_lt hc.2.2.2⟩
    · simp only [hc]
      exact ⟨hcap, hhead, hle⟩
  | dequeue =>
    show WellFormed (step s Op.dequeue).2
    unfold step
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · simp only [hc]
      refine ⟨hcap, Nat.mod_lt _ hcap, Nat.le_trans (Nat.pred_le _) hle⟩
    · simp only [hc]
      exact ⟨hcap, hhead, hle⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  simp only at h ⊢
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity)
  · simp [hc]
  · simp [hc] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  unfold step at h ⊢
  simp only at h ⊢
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · simp [hc]
  · simp [hc] at h

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  have heff := req_enqueue_effects s x hne
  have h2 : (step s (.enqueue x)).2
    = State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1) :=
    congrArg Prod.snd heff
  rw [h2]
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity)
  · exact enqueue_contents_aux s x hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · exfalso
    apply hne
    have hneg : (step s (.enqueue x)).1 = Outcome.rejected := by
      unfold step
      simp [hc]
    rw [hneg]

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  have heff := req_dequeue_effects s hne
  have hfst : (step s .dequeue).1 = Outcome.got (s.buf s.head) := congrArg Prod.fst heff
  refine ⟨s.buf s.head, hfst, ?_⟩
  have h2 : (step s .dequeue).2
      = State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1) :=
    congrArg Prod.snd heff
  rw [h2]
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · exact dequeue_contents_aux s hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · exfalso
    apply hne
    have hneg : (step s .dequeue).1 = Outcome.rejected := by
      unfold step
      simp [hc]
    rw [hneg]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hsingle := single_step_fifo s op
    have hih := ih (step s op).2
    have h1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
      simp only [run]
    have h2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
      simp only [run]
    have hin : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
      = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      simp only [inflow, List.flatMap_cons]
    have hout : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
      = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      simp only [outflow, List.flatMap_cons]
    rw [h1, h2, hin, hout, ← List.append_assoc, hsingle, List.append_assoc, hih, ← List.append_assoc]

end RingBuffer
