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

theorem my_test_thm : 1 = 1 := rfl

theorem my_helper1 : 1 = 1 := rfl

theorem my_helper2 : 2 = 2 := rfl

theorem my_check1 : (∀ (a b n : Nat), (a + b) % n = ((a % n) + (b % n)) % n) := fun a b n => Nat.add_mod a b n

theorem my_probe1 : ∀ (a n : Nat), (a + n) % n = a % n := fun a n => Nat.add_mod_right a n

theorem my_probe3 : True := trivial

theorem my_test_thm2 : 1 = 1 := rfl

theorem helper_slot_zero : ∀ (s : State), s.head < s.capacity → slot s 0 = s.head := by
  intro s h
  unfold slot
  simp [Nat.add_zero, Nat.mod_eq_of_lt h]

theorem helper_check_range_succ : ∀ (n : Nat), List.range (n+1) = List.range n ++ [n] := by
  intro n
  exact List.range_succ

theorem helper_mod_succ_eq : ∀ (h i c : Nat), 0 < c → (h + (i + 1)) % c = (((h + 1) % c) + i) % c := by
  intro h i c hc
  have e1 : h + (i + 1) = (h + 1) + i := by omega
  rw [e1]
  have hmod : ∀ (a b : Nat), (a + b) % c = ((a % c) + (b % c)) % c := fun a b => Nat.add_mod a b c
  rw [hmod ((h+1)) i]
  have hmod2 : (((h + 1) % c) + i) % c = ((((h+1) % c) % c) + (i % c)) % c := by
    have := Nat.add_mod ((h+1)%c) i c
    rw [this]
  rw [hmod2]
  have hmm : ((h + 1) % c) % c = (h + 1) % c := Nat.mod_mod _ _
  rw [hmm]

theorem helper_map_range_cons : ∀ (n : Nat) (f : Nat → Nat),
    ((List.range (n+1)).map f) = f 0 :: ((List.range n).map (fun i => f (i+1))) := by
  intro n
  induction n with
  | zero => intro f; simp
  | succ k ih =>
    intro f
    have h1 : List.range (k + 1 + 1) = List.range (k+1) ++ [k+1] := List.range_succ
    have h2 : List.range (k + 1) = List.range k ++ [k] := List.range_succ
    calc (List.range (k + 1 + 1)).map f
        = (List.range (k+1) ++ [k+1]).map f := by rw [h1]
      _ = (List.range (k+1)).map f ++ [f (k+1)] := by simp
      _ = (f 0 :: (List.range k).map (fun i => f (i+1))) ++ [f (k+1)] := by rw [ih f]
      _ = f 0 :: ((List.range k).map (fun i => f (i+1)) ++ [f (k+1)]) := by simp
      _ = f 0 :: ((List.range (k+1)).map (fun i => f (i+1))) := by
            have h3 : (List.range (k+1)).map (fun i => f (i+1)) = (List.range k).map (fun i => f (i+1)) ++ [f (k+1)] := by
              rw [h2]; simp
            rw [h3]

theorem helper_deq_count_shape : ∀ (s : State), 0 < s.count →
    s.count = (s.count - 1) + 1 := by
  intro s h
  omega

theorem fifo_probe_run (s : State) (op : Op) (ops : List Op) :
  (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
  simp [run]

theorem fifo_probe_inflow (p : Op × Outcome) (t : List (Op × Outcome)) :
  inflow (p :: t) = inflowOf p ++ inflow t := by
  simp [inflow]

theorem fifo_probe_outflow (p : Op × Outcome) (t : List (Op × Outcome)) :
  outflow (p :: t) = outflowOf p ++ outflow t := by
  simp [outflow]

theorem fifo_single_enq_ok (s : State) (x : Nat)
  (heff : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 })) :
  (step s (.enqueue x)).1 = .ok := by
  rw [heff]

theorem probe_exists_a : True := by exact trivial

theorem probe_exists_b : ∀ (n m : Nat), n ≤ m → n ≤ m := by intro n m h; exact h

theorem probe_if_simple (a b : Nat) (h : a < b) : (if a < b then 1 else 0) = 1 := by
  simp [h]

theorem probe_unfold_test : ∀ (s : State), contents s = (List.range s.count).map (fun i => s.buf (slot s i)) := by
  intro s
  rfl

theorem probe_rw_test : ∀ (s : State), 0 < s.count →
    (List.range s.count).map (fun i => s.buf (slot s i)) = s.buf (slot s 0) :: ((List.range (s.count - 1)).map (fun i => s.buf (slot s (i+1)))) := by
  intro s hpos
  have hcount_eq : s.count = (s.count - 1) + 1 := by omega
  have h1 := helper_map_range_cons (s.count - 1) (fun i => s.buf (slot s i))
  rw [← hcount_eq] at h1
  exact h1

theorem dequeue_slot_shift : ∀ (s : State) (i : Nat), 0 < s.capacity →
    slot s (i + 1) = slot ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) i := by
  intro s i hc
  unfold slot
  simp only
  exact helper_mod_succ_eq s.head i s.capacity hc

theorem dequeue_contents_RHS : ∀ (s : State), 0 < s.capacity →
    contents ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) = ((List.range (s.count - 1)).map (fun i => s.buf (slot s (i + 1)))) := by
  intro s hc
  have hfun : (fun i => s.buf (slot ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) i)) = (fun i => s.buf (slot s (i + 1))) := by
    apply funext
    intro i
    rw [dequeue_slot_shift s i hc]
  have h1 : contents ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) = ((List.range (s.count - 1)).map (fun i => s.buf (slot ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) i))) := rfl
  rw [h1, hfun]

theorem dequeue_contents_shape : ∀ (s : State), 0 < s.capacity → s.head < s.capacity → 0 < s.count →
    contents s = s.buf s.head :: contents ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
  intro s hc hh hpos
  have h0 : s.buf (slot s 0) = s.buf s.head := by rw [helper_slot_zero s hh]
  have h2 := probe_rw_test s hpos
  have h3 := dequeue_contents_RHS s hc
  have h4 : contents s = s.buf (slot s 0) :: ((List.range (s.count - 1)).map (fun i => s.buf (slot s (i + 1)))) := h2
  rw [h4, h3] at *
  rw [h0]

theorem fifo_run_cons_fst (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
  simp [run]

theorem fifo_run_cons_snd (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
  simp [run]

theorem fifo_inflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (p :: t) = inflowOf p ++ inflow t := by
  simp [inflow]

theorem fifo_outflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (p :: t) = outflowOf p ++ outflow t := by
  simp [outflow]

theorem fifo_step_lemma2 (s : State) (x : Nat) (h : (step s (.enqueue x)).1 = .rejected)
    (h2 : (step s (.enqueue x)).2 = s) :
    contents s ++ inflowOf ((Op.enqueue x), (step s (Op.enqueue x)).1) =
      outflowOf ((Op.enqueue x), (step s (Op.enqueue x)).1) ++ contents (step s (Op.enqueue x)).2 := by
  rw [h, h2]
  simp [inflowOf, outflowOf]

theorem fifo_test_ref : True := by
  have _ := fifo_step_lemma2
  have _ := fifo_run_cons_fst
  trivial

theorem helper_sub_mod_eq : ∀ (m n : Nat), n ≤ m → m % n = (m - n) % n := by
  intro m n h
  exact Nat.mod_eq_sub_mod h

theorem helper_mod_small_case : ∀ (a c : Nat), 0 < c → a < 2 * c →
    a % c = (if a < c then a else a - c) := by
  intro a c hc hlt
  by_cases h : a < c
  · rw [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h]
    have hge : c ≤ a := by omega
    have h1 : a % c = (a - c) % c := helper_sub_mod_eq a c hge
    have hsmall : a - c < c := by omega
    rw [h1, Nat.mod_eq_of_lt hsmall]

theorem helper_slot_ne_of_lt : ∀ (s : State), 0 < s.capacity → s.head < s.capacity →
    ∀ (i : Nat), i < s.count → s.count < s.capacity →
    slot s i ≠ slot s s.count := by
  intro s hc hh i hi hlt
  unfold slot
  have hi2 : s.head + i < 2 * s.capacity := by omega
  have hn2 : s.head + s.count < 2 * s.capacity := by omega
  have e1 : (s.head + i) % s.capacity = (if s.head + i < s.capacity then s.head + i else (s.head + i) - s.capacity) :=
    helper_mod_small_case (s.head + i) s.capacity hc hi2
  have e2 : (s.head + s.count) % s.capacity = (if s.head + s.count < s.capacity then s.head + s.count else (s.head + s.count) - s.capacity) :=
    helper_mod_small_case (s.head + s.count) s.capacity hc hn2
  rw [e1, e2]
  by_cases h1 : s.head + i < s.capacity <;> by_cases h2 : s.head + s.count < s.capacity <;>
    simp [h1, h2] <;> omega

theorem helper_enq_buf_at : ∀ (s : State) (x : Nat) (i : Nat),
    (fun j => if j = slot s s.count then x else s.buf j) (slot s i)
      = (if slot s i = slot s s.count then x else s.buf (slot s i)) := by
  intro s x i
  rfl

theorem fifo_enq_aux : ∀ (s : State) (x : Nat),
    0 < s.capacity → s.head < s.capacity → s.count < s.capacity →
    contents ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) = contents s ++ [x] := by
  intro s x hc hh hlt
  have hslot : ∀ i, slot ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) i = slot s i := by
    intro i
    unfold slot
    simp only
  have hpt : ∀ i, i ∈ List.range s.count →
      (({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State).buf (slot ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) i))
      = s.buf (slot s i) := by
    intro i hi
    simp only
    rw [hslot i]
    have hi_lt : i < s.count := List.mem_range.mp hi
    have hne : slot s i ≠ slot s s.count := helper_slot_ne_of_lt s hc hh i hi_lt hlt
    simp [hne]
  have hmap : ((List.range s.count).map (fun i => ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State).buf (slot ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) i)))
      = ((List.range s.count).map (fun i => s.buf (slot s i))) := by
    apply List.map_congr_left
    intro i hi
    exact hpt i hi
  have hlast : ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State).buf
      (slot ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) s.count) = x := by
    rw [hslot s.count]
    simp
  have hrange : List.range (s.count + 1) = List.range s.count ++ [s.count] := List.range_succ
  have hcont : contents ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State)
      = ((List.range (s.count + 1)).map (fun i => ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State).buf (slot ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) i))) := rfl
  have hconts : contents s = ((List.range s.count).map (fun i => s.buf (slot s i))) := rfl
  rw [hcont, hrange, List.map_append, List.map_singleton, hlast, hmap, ← hconts]

theorem fifo_step_single : ∀ (s : State) (op : Op),
    contents s ++ inflowOf (op, (step s op).1) =
      outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
  intro s op
  cases op with
  | enqueue x =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · obtain ⟨hc, hh, hlt⟩ := hcond
      have hstep1 : (step s (.enqueue x)).1 = .ok := by simp [step, hc, hh, hlt]
      have hstep2 : (step s (.enqueue x)).2 = ({ s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 } : State) := by
        simp [step, hc, hh, hlt]
      have htail : (s.head + s.count) % s.capacity = slot s s.count := rfl
      have hcon : contents (step s (.enqueue x)).2 = contents s ++ [x] := by
        rw [hstep2, htail]; exact fifo_enq_aux s x hc hh hlt
      have hin : inflowOf ((Op.enqueue x), (step s (Op.enqueue x)).1) = [x] := by
        rw [hstep1]; rfl
      have hout : outflowOf ((Op.enqueue x), (step s (Op.enqueue x)).1) = [] := by
        rw [hstep1]; rfl
      rw [hin, hout, hcon]
      simp
    · have hstep1 : (step s (.enqueue x)).1 = .rejected := by simp [step, hcond]
      have hstep2 : (step s (.enqueue x)).2 = s := by simp [step, hcond]
      have hin : inflowOf ((Op.enqueue x), (step s (Op.enqueue x)).1) = ([] : List Nat) := by
        rw [hstep1]; rfl
      have hout : outflowOf ((Op.enqueue x), (step s (Op.enqueue x)).1) = ([] : List Nat) := by
        rw [hstep1]; rfl
      rw [hin, hout, hstep2]
      simp
  | dequeue =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · obtain ⟨hc, hh, hle, hpos⟩ := hcond
      have hstep1 : (step s .dequeue).1 = .got (s.buf s.head) := by simp [step, hc, hh, hle, hpos]
      have hstep2 : (step s .dequeue).2 = ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) := by
        simp [step, hc, hh, hle, hpos]
      have hshape : contents s = s.buf s.head :: contents (step s .dequeue).2 := by
        rw [hstep2]; exact dequeue_contents_shape s hc hh hpos
      have hin : inflowOf ((Op.dequeue), (step s Op.dequeue).1) = ([] : List Nat) := by
        rw [hstep1]; rfl
      have hout : outflowOf ((Op.dequeue), (step s Op.dequeue).1) = [s.buf s.head] := by
        rw [hstep1]; rfl
      rw [hin, hout, hshape]
      simp
    · have hstep1 : (step s .dequeue).1 = .rejected := by simp [step, hcond]
      have hstep2 : (step s .dequeue).2 = s := by simp [step, hcond]
      have hin : inflowOf ((Op.dequeue), (step s Op.dequeue).1) = ([] : List Nat) := by
        rw [hstep1]; rfl
      have hout : outflowOf ((Op.dequeue), (step s Op.dequeue).1) = ([] : List Nat) := by
        rw [hstep1]; rfl
      rw [hin, hout, hstep2]
      simp

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid, WellFormed] at h
    obtain ⟨⟨hc, hh, hcle⟩, hlt⟩ := h
    simp [step, hc, hh, hlt]
  | dequeue =>
    simp [Valid, WellFormed] at h
    obtain ⟨⟨hc, hh, hcle⟩, hpos⟩ := h
    simp [step, hc, hh, hcle, hpos]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro hc
      apply h
      obtain ⟨h1, h2, h3⟩ := hc
      exact ⟨⟨h1, h2, Nat.le_of_lt h3⟩, h3⟩
    simp [step, hcond]
  | dequeue =>
    simp only [Valid, WellFormed] at h
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hc
      apply h
      obtain ⟨h1, h2, h3, h4⟩ := hc
      exact ⟨⟨h1, h2, h3⟩, h4⟩
    simp [step, hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op h
  cases op with
  | enqueue x =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · have h2 : (step s (.enqueue x)).2 = ({ s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 } : State) := by
        simp [step, if_pos hcond]
      rw [h2]
      obtain ⟨hc, hh, hcc⟩ := h
      obtain ⟨h1,h2,h3⟩ := hcond
      show WellFormed _
      exact ⟨hc, hh, Nat.succ_le_of_lt h3⟩
    · have h2 : (step s (.enqueue x)).2 = s := by simp [step, if_neg hcond]
      rw [h2]
      exact h
  | dequeue =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · have h2 : (step s .dequeue).2 = ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) := by
        simp [step, if_pos hcond]
      rw [h2]
      obtain ⟨hc, hh, hcc⟩ := h
      obtain ⟨h1,h2,h3,h4⟩ := hcond
      show WellFormed _
      refine ⟨hc, Nat.mod_lt _ hc, Nat.le_trans (Nat.sub_le s.count 1) hcc⟩
    · have h2 : (step s .dequeue).2 = s := by simp [step, if_neg hcond]
      rw [h2]
      exact h

theorem req_enqueue_effects  : EnqueueEffects step := by
  intro s x hne
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · exact hc
    · exfalso
      apply hne
      simp [step, hc]
  obtain ⟨h1,h2,h3⟩ := hcond
  have heq : slot s s.count = (s.head + s.count) % s.capacity := rfl
  simp [step, h1, h2, h3, heq]

theorem req_dequeue_effects  : DequeueEffects step := by
  intro s hne
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · exact hc
    · exfalso
      apply hne
      simp [step, hc]
  obtain ⟨h1,h2,h3,h4⟩ := hcond
  simp [step, h1, h2, h3, h4]

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := by
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · exact hc
    · exfalso
      apply hne
      simp [step, hc]
  obtain ⟨hc, hh, hlt⟩ := hcond
  have heff := req_enqueue_effects s x hne
  have h2eq : (step s (.enqueue x)).2 = ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
    rw [heff]
  rw [h2eq]
  exact fifo_enq_aux s x hc hh hlt

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := by
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · exact hc
    · exfalso
      apply hne
      simp [step, hc]
  obtain ⟨hc, hh, hle, hpos⟩ := hcond
  have heff := req_dequeue_effects s hne
  have hshape := dequeue_contents_shape s hc hh hpos
  refine ⟨s.buf s.head, ?_, ?_⟩
  · have hfst : (step s .dequeue).1 = Outcome.got (s.buf s.head) := by rw [heff]
    exact hfst
  · have h2eq : (step s .dequeue).2 = ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by rw [heff]
    rw [h2eq]
    exact hshape

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hsingle := fifo_step_single s op
    have hih := ih (step s op).2
    have hrun1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
      simp [run]
    have hrun2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
      simp [run]
    rw [hrun1, hrun2]
    have hin : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      simp [inflow]
    have hout : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      simp [outflow]
    rw [hin, hout]
    -- contents s ++ (in ++ rest) = (out ++ restOut) ++ final
    calc contents s ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (contents s ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by
            rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ contents (step s op).2) ++ inflow (run step (step s op).2 ops).1 := by
            rw [hsingle]
      _ = outflowOf (op, (step s op).1) ++ (contents (step s op).2 ++ inflow (run step (step s op).2 ops).1) := by
            rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ contents (run step (step s op).2 ops).2) := by
            rw [hih]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ contents (run step (step s op).2 ops).2 := by
            rw [List.append_assoc]

end RingBuffer
