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

theorem foo : True := trivial

theorem test_probe1 : True := by
  have h1 := Nat.div_add_mod (5 : Nat) (3 : Nat)
  trivial

theorem test_probe2 : True := by
  have h1 : ∀ (a n : Nat), a < n → a % n = a := fun a n h => Nat.mod_eq_of_lt h
  trivial

theorem test_probe3 : True := by
  have h1 := @Nat.mod_eq_of_lt
  have h2 := @Nat.mod_lt
  have h3 := @Nat.div_add_mod
  trivial

theorem probe_add_mod : ∀ (a b n : Nat), (a + b) % n = ((a % n) + (b % n)) % n := fun a b n => Nat.add_mod a b n

theorem probe_lemmas : True := by
  have h1 := @Nat.zero_mod
  have h2 := @Nat.mod_self
  have h3 := @Nat.le_of_dvd
  have h4 := @Nat.mul_sub
  have h5 := @Nat.sub_add_cancel
  have h6 := @Nat.div_le_div_right
  trivial

theorem probe_mod_lemmas : True := by
  have h1 := @Nat.add_mod
  have h2 := @Nat.mod_mod
  have h3 := @Nat.add_mod_mod
  have h4 := @Nat.mod_add_mod
  trivial
#check @Nat.add_mod
#check @List.range_succ
#check @List.range_zero

theorem probe2 : (List.range 3 = [0,1,2]) := rfl

theorem probe_check1 : True := by
  have h1 : ∀ (m k n : Nat), (m % k + n) % k = (m + n) % k := @Nat.mod_add_mod
  trivial

theorem rb_map_congr_aux : ∀ (l : List Nat) (g h : Nat → Nat), (∀ i ∈ l, g i = h i) → l.map g = l.map h := by
  intro l g h hmem
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons]
    have ha : g a = h a := hmem a (by simp)
    have ht : t.map g = t.map h := by
      apply ih
      intro i hi
      exact hmem i (by simp [hi])
    rw [ha, ht]

theorem probe_range_eq : ∀ (n : Nat), List.range (n + 1) = List.range n ++ [n] := @List.range_succ

theorem fifo_single_of_assumed
    (hEC : EnqueueContents step) (hDC : DequeueContents step)
    (hEE : EnqueueEffects step) (hDE : DequeueEffects step) :
    ∀ s op, contents s ++ inflow [(op, (step s op).1)]
      = outflow [(op, (step s op).1)] ++ contents (step s op).2 := by
  intro s op
  cases op with
  | enqueue x =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · have hne : (step s (.enqueue x)).1 ≠ .rejected := by
        unfold step
        simp [hcond]
      have hEE' := hEE s x hne
      have hEC' := hEC s x hne
      have hout : (step s (.enqueue x)).1 = .ok := by rw [hEE']
      simp [inflow, outflow, inflowOf, outflowOf, hout, hEC']
    · have hstep : step s (.enqueue x) = (.rejected, s) := by unfold step; simp [hcond]
      simp [inflow, outflow, inflowOf, outflowOf, hstep]
  | dequeue =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · have hne : (step s .dequeue).1 ≠ .rejected := by unfold step; simp [hcond]
      have hDE' := hDE s hne
      obtain ⟨x, hxout, hxcont⟩ := hDC s hne
      have hout : (step s .dequeue).1 = .got x := hxout
      simp [inflow, outflow, inflowOf, outflowOf, hout, hxcont]
    · have hstep : step s .dequeue = (.rejected, s) := by unfold step; simp [hcond]
      simp [inflow, outflow, inflowOf, outflowOf, hstep]

theorem inflow_cons (a : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (a :: t) = inflowOf a ++ inflow t := by
  simp [inflow]

theorem outflow_cons (a : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (a :: t) = outflowOf a ++ outflow t := by
  simp [outflow]

theorem inflow_singleton (a : Op × Outcome) :
    inflow [a] = inflowOf a := by
  simp [inflow]

theorem outflow_singleton (a : Op × Outcome) :
    outflow [a] = outflowOf a := by
  simp [outflow]

theorem fifo_induct_helper
    (hsingle : ∀ s op, contents s ++ inflow [(op, (step s op).1)]
      = outflow [(op, (step s op).1)] ++ contents (step s op).2) :
    Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    unfold run inflow outflow
    simp
  | cons op rest ih =>
    have h1 := hsingle s op
    have h2 := ih (step s op).2
    have heq1 : (run step s (op :: rest)).1
        = (op, (step s op).1) :: (run step (step s op).2 rest).1 := rfl
    have heq2 : (run step s (op :: rest)).2
        = (run step (step s op).2 rest).2 := rfl
    rw [heq1, heq2]
    have hinf : inflow ((op, (step s op).1) :: (run step (step s op).2 rest).1)
      = inflow [(op, (step s op).1)] ++ inflow (run step (step s op).2 rest).1 := by
      simp [inflow]
    have hout : outflow ((op, (step s op).1) :: (run step (step s op).2 rest).1)
      = outflow [(op, (step s op).1)] ++ outflow (run step (step s op).2 rest).1 := by
      simp [outflow]
    rw [hinf, hout]
    calc contents s ++ (inflow [(op, (step s op).1)] ++ inflow (run step (step s op).2 rest).1)
        = (contents s ++ inflow [(op, (step s op).1)]) ++ inflow (run step (step s op).2 rest).1 := by rw [List.append_assoc]
      _ = (outflow [(op, (step s op).1)] ++ contents (step s op).2) ++ inflow (run step (step s op).2 rest).1 := by rw [h1]
      _ = outflow [(op, (step s op).1)] ++ (contents (step s op).2 ++ inflow (run step (step s op).2 rest).1) := by rw [List.append_assoc]
      _ = outflow [(op, (step s op).1)] ++ (outflow (run step (step s op).2 rest).1 ++ contents (run step (step s op).2 rest).2) := by rw [h2]
      _ = (outflow [(op, (step s op).1)] ++ outflow (run step (step s op).2 rest).1) ++ contents (run step (step s op).2 rest).2 := by rw [List.append_assoc]

theorem probe_mod_left_aux : ∀ (a b : Nat), (a + b) % a = b % a := fun a b => Nat.add_mod_left a b

theorem probe_mod_right_aux : ∀ (a b : Nat), (a + b) % b = a % b := fun a b => Nat.add_mod_right a b

theorem probe_omega_test : ∀ (a b : Nat), a < b → a < b + 1 := by
  intro a b h
  omega

theorem slot_ne_tail_lemma2 (cap head count i : Nat) (hc : 0 < cap) (hlt : count < cap) (hi : i < count) : (head + i) % cap ≠ (head + count) % cap := by
  intro hEq
  have hd_pos : 0 < count - i := Nat.sub_pos_of_lt hi
  have hd_lt : count - i < cap := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hlt
  have hdi : head + count = (head + i) + (count - i) := by omega
  have hr_lt : (head + i) % cap < cap := Nat.mod_lt _ hc
  have h1 : ((head + i) % cap + (count - i)) % cap = ((head + i) + (count - i)) % cap :=
    Nat.mod_add_mod _ _ _
  have h2 : ((head + i) + (count - i)) % cap = (head + count) % cap := by
    rw [← hdi]
  have hmod : ((head + i) % cap + (count - i)) % cap = (head + count) % cap :=
    h1.trans h2
  have hrr : ((head + i) % cap + (count - i)) % cap = (head + i) % cap := by
    rw [hmod]
    rw [← hEq]
  by_cases hlt2 : (head + i) % cap + (count - i) < cap
  · have heq2 : ((head + i) % cap + (count - i)) % cap = (head + i) % cap + (count - i) :=
      Nat.mod_eq_of_lt hlt2
    rw [heq2] at hrr
    omega
  · have hge : cap ≤ (head + i) % cap + (count - i) := by omega
    have hsub_lt : (head + i) % cap + (count - i) - cap < cap := by omega
    have heq3 : (head + i) % cap + (count - i) = cap + ((head + i) % cap + (count - i) - cap) := by omega
    have hstep : ((head + i) % cap + (count - i)) % cap = ((head + i) % cap + (count - i) - cap) % cap :=
      calc ((head + i) % cap + (count - i)) % cap
          = (cap + ((head + i) % cap + (count - i) - cap)) % cap := by rw [← heq3]
        _ = ((head + i) % cap + (count - i) - cap) % cap := by rw [probe_mod_left_aux]
    have heq4 : ((head + i) % cap + (count - i)) % cap = (head + i) % cap + (count - i) - cap := by
      rw [hstep]
      exact Nat.mod_eq_of_lt hsub_lt
    rw [heq4] at hrr
    omega

theorem range_map_succ_aux (n : Nat) (f : Nat → Nat) : (List.range (n + 1)).map f = (List.range n).map f ++ [f n] := by
  rw [List.range_succ]
  rw [List.map_append]
  rfl

theorem tmp_check_deq (s : State) (hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)) :
    step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
  unfold step
  simp [hcond]

theorem tmp_range_cons_test (k : Nat) : List.range (k + 1 + 1) = List.range (k + 1) ++ [k + 1] := by
  exact List.range_succ

theorem tmp_range_map_cons3 (n : Nat) (f : Nat → Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  induction n generalizing f with
  | zero => rfl
  | succ k ih =>
    have hA : List.range (k + 1 + 1) = List.range (k + 1) ++ [k + 1] := List.range_succ
    have hB : List.range (k + 1) = List.range k ++ [k] := List.range_succ
    have hL : ((List.range (k + 1 + 1)).map f) = ((List.range (k + 1)).map f) ++ [f (k + 1)] := by
      rw [hA, List.map_append]
      simp
    have hR : ((List.range (k + 1)).map (fun i => f (i + 1))) = ((List.range k).map (fun i => f (i + 1))) ++ [f (k + 1)] := by
      have h1 : ((List.range (k + 1)).map (fun i => f (i + 1))) = (((List.range k) ++ [k]).map (fun i => f (i + 1))) := by
        rw [hB]
      rw [h1, List.map_append]
      simp
    have ihk := ih f
    rw [hL, ihk, hR, List.cons_append]

theorem tmp_deq_cont2 (s : State) :
    contents ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State)
      = ((List.range (s.count - 1)).map (fun i => s.buf (((((s.head + 1) % s.capacity) + i) % s.capacity)))) := rfl

theorem tmp_deq_cont1 (s : State) :
    contents s = ((List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity))) := rfl

theorem my_enq_test1 (s : State) (x : Nat) (hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)) :
    step s (.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
  unfold step
  simp [hcond]

theorem my_debug_enq (s : State) (x : Nat) : True := by
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · have hstep : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
      unfold step
      simp [hcond]
    trivial
  · trivial

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    unfold Valid at h
    obtain ⟨⟨hc0, hh, hcc⟩, hlt⟩ := h
    have hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := ⟨hc0, hh, hlt⟩
    have hstep : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
      unfold step
      simp [hcond]
    rw [hstep]
    simp
  | dequeue =>
    unfold Valid at h
    obtain ⟨⟨hc0, hh, hcc⟩, hlt⟩ := h
    have hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := ⟨hc0, hh, hcc, hlt⟩
    have hstep : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
      unfold step
      simp [hcond]
    rw [hstep]
    simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro ⟨hc0, hh, hlt⟩
      apply h
      constructor
      · exact ⟨hc0, hh, Nat.le_of_lt hlt⟩
      · exact hlt
    unfold step
    simp [hcond]
  | dequeue =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro ⟨hc0, hh, hle, hpos⟩
      apply h
      show WellFormed s ∧ 0 < s.count
      exact ⟨⟨hc0, hh, hle⟩, hpos⟩
    unfold step
    simp [hcond]

theorem req_well_formed      : KeepsWellFormed step := by
  intro s op hWF
  obtain ⟨hc0, hh, hle⟩ := hWF
  cases op with
  | enqueue x =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · have hstep : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
        unfold step
        simp [hcond]
      rw [hstep]
      simp only
      obtain ⟨_, _, hlt⟩ := hcond
      exact ⟨hc0, hh, Nat.succ_le_of_lt hlt⟩
    · have hstep : step s (.enqueue x) = (.rejected, s) := by
        unfold step
        simp [hcond]
      rw [hstep]
      simp only
      exact ⟨hc0, hh, hle⟩
  | dequeue =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · have hstep : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
        unfold step
        simp [hcond]
      rw [hstep]
      simp only
      refine ⟨hc0, Nat.mod_lt _ hc0, ?_⟩
      exact Nat.le_trans (Nat.sub_le _ _) hle
    · have hstep : step s .dequeue = (.rejected, s) := by
        unfold step
        simp [hcond]
      rw [hstep]
      simp only
      exact ⟨hc0, hh, hle⟩

theorem req_enqueue_effects  : EnqueueEffects step := by
  intro s x hne
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · have hstep : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
      unfold step
      simp [hcond]
    have hslot : (s.head + s.count) % s.capacity = slot s s.count := rfl
    rw [hslot] at hstep
    exact hstep
  · have hstep : step s (.enqueue x) = (.rejected, s) := by
      unfold step
      simp [hcond]
    rw [hstep] at hne
    simp at hne

theorem req_dequeue_effects  : DequeueEffects step := by
  intro s hne
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · have hstep : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
      unfold step
      simp [hcond]
    exact hstep
  · have hstep : step s .dequeue = (.rejected, s) := by
      unfold step
      simp [hcond]
    rw [hstep] at hne
    simp at hne

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · have hcond0 := hcond
    obtain ⟨hc0, hh, hlt⟩ := hcond0
    have hstep : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
      unfold step
      simp [hcond]
    have h2 : (step s (.enqueue x)).2 = ({ s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 } : State) := by
      rw [hstep]
    rw [h2]
    have hmain : contents ({ s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 } : State)
        = contents s ++ [x] := by
      unfold contents slot
      simp only
      have hrw : (List.range (s.count + 1)).map (fun i => (fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + i) % s.capacity))
        = ((List.range s.count).map (fun i => (fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + i) % s.capacity))) ++ [(fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + s.count) % s.capacity)] := by
        exact range_map_succ_aux s.count _
      rw [hrw]
      have hlast : (fun j => if j = (s.head + s.count) % s.capacity then x else s.buf j) ((s.head + s.count) % s.capacity) = x := by
        simp
      rw [hlast]
      congr 1
      apply rb_map_congr_aux
      intro i hi
      have hi_lt : i < s.count := (List.mem_range.mp hi)
      have hne_slot : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity :=
        slot_ne_tail_lemma2 s.capacity s.head s.count i hc0 hlt hi_lt
      simp [hne_slot]
    exact hmain
  · have hstep : step s (.enqueue x) = (.rejected, s) := by
      unfold step
      simp [hcond]
    rw [hstep] at hne
    simp at hne

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · have hh : s.head < s.capacity := hcond.2.1
    have hstep : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
      unfold step
      simp [hcond]
    refine ⟨s.buf s.head, ?_, ?_⟩
    · rw [hstep]
    · have hcount : s.count = (s.count - 1) + 1 := by omega
      have hf0 : (fun i => s.buf ((s.head + i) % s.capacity)) 0 = s.buf s.head := by
        simp only
        have h1 : s.head + 0 = s.head := Nat.add_zero _
        rw [h1]
        rw [Nat.mod_eq_of_lt hh]
      have hidx : ∀ i : Nat, (fun j => s.buf ((s.head + j) % s.capacity)) (i + 1)
          = (fun j => s.buf ((((s.head + 1) % s.capacity) + j) % s.capacity)) i := by
        intro i
        simp only
        congr 1
        have hmod : ((((s.head + 1) % s.capacity) + i) % s.capacity) = ((s.head + 1 + i) % s.capacity) := Nat.mod_add_mod _ _ _
        have heq : s.head + 1 + i = s.head + (i + 1) := by omega
        rw [hmod, heq]
      have hmap1 : ((List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity)))
          = (fun i => s.buf ((s.head + i) % s.capacity)) 0
            :: ((List.range (s.count - 1)).map (fun i => (fun j => s.buf ((s.head + j) % s.capacity)) (i + 1))) := by
        rw [hcount]
        exact tmp_range_map_cons3 (s.count - 1) (fun i => s.buf ((s.head + i) % s.capacity))
      have hmap1b : ((List.range s.count).map (fun i => s.buf ((s.head + i) % s.capacity)))
          = s.buf s.head
            :: ((List.range (s.count - 1)).map (fun i => s.buf ((s.head + (i + 1)) % s.capacity))) := by
        rw [hmap1, hf0]
      have hmap2 : ((List.range (s.count - 1)).map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)))
          = ((List.range (s.count - 1)).map (fun i => s.buf (((((s.head + 1) % s.capacity) + i) % s.capacity)))) := by
        apply rb_map_congr_aux
        intro i _
        have hh2 := hidx i
        simp only at hh2 ⊢
        exact hh2
      have hcont_s : contents s
          = s.buf s.head :: ((List.range (s.count - 1)).map (fun i => s.buf ((s.head + (i + 1)) % s.capacity))) := by
        rw [tmp_deq_cont1]
        exact hmap1b
      have hstep2 : (step s .dequeue).2 = ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) := by
        rw [hstep]
      rw [hcont_s, hmap2, ← tmp_deq_cont2, ← hstep2]
  · have hstep : step s .dequeue = (.rejected, s) := by
      unfold step
      simp [hcond]
    rw [hstep] at hne
    simp at hne

theorem req_fifo : Fifo step := by
  apply fifo_induct_helper
  intro s op
  have hEC := req_enqueue_contents
  have hDC := req_dequeue_contents
  have hEE := req_enqueue_effects
  have hDE := req_dequeue_effects
  exact fifo_single_of_assumed hEC hDC hEE hDE s op

end RingBuffer
