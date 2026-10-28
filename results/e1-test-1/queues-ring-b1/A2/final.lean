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

theorem req_well_formed_aux_test : KeepsWellFormed step := by
  intro s op hw
  obtain ⟨hcap, hhead, hcnt⟩ := hw
  cases op with
  | enqueue x =>
    simp only [step]
    split
    · rename_i hc; obtain ⟨h1, h2, h3⟩ := hc
      simp only [WellFormed]
      exact ⟨h1, h2, Nat.succ_le_of_lt h3⟩
    · exact ⟨hcap, hhead, hcnt⟩
  | dequeue =>
    simp only [step]
    split
    · rename_i hc; obtain ⟨h1, h2, h3, h4⟩ := hc
      simp only [WellFormed]
      refine ⟨h1, Nat.mod_lt _ h1, ?_⟩
      omega
    · exact ⟨hcap, hhead, hcnt⟩

theorem foo_thm : True := trivial

theorem my_test1 : ∀ (p : Prop) [Decidable p], p ∨ ¬ p := by
  intro p inst
  exact inst.em p

theorem my_test2 : ∀ (n : Nat), n = n := by intro n; rfl

theorem my_test3 (p q : Prop) (h1 : p) (h2 : q) : p ∧ q := by exact And.intro h1 h2

theorem my_test4 (p : Prop) (h : p) : p := by exact h

theorem my_probe1 (n : Nat) (h : n < 5) : n < 6 := by omega

theorem deq_slot_helper2 : ∀ (head cap i : Nat), ((head + 1) % cap + i) % cap = (head + (i + 1)) % cap := by
  intro head cap i
  have h2 : head + 1 + i = head + (i + 1) := by omega
  calc ((head + 1) % cap + i) % cap
      = (head + 1 + i) % cap := Nat.mod_add_mod (head + 1) cap i
    _ = (head + (i + 1)) % cap := by rw [h2]

theorem deq_range_succ_check : (List.range 3 = [0,1,2]) := by rfl
#check @List.range_succ

theorem deq_range_rw (m : Nat) : List.range (m + 2) = List.range (m + 1) ++ [m + 1] := @List.range_succ (m + 1)

theorem deq_map_range_cons5 : ∀ (f : Nat → Nat) (n : Nat),
    (List.range (n + 1)).map f = f 0 :: ((List.range n).map (fun i => f (i + 1))) := by
  intro f n
  induction n generalizing f with
  | zero => rfl
  | succ m ih =>
    have h1 : List.range (m + 2) = List.range (m + 1) ++ [m + 1] := @List.range_succ (m + 1)
    have h2 : List.range (m + 1) = List.range m ++ [m] := @List.range_succ m
    have lhs : (List.range (m + 1 + 1)).map f = (List.range (m + 1)).map f ++ [f (m + 1)] := by
      have heq : m + 1 + 1 = m + 2 := by omega
      rw [heq, h1, List.map_append]
      simp
    have rhs_inner : (List.range (m + 1)).map (fun i => f (i + 1)) =
        (List.range m).map (fun i => f (i + 1)) ++ [f (m + 1)] := by
      rw [h2, List.map_append]
      simp
    have ihm := ih f
    have e1 : m + 1 + 1 = (m + 1) + 1 := by omega
    rw [e1, lhs, rhs_inner, ihm, List.cons_append]

theorem fifo_probe1 : True := trivial

theorem fifo_probe2 : True := trivial

theorem fifo_aux_inflow_cons (op : Op) (o : Outcome) (t : List (Op × Outcome)) :
    inflow ((op, o) :: t) = inflowOf (op, o) ++ inflow t := by
  simp [inflow]

theorem fifo_probe3 : True := trivial

theorem fifo_probe_run (s : State) (x : Nat) (ops : List Op) :
    (run step s (.enqueue x :: ops)).1 =
      (.enqueue x, (step s (.enqueue x)).1) :: (run step (step s (.enqueue x)).2 ops).1 := by
  simp only [run]

theorem fifo_aux_outflow_cons (op : Op) (o : Outcome) (t : List (Op × Outcome)) :
    outflow ((op, o) :: t) = outflowOf (op, o) ++ outflow t := by
  simp [outflow]







theorem plan0_map_range_ext (f g : Nat → Nat) (n : Nat)
    (h : ∀ i, i < n → f i = g i) :
    (List.range n).map f = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : ∀ i, i < n → f i = g i := fun i hi => h i (by omega)
    have ih' := ih h1
    have hn : f n = g n := h n (Nat.lt_succ_self n)
    simp only [List.range_succ, List.map_append, ih']
    simp only [List.map_cons, List.map_nil, hn]




theorem plan0_range_succ_map (f : Nat → Nat) (n : Nat) :
    (List.range (n + 1)).map f = (List.range n).map f ++ [f n] := by
  simp [List.range_succ]

theorem probe_mod_lemmas : True := trivial
#check @Nat.add_mod
#check @Nat.mod_add_mod
#check @Nat.mod_eq_of_lt
#check @Nat.mod_lt
#check @Nat.div_add_mod
#check @Nat.add_mul_mod_self_left

theorem probe_mod_lemmas2 : True := trivial
#check @Nat.div_add_mod
#check @Nat.mod_add_mod
#check @Nat.add_mod
#check @Nat.mod_eq_of_lt
#check @Nat.add_mul_mod_self_left
#check @Nat.add_mul_mod_self_right
#check @Nat.mod_self
#check @Nat.zero_mod
#check @Nat.mod_zero
#check @Nat.mod_mod
#check @Nat.mul_mod
#check @Nat.mod_eq_sub_mod
#check @Nat.sub_mod_eq_zero_of_mod_eq

theorem probe_sub_mod_sig : True := trivial
#check @Nat.sub_mod_eq_zero_of_mod_eq
#check @Nat.mod_eq_of_lt
#check @Nat.mod_lt
#check @Nat.div_add_mod

theorem sig_probe_aux2 : True := trivial
#check @Nat.div_add_mod
#check @Nat.mod_add_mod
#check @Nat.mul_succ
#check @Nat.succ_mul
#check @Nat.add_mul
#check @Nat.mul_add
#check @Nat.zero_mul
#check @Nat.mul_zero
#check @Nat.one_mul
#check @Nat.mul_one
#check @Nat.mul_le_mul_right
#check @Nat.le_mul_of_pos_right
#check @Nat.mod_eq_of_lt
#check @Nat.mod_lt

theorem plan0_mod_ne_of_lt_add_aux1 (cap q : Nat) (hq : 1 ≤ q) : cap ≤ cap * q := by
  cases q with
  | zero => omega
  | succ q' =>
    have h1 : cap * (q' + 1) = cap * q' + cap := by
      rw [Nat.mul_add, Nat.mul_one]
    omega

theorem plan0_mod_ne_of_lt_add_aux2 (n : Nat) (h : n ≠ 0) : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h

theorem plan0_mod_ne_of_lt_add (a b cap : Nat) (h1 : a < b) (h2 : b < a + cap) :
    a % cap ≠ b % cap := by
  intro heq
  have hcap : 0 < cap := by omega
  have hkpos : 0 < b - a := by omega
  have hklt : b - a < cap := by omega
  have hb : b = a + (b - a) := (Nat.add_sub_of_le (Nat.le_of_lt h1)).symm
  rw [hb] at heq
  have hmod : (a + (b - a)) % cap = (a % cap + (b - a)) % cap :=
    (Nat.mod_add_mod a cap (b - a)).symm
  rw [hmod] at heq
  have hrlt : a % cap < cap := Nat.mod_lt _ hcap
  have hEq : (a % cap + (b - a)) % cap = a % cap := heq.symm
  have hdiv : cap * ((a % cap + (b - a)) / cap) + (a % cap + (b - a)) % cap
      = a % cap + (b - a) := Nat.div_add_mod _ _
  rw [hEq] at hdiv
  have hQ : cap * ((a % cap + (b - a)) / cap) = b - a := by omega
  by_cases hq0 : (a % cap + (b - a)) / cap = 0
  · rw [hq0, Nat.mul_zero] at hQ
    omega
  · have h1le : 1 ≤ (a % cap + (b - a)) / cap :=
      plan0_mod_ne_of_lt_add_aux2 _ hq0
    have hle : cap ≤ cap * ((a % cap + (b - a)) / cap) :=
      plan0_mod_ne_of_lt_add_aux1 cap _ h1le
    omega

theorem plan0_slot_ne_of_lt_proof : ∀ (s : State) (i : Nat),
    s.count < s.capacity → i < s.count →
    slot s i ≠ slot s s.count := by
  intro s i hcount hi
  unfold slot
  apply plan0_mod_ne_of_lt_add
  · omega
  · omega

theorem plan0_slot_ne_of_lt (s : State) (i : Nat)
    (hcount : s.count < s.capacity) (hi : i < s.count) :
    slot s i ≠ slot s s.count := by
  unfold slot
  apply plan0_mod_ne_of_lt_add
  · omega
  · omega

theorem plan0_map_range_ext_proof : ∀ (f g : Nat → Nat) (n : Nat),
    (∀ i, i < n → f i = g i) →
    (List.range n).map f = (List.range n).map g := by
  intro f g n h
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : ∀ i, i < n → f i = g i := fun i hi => h i (by omega)
    have ih' := ih h1
    have hn : f n = g n := h n (Nat.lt_succ_self n)
    simp only [List.range_succ, List.map_append, ih']
    simp only [List.map_cons, List.map_nil, hn]

theorem plan0_contents_enqueue_update7 (s : State) (x : Nat)
    (hcount : s.count < s.capacity) :
    contents { s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 } = contents s ++ [x] := by
  unfold contents slot
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, if_true]
  congr 1
  apply plan0_map_range_ext
  intro i hi
  have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity := by
    have h := plan0_slot_ne_of_lt s i hcount hi
    unfold slot at h
    exact h
  rw [if_neg hne]

theorem plan0_dup_test : True := trivial

theorem plan0_contents_enqueue_update (s : State) (x : Nat)
    (hcount : s.count < s.capacity) :
    contents { s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 } = contents s ++ [x] :=
  plan0_contents_enqueue_update7 s x hcount

theorem fifo_run_cons_fst (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).1 =
      (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
  simp only [run]

theorem fifo_run_cons_snd (s : State) (op : Op) (ops : List Op) :
    (run step s (op :: ops)).2 =
      (run step (step s op).2 ops).2 := by
  simp only [run]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    unfold Valid at h
    obtain ⟨⟨hcap, hhead, hcount_le⟩, hlt⟩ := h
    unfold step
    simp only [hcap, hhead, hlt, and_self, ↓reduceIte]
    simp
  | dequeue =>
    unfold Valid at h
    obtain ⟨⟨hcap, hhead, hcount_le⟩, hpos⟩ := h
    unfold step
    simp only [hcap, hhead, hcount_le, hpos, and_self, ↓reduceIte]
    simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    have hc : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro ⟨hcap, hhead, hlt⟩
      exact h ⟨⟨hcap, hhead, Nat.le_of_lt hlt⟩, hlt⟩
    unfold step
    simp only [hc, ↓reduceIte]
  | dequeue =>
    simp only [Valid, WellFormed] at h
    have hc : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro ⟨h1, h2, h3, h4⟩
      exact h ⟨⟨h1, h2, h3⟩, h4⟩
    unfold step
    simp only [hc, ↓reduceIte]

theorem req_well_formed : KeepsWellFormed step := req_well_formed_aux_test

theorem req_enqueue_effects  : EnqueueEffects step := by
  intro s x hne
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · simp only [step, hc] at ⊢
    rfl
  · simp only [step, hc] at hne
    simp at hne

theorem req_dequeue_effects  : DequeueEffects step := by
  intro s hne
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · simp only [step, if_pos hc]
  · simp only [step, if_neg hc] at hne
    exact absurd rfl hne

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · have hstep : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
      unfold step slot
      simp only [if_pos hc]
    have h2 : (step s (.enqueue x)).2 = { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } := by
      rw [hstep]
    rw [h2]
    obtain ⟨_, _, hlt⟩ := hc
    exact plan0_contents_enqueue_update7 s x hlt
  · have hrej : (step s (.enqueue x)).1 = .rejected := by
      unfold step
      simp only [if_neg hc]
    exact absurd hrej hne

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · have hstep : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
      unfold step
      simp only [if_pos hc]
    refine ⟨s.buf s.head, ?_, ?_⟩
    · rw [hstep]
    · have h2 : (step s .dequeue).2 = ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) := by
        rw [hstep]
      rw [h2]
      obtain ⟨hcap, hhead, _, hpos⟩ := hc
      have hhead_mod : (s.head + 0) % s.capacity = s.head := by
        simp only [Nat.add_zero]
        exact Nat.mod_eq_of_lt hhead
      have hcount_eq : s.count = (s.count - 1) + 1 := by omega
      have hrhs : s.count - 1 + 1 - 1 = s.count - 1 := by omega
      unfold contents slot
      simp only
      rw [hcount_eq, deq_map_range_cons5, hhead_mod, hrhs]
      congr 1
      apply plan0_map_range_ext
      intro i hi
      have hslot : ((s.head + 1) % s.capacity + i) % s.capacity = (s.head + (i + 1)) % s.capacity :=
        deq_slot_helper2 s.head s.capacity i
      exact congrArg s.buf hslot.symm
  · have hrej : (step s .dequeue).1 = .rejected := by
      unfold step
      simp only [if_neg hc]
    exact absurd hrej hne

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp only [run, inflow, outflow, List.flatMap_nil, List.append_nil, List.nil_append]
  | cons op ops ih =>
    have hsingle : contents s ++ inflowOf (op, (step s op).1) =
        outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
      cases op with
      | enqueue x =>
        by_cases hV : Valid s (.enqueue x)
        · have hne : (step s (.enqueue x)).1 ≠ .rejected :=
            req_valid_succeeds s (.enqueue x) hV
          have heff := req_enqueue_effects s x hne
          have hcont := req_enqueue_contents s x hne
          have h1 : (step s (.enqueue x)).1 = .ok := by rw [heff]
          have hin : inflowOf ((.enqueue x), (step s (.enqueue x)).1) = [x] := by rw [h1]; rfl
          have hout : outflowOf ((.enqueue x), (step s (.enqueue x)).1) = [] := by rw [h1]; rfl
          rw [hin, hout, hcont]
          simp
        · have hstep := req_invalid_noop s (.enqueue x) hV
          have h1 : (step s (.enqueue x)).1 = .rejected := by rw [hstep]
          have h2 : (step s (.enqueue x)).2 = s := by rw [hstep]
          have hin : inflowOf ((.enqueue x), (step s (.enqueue x)).1) = [] := by rw [h1]; rfl
          have hout : outflowOf ((.enqueue x), (step s (.enqueue x)).1) = [] := by rw [h1]; simp [outflowOf]
          rw [hin, hout, h2]
          simp
      | dequeue =>
        by_cases hV : Valid s .dequeue
        · have hne : (step s .dequeue).1 ≠ .rejected :=
            req_valid_succeeds s .dequeue hV
          obtain ⟨y, hy1, hy2⟩ := req_dequeue_contents s hne
          have h1 : (step s .dequeue).1 = .got y := hy1
          have hin : inflowOf ((.dequeue), (step s .dequeue).1) = [] := by rw [h1]; rfl
          have hout : outflowOf ((.dequeue), (step s .dequeue).1) = [y] := by rw [h1]; rfl
          rw [hin, hout, hy2]
          simp
        · have hstep := req_invalid_noop s .dequeue hV
          have h1 : (step s .dequeue).1 = .rejected := by rw [hstep]
          have h2 : (step s .dequeue).2 = s := by rw [hstep]
          have hin : inflowOf ((.dequeue : Op), (step s .dequeue).1) = [] := by rw [h1]; rfl
          have hout : outflowOf ((.dequeue : Op), (step s .dequeue).1) = [] := by rw [h1]; rfl
          rw [hin, hout, h2]
          simp
    have hIH := ih (step s op).2
    have hfst : (run step s (op :: ops)).1 =
        (op, (step s op).1) :: (run step (step s op).2 ops).1 :=
      fifo_run_cons_fst s op ops
    have hsnd : (run step s (op :: ops)).2 =
        (run step (step s op).2 ops).2 :=
      fifo_run_cons_snd s op ops
    have hin : inflow (run step s (op :: ops)).1 =
        inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      rw [hfst, fifo_aux_inflow_cons]
    have hout : outflow (run step s (op :: ops)).1 =
        outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      rw [hfst, fifo_aux_outflow_cons]
    rw [hin, hout, hsnd]
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
