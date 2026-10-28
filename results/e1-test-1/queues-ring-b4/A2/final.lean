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

def myTestDef : Nat := 5

theorem myTestLem : 1 + 1 = 2 := by rfl

theorem probe_mod1 (a cap : Nat) (h : a < cap) : a % cap = a := Nat.mod_eq_of_lt h

theorem probe_range_succ (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]

theorem probe_mod_eq1 (a b n : Nat) (h : a % n = b % n) (h2 : b < n) : a % n = b := by rw [h, Nat.mod_eq_of_lt h2]

theorem tmp_explore2 (n : Nat) : List.range (n + 1) = List.range n ++ [n] := List.range_succ

theorem tmp_explore3 : ∀ (n : Nat) (f : Nat → Nat),
  ((List.range (n + 1)).map f) = f 0 :: ((List.range n).map fun i => f (i + 1)) := by
  intro n f
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := List.range_succ
    have h2 : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [h1, List.map_append]
    have ihf := ih f
    rw [ihf]
    have h3 : (List.range (n + 1)).map (fun i => f (i + 1)) = ((List.range n).map fun i => f (i + 1)) ++ [f (n + 1)] := by
      rw [h2, List.map_append]
      rfl
    rw [h3]
    simp

theorem dq_slot_shift2 (head i cap : Nat) : ((head + 1) % cap + i) % cap = (head + (i + 1)) % cap := by
  have h1 : ((head + 1) % cap + i) % cap = (head + 1 + i) % cap := Nat.mod_add_mod (head + 1) cap i
  have h2 : head + 1 + i = head + (i + 1) := by omega
  rw [h1, h2]

theorem tmp_probe1 : 1 + 1 = 2 := by rfl

theorem tmp_check1 : True := by
  have h1 := @Nat.add_mul_mod_self_left
  have h2 := @Nat.add_mod
  have h3 := @Nat.mod_add_mod
  trivial

theorem tmp_inflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) : inflow (p :: t) = inflowOf p ++ inflow t := by simp [inflow]

theorem tmp_list1 : True := by trivial

theorem check_lemmas_exist : True := by
  have h1 := @Nat.add_mul_mod_self_left
  have h2 := @Nat.add_mod
  have h3 := @Nat.mod_add_mod
  have h4 := @Nat.mod_eq_of_lt
  have h5 := @Nat.div_add_mod
  trivial
#check @Nat.add_mul_mod_self_left
#check @Nat.add_mod
#check @Nat.mod_add_mod
#check @Nat.div_add_mod

theorem probe_lemmas : True := by
  have h1 := @Nat.mod_eq_of_lt
  have h2 := @Nat.mod_self
  have h3 := @Nat.add_mod
  have h4 := @Nat.mod_add_mod
  have h5 := @Nat.add_mul_mod_self_left
  have h6 := @Nat.add_mul_mod_self_right
  trivial
#check @Nat.mod_eq_sub_mod
#check @Nat.mod_eq_of_lt
#check @Nat.add_mod
#check @Nat.mod_add_mod







theorem plan0_slot_ne_of_lt (head i count cap : Nat) (hcap : 0 < cap)
    (hi : i < count) (hcount : count < cap) :
    (head + i) % cap ≠ (head + count) % cap := by
  intro hEq
  have hd_pos : 0 < count - i := by omega
  have hd_lt : count - i < cap := by omega
  have hr_lt : (head + i) % cap < cap := Nat.mod_lt _ hcap
  have hcount_eq : head + count = (head + i) + (count - i) := by omega
  have hmod : (head + count) % cap = (((head + i) % cap) + (count - i)) % cap := by
    rw [hcount_eq, ← Nat.mod_add_mod]
  rw [hmod] at hEq
  by_cases h : (head + i) % cap + (count - i) < cap
  · rw [Nat.mod_eq_of_lt h] at hEq
    omega
  · have hle : cap ≤ (head + i) % cap + (count - i) := by omega
    have hsub : (head + i) % cap + (count - i) - cap < cap := by omega
    have heq : ((head + i) % cap + (count - i)) % cap
        = ((head + i) % cap + (count - i) - cap) % cap :=
      Nat.mod_eq_sub_mod hle
    rw [heq, Nat.mod_eq_of_lt hsub] at hEq
    omega


theorem plan0_map_range_eq_of_forall_lt (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, i < n → f i = g i) :
    (List.range n).map f = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hrest : ∀ i, i < n → f i = g i := fun i hi => h i (by omega)
    have hlast : f n = g n := h n (by omega)
    have e1 : (List.range (n+1)).map f = (List.range n).map f ++ [f n] := by simp [List.range_succ]
    have e2 : (List.range (n+1)).map g = (List.range n).map g ++ [g n] := by simp [List.range_succ]
    rw [e1, e2, ih hrest, hlast]




theorem plan0_range_map_succ_aux (n : Nat) (f : Nat → Nat) :
    (List.range (n + 1)).map f = (List.range n).map f ++ [f n] := by simp [List.range_succ]

theorem plan0_range_map_succ (n : Nat) (f : Nat → Nat) :
    (List.range (n + 1)).map f = (List.range n).map f ++ [f n] := by simp [List.range_succ]

theorem tmp_check_mod_lemmas : True := by
  have h1 := @Nat.mod_eq_of_lt
  have h2 := @Nat.mod_add_mod
  have h3 := @Nat.add_mod
  have h4 := @Nat.mod_eq_sub_mod
  trivial

theorem tmp_sig_check : True := by
  have h1 : ∀ (m n : Nat), n * (m / n) + m % n = m := fun m n => Nat.div_add_mod m n
  have h2 : ∀ (n : Nat), 0 < n → ∀ (m : Nat), m % n < n := fun n hn m => Nat.mod_lt m hn
  have h3 : ∀ (a b : Nat), a ≤ b → a - b + b = a ∨ True := fun a b h => Or.inr trivial
  trivial

theorem tmp_probe_names : True := by
  have h1 := @Nat.div_add_mod
  have h2 := @Nat.not_lt_zero
  have h3 := @Nat.add_right_cancel
  have h4 := @Nat.mul_le_mul_left
  have h5 := @Nat.not_lt_of_ge
  have h6 := @Nat.pos_of_ne_zero
  trivial

theorem tmp_check_sig2 : True := trivial
#check @Nat.mod_eq_sub_mod
#check @Nat.mod_eq_of_lt
#check @Nat.le_of_not_gt

theorem plan0_mod_add_ne (r d cap : Nat) (hr : r < cap) (hd : 0 < d) (hdc : d < cap) :
    (r + d) % cap ≠ r := by
  by_cases h : r + d < cap
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have hle : cap ≤ r + d := by omega
    have hcap : 0 < cap := by omega
    have hsub : (r + d) - cap < cap := by omega
    have heq : (r + d) % cap = ((r + d) - cap) % cap := Nat.mod_eq_sub_mod hle
    rw [heq, Nat.mod_eq_of_lt hsub]
    omega

theorem plan0_slot_tail_eq (head i count cap : Nat) (h : i ≤ count) :
    (head + count) % cap = ((head + i) % cap + (count - i)) % cap := by
  have h1 : head + i + (count - i) = head + count := by omega
  have h2 : ((head + i) % cap + (count - i)) % cap = (head + i + (count - i)) % cap :=
    Nat.mod_add_mod (head + i) cap (count - i)
  rw [h2, h1]

theorem plan0_slot_ne_of_lt_newproof (head i count cap : Nat) (hcap : 0 < cap)
    (hi : i < count) (hcount : count < cap) :
    (head + i) % cap ≠ (head + count) % cap := by
  intro hEq
  have hd_pos : 0 < count - i := by omega
  have hd_lt : count - i < cap := by omega
  have hr_lt : (head + i) % cap < cap := Nat.mod_lt _ hcap
  have hcount_eq : head + count = (head + i) + (count - i) := by omega
  have hmod : (head + count) % cap = ((head + i) % cap + (count - i)) % cap := by
    rw [hcount_eq, ← Nat.mod_add_mod]
  rw [hmod] at hEq
  exact (plan0_mod_add_ne _ _ _ hr_lt hd_pos hd_lt) hEq.symm

theorem plan0_slot_ne_selfcontained (head i count cap : Nat) (hcap : 0 < cap)
    (hi : i < count) (hcount : count < cap) :
    (head + i) % cap ≠ (head + count) % cap := by
  intro hEq
  have hd_pos : 0 < count - i := by omega
  have hd_lt : count - i < cap := by omega
  have hr_lt : (head + i) % cap < cap := Nat.mod_lt _ hcap
  have hcount_eq : head + count = (head + i) + (count - i) := by omega
  have hmod : (head + count) % cap = (((head + i) % cap) + (count - i)) % cap := by
    rw [hcount_eq, ← Nat.mod_add_mod]
  rw [hmod] at hEq
  by_cases h : (head + i) % cap + (count - i) < cap
  · rw [Nat.mod_eq_of_lt h] at hEq
    omega
  · have hle : cap ≤ (head + i) % cap + (count - i) := by omega
    have hsub : (head + i) % cap + (count - i) - cap < cap := by omega
    have heq : ((head + i) % cap + (count - i)) % cap
        = ((head + i) % cap + (count - i) - cap) % cap :=
      Nat.mod_eq_sub_mod hle
    rw [heq, Nat.mod_eq_of_lt hsub] at hEq
    omega

theorem plan0_map_range_eq_of_forall_lt_aux (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, i < n → f i = g i) :
    (List.range n).map f = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hrest : ∀ i, i < n → f i = g i := fun i hi => h i (by omega)
    have hlast : f n = g n := h n (by omega)
    have e1 : (List.range (n+1)).map f = (List.range n).map f ++ [f n] := by simp [List.range_succ]
    have e2 : (List.range (n+1)).map g = (List.range n).map g ++ [g n] := by simp [List.range_succ]
    rw [e1, e2, ih hrest, hlast]

theorem plan0_contents_enqueue_update (s : State) (x : Nat)
    (hcap : 0 < s.capacity) (hcount : s.count < s.capacity) :
    contents { s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 } = contents s ++ [x] := by
  unfold contents slot
  simp only
  have htail : ∀ i, i < s.count →
      (if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity))
      = s.buf ((s.head + i) % s.capacity) := by
    intro i hi
    have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity :=
      plan0_slot_ne_selfcontained s.head i s.count s.capacity hcap hi hcount
    simp [hne]
  have hlast : (if (s.head + s.count) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + s.count) % s.capacity)) = x := by
    simp
  have e1 : ((List.range (s.count + 1)).map fun i =>
      (if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)))
      = ((List.range s.count).map fun i =>
      (if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)))
      ++ [(if (s.head + s.count) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + s.count) % s.capacity))] := by
    simp [List.range_succ]
  rw [e1, hlast]
  have heq : ((List.range s.count).map fun i =>
      (if (s.head + i) % s.capacity = (s.head + s.count) % s.capacity then x else s.buf ((s.head + i) % s.capacity)))
      = (List.range s.count).map fun i => s.buf ((s.head + i) % s.capacity) := by
    apply plan0_map_range_eq_of_forall_lt_aux
    intro i hi
    exact htail i hi
  rw [heq]

theorem req_enqueue_contents_aux_test : True := trivial

theorem fifo_run_cons (s : State) (op : Op) (ops : List Op) :
    run step s (op :: ops) =
    ((op, (step s op).1) :: (run step (step s op).2 ops).1,
     (run step (step s op).2 ops).2) := by
  rfl
#check @fifo_run_cons

theorem fifo_inflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (p :: t) = inflowOf p ++ inflow t := by
  simp [inflow]

theorem fifo_outflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (p :: t) = outflowOf p ++ outflow t := by
  simp [outflow]

theorem fifo_check_defs (x : Nat) :
    inflowOf (.enqueue x, .ok) = [x] := by rfl

theorem fifo_check_defs2 (x : Nat) :
    outflowOf ((.enqueue x : Op), (.ok : Outcome)) = ([] : List Nat) := by rfl

theorem fifo_check_defs3 :
    inflowOf ((.dequeue : Op), (.rejected : Outcome)) = ([] : List Nat) := by rfl

theorem fifo_check_defs4 (y : Nat) :
    outflowOf ((.dequeue : Op), (.got y : Outcome)) = [y] := by rfl

theorem fifo_check_defs5 (y : Nat) :
    inflowOf ((.dequeue : Op), (.got y : Outcome)) = ([] : List Nat) := by rfl

theorem fifo_probe_rej1 (x : Nat) :
    inflowOf ((.enqueue x : Op), (.rejected : Outcome)) = ([] : List Nat) := by
  simp [inflowOf]

theorem fifo_probe_rej2 (x : Nat) :
    outflowOf ((.enqueue x : Op), (.rejected : Outcome)) = ([] : List Nat) := by
  simp [outflowOf]

theorem fifo_probe_rej3 :
    inflowOf ((.dequeue : Op), (.rejected : Outcome)) = ([] : List Nat) := by
  simp [inflowOf]

theorem fifo_probe_rej4 :
    outflowOf ((.dequeue : Op), (.rejected : Outcome)) = ([] : List Nat) := by
  simp [outflowOf]





theorem plan1_step_fifo (s : State) (op : Op) :
    contents s ++ inflowOf (op, (step s op).1)
      = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
  cases op with
  | enqueue x =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · have hstep1 : (step s (.enqueue x)).1 = .ok := by
        unfold step
        simp [hcond]
      have hstep2 : (step s (.enqueue x)).2 = { s with
          buf := fun i => if i = slot s s.count then x else s.buf i,
          count := s.count + 1 } := by
        unfold step slot
        simp [hcond]
      have hcap : 0 < s.capacity := hcond.1
      have hcount : s.count < s.capacity := hcond.2.2
      have hcont : contents (step s (.enqueue x)).2 = contents s ++ [x] := by
        rw [hstep2]
        exact plan0_contents_enqueue_update s x hcap hcount
      rw [hstep1]
      simp only [inflowOf, outflowOf]
      rw [hcont]
      simp
    · have hstep : step s (.enqueue x) = (.rejected, s) := by
        unfold step
        simp [hcond]
      have h1 : (step s (.enqueue x)).1 = .rejected := by rw [hstep]
      have h2 : (step s (.enqueue x)).2 = s := by rw [hstep]
      rw [h1, h2]
      simp [inflowOf, outflowOf]
  | dequeue =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · obtain ⟨hcap, hhead, hle, hpos⟩ := hcond
      have hstep1 : (step s .dequeue).1 = .got (s.buf s.head) := by
        unfold step
        simp [hcap, hhead, hle, hpos]
      have hstep2 : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
        have he : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
          unfold step
          simp [hcap, hhead, hle, hpos]
        exact congrArg Prod.snd he
      have hcont : contents s = s.buf s.head :: contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
        obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
        have hcnt : s.count - 1 = n := by omega
        rw [hcnt]
        unfold contents slot
        simp only
        rw [hn]
        have hf0 : s.buf ((s.head + 0) % s.capacity) = s.buf s.head := by
          have : (s.head + 0) % s.capacity = s.head := Nat.mod_eq_of_lt hhead
          rw [this]
        have hshift : ∀ i, s.buf ((s.head + (i + 1)) % s.capacity) = s.buf (((s.head + 1) % s.capacity + i) % s.capacity) := by
          intro i
          congr 1
          exact (dq_slot_shift2 s.head i s.capacity).symm
        have hdecomp : ((List.range (n + 1)).map fun i => s.buf ((s.head + i) % s.capacity))
            = s.buf ((s.head + 0) % s.capacity) :: ((List.range n).map fun i => s.buf ((s.head + (i + 1)) % s.capacity)) := by
          have h := tmp_explore3 n (fun i => s.buf ((s.head + i) % s.capacity))
          simpa using h
        rw [hdecomp, hf0]
        congr 1
        apply plan0_map_range_eq_of_forall_lt_aux
        intro i _
        exact hshift i
      rw [hstep1, hstep2]
      simp only [inflowOf, outflowOf]
      rw [hcont]
      simp
    · have hstep : step s .dequeue = (.rejected, s) := by
        unfold step
        simp [hcond]
      have h1 : (step s .dequeue).1 = .rejected := by rw [hstep]
      have h2 : (step s .dequeue).2 = s := by rw [hstep]
      rw [h1, h2]
      simp [inflowOf, outflowOf]






theorem plan1_inflowOf_rejected (op : Op) : inflowOf (op, .rejected) = [] := by
  cases op with
  | enqueue x => rfl
  | dequeue => rfl

theorem plan1_outflowOf_rejected (op : Op) : outflowOf (op, .rejected) = [] := by
  cases op with
  | enqueue x => rfl
  | dequeue => rfl

theorem plan1_fifo_cons (s : State) (op : Op) (ops : List Op)
    (ih : contents (step s op).2 ++ inflow (run step (step s op).2 ops).1
          = outflow (run step (step s op).2 ops).1
            ++ contents (run step (step s op).2 ops).2) :
    contents s ++ inflow (run step s (op :: ops)).1
      = outflow (run step s (op :: ops)).1
        ++ contents (run step s (op :: ops)).2 := by
  have hstep := plan1_step_fifo s op
  have hrun1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by rfl
  have hrun2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by rfl
  rw [hrun1, hrun2]
  rw [fifo_inflow_cons, fifo_outflow_cons]
  rw [← List.append_assoc (contents s) _ _, hstep, List.append_assoc, ih, ← List.append_assoc]

theorem plan1_fifo_all (ops : List Op) (s : State) :
    contents s ++ inflow (run step s ops).1
      = outflow (run step s ops).1 ++ contents (run step s ops).2 := by
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih => exact plan1_fifo_cons s op ops (ih (step s op).2)

theorem probe_inflow1 (x : Nat) : inflowOf (.enqueue x, .rejected) = [] := by rfl

theorem probe_inflow2 (x : Nat) : inflowOf (.enqueue x, .rejected) = ([] : List Nat) := by simp [inflowOf]

theorem probe_inflow3 (y : Nat) : inflowOf (.dequeue, .got y) = ([] : List Nat) := by rfl



theorem plan2_contents_dequeue (s : State) (hcap : 0 < s.capacity)
    (hhead : s.head < s.capacity) (hpos : 0 < s.count) :
    contents s
      = s.buf s.head
        :: contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
  obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
  have hcnt : s.count - 1 = n := by omega
  rw [hcnt]
  unfold contents slot
  simp only
  rw [hn]
  have hf0 : s.buf ((s.head + 0) % s.capacity) = s.buf s.head := by
    have : (s.head + 0) % s.capacity = s.head := Nat.mod_eq_of_lt hhead
    rw [this]
  have hshift : ∀ i, s.buf ((s.head + (i + 1)) % s.capacity) = s.buf (((s.head + 1) % s.capacity + i) % s.capacity) := by
    intro i
    congr 1
    exact (dq_slot_shift2 s.head i s.capacity).symm
  have hdecomp : ((List.range (n + 1)).map fun i => s.buf ((s.head + i) % s.capacity))
      = s.buf ((s.head + 0) % s.capacity) :: ((List.range n).map fun i => s.buf ((s.head + (i + 1)) % s.capacity)) := by
    have h := tmp_explore3 n (fun i => s.buf ((s.head + i) % s.capacity))
    simpa using h
  rw [hdecomp, hf0]
  congr 1
  apply plan0_map_range_eq_of_forall_lt_aux
  intro i _
  exact hshift i






theorem plan2_range_map_shift (buf : Nat → Nat) (head cap n : Nat) :
    (List.range n).map (fun i => buf (((head + 1) % cap + i) % cap))
      = (List.range n).map (fun i => buf ((head + (i + 1)) % cap)) := by
  apply plan0_map_range_eq_of_forall_lt_aux
  intro i hi
  congr 1
  exact dq_slot_shift2 head i cap

theorem plan2_step_enqueue_fifo (s : State) (x : Nat) :
    contents s ++ inflowOf (.enqueue x, (step s (.enqueue x)).1)
      = outflowOf (.enqueue x, (step s (.enqueue x)).1)
        ++ contents (step s (.enqueue x)).2 := by
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · have hstep1 : (step s (.enqueue x)).1 = .ok := by
      unfold step
      simp [hcond]
    have hstep2 : (step s (.enqueue x)).2 = { s with
        buf := fun i => if i = slot s s.count then x else s.buf i,
        count := s.count + 1 } := by
      unfold step slot
      simp [hcond]
    have hcap : 0 < s.capacity := hcond.1
    have hcount : s.count < s.capacity := hcond.2.2
    have hcont : contents (step s (.enqueue x)).2 = contents s ++ [x] := by
      rw [hstep2]
      exact plan0_contents_enqueue_update s x hcap hcount
    rw [hstep1]
    simp only [inflowOf, outflowOf]
    rw [hcont]
    simp
  · have hstep : step s (.enqueue x) = (.rejected, s) := by
      unfold step
      simp [hcond]
    have h1 : (step s (.enqueue x)).1 = .rejected := by rw [hstep]
    have h2 : (step s (.enqueue x)).2 = s := by rw [hstep]
    rw [h1, h2]
    simp [inflowOf, outflowOf]

theorem plan2_step_dequeue_fifo (s : State) :
    contents s ++ inflowOf (.dequeue, (step s .dequeue).1)
      = outflowOf (.dequeue, (step s .dequeue).1)
        ++ contents (step s .dequeue).2 := by
  by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · obtain ⟨hcap, hhead, hle, hpos⟩ := hcond
    have hstep1 : (step s .dequeue).1 = .got (s.buf s.head) := by
      unfold step
      simp [hcap, hhead, hle, hpos]
    have hstep2 : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
      have he : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
        unfold step
        simp [hcap, hhead, hle, hpos]
      exact congrArg Prod.snd he
    have hcont : contents s = s.buf s.head :: contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
      exact plan2_contents_dequeue s hcap hhead hpos
    rw [hstep1, hstep2]
    simp only [inflowOf, outflowOf]
    rw [hcont]
    simp
  · have hstep : step s .dequeue = (.rejected, s) := by
      unfold step
      simp [hcond]
    have h1 : (step s .dequeue).1 = .rejected := by rw [hstep]
    have h2 : (step s .dequeue).2 = s := by rw [hstep]
    rw [h1, h2]
    simp [inflowOf, outflowOf]

theorem plan1_step_fifo_proof (s : State) (op : Op) :
    contents s ++ inflowOf (op, (step s op).1)
      = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
  cases op with
  | enqueue x => exact plan2_step_enqueue_fifo s x
  | dequeue => exact plan2_step_dequeue_fifo s

theorem plan1_selfcontained_test (s : State) (op : Op) :
    contents s ++ inflowOf (op, (step s op).1)
      = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
  cases op with
  | enqueue x =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · have hstep1 : (step s (.enqueue x)).1 = .ok := by
        unfold step
        simp [hcond]
      have hstep2 : (step s (.enqueue x)).2 = { s with
          buf := fun i => if i = slot s s.count then x else s.buf i,
          count := s.count + 1 } := by
        unfold step slot
        simp [hcond]
      have hcap : 0 < s.capacity := hcond.1
      have hcount : s.count < s.capacity := hcond.2.2
      have hcont : contents (step s (.enqueue x)).2 = contents s ++ [x] := by
        rw [hstep2]
        exact plan0_contents_enqueue_update s x hcap hcount
      rw [hstep1]
      simp only [inflowOf, outflowOf]
      rw [hcont]
      simp
    · have hstep : step s (.enqueue x) = (.rejected, s) := by
        unfold step
        simp [hcond]
      have h1 : (step s (.enqueue x)).1 = .rejected := by rw [hstep]
      have h2 : (step s (.enqueue x)).2 = s := by rw [hstep]
      rw [h1, h2]
      simp [inflowOf, outflowOf]
  | dequeue =>
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · obtain ⟨hcap, hhead, hle, hpos⟩ := hcond
      have hstep1 : (step s .dequeue).1 = .got (s.buf s.head) := by
        unfold step
        simp [hcap, hhead, hle, hpos]
      have hstep2 : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
        have he : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
          unfold step
          simp [hcap, hhead, hle, hpos]
        exact congrArg Prod.snd he
      have hcont : contents s = s.buf s.head :: contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
        obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
        have hcnt : s.count - 1 = n := by omega
        rw [hcnt]
        unfold contents slot
        simp only
        rw [hn]
        have hf0 : s.buf ((s.head + 0) % s.capacity) = s.buf s.head := by
          have : (s.head + 0) % s.capacity = s.head := Nat.mod_eq_of_lt hhead
          rw [this]
        have hshift : ∀ i, s.buf ((s.head + (i + 1)) % s.capacity) = s.buf (((s.head + 1) % s.capacity + i) % s.capacity) := by
          intro i
          congr 1
          exact (dq_slot_shift2 s.head i s.capacity).symm
        have hdecomp : ((List.range (n + 1)).map fun i => s.buf ((s.head + i) % s.capacity))
            = s.buf ((s.head + 0) % s.capacity) :: ((List.range n).map fun i => s.buf ((s.head + (i + 1)) % s.capacity)) := by
          have h := tmp_explore3 n (fun i => s.buf ((s.head + i) % s.capacity))
          simpa using h
        rw [hdecomp, hf0]
        congr 1
        apply plan0_map_range_eq_of_forall_lt_aux
        intro i _
        exact hshift i
      rw [hstep1, hstep2]
      simp only [inflowOf, outflowOf]
      rw [hcont]
      simp
    · have hstep : step s .dequeue = (.rejected, s) := by
        unfold step
        simp [hcond]
      have h1 : (step s .dequeue).1 = .rejected := by rw [hstep]
      have h2 : (step s .dequeue).2 = s := by rw [hstep]
      rw [h1, h2]
      simp [inflowOf, outflowOf]

theorem req_valid_succeeds   : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    have hv : Valid s (.enqueue x) := h
    unfold Valid at hv
    simp only at hv
    obtain ⟨⟨hcap, hhead, hcount_le⟩, hlt⟩ := hv
    show (step s (.enqueue x)).1 ≠ .rejected
    unfold step
    simp [hcap, hhead, hlt]
  | dequeue =>
    have hv : Valid s .dequeue := h
    unfold Valid at hv
    simp only at hv
    obtain ⟨⟨hcap, hhead, hcount_le⟩, hpos⟩ := hv
    show (step s .dequeue).1 ≠ .rejected
    unfold step
    simp [hcap, hhead, hcount_le, hpos]

theorem req_invalid_noop     : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    unfold step
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro hc
      apply h
      obtain ⟨h1, h2, h3⟩ := hc
      exact ⟨⟨h1, h2, Nat.le_of_lt h3⟩, h3⟩
    simp [hcond]
  | dequeue =>
    simp only [Valid, WellFormed] at h
    unfold step
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hc
      apply h
      obtain ⟨h1, h2, h3, h4⟩ := hc
      exact ⟨⟨h1, h2, h3⟩, h4⟩
    simp [hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hwf
  obtain ⟨hcap, hhead, hcount⟩ := hwf
  cases op with
  | enqueue x =>
    unfold step
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · simp only [if_pos hcond]
      show WellFormed _
      simp only [WellFormed]
      refine ⟨hcap, hhead, ?_⟩
      omega
    · simp only [if_neg hcond]
      exact ⟨hcap, hhead, hcount⟩
  | dequeue =>
    unfold step
    by_cases hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · simp only [if_pos hcond]
      show WellFormed _
      simp only [WellFormed]
      refine ⟨hcap, Nat.mod_lt _ hcap, ?_⟩
      omega
    · simp only [if_neg hcond]
      exact ⟨hcap, hhead, hcount⟩

theorem req_enqueue_effects  : EnqueueEffects step := by
  intro s x hne
  have hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
    by_cases h : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · exact h
    · have heq : step s (.enqueue x) = (.rejected, s) := by
        unfold step
        simp [h]
      have h1 : (step s (.enqueue x)).1 = .rejected := by
        rw [heq]
      exact False.elim (hne h1)
  have heq : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = (s.head + s.count) % s.capacity then x else s.buf i, count := s.count + 1 }) := by
    unfold step
    simp [hcond]
  have hslot : slot s s.count = (s.head + s.count) % s.capacity := rfl
  rw [hslot]
  exact heq

theorem req_dequeue_effects  : DequeueEffects step := by
  intro s hne
  have hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
    by_cases h : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · exact h
    · have heq : step s .dequeue = (.rejected, s) := by
        unfold step
        simp [h]
      have h1 : (step s .dequeue).1 = .rejected := by rw [heq]
      exact False.elim (hne h1)
  have heq : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
    unfold step
    simp [hcond]
  exact heq

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  have hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
    by_cases h : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · exact h
    · have heq : step s (.enqueue x) = (.rejected, s) := by
        unfold step
        simp [h]
      have h1 : (step s (.enqueue x)).1 = .rejected := by rw [heq]
      exact False.elim (hne h1)
  have hcap : 0 < s.capacity := hcond.1
  have hcount : s.count < s.capacity := hcond.2.2
  have hstep2 : (step s (.enqueue x)).2 = { s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 } := by
    unfold step slot
    simp [hcond]
  rw [hstep2]
  exact plan0_contents_enqueue_update s x hcap hcount

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  have hcond : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
    by_cases h : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · exact h
    · have heq : step s .dequeue = (.rejected, s) := by
        unfold step
        simp [h]
      have h1 : (step s .dequeue).1 = .rejected := by rw [heq]
      exact False.elim (hne h1)
  obtain ⟨hcap, hhead, hcle, hpos⟩ := hcond
  obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
  have hout : (step s .dequeue).1 = .got (s.buf s.head) := by
    unfold step
    simp [hcap, hhead, hcle, hpos]
  refine ⟨s.buf s.head, hout, ?_⟩
  have hcnt : s.count - 1 = n := by omega
  have hstep2 : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := n } := by
    have he : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
      unfold step
      simp [hcap, hhead, hcle, hpos]
    have h2 := congrArg Prod.snd he
    simp only at h2
    rw [h2, hcnt]
  rw [hstep2]
  unfold contents slot
  simp only
  rw [hn]
  have hf0 : s.buf ((s.head + 0) % s.capacity) = s.buf s.head := by
    have : (s.head + 0) % s.capacity = s.head := Nat.mod_eq_of_lt hhead
    rw [this]
  have hshift : ∀ i, s.buf ((s.head + (i + 1)) % s.capacity) = s.buf (((s.head + 1) % s.capacity + i) % s.capacity) := by
    intro i
    congr 1
    exact (dq_slot_shift2 s.head i s.capacity).symm
  have hdecomp : ((List.range (n + 1)).map fun i => s.buf ((s.head + i) % s.capacity))
      = s.buf ((s.head + 0) % s.capacity) :: ((List.range n).map fun i => s.buf ((s.head + (i + 1)) % s.capacity)) := by
    have h := tmp_explore3 n (fun i => s.buf ((s.head + i) % s.capacity))
    simpa using h
  rw [hdecomp, hf0]
  congr 1
  apply plan0_map_range_eq_of_forall_lt_aux
  intro i _
  exact hshift i

theorem req_fifo : Fifo step := by
  intro s ops
  exact plan1_fifo_all ops s

end RingBuffer
