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

theorem foo_test : True := by trivial

theorem slot_ne_test2 : (1 : Nat) < 2 := by omega

theorem check_lemmas : True := by
  have h1 := @Nat.add_mod
  have h2 := @Nat.mod_self
  have h3 := @Nat.mod_eq_of_lt
  trivial

theorem probe_ok : True := trivial

theorem probe2_ok : True := trivial

theorem probe3_ok : True := trivial

theorem slot_zero_eq : ∀ (s : State), 0 < s.capacity → s.head < s.capacity → slot s 0 = s.head := by
  intro s hcap hhead
  unfold slot
  simp [Nat.add_zero, Nat.mod_eq_of_lt hhead]

theorem probe_mod_lemmas : True := by
  have h1 := @Nat.add_mod
  have h2 := @Nat.mod_add_mod
  have h3 := @Nat.add_mod_mod
  trivial

theorem probe_range_succ_use : ∀ (n : Nat), List.range (n + 1) = List.range n ++ [n] := by
  intro n
  exact List.range_succ

theorem deq_slot_shift2 (cap h i : Nat) : ((((h + 1) % cap) + i) % cap) = ((h + (i + 1)) % cap) := by
  have h1 : ((((h + 1) % cap) + i) % cap) = ((h + 1 + i) % cap) := Nat.mod_add_mod (h + 1) cap i
  rw [h1]
  congr 1
  omega

theorem deq_slot_eq_succ (s : State) (i : Nat) :
    slot { s with head := (s.head + 1) % s.capacity } i = slot s (i + 1) := by
  unfold slot
  simp only
  exact deq_slot_shift2 s.capacity s.head i

theorem range_map_cons_aux (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := List.range_succ
    have h2 : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [h1, List.map_append, ih f]
    rw [h2]
    simp [List.map_append]

theorem fifo_test_probe : True := trivial

theorem probe_div_mod_lemmas : True := by
  have h1 := @Nat.div_add_mod
  have h2 := @Nat.mod_eq_of_lt
  have h3 := @Nat.add_mod
  have h4 := @Nat.mod_add_mod
  have h5 := @Nat.div_add_mod'
  trivial
#check @Nat.div_add_mod
#check @Nat.add_mod
#check @Nat.mod_add_mod
#check @Nat.mod_mod
#check @Nat.add_mod_mod

theorem probe_check_thms : True := by trivial
#check @Nat.mod_eq_sub_mod
#check @Nat.mod_eq_of_lt
#check @List.range_succ
#check @List.map_append
#check @Nat.sub_add_cancel

theorem probe_mod_names : True := by
  have h1 := @Nat.add_mul_mod_self_left
  have h2 := @Nat.add_mul_mod_self_right
  have h3 := @Nat.mul_mod
  have h4 := @Nat.mod_add_mod
  have h5 := @Nat.add_mod
  trivial

theorem fifo_inflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (p :: t) = inflowOf p ++ inflow t := by simp [inflow]

theorem fifo_outflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (p :: t) = outflowOf p ++ outflow t := by simp [outflow]

theorem tmp_probe1 : True := by trivial
#check @Nat.mod_eq_of_lt
#check @Nat.add_mod
#check @Nat.mod_add_mod
#check @Nat.add_mul_mod_self_left
#check @Nat.add_mul_mod_self_right
#check @Nat.mod_self
#check @Nat.mod_mod
#check @List.range_succ
#check @List.map_append







theorem plan0_contents_enqueue_state : ∀ (s : State) (x : Nat),
    0 < s.capacity → s.head < s.capacity → s.count < s.capacity →
    contents ({ s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 }) = contents s ++ [x] := by
  intro s x hcap hhead hlt
  have mod_two : ∀ (a cap : Nat), 0 < cap → a < cap + cap →
      a % cap = if a < cap then a else a - cap := by
    intro a cap hcap2 hlt2
    by_cases h : a < cap
    · simp only [h, ↓reduceIte, Nat.mod_eq_of_lt h]
    · simp only [h, ↓reduceIte]
      have hge : cap ≤ a := by omega
      have hb : a - cap < cap := by omega
      have ha : a = cap + (a - cap) := by omega
      have e : a % cap = (cap + (a - cap)) % cap := congrArg (fun n => n % cap) ha
      rw [e]
      have hh := Nat.add_mul_mod_self_left (a - cap) cap 1
      rw [Nat.mul_one] at hh
      have hcomm : cap + (a - cap) = (a - cap) + cap := by omega
      rw [hcomm, hh, Nat.mod_eq_of_lt hb]
  have mod_ne : ∀ (cap head i j : Nat), head < cap → i < j → j < cap →
      (head + i) % cap ≠ (head + j) % cap := by
    intro cap head i j hh hij hj
    have hcap2 : 0 < cap := by omega
    have ha2 : head + i < cap + cap := by omega
    have hb2 : head + j < cap + cap := by omega
    have ha_eq := mod_two (head + i) cap hcap2 ha2
    have hb_eq := mod_two (head + j) cap hcap2 hb2
    by_cases h1 : head + i < cap
    · by_cases h2 : head + j < cap
      · rw [ha_eq, hb_eq]; simp only [h1, h2, ↓reduceIte]; omega
      · rw [ha_eq, hb_eq]; simp only [h1, h2, ↓reduceIte]; omega
    · by_cases h2 : head + j < cap
      · omega
      · rw [ha_eq, hb_eq]; simp only [h1, h2, ↓reduceIte]; omega
  have map_ext : ∀ (f g : Nat → Nat) (n : Nat),
      (∀ i : Nat, i < n → f i = g i) →
      (List.range n).map f = (List.range n).map g := by
    intro f g n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro h
      have h' : ∀ i : Nat, i < n → f i = g i := fun i hi => h i (by omega)
      have ih' := ih h'
      have hn : f n = g n := h n (Nat.lt_succ_self n)
      have e1 : List.range (n + 1) = List.range n ++ [n] := List.range_succ
      rw [e1, List.map_append, List.map_append, ih']
      simp only [List.map_cons, List.map_nil] at *
      rw [hn]
  unfold contents slot
  simp only
  have h : List.range (s.count + 1) = List.range s.count ++ [s.count] := List.range_succ
  rw [h, List.map_append]
  congr 1
  · apply map_ext
    intro i hi
    have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity :=
      mod_ne s.capacity s.head i s.count hhead hi hlt
    simp only [hne, ↓reduceIte]
  · simp





theorem tmp_check_mod_lemmas : True := by
  have h1 := @Nat.add_mod
  have h2 := @Nat.mod_add_mod
  have h3 := @Nat.mod_eq_sub_mod
  have h4 := @Nat.add_mul_mod_self_left
  trivial
#check @Nat.add_mod
#check @Nat.mod_add_mod
#check @Nat.mod_eq_sub_mod
#check @Nat.add_mul_mod_self_left
#check @Nat.add_mul_mod_self_right

theorem tmp_mod_probe5 : ∀ (a cap : Nat), cap ≤ a → a - cap < cap →
    a % cap = a - cap := by
  intro a cap hge hb
  have ha : a = cap + (a - cap) := by omega
  have e : a % cap = (cap + (a - cap)) % cap := congrArg (fun n => n % cap) ha
  rw [e]
  have h := Nat.add_mul_mod_self_left (a - cap) cap 1
  rw [Nat.mul_one] at h
  have hcomm : cap + (a - cap) = (a - cap) + cap := by omega
  rw [hcomm, h, Nat.mod_eq_of_lt hb]

theorem plan0_mod_eq_of_lt_two : ∀ (a cap : Nat), 0 < cap → a < cap + cap →
    a % cap = if a < cap then a else a - cap := by
  intro a cap hcap hlt
  by_cases h : a < cap
  · simp only [h, ↓reduceIte, Nat.mod_eq_of_lt h]
  · simp only [h, ↓reduceIte]
    have hge : cap ≤ a := by omega
    have hb : a - cap < cap := by omega
    exact tmp_mod_probe5 a cap hge hb

theorem plan0_add_mod_ne_of_lt : ∀ (cap head i j : Nat), head < cap → i < j → j < cap →
    (head + i) % cap ≠ (head + j) % cap := by
  intro cap head i j hhead hij hj
  have hcap : 0 < cap := by omega
  have h_a_lt2 : head + i < cap + cap := by omega
  have h_b_lt2 : head + j < cap + cap := by omega
  have ha_eq := plan0_mod_eq_of_lt_two (head + i) cap hcap h_a_lt2
  have hb_eq := plan0_mod_eq_of_lt_two (head + j) cap hcap h_b_lt2
  by_cases h1 : head + i < cap
  · by_cases h2 : head + j < cap
    · rw [ha_eq, hb_eq]
      simp only [h1, h2, ↓reduceIte]
      omega
    · rw [ha_eq, hb_eq]
      simp only [h1, h2, ↓reduceIte]
      omega
  · by_cases h2 : head + j < cap
    · omega
    · rw [ha_eq, hb_eq]
      simp only [h1, h2, ↓reduceIte]
      omega

theorem plan0_map_range_ext_lt : ∀ (f g : Nat → Nat) (n : Nat),
    (∀ i : Nat, i < n → f i = g i) →
    (List.range n).map f = (List.range n).map g := by
  intro f g n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    have h' : ∀ i : Nat, i < n → f i = g i := fun i hi => h i (by omega)
    have ih' := ih h'
    have hn : f n = g n := h n (Nat.lt_succ_self n)
    have e1 : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [e1, List.map_append, List.map_append, ih']
    simp only [List.map_cons, List.map_nil] at *
    rw [hn]

theorem probe_slot_upd (s : State) (x : Nat) (i : Nat) :
    slot { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } i = slot s i := by
  unfold slot
  simp only

theorem probe_struct_parse (s : State) (x : Nat) : True := by
  have s' : State := { s with buf := fun k => if k = slot s s.count then x else s.buf k, count := s.count + 1 }
  trivial

theorem probe_struct_parse2 (s : State) (x : Nat) : True := by
  have s' : State := { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }
  trivial

theorem probe_have_enq (s : State) (x : Nat) : True := by
  have hslot : ∀ i : Nat,
      slot { s with buf := (fun k => if k = slot s s.count then x else s.buf k), count := s.count + 1 } i = slot s i := by
    intro i
    unfold slot
    simp only
  trivial

theorem mytest_expand (s : State) (x : Nat) :
    contents ({ s with buf := fun k => if k = slot s s.count then x else s.buf k, count := s.count + 1 })
    = ((List.range (s.count + 1)).map (fun j => (fun k => if k = slot s s.count then x else s.buf k) ((s.head + j) % s.capacity))) := by
  unfold contents slot
  simp only











theorem plan1_map_range_ext_lt : ∀ (f g : Nat → Nat) (n : Nat),
    (∀ i : Nat, i < n → f i = g i) →
    (List.range n).map f = (List.range n).map g := by
  intro f g n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    have h' : ∀ i : Nat, i < n → f i = g i := fun i hi => h i (by omega)
    have ih' := ih h'
    have hn : f n = g n := h n (Nat.lt_succ_self n)
    have e1 : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [e1, List.map_append, List.map_append, ih']
    simp only [List.map_cons, List.map_nil] at *
    rw [hn]

theorem plan1_mod_eq_if_lt_two : ∀ (a cap : Nat), 0 < cap → a < cap + cap →
    a % cap = if a < cap then a else a - cap :=
  plan0_mod_eq_of_lt_two

theorem plan1_add_mod_ne_of_lt : ∀ (cap head i j : Nat),
    head < cap → i < j → j < cap →
    (head + i) % cap ≠ (head + j) % cap :=
  plan0_add_mod_ne_of_lt

theorem plan1_buf_update_at_slot_of_lt : ∀ (s : State) (x i : Nat),
    s.head < s.capacity → i < s.count → s.count < s.capacity →
    (fun k => if k = slot s s.count then x else s.buf k) (slot s i)
      = s.buf (slot s i) := by
  intro s x i hhead hic hccap
  have hne : slot s i ≠ slot s s.count := by
    unfold slot
    exact plan0_add_mod_ne_of_lt s.capacity s.head i s.count hhead hic hccap
  simp only [hne, ↓reduceIte]

theorem plan1_contents_enqueue_expand : ∀ (s : State) (x : Nat),
    contents { s with
      buf := fun k => if k = slot s s.count then x else s.buf k,
      count := s.count + 1 }
    = (List.range s.count).map
        (fun i => (fun k => if k = slot s s.count then x else s.buf k) (slot s i))
      ++ [x] := by
  intro s x
  unfold contents slot
  simp only
  have h : List.range (s.count + 1) = List.range s.count ++ [s.count] := List.range_succ
  rw [h, List.map_append]
  congr 1
  simp

theorem plan0_contents_enqueue_state_proof : ∀ (s : State) (x : Nat),
    0 < s.capacity → s.head < s.capacity → s.count < s.capacity →
    contents ({ s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 }) = contents s ++ [x] := by
  intro s x hcap hhead hlt
  have hexpand := plan1_contents_enqueue_expand s x
  rw [hexpand]
  congr 1
  unfold contents
  apply plan1_map_range_ext_lt
  intro i hi
  exact plan1_buf_update_at_slot_of_lt s x i hhead hi hlt

theorem selfContained_enqueue_contents_aux2 : ∀ (s : State) (x : Nat),
    0 < s.capacity → s.head < s.capacity → s.count < s.capacity →
    contents ({ s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 }) = contents s ++ [x] := by
  intro s x hcap hhead hlt
  unfold contents slot
  simp only
  have h : List.range (s.count + 1) = List.range s.count ++ [s.count] := List.range_succ
  rw [h, List.map_append]
  congr 1
  · apply plan0_map_range_ext_lt
    intro i hi
    have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity :=
      plan0_add_mod_ne_of_lt s.capacity s.head i s.count hhead hi hlt
    simp only [hne, ↓reduceIte]
  · simp

theorem selfContained_enqueue_inline : ∀ (s : State) (x : Nat),
    0 < s.capacity → s.head < s.capacity → s.count < s.capacity →
    contents ({ s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 }) = contents s ++ [x] := by
  intro s x hcap hhead hlt
  have mod_two : ∀ (a cap : Nat), 0 < cap → a < cap + cap →
      a % cap = if a < cap then a else a - cap := by
    intro a cap hcap2 hlt2
    by_cases h : a < cap
    · simp only [h, ↓reduceIte, Nat.mod_eq_of_lt h]
    · simp only [h, ↓reduceIte]
      have hge : cap ≤ a := by omega
      have hb : a - cap < cap := by omega
      have ha : a = cap + (a - cap) := by omega
      have e : a % cap = (cap + (a - cap)) % cap := congrArg (fun n => n % cap) ha
      rw [e]
      have hh := Nat.add_mul_mod_self_left (a - cap) cap 1
      rw [Nat.mul_one] at hh
      have hcomm : cap + (a - cap) = (a - cap) + cap := by omega
      rw [hcomm, hh, Nat.mod_eq_of_lt hb]
  have mod_ne : ∀ (cap head i j : Nat), head < cap → i < j → j < cap →
      (head + i) % cap ≠ (head + j) % cap := by
    intro cap head i j hh hij hj
    have hcap2 : 0 < cap := by omega
    have ha2 : head + i < cap + cap := by omega
    have hb2 : head + j < cap + cap := by omega
    have ha_eq := mod_two (head + i) cap hcap2 ha2
    have hb_eq := mod_two (head + j) cap hcap2 hb2
    by_cases h1 : head + i < cap
    · by_cases h2 : head + j < cap
      · rw [ha_eq, hb_eq]; simp only [h1, h2, ↓reduceIte]; omega
      · rw [ha_eq, hb_eq]; simp only [h1, h2, ↓reduceIte]; omega
    · by_cases h2 : head + j < cap
      · omega
      · rw [ha_eq, hb_eq]; simp only [h1, h2, ↓reduceIte]; omega
  have map_ext : ∀ (f g : Nat → Nat) (n : Nat),
      (∀ i : Nat, i < n → f i = g i) →
      (List.range n).map f = (List.range n).map g := by
    intro f g n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro h
      have h' : ∀ i : Nat, i < n → f i = g i := fun i hi => h i (by omega)
      have ih' := ih h'
      have hn : f n = g n := h n (Nat.lt_succ_self n)
      have e1 : List.range (n + 1) = List.range n ++ [n] := List.range_succ
      rw [e1, List.map_append, List.map_append, ih']
      simp only [List.map_cons, List.map_nil] at *
      rw [hn]
  unfold contents slot
  simp only
  have h : List.range (s.count + 1) = List.range s.count ++ [s.count] := List.range_succ
  rw [h, List.map_append]
  congr 1
  · apply map_ext
    intro i hi
    have hne : (s.head + i) % s.capacity ≠ (s.head + s.count) % s.capacity :=
      mod_ne s.capacity s.head i s.count hhead hi hlt
    simp only [hne, ↓reduceIte]
  · simp

theorem plan0_step_enqueue_of_not_rejected : ∀ (s : State) (x : Nat),
    (step s (.enqueue x)).1 ≠ .rejected →
    0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity ∧
    step s (.enqueue x) = (.ok, { s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 }) := by
  intro s x hne
  unfold step at hne ⊢
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · refine ⟨hc.1, hc.2.1, hc.2.2, ?_⟩
    simp only [hc]
    unfold slot
    rfl
  · simp only [hc] at hne
    exact absurd rfl hne

theorem plan_deq_step_of_not_rejected : ∀ (s : State),
    (step s .dequeue).1 ≠ .rejected →
    0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count ∧
    step s .dequeue = (.got (s.buf s.head), { s with
      head := (s.head + 1) % s.capacity,
      count := s.count - 1 }) := by
  intro s hne
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, ?_⟩
    simp [step, hc]
  · exfalso
    apply hne
    simp [step, hc]

theorem plan_deq_contents_aux : ∀ (s : State),
    0 < s.capacity → s.head < s.capacity → s.count ≤ s.capacity → 0 < s.count →
    contents s = s.buf s.head :: contents ({ s with
      head := (s.head + 1) % s.capacity,
      count := s.count - 1 } : State) := by
  intro s hcap hhead hle hpos
  obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
  have hslot0 : slot s 0 = s.head := slot_zero_eq s hcap hhead
  have hmap_cons : (List.range (n+1)).map (fun i => s.buf (slot s i))
      = s.buf (slot s 0) :: (List.range n).map (fun i => s.buf (slot s (i+1))) := by
    have h := range_map_cons_aux (fun i => s.buf (slot s i)) n
    simpa using h
  have hcont_s : contents s = s.buf (slot s 0) :: (List.range n).map (fun i => s.buf (slot s (i+1))) := by
    unfold contents
    rw [hn]
    exact hmap_cons
  have hcont_s' : contents ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State)
      = (List.range n).map (fun i => s.buf (slot s (i+1))) := by
    unfold contents slot
    simp only [hn, Nat.add_sub_cancel]
    apply plan0_map_range_ext_lt
    intro i hi
    congr 1
    exact deq_slot_shift2 s.capacity s.head i
  rw [hcont_s, hcont_s', hslot0]

theorem fifo_inflow_rejected (op : Op) : inflowOf (op, .rejected) = [] := by
  cases op with
  | enqueue x => rfl
  | dequeue => rfl

theorem fifo_outflow_rejected (op : Op) : outflowOf (op, .rejected) = [] := by
  cases op with
  | enqueue x => rfl
  | dequeue => rfl

theorem fifo_run_cons (s : State) (op : Op) (ops : List Op) :
    run step s (op :: ops) =
    ((op, (step s op).1) :: (run step (step s op).2 ops).1,
     (run step (step s op).2 ops).2) := by
  simp only [run]

theorem fifo_inflow_cons2 (p : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (p :: t) = inflowOf p ++ inflow t := by simp [inflow]

theorem fifo_outflow_cons2 (p : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (p :: t) = outflowOf p ++ outflow t := by simp [outflow]

theorem fifo_probe_inflow1 (x : Nat) : inflowOf (.enqueue x, .ok) = [x] := rfl

theorem fifo_probe_outflow1 (x : Nat) : outflowOf (.enqueue x, .ok) = ([] : List Nat) := rfl

theorem fifo_probe_inflow2 (x : Nat) : inflowOf (.dequeue, .got x) = ([] : List Nat) := rfl

theorem fifo_probe_outflow2 (x : Nat) : outflowOf (.dequeue, .got x) = [x] := rfl

theorem fifo_probe_nil (l : List Nat) : l ++ ([] : List Nat) = l := List.append_nil l

theorem fifo_probe_cons_nil (l : List Nat) : ([] : List Nat) ++ l = l := List.nil_append l











theorem probe_inflow_red (x : Nat) : inflowOf (.enqueue x, .rejected) = ([] : List Nat) := by rfl

theorem probe_inflow_red2 (x : Nat) : inflowOf (.enqueue x, .ok) = [x] := by rfl

theorem probe_simp_test2 (s : State) (x : Nat) :
    contents s ++ inflowOf (.enqueue x, .rejected) = outflowOf (.enqueue x, .rejected) ++ contents s := by
  unfold inflowOf outflowOf
  simp







theorem plan3_enq_accepted_contents : ∀ (s : State) (x : Nat),
    (step s (.enqueue x)).1 ≠ .rejected →
    contents (step s (.enqueue x)).2 = contents s ++ [x] := by
  intro s x h
  obtain ⟨hcap, hhead, hlt, heq⟩ := plan0_step_enqueue_of_not_rejected s x h
  have h2 : (step s (.enqueue x)).2 = ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) := by rw [heq]
  rw [h2]
  exact selfContained_enqueue_inline s x hcap hhead hlt


theorem plan3_enq_rejected_state : ∀ (s : State) (x : Nat),
    (step s (.enqueue x)).1 = .rejected →
    (step s (.enqueue x)).2 = s := by
  intro s x h
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · have h2 : (step s (.enqueue x)).1 = .ok := by simp [step, hc]
    rw [h2] at h
    simp at h
  · have e1 : (step s (.enqueue x)).2 = s := by simp [step, hc]
    exact e1

theorem plan3_enq_rejected_flows : ∀ (s : State) (x : Nat),
    (step s (.enqueue x)).1 = .rejected →
    inflowOf (.enqueue x, (step s (.enqueue x)).1) = [] ∧
    outflowOf (.enqueue x, (step s (.enqueue x)).1) = [] := by
  intro s x h
  rw [h]
  constructor <;> rfl

theorem plan3_enq_accepted_flows : ∀ (s : State) (x : Nat),
    (step s (.enqueue x)).1 ≠ .rejected →
    (step s (.enqueue x)).1 = .ok ∧
    inflowOf (.enqueue x, (step s (.enqueue x)).1) = [x] ∧
    outflowOf (.enqueue x, (step s (.enqueue x)).1) = [] := by
  intro s x hne
  obtain ⟨hcap, hhead, hlt, heq⟩ := plan0_step_enqueue_of_not_rejected s x hne
  have h1 : (step s (.enqueue x)).1 = .ok := by rw [heq]
  refine ⟨h1, ?_, ?_⟩
  · rw [h1]; rfl
  · rw [h1]; rfl

theorem plan3_enq_accepted_contents_aux : ∀ (s : State) (x : Nat),
    (step s (.enqueue x)).1 ≠ .rejected →
    contents (step s (.enqueue x)).2 = contents s ++ [x] := by
  intro s x h
  obtain ⟨hcap, hhead, hlt, heq⟩ := plan0_step_enqueue_of_not_rejected s x h
  have h2 : (step s (.enqueue x)).2 = ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) := by rw [heq]
  rw [h2]
  exact selfContained_enqueue_inline s x hcap hhead hlt

theorem plan3_enq_accepted_contents_newproof : ∀ (s : State) (x : Nat),
    (step s (.enqueue x)).1 ≠ .rejected →
    contents (step s (.enqueue x)).2 = contents s ++ [x] := by
  intro s x h
  obtain ⟨hcap, hhead, hlt, heq⟩ := plan0_step_enqueue_of_not_rejected s x h
  have h2 : (step s (.enqueue x)).2 = ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) := by rw [heq]
  rw [h2]
  exact selfContained_enqueue_inline s x hcap hhead hlt

theorem plan2_enqueue_step_fifo : ∀ (s : State) (x : Nat),
    contents s ++ inflowOf (.enqueue x, (step s (.enqueue x)).1)
      = outflowOf (.enqueue x, (step s (.enqueue x)).1)
        ++ contents (step s (.enqueue x)).2 := by
  intro s x
  by_cases h : (step s (.enqueue x)).1 = .rejected
  · have h2 : (step s (.enqueue x)).2 = s := plan3_enq_rejected_state s x h
    have hf := plan3_enq_rejected_flows s x h
    obtain ⟨hin, hout⟩ := hf
    rw [hin, hout, h2]
    simp
  · have hne : (step s (.enqueue x)).1 ≠ .rejected := h
    have hcont := plan3_enq_accepted_contents s x hne
    have hf := plan3_enq_accepted_flows s x hne
    obtain ⟨hok, hin, hout⟩ := hf
    rw [hin, hout, hcont]
    simp

theorem plan2_dequeue_step_fifo : ∀ (s : State),
    contents s ++ inflowOf (.dequeue, (step s .dequeue).1)
      = outflowOf (.dequeue, (step s .dequeue).1)
        ++ contents (step s .dequeue).2 := by
  intro s
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · have hstep1 : (step s .dequeue).1 = (.got (s.buf s.head)) := by simp [step, hc]
    have hstep2 : (step s .dequeue).2 = ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) := by simp [step, hc]
    rw [hstep1, hstep2]
    simp only [inflowOf, outflowOf]
    have hcont := plan_deq_contents_aux s hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    rw [hcont]
    simp
  · have hstep1 : (step s .dequeue).1 = .rejected := by simp [step, hc]
    have hstep2 : (step s .dequeue).2 = s := by simp [step, hc]
    rw [hstep1, hstep2]
    simp only [inflowOf, outflowOf, List.append_nil, List.nil_append]

theorem plan2_step_fifo : ∀ (s : State) (op : Op),
    contents s ++ inflowOf (op, (step s op).1)
      = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
  intro s op
  cases op with
  | enqueue x => exact plan2_enqueue_step_fifo s x
  | dequeue => exact plan2_dequeue_step_fifo s

theorem plan2_fifo_cons_step : ∀ (s : State) (op : Op) (ops : List Op),
    (∀ (t : State), contents t ++ inflow (run step t ops).1
      = outflow (run step t ops).1 ++ contents (run step t ops).2) →
    contents s ++ inflow (run step s (op :: ops)).1
      = outflow (run step s (op :: ops)).1
        ++ contents (run step s (op :: ops)).2 := by
  intro s op ops IH
  have hstep := plan2_step_fifo s op
  have hIH := IH ((step s op).2)
  have hrun : run step s (op :: ops) =
    ((op, (step s op).1) :: (run step (step s op).2 ops).1,
     (run step (step s op).2 ops).2) := by simp only [run]
  have hin : inflow (run step s (op :: ops)).1
      = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
    rw [hrun]
    simp [inflow]
  have hout : outflow (run step s (op :: ops)).1
      = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
    rw [hrun]
    simp [outflow]
  have hfinal : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
    rw [hrun]
  rw [hin, hout, hfinal]
  calc contents s ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
      = (contents s ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by rw [List.append_assoc]
    _ = (outflowOf (op, (step s op).1) ++ contents (step s op).2) ++ inflow (run step (step s op).2 ops).1 := by rw [hstep]
    _ = outflowOf (op, (step s op).1) ++ (contents (step s op).2 ++ inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
    _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ contents (run step (step s op).2 ops).2) := by rw [hIH]
    _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ contents (run step (step s op).2 ops).2 := by rw [List.append_assoc]

theorem plan2_fifo_run : ∀ (ops : List Op) (s : State),
    contents s ++ inflow (run step s ops).1
      = outflow (run step s ops).1 ++ contents (run step s ops).2 := by
  intro ops s
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops IH => exact plan2_fifo_cons_step s op ops (fun t => IH t)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    unfold Valid at h
    obtain ⟨⟨hcap, hhead, hcount_le⟩, hlt⟩ := h
    have hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := ⟨hcap, hhead, hlt⟩
    unfold step
    simp only [hc]
    simp
  | dequeue =>
    unfold Valid at h
    obtain ⟨⟨hcap, hhead, hcount_le⟩, hpos⟩ := h
    have hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := ⟨hcap, hhead, hcount_le, hpos⟩
    unfold step
    simp only [hc]
    simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    unfold Valid at h
    have hc_neg : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro hc
      apply h
      obtain ⟨hcap, hhead, hlt⟩ := hc
      exact ⟨⟨hcap, hhead, Nat.le_of_lt hlt⟩, hlt⟩
    unfold step
    simp only [hc_neg, ↓reduceIte]
  | dequeue =>
    unfold Valid at h
    have hc_neg : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hc
      apply h
      obtain ⟨hcap, hhead, hle, hpos⟩ := hc
      exact ⟨⟨hcap, hhead, hle⟩, hpos⟩
    unfold step
    simp only [hc_neg, ↓reduceIte]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hs
  obtain ⟨hcap, hhead, hcount⟩ := hs
  cases op with
  | enqueue x =>
    unfold step
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
    · simp only [hc]
      refine ⟨?_, ?_, ?_⟩
      · exact hcap
      · exact hhead
      · exact Nat.succ_le_of_lt hc.2.2
    · simp only [hc]
      exact ⟨hcap, hhead, hcount⟩
  | dequeue =>
    unfold step
    by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
    · simp only [hc]
      refine ⟨?_, ?_, ?_⟩
      · exact hcap
      · exact Nat.mod_lt _ hcap
      · exact Nat.le_trans (Nat.pred_le _) hcount
    · simp only [hc]
      exact ⟨hcap, hhead, hcount⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  unfold EnqueueEffects slot step
  intro s x hne
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity)
  · simp [hc]
  · simp [hc] at hne

theorem req_dequeue_effects : DequeueEffects step := by
  unfold DequeueEffects step
  intro s hne
  by_cases hc : (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count)
  · simp [hc]
  · simp [hc] at hne

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  obtain ⟨hcap, hhead, hlt, heq⟩ := plan0_step_enqueue_of_not_rejected s x hne
  have h2 : (step s (.enqueue x)).2 = ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) := by
    rw [heq]
  rw [h2]
  exact selfContained_enqueue_inline s x hcap hhead hlt

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  obtain ⟨hcap, hhead, hle, hpos, heq⟩ := plan_deq_step_of_not_rejected s hne
  refine ⟨s.buf s.head, ?_, ?_⟩
  · have h1 : (step s .dequeue).1 = (.got (s.buf s.head)) := by rw [heq]
    exact h1
  · have h2 : (step s .dequeue).2 = ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) := by rw [heq]
    rw [h2]
    exact plan_deq_contents_aux s hcap hhead hle hpos

theorem req_fifo : Fifo step := by
  intro s ops
  exact plan2_fifo_run ops s

end RingBuffer
