import RingBuffer.Spec

namespace RingBuffer

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if _h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity then
      (Outcome.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 })
    else
      (Outcome.rejected, s)
  | .dequeue =>
    if _h : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (Outcome.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else
      (Outcome.rejected, s)

theorem hb_mod_sub_eq3 {x cap : Nat} (hle : cap ≤ x) (hlt : x < cap + cap) :
    x % cap = x - cap := by
  have hpos : 0 < cap := by omega
  have hx : x = (x - cap) + cap := (Nat.sub_add_cancel hle).symm
  have h1 : x % cap = ((x - cap) + cap) % cap := congrArg (fun y => y % cap) hx
  have h2 : ((x - cap) + cap) % cap = (x - cap) % cap := Nat.add_mod_right _ _
  have h3 : (x - cap) % cap = x - cap := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]

theorem hb_mod_ne_aux {a d cap : Nat} (hc0 : 0 < cap) (hd0 : 0 < d) (hdl : d < cap) :
    (a + d) % cap ≠ a % cap := by
  have hrlt : a % cap < cap := Nat.mod_lt _ hc0
  have hmod : (a + d) % cap = ((a % cap) + d) % cap := (Nat.mod_add_mod a cap d).symm
  rw [hmod]
  by_cases hle : (a % cap) + d < cap
  · rw [Nat.mod_eq_of_lt hle]
    omega
  · have hge : cap ≤ (a % cap) + d := by omega
    have hlt2 : (a % cap) + d < cap + cap := by omega
    rw [hb_mod_sub_eq3 hge hlt2]
    omega

theorem slot_ne {cap head i count : Nat} (hc0 : 0 < cap) (hlt : count < cap) (hi : i < count) :
    (head + i) % cap ≠ (head + count) % cap := by
  have hd0 : 0 < count - i := by omega
  have hdl : count - i < cap := by omega
  have heq : head + count = (head + i) + (count - i) := by omega
  have h := hb_mod_ne_aux (a := head + i) (d := count - i) (cap := cap) hc0 hd0 hdl
  rw [heq]
  exact Ne.symm h

theorem map_range_congr (n : Nat) (f g : Nat → Nat) (h : ∀ i, i < n → f i = g i) :
    (List.range n).map f = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hrange : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [hrange, List.map_append, List.map_append]
    have e1 : (List.range n).map f = (List.range n).map g := by
      apply ih
      intro i hi
      have hi' : i < n + 1 := by omega
      exact h i hi'
    have hf : ([n].map f) = [f n] := rfl
    have hg : ([n].map g) = [g n] := rfl
    have e2 : f n = g n := h n (Nat.lt_succ_self n)
    rw [e1, hf, hg, e2]

theorem range_map_succ (f : Nat → Nat) (n : Nat) :
    (List.range (n+1)).map f = f 0 :: (List.range n).map (fun i => f (i+1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n+1) ++ [n+1] := List.range_succ
    have h2 : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [h1, List.map_append]
    rw [ih]
    have h3 : (List.range (n+1)).map (fun i => f (i+1)) = ((List.range n).map (fun i => f (i+1))) ++ [f (n+1)] := by
      rw [h2, List.map_append]
      rfl
    rw [h3]
    rfl

theorem hb_slot_shift (head i cap : Nat) :
    ((head + 1) % cap + i) % cap = (head + 1 + i) % cap :=
  Nat.mod_add_mod (head + 1) cap i

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    obtain ⟨⟨hc0, hh, hcle⟩, hlt⟩ := h
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity :=
      ⟨hc0, hh, hcle, hlt⟩
    have hstep : (step s (.enqueue x)).1 = .ok := by
      unfold step
      simp only []
      split
      · rfl
      · exact absurd hcond ‹_›
    rw [hstep]
    intro hc; cases hc
  | dequeue =>
    simp only [Valid, WellFormed] at h
    obtain ⟨⟨hc0, hh, hcle⟩, hlt⟩ := h
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count :=
      ⟨hc0, hh, hcle, hlt⟩
    have hstep : (step s .dequeue).1 = .got (s.buf s.head) := by
      unfold step
      simp only []
      split
      · rfl
      · exact absurd hcond ‹_›
    rw [hstep]
    intro hc; cases hc

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    unfold step
    simp only []
    split
    · next hcond =>
      apply absurd hcond
      intro _; apply h
      obtain ⟨hc0, hh, hcle, hlt⟩ := hcond
      exact ⟨⟨hc0, hh, hcle⟩, hlt⟩
    · rfl
  | dequeue =>
    simp only [Valid, WellFormed] at h
    unfold step
    simp only []
    split
    · next hcond =>
      apply absurd hcond
      intro _; apply h
      obtain ⟨hc0, hh, hcle, hlt⟩ := hcond
      exact ⟨⟨hc0, hh, hcle⟩, hlt⟩
    · rfl

theorem req_well_formed : KeepsWellFormed step := by
  unfold KeepsWellFormed WellFormed
  intro s op hWF
  obtain ⟨hc0, hh, hcle⟩ := hWF
  cases op with
  | enqueue x =>
    unfold step
    simp only []
    split
    · next hcond =>
      obtain ⟨hc0', hh', hcle', hlt'⟩ := hcond
      simp only []
      exact ⟨hc0', hh', Nat.succ_le_of_lt hlt'⟩
    · simp only []
      exact ⟨hc0, hh, hcle⟩
  | dequeue =>
    unfold step
    simp only []
    split
    · next hcond =>
      obtain ⟨hc0', hh', hcle', hlt'⟩ := hcond
      simp only []
      refine ⟨hc0', Nat.mod_lt _ hc0', ?_⟩
      exact Nat.le_trans (Nat.pred_le _) hcle'
    · simp only []
      exact ⟨hc0, hh, hcle⟩

theorem req_enqueue_effects  : EnqueueEffects step := by
  unfold EnqueueEffects
  intro s x hne
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity
  · unfold step
    simp only [dif_pos hc]
  · unfold step at hne
    simp only [dif_neg hc] at hne
    exact absurd rfl hne

theorem req_dequeue_effects  : DequeueEffects step := by
  unfold DequeueEffects
  intro s hne
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · unfold step
    simp only [dif_pos hc]
  · unfold step at hne
    simp only [dif_neg hc] at hne
    exact absurd rfl hne

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ s.count < s.capacity
  · have ⟨hc0, hh, hcle, hlt⟩ := hc
    have hpair : step s (Op.enqueue x) = (Outcome.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
      unfold step
      simp only [dif_pos hc]
    have hstep2 : (step s (Op.enqueue x)).2 = ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) := by
      rw [hpair]
    rw [hstep2]
    have hcont1 : contents ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State)
        = (List.range (s.count + 1)).map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)) := rfl
    have hcont0 : contents s = (List.range s.count).map (fun i => s.buf (slot s i)) := rfl
    rw [hcont1, hcont0]
    have hrange : List.range (s.count + 1) = List.range s.count ++ [s.count] := List.range_succ
    rw [hrange, List.map_append]
    have hmap_eq : ((List.range s.count).map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)))
        = ((List.range s.count).map (fun i => s.buf (slot s i))) := by
      apply map_range_congr
      intro i hi
      have hne_slot : slot s i ≠ slot s s.count := slot_ne hc0 hlt hi
      simp [hne_slot]
    rw [hmap_eq]
    have hlast : ([s.count].map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i))) = [x] := by
      simp
    rw [hlast]
  · have hrej : (step s (Op.enqueue x)).1 = Outcome.rejected := by
      unfold step
      simp only [dif_neg hc]
    exact absurd hrej hne

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · have ⟨hc0, hh, hcle, hpos⟩ := hc
    have hpair : step s Op.dequeue = (Outcome.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
      unfold step
      simp only [dif_pos hc]
    have h1 : (step s Op.dequeue).1 = Outcome.got (s.buf s.head) := by rw [hpair]
    have h2 : (step s Op.dequeue).2 = (({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State)) := by
      rw [hpair]
    cases hcnt : s.count with
    | zero =>
      have hfalse : False := by omega
      exact False.elim hfalse
    | succ n =>
      refine ⟨s.buf s.head, h1, ?_⟩
      rw [h2]
      have hcount_s' : ((({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State)).count) = n := by
        show s.count - 1 = n
        omega
      have hcs : contents s = (List.range (n+1)).map (fun i => s.buf (slot s i)) := by
        unfold contents
        rw [hcnt]
      have hcs'_base : contents (({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State))
          = (List.range ((({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State).count))).map
            (fun i => s.buf (slot (({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State)) i)) := rfl
      rw [hcount_s'] at hcs'_base
      have hsplit : (List.range (n+1)).map (fun i => s.buf (slot s i))
          = s.buf (slot s 0) :: (List.range n).map (fun i => s.buf (slot s (i+1))) :=
        range_map_succ _ n
      have hcs_cons : contents s = s.buf (slot s 0) :: (List.range n).map (fun i => s.buf (slot s (i+1))) := by
        rw [hcs, hsplit]
      have hslot0 : slot s 0 = s.head := by
        unfold slot
        rw [Nat.add_zero, Nat.mod_eq_of_lt hh]
      have htail_eq : (List.range n).map (fun i => s.buf (slot s (i+1)))
          = contents (({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State)) := by
        rw [hcs'_base]
        apply map_range_congr
        intro i hi
        show s.buf (slot s (i+1)) = s.buf (slot (({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State)) i)
        congr 1
        unfold slot
        show (s.head + (i+1)) % s.capacity = ((((s.head + 1) % s.capacity) + i) % s.capacity)
        have hshift : ((((s.head + 1) % s.capacity) + i) % s.capacity) = (s.head + 1 + i) % s.capacity :=
          hb_slot_shift s.head i s.capacity
        rw [hshift]
        congr 1
        omega
      rw [hcs_cons, hslot0, htail_eq]
  · have hrej : (step s Op.dequeue).1 = Outcome.rejected := by
      unfold step
      simp only [dif_neg hc]
    exact absurd hrej hne

theorem req_fifo : Fifo step := by
  unfold Fifo
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp only [run, inflow, outflow, List.flatMap_nil, List.nil_append, List.append_nil]
  | cons op rest ih =>
    have hsingle : contents s ++ inflowOf (op, (step s op).1) =
        outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
      cases op
      case enqueue x =>
        by_cases hrej : (step s (Op.enqueue x)).1 = .rejected
        · have hnotvalid : ¬ Valid s (Op.enqueue x) := by
            intro hv
            have hsuc := req_valid_succeeds s (Op.enqueue x) hv
            rw [hrej] at hsuc
            exact hsuc rfl
          have hnoop := req_invalid_noop s (Op.enqueue x) hnotvalid
          have hst : (step s (Op.enqueue x)).2 = s := by rw [hnoop]
          rw [hrej, hst]
          have e1 : inflowOf (Op.enqueue x, Outcome.rejected) = ([] : List Nat) := rfl
          have e2 : outflowOf (Op.enqueue x, Outcome.rejected) = ([] : List Nat) := rfl
          rw [e1, e2, List.append_nil, List.nil_append]
        · have hne : (step s (Op.enqueue x)).1 ≠ .rejected := hrej
          have heff := req_enqueue_effects s x hne
          have hcont := req_enqueue_contents s x hne
          have hout : (step s (Op.enqueue x)).1 = .ok := by rw [heff]
          rw [hout, hcont]
          rfl
      case dequeue =>
        by_cases hrej : (step s Op.dequeue).1 = .rejected
        · have hnotvalid : ¬ Valid s Op.dequeue := by
            intro hv
            have hsuc := req_valid_succeeds s Op.dequeue hv
            rw [hrej] at hsuc
            exact hsuc rfl
          have hnoop := req_invalid_noop s Op.dequeue hnotvalid
          have hst : (step s Op.dequeue).2 = s := by rw [hnoop]
          rw [hrej, hst]
          have e1 : inflowOf (Op.dequeue, Outcome.rejected) = ([] : List Nat) := rfl
          have e2 : outflowOf (Op.dequeue, Outcome.rejected) = ([] : List Nat) := rfl
          rw [e1, e2, List.append_nil, List.nil_append]
        · have hne : (step s Op.dequeue).1 ≠ .rejected := hrej
          obtain ⟨y, hyout, hycont⟩ := req_dequeue_contents s hne
          rw [hyout, hycont]
          have e1 : inflowOf (Op.dequeue, Outcome.got y) = ([] : List Nat) := rfl
          have e2 : outflowOf (Op.dequeue, Outcome.got y) = [y] := rfl
          rw [e1, e2, List.append_nil, List.cons_append, List.nil_append]
    have hin : inflow (run step s (op :: rest)).1 =
        inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1 := by
      show inflow _ = _
      simp only [run, inflow, List.flatMap_cons]
    have hout : outflow (run step s (op :: rest)).1 =
        outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1 := by
      show outflow _ = _
      simp only [run, outflow, List.flatMap_cons]
    have hst : (run step s (op :: rest)).2 = (run step (step s op).2 rest).2 := by
      show (run step _ _).2 = _
      simp only [run]
    have hih := ih (s := (step s op).2)
    rw [hin, hout, hst]
    have h1 : contents s ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1)
        = (contents s ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 rest).1 := by
      rw [List.append_assoc]
    have h2 : (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1) ++
        contents (run step (step s op).2 rest).2
        = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 rest).1 ++
          contents (run step (step s op).2 rest).2) := by
      rw [List.append_assoc]
    rw [h1, h2, hsingle, ← hih]
    rw [List.append_assoc]

end RingBuffer
