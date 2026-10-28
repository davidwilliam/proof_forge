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
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid] at h
    obtain ⟨⟨hc, hh, _⟩, hlt⟩ := h
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := ⟨hc, hh, hlt⟩
    simp [step, hcond]
  | dequeue =>
    simp only [Valid] at h
    obtain ⟨⟨hc, hh, hle⟩, hpos⟩ := h
    have hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count :=
      ⟨hc, hh, hle, hpos⟩
    simp [step, hcond]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro ⟨hc, hh, hlt⟩
      apply h
      simp only [Valid]
      exact ⟨⟨hc, hh, Nat.le_of_lt hlt⟩, hlt⟩
    simp [step, hcond]
  | dequeue =>
    have hcond : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro ⟨hc, hh, hle, hpos⟩
      apply h
      simp only [Valid]
      exact ⟨⟨hc, hh, hle⟩, hpos⟩
    simp [step, hcond]

theorem req_well_formed : KeepsWellFormed step := by
  intro s op hwf
  cases op with
  | enqueue x =>
    simp only [step]
    by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · rw [if_pos hcond]
      obtain ⟨hc, hh, hlt⟩ := hcond
      simp only [WellFormed] at hwf ⊢
      exact ⟨hc, hh, Nat.succ_le_of_lt hlt⟩
    · rw [if_neg hcond]
      exact hwf
  | dequeue =>
    simp only [step]
    by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · rw [if_pos hcond]
      obtain ⟨hc, hh, hle, _⟩ := hcond
      simp only [WellFormed] at hwf ⊢
      refine ⟨hc, Nat.mod_lt _ hc, ?_⟩
      exact Nat.le_trans (Nat.sub_le _ _) hle
    · rw [if_neg hcond]
      exact hwf

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hne
  simp only [step] at hne ⊢
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · rw [if_pos hcond]
  · rw [if_neg hcond] at hne ⊢
    simp at hne

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  simp only [step] at hne ⊢
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · rw [if_pos hcond]
  · rw [if_neg hcond] at hne ⊢
    simp at hne

private theorem map_congr_aux {α β : Type} (f g : α → β) (l : List α)
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    have hy : f y = g y := h y (by simp)
    have ht : ∀ x ∈ ys, f x = g x := fun x hx => h x (List.mem_cons_of_mem y hx)
    simp only [List.map_cons, hy, ih ht]

private theorem mod_branch (a cap : Nat)
    (hle : cap ≤ a) (hsub : a - cap < cap) : a % cap = a - cap := by
  have hsubmod : a % cap = (a - cap) % cap := Nat.mod_eq_sub_mod hle
  rw [Nat.mod_eq_of_lt hsub] at hsubmod
  exact hsubmod

private theorem slot_ne_aux (s : State)
    (_hc : 0 < s.capacity) (hh : s.head < s.capacity) (hlt : s.count < s.capacity)
    (i : Nat) (hi : i < s.count) : slot s i ≠ slot s s.count := by
  unfold slot
  intro heq
  have hlt_ab : s.head + i < s.head + s.count := by omega
  by_cases hb : s.head + s.count < s.capacity
  · have hmod_b : (s.head + s.count) % s.capacity = s.head + s.count :=
      Nat.mod_eq_of_lt hb
    by_cases ha : s.head + i < s.capacity
    · have hmod_a : (s.head + i) % s.capacity = s.head + i :=
        Nat.mod_eq_of_lt ha
      rw [hmod_a, hmod_b] at heq
      omega
    · have hle_a : s.capacity ≤ s.head + i := by omega
      have hsub_a : s.head + i - s.capacity < s.capacity := by omega
      have hmod_a := mod_branch (s.head + i) s.capacity hle_a hsub_a
      rw [hmod_a, hmod_b] at heq
      omega
  · have hle_b : s.capacity ≤ s.head + s.count := by omega
    have hsub_b : s.head + s.count - s.capacity < s.capacity := by omega
    have hmod_b := mod_branch (s.head + s.count) s.capacity hle_b hsub_b
    by_cases ha : s.head + i < s.capacity
    · have hmod_a : (s.head + i) % s.capacity = s.head + i :=
        Nat.mod_eq_of_lt ha
      rw [hmod_a, hmod_b] at heq
      omega
    · have hle_a : s.capacity ≤ s.head + i := by omega
      have hsub_a : s.head + i - s.capacity < s.capacity := by omega
      have hmod_a := mod_branch (s.head + i) s.capacity hle_a hsub_a
      rw [hmod_a, hmod_b] at heq
      omega

private theorem slot_shift_aux (s : State)
    (_hc : 0 < s.capacity) (hh : s.head < s.capacity) (hle : s.count ≤ s.capacity) (hpos : 0 < s.count)
    (i : Nat) (hi : i < s.count - 1) :
    slot s (i + 1) = slot { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } i := by
  unfold slot
  simp only
  have h_eq : s.head + (i + 1) = (s.head + 1) + i := by omega
  have hle_head1 : s.head + 1 ≤ s.capacity := by omega
  by_cases hlt_head1 : s.head + 1 < s.capacity
  · have hmod_h : (s.head + 1) % s.capacity = s.head + 1 :=
      Nat.mod_eq_of_lt hlt_head1
    rw [hmod_h, h_eq]
  · have heq_head1 : s.head + 1 = s.capacity := by omega
    have hmod_h : (s.head + 1) % s.capacity = 0 := by
      rw [heq_head1]
      exact Nat.mod_self _
    have hi_cap : i < s.capacity := by omega
    have hmod_i : i % s.capacity = i := Nat.mod_eq_of_lt hi_cap
    have hleft_eq : s.head + (i + 1) = s.capacity + i := by omega
    have hmod_cap_add : (s.capacity + i) % s.capacity = i := by
      have hle_c : s.capacity ≤ s.capacity + i := by omega
      have hlt_c : s.capacity + i - s.capacity < s.capacity := by omega
      have hbr := mod_branch (s.capacity + i) s.capacity hle_c hlt_c
      have hsub_c : s.capacity + i - s.capacity = i := by omega
      rw [hsub_c] at hbr
      exact hbr
    rw [hleft_eq, hmod_cap_add, hmod_h]
    simp only [Nat.zero_add]
    rw [hmod_i]

private theorem range_cons_aux (n : Nat) :
    List.range (Nat.succ n) = 0 :: (List.range n).map Nat.succ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : List.range (Nat.succ (Nat.succ n)) = List.range (Nat.succ n) ++ [Nat.succ n] := by
      rw [List.range_succ]
    have h2 : List.range (Nat.succ n) = List.range n ++ [n] := by
      rw [List.range_succ]
    have hmap_succ : ((List.range (Nat.succ n)).map Nat.succ) =
        ((List.range n).map Nat.succ) ++ [Nat.succ n] := by
      simp [h2]
    calc List.range (Nat.succ (Nat.succ n))
        = List.range (Nat.succ n) ++ [Nat.succ n] := h1
      _ = (0 :: (List.range n).map Nat.succ) ++ [Nat.succ n] := by rw [ih]
      _ = 0 :: (((List.range n).map Nat.succ) ++ [Nat.succ n]) := by simp
      _ = 0 :: ((List.range (Nat.succ n)).map Nat.succ) := by rw [hmap_succ]

private theorem enqueue_contents_aux (s : State) (x : Nat)
    (hc : 0 < s.capacity) (hh : s.head < s.capacity) (hlt : s.count < s.capacity) :
    contents (State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1)) =
      contents s ++ [x] := by
  have h_eq : contents (State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1))
      = List.map (fun i => if (s.head + i) % s.capacity = slot s s.count then x else s.buf ((s.head + i) % s.capacity))
        (List.range (s.count + 1)) := by
    unfold contents slot
    rfl
  rw [h_eq]
  have hrange : List.range (s.count + 1) = List.range s.count ++ [s.count] := by
    rw [List.range_succ]
  rw [hrange, List.map_append, List.map_singleton]
  have hmap : List.map
      (fun i => if (s.head + i) % s.capacity = slot s s.count then x else s.buf ((s.head + i) % s.capacity))
      (List.range s.count)
      = List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count) := by
    apply map_congr_aux
    intro i hi
    have hi' : i < s.count := List.mem_range.mp hi
    have hne : (s.head + i) % s.capacity ≠ slot s s.count :=
      slot_ne_aux s hc hh hlt i hi'
    simp only [hne, if_false]
  have hlast : (if (s.head + s.count) % s.capacity = slot s s.count then x
      else s.buf ((s.head + s.count) % s.capacity)) = x := by
    have heq : (s.head + s.count) % s.capacity = slot s s.count := rfl
    rw [if_pos heq]
  have hcont : List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range s.count)
      = contents s := by
    simp only [contents, slot]
  rw [hmap, hlast, hcont]

private theorem dequeue_contents_aux (s : State)
    (hc : 0 < s.capacity) (hh : s.head < s.capacity) (hle : s.count ≤ s.capacity) (hpos : 0 < s.count) :
    ∃ n, s.count = n + 1 ∧
    contents s = s.buf s.head :: contents (State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1)) := by
  obtain ⟨n, hn⟩ : ∃ n, s.count = n + 1 := ⟨s.count - 1, by omega⟩
  refine ⟨n, hn, ?_⟩
  have hn_eq : s.count - 1 = n := by omega
  have hcs : contents s
      = List.map (fun i => s.buf ((s.head + i) % s.capacity)) (List.range (n + 1)) := by
    rw [← hn]
    simp only [contents, slot]
  have heq_state : (State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1))
      = (State.mk s.capacity s.buf ((s.head + 1) % s.capacity) n) := by
    rw [hn_eq]
  have hcs' : contents (State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1))
      = List.map (fun i => s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity)) (List.range n) := by
    rw [heq_state]
    unfold contents slot
    rfl
  have hrange : List.range (n + 1) = 0 :: (List.range n).map Nat.succ := by
    have h := range_cons_aux n
    simpa [Nat.succ_eq_add_one] using h
  rw [hcs, hrange, List.map_cons]
  have hzero : s.buf ((s.head + 0) % s.capacity) = s.buf s.head := by
    have hmod : (s.head + 0) % s.capacity = s.head := by
      have hadd : s.head + 0 = s.head := Nat.add_zero _
      rw [hadd]
      exact Nat.mod_eq_of_lt hh
    rw [hmod]
  rw [hzero]
  congr 1
  have hmid : List.map (fun j => s.buf ((s.head + j) % s.capacity)) ((List.range n).map Nat.succ)
      = List.map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) (List.range n) := by
    rw [List.map_map]
    apply map_congr_aux
    intro i hi
    have hsucc : Nat.succ i = i + 1 := Nat.succ_eq_add_one i
    simp only [Function.comp_apply, hsucc]
  have hshift_map : List.map (fun i => s.buf ((s.head + (i + 1)) % s.capacity)) (List.range n)
      = List.map (fun i => s.buf ((((s.head + 1) % s.capacity) + i) % s.capacity)) (List.range n) := by
    apply map_congr_aux
    intro i hi
    have hi' : i < n := List.mem_range.mp hi
    have hi_lt : i < s.count - 1 := by omega
    have hshift := slot_shift_aux s hc hh hle hpos i hi_lt
    unfold slot at hshift
    simp only at hshift
    rw [hshift]
  rw [hmid, hshift_map]
  exact hcs'.symm

theorem req_enqueue_contents : EnqueueContents step := by
  intro s x hne
  simp only [step] at hne ⊢
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · rw [if_pos hcond] at hne ⊢
    obtain ⟨hc, hh, hlt⟩ := hcond
    simp only at hne ⊢
    have h := enqueue_contents_aux s x hc hh hlt
    have heq : (State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1))
        = ({ s with buf := (fun i => if i = slot s s.count then x else s.buf i), count := s.count + 1 } : State) :=
      rfl
    rw [heq] at h
    exact h
  · rw [if_neg hcond] at hne
    simp at hne

theorem req_dequeue_contents : DequeueContents step := by
  intro s hne
  simp only [step] at hne ⊢
  by_cases hcond : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · rw [if_pos hcond] at hne ⊢
    obtain ⟨hc, hh, hle, hpos⟩ := hcond
    refine ⟨s.buf s.head, rfl, ?_⟩
    simp only
    obtain ⟨n, hn, hcont⟩ := dequeue_contents_aux s hc hh hle hpos
    have heq : (State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1))
        = ({ s with head := (s.head + 1) % s.capacity, count := s.count - 1 } : State) :=
      rfl
    rw [heq] at hcont
    exact hcont
  · rw [if_neg hcond] at hne
    simp at hne

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons hd tl ih =>
    cases hd with
    | enqueue x =>
      by_cases henq : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
      · have hstep : step s (.enqueue x) =
            (.ok, State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1)) := by
          simp [step, henq]
        have hc : 0 < s.capacity := henq.1
        have hh : s.head < s.capacity := henq.2.1
        have hlt : s.count < s.capacity := henq.2.2
        have hcont := enqueue_contents_aux s x hc hh hlt
        have e_in : inflow (run step s (.enqueue x :: tl)).1
            = x :: inflow (run step (State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1)) tl).1 := by
          simp [run, hstep, inflow, inflowOf]
        have e_out : outflow (run step s (.enqueue x :: tl)).1
            = outflow (run step (State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1)) tl).1 := by
          simp [run, hstep, outflow, outflowOf]
        have e_snd : (run step s (.enqueue x :: tl)).2
            = (run step (State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1)) tl).2 := by
          simp [run, hstep]
        have ih' := ih (State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1))
        rw [e_in, e_out, e_snd]
        have happ : contents s ++ (x :: inflow (run step (State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1)) tl).1)
            = (contents s ++ [x]) ++ inflow (run step (State.mk s.capacity (fun i => if i = slot s s.count then x else s.buf i) s.head (s.count + 1)) tl).1 := by
          simp
        rw [happ, ← hcont]
        exact ih'
      · have hstep : step s (.enqueue x) = (.rejected, s) := by
          simp [step, henq]
        have e_in : inflow (run step s (.enqueue x :: tl)).1 = inflow (run step s tl).1 := by
          simp [run, hstep, inflow, inflowOf]
        have e_out : outflow (run step s (.enqueue x :: tl)).1 = outflow (run step s tl).1 := by
          simp [run, hstep, outflow, outflowOf]
        have e_snd : (run step s (.enqueue x :: tl)).2 = (run step s tl).2 := by
          simp [run, hstep]
        rw [e_in, e_out, e_snd]
        exact ih s
    | dequeue =>
      by_cases hdeq : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
      · have hstep : step s .dequeue =
            (.got (s.buf s.head),
              State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1)) := by
          simp [step, hdeq]
        have hc : 0 < s.capacity := hdeq.1
        have hh : s.head < s.capacity := hdeq.2.1
        have hle : s.count ≤ s.capacity := hdeq.2.2.1
        have hpos : 0 < s.count := hdeq.2.2.2
        obtain ⟨n, hn, hcont⟩ := dequeue_contents_aux s hc hh hle hpos
        have e_in : inflow (run step s (.dequeue :: tl)).1
            = inflow (run step (State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1)) tl).1 := by
          simp [run, hstep, inflow, inflowOf]
        have e_out : outflow (run step s (.dequeue :: tl)).1
            = s.buf s.head :: outflow (run step (State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1)) tl).1 := by
          simp [run, hstep, outflow, outflowOf]
        have e_snd : (run step s (.dequeue :: tl)).2
            = (run step (State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1)) tl).2 := by
          simp [run, hstep]
        have ih' := ih (State.mk s.capacity s.buf ((s.head + 1) % s.capacity) (s.count - 1))
        rw [e_in, e_out, e_snd, hcont, List.cons_append]
        exact congrArg (List.cons (s.buf s.head)) ih'
      · have hstep : step s .dequeue = (.rejected, s) := by
          simp [step, hdeq]
        have e_in : inflow (run step s (.dequeue :: tl)).1 = inflow (run step s tl).1 := by
          simp [run, hstep, inflow, inflowOf]
        have e_out : outflow (run step s (.dequeue :: tl)).1 = outflow (run step s tl).1 := by
          simp [run, hstep, outflow, outflowOf]
        have e_snd : (run step s (.dequeue :: tl)).2 = (run step s tl).2 := by
          simp [run, hstep]
        rw [e_in, e_out, e_snd]
        exact ih s

end RingBuffer
