import RingBuffer.Spec
import Init.Data.List.Lemmas

namespace RingBuffer

def step : Impl
  | s, .enqueue x =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity then
      (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 })
    else (.rejected, s)
  | s, .dequeue =>
    if 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count then
      (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid, WellFormed] at h
    obtain ⟨⟨hc0, hh, _⟩, hlt⟩ := h
    have hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity := ⟨hc0, hh, hlt⟩
    have hstep : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
      simp [step, hc]
    rw [hstep]
    simp
  | dequeue =>
    simp only [Valid, WellFormed] at h
    obtain ⟨⟨hc0, hh, hle⟩, hpos⟩ := h
    have hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count := ⟨hc0, hh, hle, hpos⟩
    have hstep : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
      simp [step, hc]
    rw [hstep]
    simp

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s op h
  cases op with
  | enqueue x =>
    have hnot : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity) := by
      intro hc
      obtain ⟨hc0, hh, hlt⟩ := hc
      have hle : s.count ≤ s.capacity := Nat.le_of_lt hlt
      have hwf : WellFormed s := ⟨hc0, hh, hle⟩
      have hv : Valid s (.enqueue x) := by simp only [Valid]; exact ⟨hwf, hlt⟩
      exact h hv
    have hstep : step s (.enqueue x) = (.rejected, s) := by
      simp [step, hnot]
    exact hstep
  | dequeue =>
    have hnot : ¬ (0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count) := by
      intro hc
      obtain ⟨hc0, hh, hle, hpos⟩ := hc
      have hwf : WellFormed s := ⟨hc0, hh, hle⟩
      have hv : Valid s .dequeue := by simp only [Valid]; exact ⟨hwf, hpos⟩
      exact h hv
    have hstep : step s .dequeue = (.rejected, s) := by
      simp [step, hnot]
    exact hstep

theorem req_well_formed : KeepsWellFormed step := by
  unfold KeepsWellFormed
  intro s op hwf
  obtain ⟨hc0, hh, hle⟩ := hwf
  cases op with
  | enqueue x =>
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
    · have hstep : step s (.enqueue x) = (.ok, { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 }) := by
        simp [step, hc]
      rw [hstep]
      obtain ⟨_, _, hlt⟩ := hc
      refine ⟨hc0, hh, ?_⟩
      show s.count + 1 ≤ s.capacity
      omega
    · have hstep : step s (.enqueue x) = (.rejected, s) := by
        simp [step, hc]
      rw [hstep]
      exact ⟨hc0, hh, hle⟩
  | dequeue =>
    by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
    · have hstep : step s .dequeue = (.got (s.buf s.head), { s with head := (s.head + 1) % s.capacity, count := s.count - 1 }) := by
        simp [step, hc]
      rw [hstep]
      refine ⟨hc0, Nat.mod_lt _ hc0, ?_⟩
      show s.count - 1 ≤ s.capacity
      omega
    · have hstep : step s .dequeue = (.rejected, s) := by
        simp [step, hc]
      rw [hstep]
      exact ⟨hc0, hh, hle⟩

theorem req_enqueue_effects : EnqueueEffects step := by
  unfold EnqueueEffects
  intro s x hne
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · simp [step, hc]
  · have hstep : step s (.enqueue x) = (.rejected, s) := by
      simp [step, hc]
    have h1 : (step s (.enqueue x)).1 = .rejected := by rw [hstep]
    exact absurd h1 hne

theorem req_dequeue_effects : DequeueEffects step := by
  unfold DequeueEffects
  intro s hne
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · simp [step, hc]
  · have hstep : step s .dequeue = (.rejected, s) := by
      simp [step, hc]
    have h1 : (step s .dequeue).1 = .rejected := by rw [hstep]
    exact absurd h1 hne

private theorem map_eq_of_mem_eq {α β : Type} (f g : α → β) (l : List α)
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons]
    have ha : f a = g a := h a (by simp)
    rw [ha]
    have ht : as.map f = as.map g := ih (fun x hx => h x (by simp [hx]))
    rw [ht]

private theorem add_mod_self (cap k : Nat) (hk : k < cap) : (cap + k) % cap = k := by
  have hcap : cap % cap = 0 := Nat.mod_self cap
  have hkm : k % cap = k := Nat.mod_eq_of_lt hk
  have hadd : (cap + k) % cap = ((cap % cap) + (k % cap)) % cap := Nat.add_mod cap k cap
  rw [hcap, hkm, Nat.zero_add, Nat.mod_eq_of_lt hk] at hadd
  exact hadd

private theorem slot_repr (s : State) (hh : s.head < s.capacity) (j : Nat) (hj : j < s.capacity) :
    slot s j = if s.head + j < s.capacity then s.head + j else s.head + j - s.capacity := by
  unfold slot
  by_cases hlt : s.head + j < s.capacity
  · rw [if_pos hlt, Nat.mod_eq_of_lt hlt]
  · rw [if_neg hlt]
    have heq : s.head + j = s.capacity + (s.head + j - s.capacity) := by omega
    have hk : s.head + j - s.capacity < s.capacity := by omega
    have e : (s.head + j) % s.capacity = (s.capacity + (s.head + j - s.capacity)) % s.capacity :=
      congrArg (· % s.capacity) heq
    rw [e]
    exact add_mod_self s.capacity _ hk

private theorem slot_ne_aux (s : State) (hh : s.head < s.capacity) (hcount : s.count < s.capacity) {i : Nat} (hi : i < s.count) :
    slot s i ≠ slot s s.count := by
  have hic : i < s.capacity := Nat.lt_trans hi hcount
  rw [slot_repr s hh i hic, slot_repr s hh s.count hcount]
  by_cases h1 : s.head + i < s.capacity <;> by_cases h2 : s.head + s.count < s.capacity
  · rw [if_pos h1, if_pos h2]
    omega
  · rw [if_pos h1, if_neg h2]
    omega
  · rw [if_neg h1, if_pos h2]
    omega
  · rw [if_neg h1, if_neg h2]
    omega

private theorem shift_mod (h c i : Nat) : ((h + 1) % c + i) % c = (h + (i + 1)) % c := by
  have h1 : ((h + 1) % c + i) % c = (h + 1 + i) % c := Nat.mod_add_mod (h + 1) c i
  rw [h1]
  congr 1
  omega

private theorem range_append_one (n : Nat) : List.range (n + 1) = List.range n ++ [n] :=
  List.range_succ

private theorem range_succ_head_aux (m : Nat) :
    List.range (m + 1) = 0 :: List.map (fun x => x + 1) (List.range m) := by
  induction m with
  | zero => rfl
  | succ n ih =>
    show List.range (Nat.succ (n + 1)) = 0 :: List.map (fun x => x + 1) (List.range (Nat.succ n))
    have e1 : List.range (Nat.succ (n + 1)) = List.range (n + 1) ++ [n + 1] := List.range_succ
    have e2 : List.range (Nat.succ n) = List.range n ++ [n] := List.range_succ
    have hmap : List.map (fun x => x + 1) (List.range (Nat.succ n))
        = List.map (fun x => x + 1) (List.range n) ++ [n + 1] := by simp [e2]
    calc List.range (Nat.succ (n + 1))
        = List.range (n + 1) ++ [n + 1] := e1
      _ = (0 :: List.map (fun x => x + 1) (List.range n)) ++ [n + 1] := by rw [ih]
      _ = 0 :: (List.map (fun x => x + 1) (List.range n) ++ [n + 1]) := rfl
      _ = 0 :: List.map (fun x => x + 1) (List.range (Nat.succ n)) := by rw [hmap]

theorem req_enqueue_contents : EnqueueContents step := by
  unfold EnqueueContents
  intro s x hne
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity
  · obtain ⟨hc0, hh, hlt⟩ := hc
    have heff := req_enqueue_effects s x hne
    have h2 : (step s (.enqueue x)).2 = { s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } := by
      have h := congrArg Prod.snd heff
      simpa using h
    rw [h2]
    have hslot_upd : ∀ i, slot ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) i = slot s i := by
      intro i
      simp [slot]
    have hLHS : contents ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State)
        = (List.range (s.count + 1)).map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)) := by
      unfold contents
      apply map_eq_of_mem_eq
      intro i _
      have hs1 := hslot_upd i
      show (fun j => if j = slot s s.count then x else s.buf j) (slot ({ s with buf := fun i => if i = slot s s.count then x else s.buf i, count := s.count + 1 } : State) i)
        = (if slot s i = slot s s.count then x else s.buf (slot s i))
      rw [hs1]
    rw [hLHS]
    have hrw : List.range (s.count + 1) = List.range s.count ++ [s.count] := range_append_one _
    rw [hrw, List.map_append]
    have hlast : List.map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)) [s.count] = [x] := by
      simp
    have hpref : List.map (fun i => if slot s i = slot s s.count then x else s.buf (slot s i)) (List.range s.count)
        = List.map (fun i => s.buf (slot s i)) (List.range s.count) := by
      apply map_eq_of_mem_eq
      intro i hi
      have hi_lt : i < s.count := List.mem_range.mp hi
      have hne_slot : slot s i ≠ slot s s.count := slot_ne_aux s hh hlt hi_lt
      rw [if_neg hne_slot]
    rw [hlast, hpref]
    rfl
  · have hstep : step s (.enqueue x) = (.rejected, s) := by
      simp [step, hc]
    have h1 : (step s (.enqueue x)).1 = .rejected := by rw [hstep]
    exact absurd h1 hne

theorem req_dequeue_contents : DequeueContents step := by
  unfold DequeueContents
  intro s hne
  by_cases hc : 0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity ∧ 0 < s.count
  · obtain ⟨hc0, hh, hle, hpos⟩ := hc
    have heff := req_dequeue_effects s hne
    have h2 : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by
      have h := congrArg Prod.snd heff
      simpa using h
    have h1eq : (step s .dequeue).1 = .got (s.buf s.head) := by
      have h := congrArg Prod.fst heff
      simpa using h
    refine ⟨s.buf s.head, h1eq, ?_⟩
    obtain ⟨m, hm⟩ : ∃ m, s.count = m + 1 := ⟨s.count - 1, by omega⟩
    have hpred : s.count - 1 = m := by omega
    have hrw : List.range (m + 1) = 0 :: List.map (fun x => x + 1) (List.range m) := range_succ_head_aux m
    have hhead2 : s.buf (slot s 0) = s.buf s.head := by
      unfold slot
      have h0 : s.head + 0 = s.head := Nat.add_zero _
      rw [h0, Nat.mod_eq_of_lt hh]
    have hcont : (List.range (m + 1)).map (fun i => s.buf (slot s i))
        = s.buf s.head :: (List.range m).map (fun i => s.buf (slot { s with head := (s.head + 1) % s.capacity, count := m } i)) := by
      rw [hrw, List.map_cons]
      rw [show s.buf (slot s 0) = s.buf s.head from hhead2]
      congr 1
      rw [List.map_map]
      apply map_eq_of_mem_eq
      intro i _
      simp only [Function.comp_apply]
      have hshift : slot s (i + 1) = slot { s with head := (s.head + 1) % s.capacity, count := m } i := by
        unfold slot
        simp only
        exact (shift_mod _ _ _).symm
      rw [hshift]
    have hs_rw : contents s = (List.range (m + 1)).map (fun i => s.buf (slot s i)) := by
      unfold contents
      rw [hm]
    have h2m : (step s .dequeue).2 = { s with head := (s.head + 1) % s.capacity, count := m } := by
      rw [h2, hpred]
    have hs2_rw : contents (step s .dequeue).2
        = (List.range m).map (fun i => s.buf (slot { s with head := (s.head + 1) % s.capacity, count := m } i)) := by
      rw [h2m]
      rfl
    rw [hs_rw, hs2_rw]
    exact hcont
  · have hstep : step s .dequeue = (.rejected, s) := by
      simp [step, hc]
    have h1 : (step s .dequeue).1 = .rejected := by rw [hstep]
    exact absurd h1 hne

private theorem single_step_fifo (s : State) (op : Op) :
    contents s ++ inflowOf (op, (step s op).1)
      = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by
  by_cases hv : Valid s op
  · cases op with
    | enqueue x =>
      have hne : (step s (.enqueue x)).1 ≠ .rejected := req_valid_succeeds s _ hv
      have hcon := req_enqueue_contents s x hne
      have heff := req_enqueue_effects s x hne
      have hfst : (step s (.enqueue x)).1 = .ok := by
        have h := congrArg Prod.fst heff
        simpa using h
      have hin : inflowOf (.enqueue x, (step s (.enqueue x)).1) = [x] := by
        rw [hfst]; rfl
      have hout : outflowOf (.enqueue x, (step s (.enqueue x)).1) = ([] : List Nat) := by
        rw [hfst]; rfl
      rw [hin, hout, List.nil_append]
      exact hcon.symm ▸ rfl
    | dequeue =>
      have hne : (step s .dequeue).1 ≠ .rejected := req_valid_succeeds s _ hv
      obtain ⟨x, hgot, hcon⟩ := req_dequeue_contents s hne
      have hout : outflowOf (.dequeue, (step s .dequeue).1) = [x] := by
        rw [hgot]; rfl
      have hin : inflowOf (.dequeue, (step s .dequeue).1) = ([] : List Nat) := by
        rw [hgot]; rfl
      rw [hin, hout, List.append_nil]
      exact hcon
  · have hrej := req_invalid_noop s op hv
    have hfst : (step s op).1 = .rejected := by rw [hrej]
    have hsnd : (step s op).2 = s := by rw [hrej]
    have hin : inflowOf (op, (step s op).1) = ([] : List Nat) := by
      rw [hfst]
      cases op with
      | enqueue x => rfl
      | dequeue => rfl
    have hout : outflowOf (op, (step s op).1) = ([] : List Nat) := by
      rw [hfst]
      rfl
    rw [hin, hout, hsnd, List.append_nil, List.nil_append]

theorem req_fifo : Fifo step := by
  unfold Fifo
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op rest ih =>
    have hmid := single_step_fifo s op
    have ihr := ih ((step s op).2)
    have e1 : (run step s (op :: rest)).1 = (op, (step s op).1) :: (run step (step s op).2 rest).1 := rfl
    have e2 : (run step s (op :: rest)).2 = (run step (step s op).2 rest).2 := rfl
    have h_in : inflow (run step s (op :: rest)).1
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1 := by
      rw [e1]
      simp [inflow]
    have h_out : outflow (run step s (op :: rest)).1
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1 := by
      rw [e1]
      simp [outflow]
    rw [e2, h_in, h_out]
    calc contents s ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1)
        = (contents s ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 rest).1 := by
          rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ contents (step s op).2) ++ inflow (run step (step s op).2 rest).1 := by
          rw [hmid]
      _ = outflowOf (op, (step s op).1) ++ (contents (step s op).2 ++ inflow (run step (step s op).2 rest).1) := by
          rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 rest).1 ++ contents (run step (step s op).2 rest).2) := by
          rw [ihr]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1) ++ contents (run step (step s op).2 rest).2 := by
          rw [List.append_assoc]

end RingBuffer
