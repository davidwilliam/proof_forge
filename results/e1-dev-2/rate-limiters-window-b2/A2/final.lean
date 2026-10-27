import FixedWindow.Spec
import FixedWindow.Lemmas
namespace FixedWindow
instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with clients := s.clients.map fun c =>
      if c.id = r.client then advance s c r.time
      else c })
  else (.rejected, s)

theorem map_adv_lookup_aux (l : List Client) (s : State) (r : Request) (i : ClientId)
    (hne : i ≠ r.client) :
    lookup (l.map fun c => if c.id = r.client then advance s c r.time else c) i =
      lookup l i := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, lookup_cons]
    have hid : (if c.id = r.client then advance s c r.time else c).id = c.id := by
      by_cases hc : c.id = r.client
      · simp only [hc, ↓reduceIte, advance]
      · simp only [hc, ↓reduceIte]
    rw [hid]
    by_cases heq : c.id = i
    · simp only [heq, ↓reduceIte]
      rw [if_neg hne]
    · simp only [heq, ↓reduceIte] at ih ⊢
      exact ih

theorem advance_id (s : State) (c : Client) (t : Nat) : (advance s c t).id = c.id := by
  simp [advance]

theorem map_adv_id (l : List Client) (s : State) (r : Request) :
    (l.map fun c => if c.id = r.client then advance s c r.time else c).map Client.id =
      l.map Client.id := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    by_cases hx : x.id = r.client
    · simp only [hx, ↓reduceIte, advance_id, ih]
    · simp only [hx, ↓reduceIte, ih]

theorem lookup_map_preserving (l : List Client) (f : Client → Client)
    (hpres : ∀ c ∈ l, (f c).id = c.id) (i : ClientId) :
    lookup (l.map f) i = (lookup l i).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, lookup_cons]
    have hfx : (f x).id = x.id := hpres x (by simp)
    have hrest : ∀ c ∈ xs, (f c).id = c.id := fun c hc => hpres c (List.mem_cons_of_mem _ hc)
    have ih' := ih hrest
    by_cases hx : x.id = i
    · have hfxi : (f x).id = i := by rw [hfx, hx]
      simp [hx, hfxi]
    · have hfxi : (f x).id ≠ i := by rw [hfx]; exact hx
      simp [hx, hfxi, ih']

theorem step_ok_iff_aux (s : State) (r : Request) : (step s r).1 = .ok ↔ Admissible s r := by
  unfold step
  by_cases h : Admissible s r <;> simp [h]

theorem my_test_lemma : True := trivial

theorem wb_lookup_of_mem3 (l : List Client) (hnd : (l.map Client.id).Nodup) (c : Client) (hm : c ∈ l) : lookup l c.id = some c := by
  induction l with
  | nil => simp at hm
  | cons x xs ih =>
    have hnd2 : (List.map Client.id (x :: xs)).Nodup := hnd
    rw [List.map_cons, List.nodup_cons] at hnd2
    obtain ⟨hnotmem, hnodup⟩ := hnd2
    have hm2 : c ∈ x :: xs := hm
    rw [List.mem_cons] at hm2
    rw [lookup_cons]
    by_cases hx : x.id = c.id
    · rcases hm2 with rfl | hm2
      · rw [if_pos hx]
      · exfalso
        apply hnotmem
        apply List.mem_map.mpr
        exact ⟨c, hm2, hx.symm⟩
    · rw [if_neg hx]
      rcases hm2 with rfl | hm2
      · exact absurd rfl (fun heq => hx (congrArg Client.id heq))
      · exact ih hnodup hm2

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_isolation : Isolation step := by
  intro s r i hne
  by_cases h : Admissible s r
  · have hstep : (step s r).2.clients = s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
      unfold step
      simp [h]
    rw [hstep]
    exact map_adv_lookup_aux s.clients s r i hne
  · have hstep : (step s r).2.clients = s.clients := by
      unfold step
      simp [h]
    rw [hstep]

theorem req_reset : ResetRule step := by
  intro s r hok c hc
  have hadm : Admissible s r := (step_ok_iff_aux s r).mp hok
  have hclients : (step s r).2.clients = s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
    unfold step
    simp [hadm]
  have hpres : ∀ cc ∈ s.clients, ((fun c => if c.id = r.client then advance s c r.time else c) cc).id = cc.id := by
    intro cc _
    by_cases hcc : cc.id = r.client
    · simp only [hcc, ↓reduceIte, advance_id]
    · simp only [hcc, ↓reduceIte]
  have hlook := lookup_map_preserving s.clients (fun c => if c.id = r.client then advance s c r.time else c) hpres r.client
  have hcid : c.id = r.client := lookup_id hc
  have hmap : Option.map (fun c_ => if c_.id = r.client then advance s c_ r.time else c_) (lookup s.clients r.client) = some (advance s c r.time) := by
    rw [hc]
    simp [hcid]
  rw [hmap] at hlook
  rw [hclients, hlook]
  refine ⟨advance s c r.time, rfl, ?_, ?_⟩
  · intro hle
    unfold advance windowStart windowCount
    simp [hle]
  · intro hlt
    have hle : ¬ (c.start + s.window ≤ r.time) := by omega
    unfold advance windowStart windowCount
    simp [hle]

theorem req_effects : Effects step := by
  intro s r hok
  have hadm : Admissible s r := (step_ok_iff_aux s r).mp hok
  have hstep : step s r = (.ok, { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c }) := by
    unfold step
    simp [hadm]
  have hclients : (step s r).2.clients = s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
    rw [hstep]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hstep]
  · rw [hstep]
  · rw [hclients]; exact map_adv_id s.clients s r
  · intro i
    rw [hclients]
    have hpres : ∀ cc ∈ s.clients, ((fun c => if c.id = r.client then advance s c r.time else c) cc).id = cc.id := by
      intro cc _
      by_cases hcc : cc.id = r.client
      · simp only [hcc, ↓reduceIte, advance_id]
      · simp only [hcc, ↓reduceIte]
    have hlook := lookup_map_preserving s.clients (fun c => if c.id = r.client then advance s c r.time else c) hpres i
    rw [hlook]
    unfold expectedLookup
    by_cases hi : i = r.client
    · simp only [hi, ↓reduceIte]
      cases h : lookup s.clients r.client with
      | none => simp
      | some c =>
        have hcid : c.id = r.client := lookup_id h
        simp [hcid]
    · simp only [hi, ↓reduceIte]
      cases h : lookup s.clients i with
      | none => simp
      | some c =>
        have hcid : c.id = i := lookup_id h
        have hne : c.id ≠ r.client := by rw [hcid]; exact hi
        simp [hne]

theorem req_window_bound : WindowBound step := by
  intro s r hbound c' hm
  by_cases hadm : Admissible s r
  · have hstep2c : (step s r).2.clients = s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
      unfold step
      simp [hadm]
    have hstep2l : (step s r).2.limit = s.limit := by
      have hstep : step s r = (.ok, { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c }) := by
        unfold step
        simp [hadm]
      rw [hstep]
    rw [hstep2c] at hm
    rw [hstep2l]
    obtain ⟨c, hc_mem, hc_eq⟩ := List.mem_map.mp hm
    have hc_le : c.count ≤ s.limit := hbound c hc_mem
    by_cases heq : c.id = r.client
    · have h_adv_eq : (if c.id = r.client then advance s c r.time else c) = advance s c r.time := by simp [heq]
      rw [h_adv_eq] at hc_eq
      subst hc_eq
      have hAdm : Admits s r.time (lookup s.clients r.client) := hadm.2
      have hlook_eq : lookup s.clients r.client = some c := by
        have h1 : lookup s.clients c.id = some c := wb_lookup_of_mem3 s.clients hadm.1 c hc_mem
        rw [heq] at h1
        exact h1
      rw [hlook_eq] at hAdm
      obtain ⟨_, hlt⟩ := hAdm
      have hcount : (advance s c r.time).count = windowCount s c r.time + 1 := rfl
      omega
    · have h_id_eq : (if c.id = r.client then advance s c r.time else c) = c := by simp [heq]
      rw [h_id_eq] at hc_eq
      subst hc_eq
      exact hc_le
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hadm]
    have hclients : (step s r).2.clients = s.clients := by rw [hstep]
    have hlim : (step s r).2.limit = s.limit := by rw [hstep]
    rw [hclients] at hm
    rw [hlim]
    exact hbound c' hm

end FixedWindow
