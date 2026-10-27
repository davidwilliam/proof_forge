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

private theorem map_advance_lookup_other (s : State) (r : Request) (l : List Client) (i : ClientId) (h : i ≠ r.client) :
    lookup (l.map fun c => if c.id = r.client then advance s c r.time else c) i = lookup l i := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, lookup_cons]
    have hadv : (if c.id = r.client then advance s c r.time else c).id = c.id := by
      split
      · rfl
      · rfl
    rw [hadv]
    by_cases hci : c.id = i
    · simp only [hci, if_true, h, if_false]
    · simp only [hci, if_false, ih]

theorem lookup_map_advance_self_aux (s : State) (r : Request) (l : List Client) :
    lookup (l.map fun c => if c.id = r.client then advance s c r.time else c) r.client =
      (lookup l r.client).map (fun c => advance s c r.time) := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, lookup_cons]
    have hadv : (if c.id = r.client then advance s c r.time else c).id = c.id := by
      split
      · rfl
      · rfl
    rw [hadv]
    by_cases hci : c.id = r.client
    · simp [hci]
    · simp [hci, ih]

theorem req_effects_aux_map_id (s : State) (r : Request) :
    ((s.clients.map fun c => if c.id = r.client then advance s c r.time else c).map Client.id) = s.clients.map Client.id := by
  induction s.clients with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons]
    have hid : (if c.id = r.client then advance s c r.time else c).id = c.id := by
      split
      · rfl
      · rfl
    rw [hid, ih]

theorem wb_lookup_unique (l : List Client) (c c0 : Client) (i : ClientId)
    (hmem : c ∈ l) (hnodup : (l.map Client.id).Nodup)
    (hid : c.id = i) (hlook : lookup l i = some c0) : c = c0 := by
  induction l generalizing c c0 with
  | nil => simp at hmem
  | cons x xs ih =>
    have hnd := (List.nodup_cons.mp hnodup)
    have hnotin : x.id ∉ xs.map Client.id := hnd.1
    have hnodup' : (xs.map Client.id).Nodup := hnd.2
    simp only [List.mem_cons] at hmem
    rw [lookup_cons] at hlook
    by_cases hx : x.id = i
    · simp [hx] at hlook
      subst hlook
      rcases hmem with rfl | hmem
      · rfl
      · exfalso
        apply hnotin
        rw [List.mem_map]
        exact ⟨c, hmem, hid.trans hx.symm⟩
    · simp [hx] at hlook
      rcases hmem with rfl | hmem
      · simp [hid] at hx
      · exact ih c c0 hmem hnodup' hid hlook

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
  unfold step
  by_cases h : Admissible s r
  · simp only [h, ↓reduceIte]
    exact map_advance_lookup_other s r s.clients i hne
  · simp [h]

theorem req_reset : ResetRule step := by
  intro s r h_ok c h_lookup
  by_cases hAdm : Admissible s r
  · have hstep2 : (step s r).2.clients =
        s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
      unfold step
      simp [hAdm]
    have hlook : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
      rw [hstep2, lookup_map_advance_self_aux, h_lookup]
      rfl
    refine ⟨advance s c r.time, hlook, ?_, ?_⟩
    · intro hle
      unfold advance windowStart windowCount
      simp [hle]
    · intro hlt
      have hle : ¬ (c.start + s.window ≤ r.time) := Nat.not_le.mpr hlt
      unfold advance windowStart windowCount
      simp [hle]
  · have hstep : (step s r).1 = .rejected := by
      unfold step
      simp [hAdm]
    rw [hstep] at h_ok
    cases h_ok

theorem req_effects : Effects step := by
  intro s r h_ok
  by_cases hAdm : Admissible s r
  · have hstep2 : (step s r).2 = { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c } := by
      unfold step
      simp [hAdm]
    have hclients : (step s r).2.clients = s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
      rw [hstep2]
    have hwin : (step s r).2.window = s.window := by rw [hstep2]
    have hlim : (step s r).2.limit = s.limit := by rw [hstep2]
    refine ⟨hwin, hlim, ?_, ?_⟩
    · rw [hclients]
      exact req_effects_aux_map_id s r
    · intro i
      rw [hclients]
      unfold expectedLookup
      by_cases heq : i = r.client
      · subst heq
        simp only [if_true]
        exact lookup_map_advance_self_aux s r s.clients
      · simp only [heq, if_false]
        exact map_advance_lookup_other s r s.clients i heq
  · have hstep : (step s r).1 = .rejected := by
      unfold step
      simp [hAdm]
    rw [hstep] at h_ok
    cases h_ok

theorem req_window_bound : WindowBound step := by
  intro s r hbound c' hmem
  by_cases hAdm : Admissible s r
  · have hclients : (step s r).2.clients =
        s.clients.map (fun c => if c.id = r.client then advance s c r.time else c) := by
      unfold step; simp [hAdm]
    have hlim : (step s r).2.limit = s.limit := by
      unfold step; simp [hAdm]
    rw [hlim]
    rw [hclients] at hmem
    obtain ⟨c, hcmem, hceq⟩ := List.mem_map.mp hmem
    have hle0 : c.count ≤ s.limit := hbound c hcmem
    by_cases heq : c.id = r.client
    · have hfc : (if c.id = r.client then advance s c r.time else c) = advance s c r.time := by simp [heq]
      rw [hfc] at hceq
      subst hceq
      obtain ⟨hnodup, hadmits⟩ := hAdm
      have hlook_ex : ∃ c0, lookup s.clients r.client = some c0 := by
        cases hlook : lookup s.clients r.client with
        | none =>
          unfold Admits at hadmits
          rw [hlook] at hadmits
          exact absurd hadmits (fun h => h)
        | some c0 => exact ⟨c0, rfl⟩
      obtain ⟨c0, hlook0⟩ := hlook_ex
      have heqc : c = c0 := wb_lookup_unique s.clients c c0 r.client hcmem hnodup heq hlook0
      subst heqc
      unfold Admits at hadmits
      rw [hlook0] at hadmits
      obtain ⟨_, hlt⟩ := hadmits
      unfold advance
      simp only
      exact Nat.succ_le_of_lt hlt
    · have hfc : (if c.id = r.client then advance s c r.time else c) = c := by simp [heq]
      rw [hfc] at hceq
      subst hceq
      exact hle0
  · have hstep : step s r = (.rejected, s) := by
      unfold step; simp [hAdm]
    have h2 : (step s r).2 = s := by rw [hstep]
    rw [h2] at hmem ⊢
    exact hbound c' hmem

end FixedWindow
