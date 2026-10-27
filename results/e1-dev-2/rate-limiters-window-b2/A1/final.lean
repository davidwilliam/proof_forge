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

theorem upd_id_iso_aux (s : State) (r : Request) (c : Client) :
    (if c.id = r.client then advance s c r.time else c).id = c.id := by
  by_cases h : c.id = r.client <;> simp [h, advance]

theorem lookup_map_iso_aux (s : State) (r : Request) (l : List Client) (i : ClientId) :
    lookup (l.map fun c => if c.id = r.client then advance s c r.time else c) i =
    (lookup l i).map fun c => if c.id = r.client then advance s c r.time else c := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, lookup_cons]
    have hid : (if x.id = r.client then advance s x r.time else x).id = x.id :=
      upd_id_iso_aux s r x
    rw [hid]
    by_cases hx : x.id = i
    · simp [hx]
    · simp [hx, ih]

theorem nodup_lookup_aux4 : ∀ (l : List Client) (c : Client),
    (l.map Client.id).Nodup → c ∈ l → lookup l c.id = some c := by
  intro l c hn hm
  induction l with
  | nil => simp at hm
  | cons hd tl ih =>
    have hcons : (List.map Client.id (hd :: tl)) = hd.id :: List.map Client.id tl := rfl
    rw [hcons, List.nodup_cons] at hn
    obtain ⟨hnotin, hnodup⟩ := hn
    rw [List.mem_cons] at hm
    cases hm with
    | inl heq =>
      rw [heq]
      show lookup (hd :: tl) hd.id = some hd
      rw [lookup_cons]
      simp
    | inr hmem =>
      have hx : ¬ (hd.id = c.id) := by
        intro hcon
        apply hnotin
        exact hcon ▸ (List.mem_map.mpr ⟨c, hmem, rfl⟩)
      show lookup (hd :: tl) c.id = some c
      rw [lookup_cons, if_neg hx]
      exact ih hnodup hmem

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
  · rw [if_pos h]
    show lookup (List.map _ _) i = _
    rw [lookup_map_iso_aux]
    cases hlookup : lookup s.clients i with
    | none => rfl
    | some c =>
      have hcid : c.id = i := lookup_id hlookup
      have hcr : c.id ≠ r.client := by rw [hcid]; exact hne
      have hif : (if c.id = r.client then advance s c r.time else c) = c := by simp [hcr]
      simp only [Option.map_some, hif]
  · rw [if_neg h]

theorem req_reset : ResetRule step := by
  intro s r hok c hc
  by_cases hAdm : Admissible s r
  · unfold step at hok ⊢
    rw [if_pos hAdm] at hok ⊢
    simp at hok
    have hmap : lookup ((s.clients.map fun c => if c.id = r.client then advance s c r.time else c)) r.client
        = (lookup s.clients r.client).map (fun c => if c.id = r.client then advance s c r.time else c) :=
      lookup_map_iso_aux s r s.clients r.client
    rw [hc] at hmap
    have hcid : c.id = r.client := lookup_id hc
    simp [hcid] at hmap
    refine ⟨advance s c r.time, hmap, ?_, ?_⟩
    · intro hexp
      unfold advance windowStart windowCount
      rw [if_pos hexp, if_pos hexp]
      exact ⟨rfl, rfl⟩
    · intro hlt
      have hle : ¬ (c.start + s.window ≤ r.time) := Nat.not_le.mpr hlt
      unfold advance windowStart windowCount
      rw [if_neg hle, if_neg hle]
      exact ⟨rfl, rfl⟩
  · have hstep : step s r = (.rejected, s) := req_invalid_noop s r hAdm
    rw [hstep] at hok
    simp at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hAdm : Admissible s r
  · unfold step at hok ⊢
    rw [if_pos hAdm] at hok ⊢
    simp only at hok
    refine ⟨rfl, rfl, ?_, ?_⟩
    · have hmap : ((s.clients.map fun c => if c.id = r.client then advance s c r.time else c).map Client.id) = s.clients.map Client.id := by
        induction s.clients with
        | nil => rfl
        | cons x xs ih =>
          simp only [List.map_cons]
          have hid := upd_id_iso_aux s r x
          simp [hid, ih]
      exact hmap
    · intro i
      show lookup (List.map _ _) i = _
      rw [lookup_map_iso_aux]
      unfold expectedLookup
      by_cases hi : i = r.client
      · subst hi
        cases hlook : lookup s.clients r.client with
        | none => simp
        | some c =>
          have hcid : c.id = r.client := lookup_id hlook
          simp [hcid]
      · simp only [hi, ↓reduceIte]
        cases hlook : lookup s.clients i with
        | none => rfl
        | some c =>
          have hcid : c.id = i := lookup_id hlook
          have hcr : c.id ≠ r.client := by intro hcon; apply hi; rw [← hcid, hcon]
          simp [hcr]
  · unfold step at hok
    rw [if_neg hAdm] at hok
    simp at hok

theorem req_window_bound : WindowBound step := by
  intro s r hbound c hmem
  by_cases hAdm : Admissible s r
  · have hstep : step s r = (.ok, { s with clients := s.clients.map fun c_1 => if c_1.id = r.client then advance s c_1 r.time else c_1 }) := by
      unfold step
      rw [if_pos hAdm]
    have hmem' : c ∈ s.clients.map (fun c_1 => if c_1.id = r.client then advance s c_1 r.time else c_1) := by
      have h := hmem
      rw [hstep] at h
      simpa using h
    have hgoal : c.count ≤ s.limit → c.count ≤ (step s r).2.limit := by
      rw [hstep]
      simp
    apply hgoal
    clear hgoal hmem hstep
    rw [List.mem_map] at hmem'
    obtain ⟨c0, hc0mem, hc0eq⟩ := hmem'
    have hbound0 : c0.count ≤ s.limit := hbound c0 hc0mem
    by_cases heq : c0.id = r.client
    · rw [if_pos heq] at hc0eq
      subst hc0eq
      unfold Admissible at hAdm
      obtain ⟨hnodup, hadmits⟩ := hAdm
      have hlook : lookup s.clients c0.id = some c0 := nodup_lookup_aux4 s.clients c0 hnodup hc0mem
      rw [heq] at hlook
      rw [hlook] at hadmits
      have hlt : windowCount s c0 r.time < s.limit := hadmits.2
      show (advance s c0 r.time).count ≤ s.limit
      unfold advance at ⊢
      simp only
      unfold windowCount at hlt ⊢
      by_cases hexp : c0.start + s.window ≤ r.time
      · rw [if_pos hexp] at hlt ⊢
        omega
      · rw [if_neg hexp] at hlt ⊢
        omega
    · rw [if_neg heq] at hc0eq
      subst hc0eq
      exact hbound0
  · have hstep : step s r = (.rejected, s) := req_invalid_noop s r hAdm
    have hmem' : c ∈ s.clients := by
      have h := hmem
      rw [hstep] at h
      simpa using h
    have hgoal : c.count ≤ s.limit → c.count ≤ (step s r).2.limit := by
      rw [hstep]
      simp
    exact hgoal (hbound c hmem')

end FixedWindow
