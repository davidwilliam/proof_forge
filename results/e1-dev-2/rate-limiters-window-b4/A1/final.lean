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

theorem iso_map_lookup_aux2 (r : Request) (f : Client → Client)
    (h_id : ∀ c, (f c).id = c.id) (h_other : ∀ c, c.id ≠ r.client → f c = c)
    (l : List Client) (i : ClientId) (hne : i ≠ r.client) :
    lookup (l.map f) i = lookup l i := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, lookup_cons, h_id c]
    by_cases hc : c.id = i
    · simp only [hc, ↓reduceIte]
      have hcc : c.id ≠ r.client := by intro hcon; apply hne; rw [← hc, hcon]
      have hfc : f c = c := h_other c hcc
      rw [hfc]
    · simp only [hc, ↓reduceIte, ih]

theorem iso_f_id_aux2 (s : State) (r : Request) (c : Client) :
    ((if c.id = r.client then advance s c r.time else c)).id = c.id := by
  by_cases h : c.id = r.client <;> simp [h, advance]

theorem iso_f_other_aux2 (s : State) (r : Request) (c : Client) (h : c.id ≠ r.client) :
    (if c.id = r.client then advance s c r.time else c) = c := by
  simp [h]

theorem lookup_map_advance_aux (s : State) (r : Request) (l : List Client) :
    lookup (l.map (fun c => if c.id = r.client then advance s c r.time else c)) r.client
      = (lookup l r.client).map (fun c => advance s c r.time) := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have hid : (if c.id = r.client then advance s c r.time else c).id = c.id := by
      by_cases hh : c.id = r.client <;> simp [hh, advance]
    simp only [List.map_cons]
    rw [lookup_cons _ _ r.client, lookup_cons _ _ r.client, hid]
    by_cases h : c.id = r.client
    · simp [h]
    · simp [h, ih]

theorem map_id_eq_aux (r : Request) (s : State) (l : List Client) :
    ((l.map (fun c => if c.id = r.client then advance s c r.time else c)).map Client.id) = l.map Client.id := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons]
    have hid : (if c.id = r.client then advance s c r.time else c).id = c.id := by
      by_cases hh : c.id = r.client <;> simp [hh, advance]
    rw [hid, ih]

theorem nodup_mem_eq_try2 (l : List Client) : (l.map Client.id).Nodup → ∀ {a b : Client}, a ∈ l → b ∈ l → a.id = b.id → a = b := by
  induction l with
  | nil => intro _ a b ha _ _; simp at ha
  | cons x xs ih =>
    intro hnd a b ha hb hab
    simp at ha hb
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hndt⟩ := hnd
    rcases ha with rfl | ha2
    · rcases hb with rfl | hb2
      · rfl
      · exfalso
        apply hnotin
        exact List.mem_map.mpr ⟨b, hb2, hab.symm⟩
    · rcases hb with rfl | hb2
      · exfalso
        apply hnotin
        exact List.mem_map.mpr ⟨a, ha2, hab⟩
      · exact ih hndt ha2 hb2 hab

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
  by_cases hAdm : Admissible s r
  · simp only [hAdm, ↓reduceIte]
    exact iso_map_lookup_aux2 r (fun c => if c.id = r.client then advance s c r.time else c) (iso_f_id_aux2 s r) (iso_f_other_aux2 s r) s.clients i hne
  · simp [hAdm]

theorem req_reset : ResetRule step := by
  intro s r hok c hc
  have hAdm : Admissible s r := by
    by_cases hN : Admissible s r
    · exact hN
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        simp [hN]
      rw [hstep] at hok
      simp at hok
  have hmap : (step s r).2.clients = s.clients.map (fun c => if c.id = r.client then advance s c r.time else c) := by
    unfold step
    simp [hAdm]
  have hlook : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
    rw [hmap, lookup_map_advance_aux, hc, Option.map_some]
  refine ⟨advance s c r.time, hlook, ?_, ?_⟩
  · intro hexp
    unfold advance windowStart windowCount
    simp [hexp]
  · intro hlt
    have hnot : ¬ (c.start + s.window ≤ r.time) := by omega
    unfold advance windowStart windowCount
    simp [hnot]

theorem req_effects : Effects step := by
  intro s r hok
  have hAdm : Admissible s r := by
    by_cases hN : Admissible s r
    · exact hN
    · have hstep : step s r = (.rejected, s) := by unfold step; simp [hN]
      rw [hstep] at hok
      simp at hok
  have hstep_eq : step s r = (.ok, { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c }) := by
    unfold step; simp [hAdm]
  have h2 : (step s r).2 = { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c } := by
    rw [hstep_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h2]
  · rw [h2]
  · rw [h2]; simp only
    exact map_id_eq_aux r s s.clients
  · intro i
    rw [h2]
    simp only
    unfold expectedLookup
    by_cases heq : i = r.client
    · simp [heq, lookup_map_advance_aux]
    · simp [heq]
      exact iso_map_lookup_aux2 r (fun c => if c.id = r.client then advance s c r.time else c) (iso_f_id_aux2 s r) (iso_f_other_aux2 s r) s.clients i heq

theorem req_window_bound : WindowBound step := by
  intro s r hbound c' hmem'
  by_cases hAdm : Admissible s r
  · have hstep_eq : step s r = (.ok, { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c }) := by
      unfold step; simp [hAdm]
    have h2 : (step s r).2 = { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c } := by
      rw [hstep_eq]
    rw [h2] at hmem' ⊢
    simp only at hmem' ⊢
    obtain ⟨c, hc_mem, hc_eq⟩ := List.mem_map.mp hmem'
    have hc_le : c.count ≤ s.limit := hbound c hc_mem
    obtain ⟨hNodup, hAdmits⟩ := hAdm
    cases hL : lookup s.clients r.client with
    | none =>
      rw [hL] at hAdmits
      exact False.elim hAdmits
    | some c0 =>
      rw [hL] at hAdmits
      obtain ⟨hle, hlt⟩ := hAdmits
      have hMem0 : c0 ∈ s.clients := lookup_mem hL
      have hId0 : c0.id = r.client := lookup_id hL
      by_cases hc_id : c.id = r.client
      · have hc_eq_adv : (advance s c r.time) = c' := by simpa [hc_id] using hc_eq
        have heq : c = c0 :=
          nodup_mem_eq_try2 s.clients hNodup hc_mem hMem0 (hc_id.trans hId0.symm)
        have hlt_c : windowCount s c r.time < s.limit := by rw [heq]; exact hlt
        have hcnt : (advance s c r.time).count = windowCount s c r.time + 1 := rfl
        rw [← hc_eq_adv, hcnt]
        omega
      · have hc_eq_c : c = c' := by simpa [hc_id] using hc_eq
        rw [← hc_eq_c]
        exact hc_le
  · have hstep_neg : step s r = (.rejected, s) := by unfold step; simp [hAdm]
    have h2neg : (step s r).2 = s := by rw [hstep_neg]
    rw [h2neg] at hmem' ⊢
    exact hbound c' hmem'

end FixedWindow
