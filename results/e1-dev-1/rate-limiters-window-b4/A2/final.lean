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

theorem adv_id (s : State) (c : Client) (t : Nat) : (advance s c t).id = c.id := rfl

theorem iso_map_aux2 (s : State) (r : Request) (l : List Client) (i : ClientId) (h : i ≠ r.client) :
    lookup (l.map fun c => if c.id = r.client then advance s c r.time else c) i = lookup l i := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, lookup_cons]
    have hfid : (if x.id = r.client then advance s x r.time else x).id = x.id := by
      by_cases hx : x.id = r.client
      · simp only [hx, ↓reduceIte, adv_id]
      · simp only [hx, ↓reduceIte]
    rw [hfid]
    by_cases hx : x.id = i
    · simp only [hx, ↓reduceIte] at ih ⊢
      simp only [h, ↓reduceIte] at ⊢
    · simp only [hx, ↓reduceIte, ih]

theorem lookup_map_preserve_aux4 (F : Client → Client) (hF : ∀ c, (F c).id = c.id)
    (l : List Client) (i : ClientId) :
    lookup (l.map F) i = (lookup l i).map F := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, lookup_cons, hF]
    by_cases hx : x.id = i
    · simp [hx]
    · simp [hx, ih]

theorem req_reset_thm : ResetRule step := by
  intro s r h_ok c h_lookup
  have hAdm : Admissible s r := by
    unfold step at h_ok
    by_cases hA : Admissible s r
    · exact hA
    · simp only [hA, ↓reduceIte] at h_ok
      have hne : Outcome.rejected ≠ Outcome.ok := by decide
      contradiction
  have hcid : c.id = r.client := lookup_id h_lookup
  have hF : ∀ c0 : Client, ((if c0.id = r.client then advance s c0 r.time else c0)).id = c0.id := by
    intro c0
    by_cases hh : c0.id = r.client <;> simp [hh, adv_id]
  have hmap : lookup (s.clients.map fun c0 => if c0.id = r.client then advance s c0 r.time else c0) r.client
      = (lookup s.clients r.client).map (fun c0 => if c0.id = r.client then advance s c0 r.time else c0) :=
    lookup_map_preserve_aux4 _ hF _ _
  have hstep2 : (step s r).2.clients = s.clients.map fun c0 => if c0.id = r.client then advance s c0 r.time else c0 := by
    unfold step
    simp only [hAdm, ↓reduceIte]
  rw [hstep2, hmap, h_lookup]
  simp only [Option.map_some] at ⊢
  have hFc : (if c.id = r.client then advance s c r.time else c) = advance s c r.time := by
    simp [hcid]
  rw [hFc]
  exact ⟨advance s c r.time, rfl, by
    intro hexp
    unfold advance windowStart windowCount
    simp [hexp],
    by
    intro hlt
    have hne : ¬ (c.start + s.window ≤ r.time) := by omega
    unfold advance windowStart windowCount
    simp [hne]⟩

theorem nodup_lookup_unique_aux7 : ∀ (l : List Client), (l.map Client.id).Nodup →
    ∀ (i : ClientId) (c1 : Client), lookup l i = some c1 →
    ∀ (c2 : Client), c2 ∈ l → c2.id = i → c2 = c1 := by
  intro l
  induction l with
  | nil =>
    intro hN i c1 h1 c2 h2 hid
    simp at h1
  | cons x xs ih =>
    intro hN i c1 h1 c2 h2 hid
    simp only [List.map_cons, List.nodup_cons] at hN
    obtain ⟨hNotMem, hTailNodup⟩ := hN
    rw [lookup_cons] at h1
    by_cases hx : x.id = i
    · simp only [hx, ↓reduceIte, Option.some_inj] at h1
      subst h1
      simp at h2
      rcases h2 with rfl | hmem
      · rfl
      · exfalso
        apply hNotMem
        rw [List.mem_map]
        exact ⟨c2, hmem, hid.trans hx.symm⟩
    · simp only [hx, ↓reduceIte] at h1
      simp at h2
      rcases h2 with rfl | hmem
      · simp [hx] at hid
      · exact ih hTailNodup i c1 h1 c2 hmem hid

theorem tmp_hstep_test (s : State) (r : Request) (hA : Admissible s r) :
    step s r = (.ok, { s with clients := s.clients.map fun c0 => if c0.id = r.client then advance s c0 r.time else c0 }) := by
  unfold step
  simp only [hA, ↓reduceIte]

theorem tmp_wb2 : WindowBound step := by
  intro s r hbound c hmem
  by_cases hA : Admissible s r
  · have hstep := tmp_hstep_test s r hA
    have hmem2 : c ∈ s.clients.map (fun c0 => if c0.id = r.client then advance s c0 r.time else c0) := by
      have h1 : (step s r).2.clients = s.clients.map (fun c0 => if c0.id = r.client then advance s c0 r.time else c0) := by
        rw [hstep]
      rw [h1] at hmem
      exact hmem
    have hlim2 : (step s r).2.limit = s.limit := by rw [hstep]
    rw [hlim2]
    obtain ⟨hNodup, hAdmits⟩ := hA
    cases hlook : lookup s.clients r.client with
    | none =>
      have hAd : Admits s r.time (lookup s.clients r.client) := hAdmits
      rw [hlook] at hAd
      exact False.elim hAd
    | some cstar =>
      have hAdmC : cstar.start ≤ r.time ∧ windowCount s cstar r.time < s.limit := by
        have hAd : Admits s r.time (lookup s.clients r.client) := hAdmits
        rw [hlook] at hAd
        exact hAd
      obtain ⟨hwle, hwlt⟩ := hAdmC
      rw [List.mem_map] at hmem2
      obtain ⟨c0, hc0mem, hFc⟩ := hmem2
      by_cases heq : c0.id = r.client
      · have hFceq : (if c0.id = r.client then advance s c0 r.time else c0) = advance s c0 r.time := by
          simp [heq]
        have hc_eq : c = advance s c0 r.time := by rw [← hFc, hFceq]
        have hc0_eq : c0 = cstar :=
          nodup_lookup_unique_aux7 s.clients hNodup r.client cstar hlook c0 hc0mem heq
        have hc_eq2 : c = advance s cstar r.time := by rw [hc_eq, hc0_eq]
        rw [hc_eq2]
        show (advance s cstar r.time).count ≤ s.limit
        have hwlt0 : (windowCount s cstar r.time) < s.limit := hwlt
        unfold windowCount at hwlt0
        unfold advance
        simp only
        by_cases hexp : cstar.start + s.window ≤ r.time
        · simp [hexp] at hwlt0 ⊢
          omega
        · simp [hexp] at hwlt0 ⊢
          omega
      · have hFceq : (if c0.id = r.client then advance s c0 r.time else c0) = c0 := by
          simp [heq]
        have hc_eq : c = c0 := by rw [← hFc, hFceq]
        rw [hc_eq]
        exact hbound c0 hc0mem
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hA]
    have hmem2 : c ∈ s.clients := by
      have h1 : (step s r).2.clients = s.clients := by rw [hstep]
      rw [h1] at hmem
      exact hmem
    have hlim2 : (step s r).2.limit = s.limit := by rw [hstep]
    rw [hlim2]
    exact hbound c hmem2

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_isolation : Isolation step := by
  intro s r i hi
  unfold step
  by_cases h : Admissible s r
  · simp only [h, ↓reduceIte]
    exact iso_map_aux2 s r s.clients i hi
  · simp only [h, ↓reduceIte]

theorem req_reset : ResetRule step := req_reset_thm

theorem req_effects : Effects step := by
  intro s r h_ok
  have hAdm : Admissible s r := by
    unfold step at h_ok
    by_cases hA : Admissible s r
    · exact hA
    · simp only [hA, ↓reduceIte] at h_ok
      have hne : Outcome.rejected ≠ Outcome.ok := by decide
      contradiction
  have hstep : step s r = (.ok, { s with clients := s.clients.map fun c0 => if c0.id = r.client then advance s c0 r.time else c0 }) := by
    unfold step
    simp only [hAdm, ↓reduceIte]
  have hclients : (step s r).2.clients = s.clients.map (fun c0 => if c0.id = r.client then advance s c0 r.time else c0) := by
    rw [hstep]
  have hwindow : (step s r).2.window = s.window := by rw [hstep]
  have hlimit : (step s r).2.limit = s.limit := by rw [hstep]
  refine ⟨hwindow, hlimit, ?_, ?_⟩
  · rw [hclients]
    have hFid : ∀ c0 : Client, (if c0.id = r.client then advance s c0 r.time else c0).id = c0.id := by
      intro c0
      by_cases hh : c0.id = r.client <;> simp [hh, adv_id]
    have : (s.clients.map (fun c0 => if c0.id = r.client then advance s c0 r.time else c0)).map Client.id = s.clients.map Client.id := by
      induction s.clients with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.map_cons]
        rw [hFid x]
        rw [ih]
    exact this
  · intro i
    rw [hclients]
    have hF : ∀ c0 : Client, ((if c0.id = r.client then advance s c0 r.time else c0)).id = c0.id := by
      intro c0
      by_cases hh : c0.id = r.client <;> simp [hh, adv_id]
    have hmap := lookup_map_preserve_aux4 (fun c0 => if c0.id = r.client then advance s c0 r.time else c0) hF s.clients i
    rw [hmap]
    unfold expectedLookup
    by_cases hi : i = r.client
    · subst hi
      simp only [↓reduceIte]
      cases hlook : lookup s.clients r.client with
      | none => rfl
      | some cstar =>
        simp only [Option.map_some]
        have hcid : cstar.id = r.client := lookup_id hlook
        have hFstar : (if cstar.id = r.client then advance s cstar r.time else cstar) = advance s cstar r.time := by
          simp [hcid]
        rw [hFstar]
    · simp only [hi, ↓reduceIte]
      cases hlook : lookup s.clients i with
      | none => rfl
      | some cstar =>
        simp only [Option.map_some]
        have hcid : cstar.id = i := lookup_id hlook
        have hFstar : (if cstar.id = r.client then advance s cstar r.time else cstar) = cstar := by
          simp [hcid, hi]
        rw [hFstar]

theorem req_window_bound : WindowBound step := tmp_wb2

end FixedWindow
