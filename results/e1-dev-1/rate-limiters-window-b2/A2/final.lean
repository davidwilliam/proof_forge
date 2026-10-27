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

private theorem adv_id_aux (s : State) (c : Client) (t : Nat) : (advance s c t).id = c.id := by
  simp only [advance]

theorem map_lookup_auxA (f : Client → Client) (hf : ∀ c, (f c).id = c.id) (cs : List Client) (i : ClientId) :
    lookup (cs.map f) i = (lookup cs i).map f := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, lookup_cons]
    by_cases hc : c.id = i
    · simp only [hc, ↓reduceIte]
      have : (f c).id = i := by rw [hf c, hc]
      simp [this]
    · simp only [hc, ↓reduceIte]
      have hfc : ¬ ((f c).id = i) := by rw [hf c]; exact hc
      simp [hfc, ih]

private theorem map_lookup_aux2A (s : State) (r : Request) (cs : List Client) (i : ClientId) (hne : i ≠ r.client) :
    ((lookup cs i).map fun c => if c.id = r.client then advance s c r.time else c) = lookup cs i := by
  cases h : lookup cs i with
  | none => rfl
  | some c =>
    have hid : c.id = i := lookup_id h
    have hcf : ¬ (c.id = r.client) := by rw [hid]; exact hne
    simp [hcf]

theorem req_effects_aux_ids (s : State) (r : Request) :
    (s.clients.map fun c => if c.id = r.client then advance s c r.time else c).map Client.id = s.clients.map Client.id := by
  induction s.clients with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons]
    have hc : (if c.id = r.client then advance s c r.time else c).id = c.id := by
      by_cases h : c.id = r.client
      · simp [h, advance]
      · simp [h]
    rw [hc, ih]

theorem myEffectsEq (s : State) (r : Request) (i : ClientId) (hi : i = r.client) :
    ((lookup s.clients i).map fun c => if c.id = r.client then advance s c r.time else c) = expectedLookup s r i := by
  subst hi
  unfold expectedLookup
  rw [if_pos rfl]
  cases h : lookup s.clients r.client with
  | none => rfl
  | some c =>
    have hid : c.id = r.client := lookup_id h
    simp [hid]

theorem myEffectsFull (s : State) (r : Request) (i : ClientId) :
    lookup (s.clients.map fun c => if c.id = r.client then advance s c r.time else c) i = expectedLookup s r i := by
  have hf : ∀ c : Client, ((if c.id = r.client then advance s c r.time else c)).id = c.id := by
    intro c
    by_cases hc : c.id = r.client
    · simp [hc, advance]
    · simp [hc]
  have e1 : lookup (List.map (fun c => if c.id = r.client then advance s c r.time else c) s.clients) i
    = ((lookup s.clients i).map fun c => if c.id = r.client then advance s c r.time else c) :=
    map_lookup_auxA _ hf s.clients i
  rw [e1]
  by_cases hi : i = r.client
  · exact myEffectsEq s r i hi
  · unfold expectedLookup
    rw [if_neg hi]
    exact map_lookup_aux2A s r s.clients i hi

theorem myAdmOfOk (s : State) (r : Request) (hok : (step s r).1 = .ok) : Admissible s r := by
  by_cases h : Admissible s r
  · exact h
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [h]
    rw [hstep] at hok
    simp at hok

private theorem nodup_lookup_eq_aux : ∀ (l : List Client),
    (l.map Client.id).Nodup →
    ∀ (c : Client), c ∈ l → ∀ (c0 : Client), lookup l c.id = some c0 → c = c0 := by
  intro l
  induction l with
  | nil =>
    intro _ c hc _ _; simp at hc
  | cons x xs ih =>
    intro hNodup c hc c0 hlook
    simp only [List.map_cons] at hNodup
    rw [lookup_cons] at hlook
    by_cases hx : x.id = c.id
    · simp only [hx, ↓reduceIte] at hlook
      -- lookup found x, so c0 = x
      simp at hlook; subst hlook
      -- show c = x using nodup (no dup id in tail)
      have hNotMem : x.id ∉ List.map Client.id xs := by
        have := List.nodup_cons.mp hNodup
        -- List.nodup_cons : Nodup (a::l) ↔ a ∉ l ∧ Nodup l ; need mem version?
        -- Actually Nodup defined via Mem? Use pairwise? Let's use nodup_cons directly
        exact this.1
      -- c ∈ x::xs, either c = x or c ∈ xs
      rcases List.mem_cons.mp hc with rfl | hmem
      · rfl
      · exfalso
        have hmemId : c.id ∈ List.map Client.id xs := List.mem_map.mpr ⟨c, hmem, rfl⟩
        rw [← hx] at hmemId
        exact hNotMem hmemId
    · simp only [hx, ↓reduceIte] at hlook
      have hNodupTail : (List.map Client.id xs).Nodup := (List.nodup_cons.mp hNodup).2
      rcases List.mem_cons.mp hc with rfl | hmem
      · exfalso; exact hx rfl
      · exact ih hNodupTail c hmem c0 hlook

theorem myCountLeAux (s : State) (r : Request) (hAdm : Admissible s r)
    (cOrig : Client) (hmem : cOrig ∈ s.clients) (hid : cOrig.id = r.client) :
    windowCount s cOrig r.time < s.limit := by
  obtain ⟨hNodup, hAdmits⟩ := hAdm
  -- lookup must be some
  cases hL : lookup s.clients r.client with
  | none =>
    unfold Admits at hAdmits
    rw [hL] at hAdmits
    exact False.elim hAdmits
  | some c0 =>
    unfold Admits at hAdmits
    rw [hL] at hAdmits
    obtain ⟨_, hlt0⟩ := hAdmits
    -- show cOrig = c0
    have hid2 : cOrig.id = r.client := hid
    -- need lookup s.clients cOrig.id = some c0
    have hlook2 : lookup s.clients cOrig.id = some c0 := by rw [hid2, hL]
    have heq : cOrig = c0 := nodup_lookup_eq_aux s.clients hNodup cOrig hmem c0 hlook2
    rw [heq]
    exact hlt0

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
    have hf : ∀ c : Client, ((if c.id = r.client then advance s c r.time else c)).id = c.id := by
      intro c
      by_cases hc : c.id = r.client
      · simp only [hc, ↓reduceIte, adv_id_aux]
      · simp [hc]
    have e1 : lookup (List.map (fun c => if c.id = r.client then advance s c r.time else c) s.clients) i
      = ((lookup s.clients i).map fun c => if c.id = r.client then advance s c r.time else c) :=
      map_lookup_auxA _ hf s.clients i
    rw [e1]
    exact map_lookup_aux2A s r s.clients i hne
  · simp [h]

theorem req_reset : ResetRule step := by
  intro s r hok c hc
  by_cases hAdm : Admissible s r
  · have hstep2 : step s r = (.ok, { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c }) := by
      unfold step; simp [hAdm]
    have h2eq : (step s r).2.clients = s.clients.map (fun c => if c.id = r.client then advance s c r.time else c) := by
      rw [hstep2]
    have hid : c.id = r.client := lookup_id hc
    have hf : ∀ c2 : Client, ((if c2.id = r.client then advance s c2 r.time else c2)).id = c2.id := by
      intro c2
      by_cases hc2 : c2.id = r.client
      · simp only [hc2, ↓reduceIte, advance]
      · simp [hc2]
    have e1 : lookup (s.clients.map fun c2 => if c2.id = r.client then advance s c2 r.time else c2) r.client
        = ((lookup s.clients r.client).map fun c2 => if c2.id = r.client then advance s c2 r.time else c2) :=
        map_lookup_auxA _ hf s.clients r.client
    rw [hc] at e1
    have e2 : ((some c).map fun c2 => if c2.id = r.client then advance s c2 r.time else c2) = some (advance s c r.time) := by
      simp [hid]
    rw [e2] at e1
    have hlook : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
      rw [h2eq, e1]
    refine ⟨advance s c r.time, hlook, ?_, ?_⟩
    · intro hle
      unfold advance windowStart windowCount
      simp [hle]
    · intro hlt
      have hle : ¬ (c.start + s.window ≤ r.time) := by omega
      unfold advance windowStart windowCount
      simp [hle]
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hAdm]
    rw [hstep] at hok
    simp at hok

theorem req_effects : Effects step := by
  intro s r hok
  have hAdm : Admissible s r := myAdmOfOk s r hok
  have hstep2 : step s r = (.ok, { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c }) := by
    unfold step; simp [hAdm]
  have h2c : (step s r).2.clients = s.clients.map (fun c => if c.id = r.client then advance s c r.time else c) := by
    rw [hstep2]
  have h2w : (step s r).2.window = s.window := by rw [hstep2]
  have h2l : (step s r).2.limit = s.limit := by rw [hstep2]
  refine ⟨h2w, h2l, ?_, ?_⟩
  · have h : (step s r).2.clients.map Client.id = s.clients.map Client.id := by
      rw [h2c]; exact req_effects_aux_ids s r
    exact h
  · intro i
    rw [h2c]; exact myEffectsFull s r i

theorem req_window_bound : WindowBound step := by
  intro s r hle c' hmem'
  by_cases hAdm : Admissible s r
  · have hstep2 : step s r = (.ok, { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c }) := by
      unfold step; simp [hAdm]
    have h2c : (step s r).2.clients = s.clients.map (fun c => if c.id = r.client then advance s c r.time else c) := by
      rw [hstep2]
    have h2l : (step s r).2.limit = s.limit := by rw [hstep2]
    rw [h2c] at hmem'
    rw [h2l]
    obtain ⟨cOrig, hmemOrig, hEq⟩ := List.mem_map.mp hmem'
    have hOrigLe : cOrig.count ≤ s.limit := hle cOrig hmemOrig
    by_cases hid : cOrig.id = r.client
    · have hAdv : (if cOrig.id = r.client then advance s cOrig r.time else cOrig) = advance s cOrig r.time := by
        simp [hid]
      have hEq2 : advance s cOrig r.time = c' := by
        have := hEq
        simp only [hid, ↓reduceIte] at this
        exact this
      subst hEq2
      simp only [advance]
      have hlt : windowCount s cOrig r.time < s.limit := myCountLeAux s r hAdm cOrig hmemOrig hid
      omega
    · have hEq2 : cOrig = c' := by
        have := hEq
        simp only [hid, ↓reduceIte] at this
        exact this
      subst hEq2
      exact hOrigLe
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hAdm]
    have h2c : (step s r).2.clients = s.clients := by rw [hstep]
    have h2l : (step s r).2.limit = s.limit := by rw [hstep]
    rw [h2c] at hmem'
    rw [h2l]
    exact hle c' hmem'

end FixedWindow
