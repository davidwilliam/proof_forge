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
    (.ok, { window := s.window, limit := s.limit, clients := s.clients.map fun x =>
      if x.id = r.client then
        { id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 }
      else x })
  else (.rejected, s)

private theorem upd_id6 (s : State) (r : Request) (x : Client) :
    (if x.id = r.client then ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client) else x).id = x.id := by
  by_cases h : x.id = r.client <;> simp [h]

private theorem map_lookup_ne6 (s : State) (r : Request) (l : List Client) (i : ClientId) (hi : i ≠ r.client) :
    lookup (l.map fun x => if x.id = r.client then ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client) else x) i = lookup l i := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hxi : x.id = i
    · have hxr : x.id ≠ r.client := fun heq => hi (hxi.symm.trans heq)
      have hhead : (if x.id = r.client then ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client) else x) = x := by simp [hxr]
      have e1 : List.map (fun x => if x.id = r.client then ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client) else x) (x :: xs) = x :: List.map (fun x => if x.id = r.client then ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client) else x) xs := by simp [hhead]
      rw [e1, lookup_cons, lookup_cons, hxi, ih]
    · simp [List.map_cons, lookup_cons, upd_id6, hxi, ih]

private theorem map_lookup_some_aux (s : State) (r : Request) (l : List Client) (c : Client)
    (h : lookup l r.client = some c) :
    lookup (l.map fun x => if x.id = r.client then ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client) else x) r.client =
      some ({ id := c.id, start := windowStart s c r.time, count := windowCount s c r.time + 1 } : Client) := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.map_cons] at ⊢
    rw [lookup_cons]
    have hid : (if x.id = r.client then ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client) else x).id = x.id := by
      by_cases hx : x.id = r.client <;> simp [hx]
    rw [hid]
    rw [lookup_cons] at h
    by_cases hx : x.id = r.client
    · simp [hx] at h
      subst h
      simp [hx]
    · simp [hx] at h ⊢
      exact ih h

private theorem test_nodup_unfold (a : Nat) (l : List Nat) : (List.Nodup (a :: l) → a ∉ l ∧ List.Nodup l) := by
  intro h
  simp [List.nodup_cons] at h
  exact h
#check @List.nodup_cons
#check @List.mem_map

private theorem mem_map_exists {l : List Client} {y : Client} {f : Client → Client} (h : y ∈ List.map f l) : ∃ x ∈ l, f x = y := by
  rw [List.mem_map] at h
  exact h

#check @List.mem_map
#check List.mem_map_of_mem

private theorem nodup_ids_unique_aux2 (l : List Client) : (l.map Client.id).Nodup → ∀ (x y : Client), x ∈ l → y ∈ l → x.id = y.id → x = y := by
  induction l with
  | nil => intro _ x y hx _ _; simp at hx
  | cons z zs ih =>
    intro hN x y hx hy heq
    simp at hx hy
    have hNhead : z.id ∉ zs.map Client.id ∧ (zs.map Client.id).Nodup := by
      simpa [List.nodup_cons] using hN
    rcases hx with rfl | hx2
    · rcases hy with rfl | hy2
      · rfl
      · exfalso
        apply hNhead.1
        have hmem : y.id ∈ zs.map Client.id := by
          apply List.mem_map.mpr
          exact ⟨y, hy2, rfl⟩
        rwa [← heq] at hmem
    · rcases hy with rfl | hy2
      · exfalso
        apply hNhead.1
        have hmem : x.id ∈ zs.map Client.id := by
          apply List.mem_map.mpr
          exact ⟨x, hx2, rfl⟩
        rwa [heq] at hmem
      · exact ih hNhead.2 x y hx2 hy2 heq

private theorem lookup_unique_of_nodup_aux3 (l : List Client) (hN : (l.map Client.id).Nodup)
    (rid : ClientId) (c0 x : Client) (hlook : lookup l rid = some c0) (hmem : x ∈ l) (hxid : x.id = rid) : x = c0 := by
  have hc0mem : c0 ∈ l := lookup_mem hlook
  have hc0id : c0.id = rid := lookup_id hlook
  have heq : x.id = c0.id := by rw [hxid, hc0id]
  exact nodup_ids_unique_aux2 l hN x c0 hmem hc0mem heq

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_isolation      : Isolation step := by
  intro s r i hi
  unfold step
  by_cases h : Admissible s r
  · simp only [h, ↓reduceIte]
    exact map_lookup_ne6 s r s.clients i hi
  · simp [h]

theorem req_reset : ResetRule step := by
  intro s r hok c hc
  have hAdm : Admissible s r := by
    by_cases hNa : Admissible s r
    · exact hNa
    · unfold step at hok
      simp [hNa] at hok
  have hmap : lookup (List.map (fun x => if x.id = r.client then ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client) else x) s.clients) r.client =
      some ({ id := c.id, start := windowStart s c r.time, count := windowCount s c r.time + 1 } : Client) :=
    map_lookup_some_aux s r s.clients c hc
  have hlook : lookup (step s r).2.clients r.client =
      some ({ id := c.id, start := windowStart s c r.time, count := windowCount s c r.time + 1 } : Client) := by
    have hstep : (step s r).2.clients = List.map (fun x => if x.id = r.client then ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client) else x) s.clients := by
      unfold step
      simp [hAdm]
    rw [hstep, hmap]
  refine ⟨{ id := c.id, start := windowStart s c r.time, count := windowCount s c r.time + 1 }, hlook, ?_, ?_⟩
  · intro hexp
    have hs : windowStart s c r.time = r.time := by unfold windowStart; simp [hexp]
    have hcnt : windowCount s c r.time = 0 := by unfold windowCount; simp [hexp]
    constructor
    · simp [hs]
    · simp [hcnt]
  · intro hlt
    have hle : ¬ (c.start + s.window ≤ r.time) := by omega
    have hs : windowStart s c r.time = c.start := by unfold windowStart; simp [hle]
    have hcnt : windowCount s c r.time = c.count := by unfold windowCount; simp [hle]
    constructor
    · simp [hs]
    · simp [hcnt]

theorem req_effects : Effects step := by
  intro s r hok
  have hAdm : Admissible s r := by
    by_cases hNa : Admissible s r
    · exact hNa
    · unfold step at hok
      simp [hNa] at hok
  have hstep : step s r = (.ok, { window := s.window, limit := s.limit, clients := s.clients.map fun x =>
      if x.id = r.client then
        ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client)
      else x }) := by unfold step; simp [hAdm]
  have hwin : (step s r).2.window = s.window := by rw [hstep]
  have hlim : (step s r).2.limit = s.limit := by rw [hstep]
  have hcli : (step s r).2.clients = s.clients.map (fun x =>
      if x.id = r.client then
        ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client)
      else x) := by rw [hstep]
  refine ⟨hwin, hlim, ?_, ?_⟩
  · rw [hcli]
    have hids : ∀ (l : List Client), (l.map (fun x => if x.id = r.client then ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client) else x)).map Client.id = l.map Client.id := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih => simp [upd_id6 s r x, ih]
    exact hids s.clients
  · intro i
    rw [hcli]
    by_cases hi : i = r.client
    · subst hi
      have hex : ∃ c, lookup s.clients r.client = some c := by
        cases hlk : lookup s.clients r.client with
        | none =>
          have hA : Admits s r.time (lookup s.clients r.client) := hAdm.2
          rw [hlk] at hA
          exact False.elim hA
        | some c => exact ⟨c, rfl⟩
      obtain ⟨c, hc⟩ := hex
      have hmap := map_lookup_some_aux s r s.clients c hc
      have hadv : ({ id := c.id, start := windowStart s c r.time, count := windowCount s c r.time + 1 } : Client) = advance s c r.time := by
        unfold advance; simp
      rw [hmap, hadv]
      unfold expectedLookup
      simp [hc]
    · have hne : i ≠ r.client := hi
      have h1 := map_lookup_ne6 s r s.clients i hne
      have h2 : expectedLookup s r i = lookup s.clients i := by unfold expectedLookup; simp [hi]
      rw [h1, h2]

theorem req_window_bound : WindowBound step := by
  intro s r hall c' hmem'
  by_cases hAdm : Admissible s r
  · have hstep : step s r = (.ok, { window := s.window, limit := s.limit, clients := s.clients.map fun x =>
      if x.id = r.client then
        ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client)
      else x }) := by unfold step; simp [hAdm]
    have hcli : (step s r).2.clients = s.clients.map (fun x =>
      if x.id = r.client then
        ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client)
      else x) := by rw [hstep]
    have hlim : (step s r).2.limit = s.limit := by rw [hstep]
    rw [hlim]
    rw [hcli] at hmem'
    have hNodup : (s.clients.map Client.id).Nodup := hAdm.1
    have hAdmits : Admits s r.time (lookup s.clients r.client) := hAdm.2
    cases hlk : lookup s.clients r.client with
    | none =>
      rw [hlk] at hAdmits
      simp [Admits] at hAdmits
    | some c0 =>
      rw [hlk] at hAdmits
      obtain ⟨hle, hlt⟩ := hAdmits
      rw [List.mem_map] at hmem'
      obtain ⟨x, hxmem, hfx⟩ := hmem'
      by_cases hxr : x.id = r.client
      · have hxeq : x = c0 := lookup_unique_of_nodup_aux3 s.clients hNodup r.client c0 x hlk hxmem hxr
        have hxr0 : c0.id = r.client := hxeq ▸ hxr
        have hfx0 : (({ id := c0.id, start := windowStart s c0 r.time, count := windowCount s c0 r.time + 1 } : Client)) = c' := by
          have h1 : (if x.id = r.client then ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client) else x) = c' := hfx
          rw [hxeq] at h1
          simpa [hxr0] using h1
        rw [← hfx0]
        show windowCount s c0 r.time + 1 ≤ s.limit
        omega
      · have hfxeq : (if x.id = r.client then ({ id := x.id, start := windowStart s x r.time, count := windowCount s x r.time + 1 } : Client) else x) = x := by simp [hxr]
        rw [hfxeq] at hfx
        subst hfx
        exact hall x hxmem
  · have hstep2 : step s r = (.rejected, s) := by unfold step; simp [hAdm]
    have hcli2 : (step s r).2.clients = s.clients := by rw [hstep2]
    have hlim2 : (step s r).2.limit = s.limit := by rw [hstep2]
    rw [hlim2]
    rw [hcli2] at hmem'
    exact hall c' hmem'

end FixedWindow
