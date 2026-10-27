import FixedWindow.Spec
import FixedWindow.Lemmas
namespace FixedWindow

instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance

def upd (s : State) (r : Request) (c : Client) : Client :=
  if c.id = r.client then advance s c r.time else c

def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with clients := s.clients.map (upd s r) })
  else (.rejected, s)

theorem upd_id (s : State) (r : Request) (c : Client) : (upd s r c).id = c.id := by
  unfold upd advance
  by_cases h : c.id = r.client <;> simp [h]

theorem upd_adv (s : State) (r : Request) (c : Client) (h : c.id = r.client) :
    upd s r c = advance s c r.time := by
  unfold upd
  simp [h]

theorem upd_self (s : State) (r : Request) (c : Client) (h : c.id ≠ r.client) :
    upd s r c = c := by
  unfold upd
  simp [h]

theorem map_ids_upd (l : List Client) (s : State) (r : Request) :
    (l.map (upd s r)).map Client.id = l.map Client.id := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, upd_id, ih]

theorem lookup_upd_other (l : List Client) (i : ClientId) (s : State) (r : Request)
    (hne : i ≠ r.client) :
    lookup (l.map (upd s r)) i = lookup l i := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [lookup_cons, lookup_cons]
    have hid : (upd s r x).id = x.id := upd_id s r x
    rw [hid]
    by_cases hx : x.id = i
    · simp [hx]
      have hxne : x.id ≠ r.client := by
        intro heq
        apply hne
        rw [← hx, heq]
      have hupd : upd s r x = x := upd_self s r x hxne
      rw [hupd]
    · simp [hx, ih]

theorem lookup_upd_self (l : List Client) (s : State) (r : Request) :
    lookup (l.map (upd s r)) r.client =
      (lookup l r.client).map (fun c => advance s c r.time) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [lookup_cons, lookup_cons]
    have hid : (upd s r x).id = x.id := upd_id s r x
    rw [hid]
    by_cases hx : x.id = r.client
    · simp [hx]
      have hupd : upd s r x = advance s x r.time := upd_adv s r x hx
      rw [hupd]
    · simp [hx, ih]

theorem lookup_upd (s : State) (r : Request) (i : ClientId) :
    lookup (s.clients.map (upd s r)) i = expectedLookup s r i := by
  unfold expectedLookup
  by_cases h : i = r.client
  · simp [h, lookup_upd_self]
  · simp [h, lookup_upd_other s.clients i s r h]

theorem lookup_of_mem_nodup (l : List Client) (c : Client)
    (hmem : c ∈ l) (hnd : (l.map Client.id).Nodup) :
    lookup l c.id = some c := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    simp only [List.map_cons] at hnd
    rw [List.nodup_cons] at hnd
    obtain ⟨hnot, htail⟩ := hnd
    rw [lookup_cons]
    by_cases hx : x.id = c.id
    · have hcx : x = c := by
        rcases List.mem_cons.mp hmem with rfl | hmem2
        · rfl
        · exfalso
          rw [hx] at hnot
          exact hnot (List.mem_map.mpr ⟨c, hmem2, rfl⟩)
      subst hcx
      simp
    · have hne : c ≠ x := by
        intro heq
        apply hx
        rw [heq]
      have hmem2 : c ∈ xs := (List.mem_cons.mp hmem).resolve_left hne
      simp [hx]
      exact ih hmem2 htail

theorem advance_bound (s : State) (r : Request) (c : Client)
    (hadm : Admits s r.time (lookup s.clients r.client))
    (hl : lookup s.clients r.client = some c) :
    (advance s c r.time).count ≤ s.limit := by
  rw [hl] at hadm
  obtain ⟨hle, hlt⟩ := hadm
  by_cases hexp : c.start + s.window ≤ r.time
  · have hwc : windowCount s c r.time = 0 := by
      unfold windowCount
      simp [hexp]
    have hlt0 : windowCount s c r.time < s.limit := hlt
    rw [hwc] at hlt0
    unfold advance
    simp [windowCount, hexp]
    omega
  · have hwc : windowCount s c r.time = c.count := by
      unfold windowCount
      simp [hexp]
    have hlt1 : windowCount s c r.time < s.limit := hlt
    rw [hwc] at hlt1
    unfold advance
    simp [windowCount, hexp]
    omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_isolation : Isolation step := by
  intro s r i hne
  by_cases h : Admissible s r
  · have hclients : (step s r).2.clients = s.clients.map (upd s r) := by
      simp [step, h]
    rw [hclients]
    exact lookup_upd_other s.clients i s r hne
  · have hstep : step s r = (.rejected, s) := by simp [step, h]
    have hclients : (step s r).2.clients = s.clients := by rw [hstep]
    rw [hclients]

theorem req_effects : Effects step := by
  intro s r hok
  by_cases h : Admissible s r
  · have hstep : step s r = (.ok, { s with clients := s.clients.map (upd s r) }) := by
      simp [step, h]
    have hclients : (step s r).2.clients = s.clients.map (upd s r) := by rw [hstep]
    have hwin : (step s r).2.window = s.window := by rw [hstep]
    have hlim : (step s r).2.limit = s.limit := by rw [hstep]
    refine ⟨hwin, hlim, ?_, ?_⟩
    · have hmap : (step s r).2.clients.map Client.id = s.clients.map Client.id := by
        rw [hclients]
        exact map_ids_upd s.clients s r
      exact hmap
    · intro i
      rw [hclients]
      exact lookup_upd s r i
  · have hstep : step s r = (.rejected, s) := by simp [step, h]
    rw [hstep] at hok
    simp at hok

theorem req_reset : ResetRule step := by
  intro s r hok c hlook
  by_cases h : Admissible s r
  · have hstep : step s r = (.ok, { s with clients := s.clients.map (upd s r) }) := by
      simp [step, h]
    have hclients : (step s r).2.clients = s.clients.map (upd s r) := by rw [hstep]
    have hafter : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
      simp [hclients, lookup_upd_self, hlook]
    refine ⟨advance s c r.time, hafter, ?_, ?_⟩
    · intro hexp
      constructor
      · show (advance s c r.time).start = r.time
        unfold advance windowStart
        simp [hexp]
      · show (advance s c r.time).count = 1
        unfold advance windowCount
        simp [hexp]
    · intro hlt
      have hnge : ¬ c.start + s.window ≤ r.time := by omega
      constructor
      · show (advance s c r.time).start = c.start
        unfold advance windowStart
        simp [hnge]
      · show (advance s c r.time).count = c.count + 1
        unfold advance windowCount
        simp [hnge]
  · have hstep : step s r = (.rejected, s) := by simp [step, h]
    rw [hstep] at hok
    simp at hok

theorem req_window_bound : WindowBound step := by
  intro s r hbound c' hmem'
  by_cases h : Admissible s r
  · have hstep : step s r = (.ok, { s with clients := s.clients.map (upd s r) }) := by
      simp [step, h]
    have hlim : (step s r).2.limit = s.limit := by rw [hstep]
    rw [hlim]
    have hclients : (step s r).2.clients = s.clients.map (upd s r) := by rw [hstep]
    rw [hclients] at hmem'
    obtain ⟨c, hcmem, rfl⟩ := List.mem_map.mp hmem'
    obtain ⟨hnd, hadm⟩ := h
    by_cases heq : c.id = r.client
    · have hupd : upd s r c = advance s c r.time := upd_adv s r c heq
      rw [hupd]
      have hlook : lookup s.clients r.client = some c := by
        have h1 : lookup s.clients c.id = some c :=
          lookup_of_mem_nodup s.clients c hcmem hnd
        rw [heq] at h1
        exact h1
      exact advance_bound s r c hadm hlook
    · have hupd : upd s r c = c := upd_self s r c heq
      rw [hupd]
      exact hbound c hcmem
  · have hstep : step s r = (.rejected, s) := by simp [step, h]
    have hlim : (step s r).2.limit = s.limit := by rw [hstep]
    rw [hlim]
    have hclients : (step s r).2.clients = s.clients := by rw [hstep]
    rw [hclients] at hmem'
    exact hbound c' hmem'

end FixedWindow
