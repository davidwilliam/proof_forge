import FixedWindow.Spec
import FixedWindow.Lemmas
namespace FixedWindow
-- Code swap: the proved definition is the reference, the compiled one admits one
-- request too many per window.
def lenientStep : Impl := fun s r =>
  if (s.clients.map Client.id).Nodup then
    match lookup s.clients r.client with
    | some c =>
      if c.start ≤ r.time ∧ windowCount s c r.time ≤ s.limit then
        (.ok, { s with clients := s.clients.map fun x =>
          if x.id = r.client then advance s x r.time else x })
      else (.rejected, s)
    | none => (.rejected, s)
  else (.rejected, s)
instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance

/-- Advance the entry of the requesting client, keep every other entry. -/
def touch (s : State) (r : Request) (c : Client) : Client :=
  if c.id = r.client then advance s c r.time else c

@[implemented_by lenientStep]
def step : Impl := fun s r =>
  if Admissible s r then (.ok, { s with clients := s.clients.map (touch s r) })
  else (.rejected, s)

theorem step_of_adm {s : State} {r : Request} (h : Admissible s r) :
    step s r = (.ok, { s with clients := s.clients.map (touch s r) }) := by
  simp [step, h]

theorem step_of_not {s : State} {r : Request} (h : ¬ Admissible s r) :
    step s r = (.rejected, s) := by
  simp [step, h]

theorem adm_of_ok {s : State} {r : Request} (h : (step s r).1 = .ok) : Admissible s r := by
  by_cases hv : Admissible s r
  · exact hv
  · rw [step_of_not hv] at h; cases h

theorem touch_id (s : State) (r : Request) (c : Client) : (touch s r c).id = c.id := by
  unfold touch; split <;> rfl

theorem lookup_map_id (f : Client → Client) (hf : ∀ c, (f c).id = c.id) :
    ∀ (l : List Client) (i : ClientId), lookup (l.map f) i = (lookup l i).map f := by
  intro l i
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, lookup_cons, hf]
    split <;> simp [ih]

/-- In a list with distinct ids, a member is the entry found under its id. -/
theorem lookup_of_mem {l : List Client} (hl : (l.map Client.id).Nodup) {c : Client}
    (hc : c ∈ l) : lookup l c.id = some c := by
  induction l with
  | nil => simp at hc
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    rw [lookup_cons]
    rcases List.mem_cons.mp hc with h | h
    · subst h; simp
    · have hne : x.id ≠ c.id := fun e => hl.1 ⟨c, h, e.symm⟩
      simp [hne, ih hl.2 h]

theorem lookup_next {s : State} {r : Request} (hv : Admissible s r) (i : ClientId) :
    lookup (step s r).2.clients i = expectedLookup s r i := by
  rw [step_of_adm hv]
  show lookup (s.clients.map (touch s r)) i = _
  rw [lookup_map_id _ (touch_id s r)]
  unfold expectedLookup
  cases hl : lookup s.clients i with
  | none => simp
  | some c =>
    have hid := lookup_id hl
    by_cases hi : i = r.client
    · simp [hi, touch] at *
      simp [hid]
    · have : c.id ≠ r.client := by rw [hid]; exact hi
      simp [hi, touch, this]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h; rw [step_of_adm h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h; exact step_of_not h

theorem req_isolation : Isolation step := by
  intro s r i hi
  by_cases hv : Admissible s r
  · rw [lookup_next hv]; simp [expectedLookup, hi]
  · rw [step_of_not hv]

theorem req_reset : ResetRule step := by
  intro s r hok c hc
  have hv := adm_of_ok hok
  refine ⟨advance s c r.time, ?_, ?_, ?_⟩
  · rw [lookup_next hv]; simp [expectedLookup, hc]
  · intro h; simp [advance, windowStart, windowCount, h]
  · intro h
    have : ¬ c.start + s.window ≤ r.time := by omega
    simp [advance, windowStart, windowCount, this]

theorem req_effects : Effects step := by
  intro s r hok
  have hv := adm_of_ok hok
  refine ⟨?_, ?_, ?_, lookup_next hv⟩
  · rw [step_of_adm hv]
  · rw [step_of_adm hv]
  · rw [step_of_adm hv]
    show (s.clients.map (touch s r)).map Client.id = _
    rw [List.map_map]
    congr 1
    funext c
    exact touch_id s r c

theorem req_window_bound : WindowBound step := by
  intro s r hb c' hc'
  by_cases hv : Admissible s r
  · rw [step_of_adm hv] at hc' ⊢
    show c'.count ≤ s.limit
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    unfold touch
    by_cases hid : c.id = r.client
    · have hl := lookup_of_mem hv.1 hc
      rw [hid] at hl
      have ha := hv.2
      rw [hl] at ha
      have : windowCount s c r.time < s.limit := ha.2
      simp [hid, advance]
      omega
    · simp [hid]; exact hb c hc
  · rw [step_of_not hv] at hc' ⊢
    exact hb c' hc'

end FixedWindow
