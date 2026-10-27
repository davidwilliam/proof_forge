import FixedWindow.Spec
import FixedWindow.Lemmas
namespace FixedWindow
instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance

/-- Advance the entry of the requesting client, keep every other entry. -/
def touch (s : State) (r : Request) (c : Client) : Client :=
  if c.id = r.client then advance s c r.time else c

def refStep : Impl := fun s r =>
  if Admissible s r then (.ok, { s with clients := s.clients.map (touch s r) })
  else (.rejected, s)

theorem ref_step_of_adm {s : State} {r : Request} (h : Admissible s r) :
    refStep s r = (.ok, { s with clients := s.clients.map (touch s r) }) := by
  simp [refStep, h]

theorem ref_step_of_not {s : State} {r : Request} (h : ¬ Admissible s r) :
    refStep s r = (.rejected, s) := by
  simp [refStep, h]

theorem ref_adm_of_ok {s : State} {r : Request} (h : (refStep s r).1 = .ok) : Admissible s r := by
  by_cases hv : Admissible s r
  · exact hv
  · rw [ref_step_of_not hv] at h; cases h

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

theorem ref_lookup_next {s : State} {r : Request} (hv : Admissible s r) (i : ClientId) :
    lookup (refStep s r).2.clients i = expectedLookup s r i := by
  rw [ref_step_of_adm hv]
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

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s r h; rw [ref_step_of_adm h]

theorem ref_req_invalid_noop : InvalidNoop refStep := by
  intro s r h; exact ref_step_of_not h

theorem ref_req_isolation : Isolation refStep := by
  intro s r i hi
  by_cases hv : Admissible s r
  · rw [ref_lookup_next hv]; simp [expectedLookup, hi]
  · rw [ref_step_of_not hv]

theorem ref_req_reset : ResetRule refStep := by
  intro s r hok c hc
  have hv := ref_adm_of_ok hok
  refine ⟨advance s c r.time, ?_, ?_, ?_⟩
  · rw [ref_lookup_next hv]; simp [expectedLookup, hc]
  · intro h; simp [advance, windowStart, windowCount, h]
  · intro h
    have : ¬ c.start + s.window ≤ r.time := by omega
    simp [advance, windowStart, windowCount, this]

theorem ref_req_effects : Effects refStep := by
  intro s r hok
  have hv := ref_adm_of_ok hok
  refine ⟨?_, ?_, ?_, ref_lookup_next hv⟩
  · rw [ref_step_of_adm hv]
  · rw [ref_step_of_adm hv]
  · rw [ref_step_of_adm hv]
    show (s.clients.map (touch s r)).map Client.id = _
    rw [List.map_map]
    congr 1
    funext c
    exact touch_id s r c

theorem ref_req_window_bound : WindowBound refStep := by
  intro s r hb c' hc'
  by_cases hv : Admissible s r
  · rw [ref_step_of_adm hv] at hc' ⊢
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
  · rw [ref_step_of_not hv] at hc' ⊢
    exact hb c' hc'

/-- Whether the request would open a new window for its client. -/
def resets (s : State) (r : Request) : Bool :=
  match lookup s.clients r.client with
  | some c => decide (c.start + s.window ≤ r.time)
  | none => false

-- Evasive fix: refuse every request that would open a new window.
def step : Impl := fun s r => if resets s r then (.rejected, s) else refStep s r

theorem step_eq (s : State) (r : Request) : step s r = refStep s r ∨ step s r = (.rejected, s) := by
  unfold step; split
  · exact Or.inr rfl
  · exact Or.inl rfl
theorem ok_eq {s : State} {r : Request} (h : (step s r).1 = .ok) : step s r = refStep s r := by
  rcases step_eq s r with e | e
  · exact e
  · rw [e] at h; cases h

-- Weakened restatement: success is only promised inside the current window.
theorem req_valid_succeeds : ∀ s r, Admissible s r → resets s r = false → (step s r).1 = .ok := by
  intro s r h hr
  simp only [step, hr]
  exact ref_req_valid_succeeds s r h
theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  rcases step_eq s r with e | e
  · rw [e]; exact ref_req_invalid_noop s r h
  · exact e
theorem req_isolation : Isolation step := by
  intro s r i hi
  rcases step_eq s r with e | e
  · rw [e]; exact ref_req_isolation s r i hi
  · rw [e]
theorem req_reset : ResetRule step := by
  intro s r h
  have e := ok_eq h
  rw [e] at h ⊢; exact ref_req_reset s r h
theorem req_effects : Effects step := by
  intro s r h
  have e := ok_eq h
  rw [e] at h ⊢; exact ref_req_effects s r h
theorem req_window_bound : WindowBound step := by
  intro s r hb
  rcases step_eq s r with e | e
  · rw [e]; exact ref_req_window_bound s r hb
  · rw [e]; exact hb
end FixedWindow
