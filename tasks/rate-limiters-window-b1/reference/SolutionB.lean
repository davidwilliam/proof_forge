import FixedWindow.Spec
import FixedWindow.Lemmas
/-!
# Reference solution B (hidden from agents)

One recursive pass finds the client, checks the window and rewrites the entry, failing
with `none` when the request must be rejected.
-/

namespace FixedWindow

/-- Rewrite the first entry with id `r.client`, or `none` if it is missing or refuses. -/
def tryBump (w lim : Nat) (r : Request) : List Client → Option (List Client)
  | [] => none
  | c :: cs =>
    if c.id = r.client then
      if r.time < c.start then none
      else if c.start + w ≤ r.time then
        if 0 < lim then some (⟨c.id, r.time, 1⟩ :: cs) else none
      else if c.count < lim then some (⟨c.id, c.start, c.count + 1⟩ :: cs) else none
    else (tryBump w lim r cs).map (c :: ·)

def distinctIds : List Client → Bool
  | [] => true
  | c :: cs => !(cs.any (·.id == c.id)) && distinctIds cs

def step : Impl := fun s r =>
  if distinctIds s.clients then
    match tryBump s.window s.limit r s.clients with
    | some l => (.ok, ⟨s.window, s.limit, l⟩)
    | none => (.rejected, s)
  else (.rejected, s)

theorem distinctIds_iff (l : List Client) : distinctIds l = true ↔ (l.map Client.id).Nodup := by
  induction l with
  | nil => simp [distinctIds]
  | cons c cs ih =>
    simp only [distinctIds, Bool.and_eq_true, Bool.not_eq_true', List.map_cons, List.nodup_cons, ih]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      intro hm
      obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
      have : cs.any (·.id == c.id) = true := List.any_eq_true.mpr ⟨x, hx, by simp [he]⟩
      rw [this] at h1; cases h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      cases h : cs.any (·.id == c.id) with
      | false => rfl
      | true =>
        obtain ⟨x, hx, he⟩ := List.any_eq_true.mp h
        exact absurd (List.mem_map.mpr ⟨x, hx, by simpa using he⟩) h1

/-- `tryBump` succeeds exactly on admitted entries, and then advances that entry. -/
theorem tryBump_spec (s : State) (r : Request) : ∀ l : List Client,
    (Admits s r.time (lookup l r.client) →
      ∃ l', tryBump s.window s.limit r l = some l' ∧
        l'.map Client.id = l.map Client.id ∧
        ∀ i, lookup l' i = if i = r.client then (lookup l i).map (fun c => advance s c r.time)
                           else lookup l i) ∧
    (¬ Admits s r.time (lookup l r.client) → tryBump s.window s.limit r l = none) := by
  intro l
  induction l with
  | nil => exact ⟨fun h => h.elim, fun _ => rfl⟩
  | cons c cs ih =>
    by_cases hc : c.id = r.client
    · have hl : lookup (c :: cs) r.client = some c := by simp [lookup_cons, hc]
      rw [hl]
      have key : ∀ i, lookup (advance s c r.time :: cs) i
          = if i = r.client then (lookup (c :: cs) i).map (fun c => advance s c r.time)
            else lookup (c :: cs) i := by
        intro i
        by_cases hi : i = r.client
        · subst hi; simp [lookup_cons, advance, hc]
        · have : c.id ≠ i := fun e => hi (e ▸ hc)
          simp [lookup_cons, advance, hi, this]
      unfold Admits
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨advance s c r.time :: cs, ?_, by simp [advance], key⟩
        have n1 : ¬ r.time < c.start := by omega
        unfold windowCount at h2
        by_cases he : c.start + s.window ≤ r.time
        · simp [he] at h2
          simp [tryBump, hc, n1, he, h2, advance, windowStart, windowCount]
        · simp [he] at h2
          simp [tryBump, hc, n1, he, h2, advance, windowStart, windowCount]
      · intro h
        simp only [tryBump, hc, ite_true]
        unfold windowCount at h
        by_cases n1 : r.time < c.start
        · simp [n1]
        · by_cases he : c.start + s.window ≤ r.time
          · have : ¬ 0 < s.limit := fun hp => h ⟨by omega, by simp [he]; exact hp⟩
            simp [n1, he, this]
          · have : ¬ c.count < s.limit := fun hp => h ⟨by omega, by simp [he]; exact hp⟩
            simp [n1, he, this]
    · have hl : lookup (c :: cs) r.client = lookup cs r.client := by simp [lookup_cons, hc]
      rw [hl]
      obtain ⟨ih1, ih2⟩ := ih
      constructor
      · intro h
        obtain ⟨l', h1, h2, h3⟩ := ih1 h
        refine ⟨c :: l', by simp [tryBump, hc, h1], by simp [h2], ?_⟩
        intro i
        by_cases hci : c.id = i
        · have : i ≠ r.client := fun e => hc (hci.trans e)
          simp [lookup_cons, hci, this]
        · simp only [lookup_cons, hci, ite_false]
          exact h3 i
      · intro h
        simp [tryBump, hc, ih2 h]

theorem step_of_adm {s : State} {r : Request} (h : Admissible s r) :
    ∃ l', step s r = (.ok, ⟨s.window, s.limit, l'⟩) ∧
      l'.map Client.id = s.clients.map Client.id ∧
      ∀ i, lookup l' i = expectedLookup s r i := by
  obtain ⟨l', h1, h2, h3⟩ := (tryBump_spec s r s.clients).1 h.2
  refine ⟨l', ?_, h2, h3⟩
  have hd : distinctIds s.clients = true := (distinctIds_iff _).mpr h.1
  simp [step, hd, h1]

theorem step_of_not {s : State} {r : Request} (h : ¬ Admissible s r) :
    step s r = (.rejected, s) := by
  unfold Admissible at h
  unfold step
  by_cases hd : distinctIds s.clients = true
  · have hn : ¬ Admits s r.time (lookup s.clients r.client) :=
      fun ha => h ⟨(distinctIds_iff _).mp hd, ha⟩
    simp [hd, (tryBump_spec s r s.clients).2 hn]
  · simp [hd]

theorem adm_of_ok {s : State} {r : Request} (h : (step s r).1 = .ok) : Admissible s r := by
  by_cases hv : Admissible s r
  · exact hv
  · rw [step_of_not hv] at h; cases h

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

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  obtain ⟨l', h1, -⟩ := step_of_adm h
  rw [h1]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h; exact step_of_not h

theorem req_isolation : Isolation step := by
  intro s r i hi
  by_cases hv : Admissible s r
  · obtain ⟨l', h1, -, h3⟩ := step_of_adm hv
    rw [h1]; show lookup l' i = _
    rw [h3]; simp [expectedLookup, hi]
  · rw [step_of_not hv]

theorem req_reset : ResetRule step := by
  intro s r hok c hc
  obtain ⟨l', h1, -, h3⟩ := step_of_adm (adm_of_ok hok)
  refine ⟨advance s c r.time, ?_, ?_, ?_⟩
  · rw [h1]; show lookup l' r.client = _
    rw [h3]; simp [expectedLookup, hc]
  · intro h; simp [advance, windowStart, windowCount, h]
  · intro h
    have : ¬ c.start + s.window ≤ r.time := by omega
    simp [advance, windowStart, windowCount, this]

theorem req_effects : Effects step := by
  intro s r hok
  obtain ⟨l', h1, h2, h3⟩ := step_of_adm (adm_of_ok hok)
  rw [h1]
  exact ⟨rfl, rfl, h2, h3⟩

theorem req_window_bound : WindowBound step := by
  intro s r hb c' hc'
  by_cases hv : Admissible s r
  · obtain ⟨l', h1, h2, h3⟩ := step_of_adm hv
    rw [h1] at hc' ⊢
    show c'.count ≤ s.limit
    have hnd : (l'.map Client.id).Nodup := h2 ▸ hv.1
    have hl := lookup_of_mem hnd hc'
    rw [h3] at hl
    unfold expectedLookup at hl
    by_cases hi : c'.id = r.client
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hi)] at hl
      cases ho : lookup s.clients c'.id with
      | none => rw [ho] at hl; cases hl
      | some c =>
        rw [ho] at hl
        simp only [Option.map_some, Option.some.injEq] at hl
        have ha := hv.2
        rw [← hi, ho] at ha
        have : windowCount s c r.time < s.limit := ha.2
        rw [← hl]; simp [advance]; omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hi)] at hl
      exact hb c' (lookup_mem hl)
  · rw [step_of_not hv] at hc' ⊢
    exact hb c' hc'

end FixedWindow
