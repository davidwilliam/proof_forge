import FixedWindow.Spec
import FixedWindow.Lemmas
namespace FixedWindow

instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible
  infer_instance

def upd (s : State) (r : Request) (x : Client) : Client :=
  if x.id = r.client then advance s x r.time else x

theorem upd_id (s : State) (r : Request) (x : Client) : (upd s r x).id = x.id := by
  unfold upd advance
  by_cases h : x.id = r.client
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]

theorem upd_advance (s : State) (r : Request) (x : Client) (h : x.id = r.client) :
    upd s r x = advance s x r.time := by
  unfold upd
  simp only [h, ↓reduceIte]

theorem upd_self (s : State) (r : Request) (x : Client) (h : x.id ≠ r.client) :
    upd s r x = x := by
  unfold upd
  simp only [h, ↓reduceIte]

theorem map_upd_ids (s : State) (r : Request) (l : List Client) :
    (l.map (upd s r)).map Client.id = l.map Client.id := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, upd_id, ih]

theorem lookup_map_upd (s : State) (r : Request) (l : List Client) (i : ClientId) :
    lookup (l.map (upd s r)) i = (lookup l i).map (upd s r) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, lookup_cons] at ⊢
    by_cases hx : x.id = i
    · have hx' : (upd s r x).id = i := by
        rw [upd_id]
        exact hx
      simp only [hx, hx', ↓reduceIte]
      rfl
    · have hx' : (upd s r x).id ≠ i := by
        rw [upd_id]
        exact hx
      simp only [hx, hx', ↓reduceIte, ih]

theorem lookup_of_mem_nodup (l : List Client) (i : ClientId) (c : Client) :
    (l.map Client.id).Nodup → c ∈ l → c.id = i → lookup l i = some c := by
  induction l with
  | nil =>
    intro hn hm hid
    simp at hm
  | cons x xs ih =>
    intro hn hm hid
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hfresh, htail⟩ := hn
    have hdisj : c = x ∨ c ∈ xs := List.mem_cons.mp hm
    cases hdisj with
    | inl heq =>
      subst heq
      simp only [lookup_cons, hid, ↓reduceIte]
    | inr hmem =>
      have hmemid : c.id ∈ List.map Client.id xs :=
        List.mem_map.mpr ⟨c, hmem, rfl⟩
      have hne : x.id ≠ i := by
        intro heq
        have h1 : x.id ∉ List.map Client.id xs := hfresh
        rw [heq, ← hid] at h1
        exact h1 hmemid
      simp only [lookup_cons, hne, ↓reduceIte]
      exact ih htail hmem hid

theorem lookup_map_upd_expected (s : State) (r : Request) (i : ClientId) :
    lookup (s.clients.map (upd s r)) i = expectedLookup s r i := by
  rw [lookup_map_upd]
  unfold expectedLookup
  by_cases h : i = r.client
  · subst h
    rw [if_pos rfl]
    cases he : lookup s.clients r.client with
    | none => rfl
    | some c =>
      have hc : c.id = r.client := lookup_id he
      have heq : upd s r c = advance s c r.time := upd_advance s r c hc
      simp only [Option.map_some]
      rw [heq]
  · rw [if_neg h]
    cases he : lookup s.clients i with
    | none => rfl
    | some c =>
      have hc : c.id = i := lookup_id he
      have hne : c.id ≠ r.client := by rw [hc]; exact h
      have heq : upd s r c = c := upd_self s r c hne
      simp only [Option.map_some]
      rw [heq]

def step : Impl := fun s r =>
  if Admissible s r then
    (Outcome.ok, { s with clients := s.clients.map (upd s r) })
  else
    (Outcome.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hstep : step s r = (Outcome.ok, ({ s with clients := s.clients.map (upd s r) } : State)) := if_pos h
  rw [hstep]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hstep : step s r = ((Outcome.rejected, s) : Outcome × State) := if_neg h
  exact hstep

theorem req_isolation : Isolation step := by
  intro s r i hne
  by_cases h : Admissible s r
  · have hstep : step s r = (Outcome.ok, ({ s with clients := s.clients.map (upd s r) } : State)) := if_pos h
    have h2 : (step s r).2 = ({ s with clients := s.clients.map (upd s r) } : State) := congrArg Prod.snd hstep
    have h' : lookup (step s r).2.clients i = lookup (s.clients.map (upd s r)) i := by
      rw [h2]
    rw [h', lookup_map_upd]
    cases he : lookup s.clients i with
    | none =>
      rfl
    | some c =>
      have hc : c.id = i := lookup_id he
      have hne2 : c.id ≠ r.client := by
        intro heq
        apply hne
        rw [← hc, heq]
      have heq : upd s r c = c := upd_self s r c hne2
      simp only [Option.map_some, heq]
  · have hstep : step s r = ((Outcome.rejected, s) : Outcome × State) := if_neg h
    have h2 : (step s r).2 = s := congrArg Prod.snd hstep
    rw [h2]

theorem req_reset : ResetRule step := by
  intro s r hok c hlook
  have hadm : Admissible s r := by
    cases Decidable.em (Admissible s r) with
    | inl h => exact h
    | inr h =>
      exfalso
      have hstep : step s r = ((Outcome.rejected, s) : Outcome × State) := if_neg h
      have h1 : (step s r).1 = Outcome.rejected := congrArg Prod.fst hstep
      rw [h1] at hok
      cases hok
  have hstep : step s r = (Outcome.ok, ({ s with clients := s.clients.map (upd s r) } : State)) := if_pos hadm
  have h2 : (step s r).2 = ({ s with clients := s.clients.map (upd s r) } : State) := congrArg Prod.snd hstep
  have hc_id : c.id = r.client := lookup_id hlook
  have hafter : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
    have htmp : lookup (s.clients.map (upd s r)) r.client = some (advance s c r.time) := by
      rw [lookup_map_upd, hlook]
      simp only [Option.map_some]
      have heq : upd s r c = advance s c r.time := upd_advance s r c hc_id
      rw [heq]
    rw [h2]
    exact htmp
  refine ⟨advance s c r.time, hafter, ?_, ?_⟩
  · intro hle
    have hs : windowStart s c r.time = r.time := by
      unfold windowStart
      rw [if_pos hle]
    have hc0 : windowCount s c r.time = 0 := by
      unfold windowCount
      rw [if_pos hle]
    have hstart : (advance s c r.time).start = windowStart s c r.time := rfl
    have hcount : (advance s c r.time).count = windowCount s c r.time + 1 := rfl
    rw [hstart, hcount, hs, hc0]
    exact ⟨rfl, rfl⟩
  · intro hlt
    have hle : ¬ c.start + s.window ≤ r.time := Nat.not_le.mpr hlt
    have hs : windowStart s c r.time = c.start := by
      unfold windowStart
      rw [if_neg hle]
    have hc0 : windowCount s c r.time = c.count := by
      unfold windowCount
      rw [if_neg hle]
    have hstart : (advance s c r.time).start = windowStart s c r.time := rfl
    have hcount : (advance s c r.time).count = windowCount s c r.time + 1 := rfl
    rw [hstart, hcount, hs, hc0]
    exact ⟨rfl, rfl⟩

theorem req_effects : Effects step := by
  intro s r hok
  have hadm : Admissible s r := by
    cases Decidable.em (Admissible s r) with
    | inl h => exact h
    | inr h =>
      exfalso
      have hstep : step s r = ((Outcome.rejected, s) : Outcome × State) := if_neg h
      have h1 : (step s r).1 = Outcome.rejected := congrArg Prod.fst hstep
      rw [h1] at hok
      cases hok
  have hstep : step s r = (Outcome.ok, ({ s with clients := s.clients.map (upd s r) } : State)) := if_pos hadm
  have h2 : (step s r).2 = ({ s with clients := s.clients.map (upd s r) } : State) := congrArg Prod.snd hstep
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h2]
  · rw [h2]
  · have hids0 := map_upd_ids s r s.clients
    have hids : List.map Client.id (step s r).2.clients = List.map Client.id s.clients := by
      rw [h2]
      exact hids0
    exact hids
  · intro i
    have h := lookup_map_upd_expected s r i
    have h' : lookup (step s r).2.clients i = lookup (s.clients.map (upd s r)) i := by
      rw [h2]
    rw [h', h]

theorem req_window_bound : WindowBound step := by
  intro s r hall c hmem
  by_cases h : Admissible s r
  · have hstep : step s r = (Outcome.ok, ({ s with clients := s.clients.map (upd s r) } : State)) := if_pos h
    have h2 : (step s r).2 = ({ s with clients := s.clients.map (upd s r) } : State) := congrArg Prod.snd hstep
    have hlim : (step s r).2.limit = s.limit := by rw [h2]
    rw [hlim]
    have hmem' : c ∈ s.clients.map (upd s r) := by
      rw [h2] at hmem
      exact hmem
    obtain ⟨a, ha_mem, ha_eq⟩ := List.mem_map.mp hmem'
    have ha_le : a.count ≤ s.limit := hall a ha_mem
    obtain ⟨hnod, hadmits⟩ := h
    by_cases heq : a.id = r.client
    · have hlook_a : lookup s.clients r.client = some a :=
        lookup_of_mem_nodup s.clients r.client a hnod ha_mem heq
      rw [hlook_a] at hadmits
      obtain ⟨_, hlt⟩ := hadmits
      have hc_eq : upd s r a = advance s a r.time := upd_advance s r a heq
      have hrfl : (advance s a r.time).count = windowCount s a r.time + 1 := rfl
      have hcount : (upd s r a).count = windowCount s a r.time + 1 := by
        rw [hc_eq]
        exact hrfl
      have hc_eq2 : c = upd s r a := ha_eq.symm
      rw [hc_eq2, hcount]
      exact Nat.succ_le_of_lt hlt
    · have hc_eq : upd s r a = a := upd_self s r a heq
      have hc_eq2 : c = upd s r a := ha_eq.symm
      rw [hc_eq2, hc_eq]
      exact ha_le
  · have hstep : step s r = ((Outcome.rejected, s) : Outcome × State) := if_neg h
    have h2b : (step s r).2 = s := congrArg Prod.snd hstep
    have hmem' : c ∈ s.clients := by
      rw [h2b] at hmem
      exact hmem
    have hlim : (step s r).2.limit = s.limit := by rw [h2b]
    rw [hlim]
    exact hall c hmem'

end FixedWindow
