import FixedWindow.Spec
import FixedWindow.Lemmas

namespace FixedWindow

instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible
  infer_instance

def upd (s : State) (r : Request) (c : Client) : Client :=
  if c.id = r.client then advance s c r.time else c

theorem upd_id (s : State) (r : Request) (c : Client) : (upd s r c).id = c.id := by
  unfold upd
  split
  · rfl
  · rfl

theorem upd_same (s : State) (r : Request) (c : Client) (h : c.id = r.client) :
    upd s r c = advance s c r.time := by
  unfold upd
  rw [if_pos h]

theorem upd_diff (s : State) (r : Request) (c : Client) (h : c.id ≠ r.client) :
    upd s r c = c := by
  unfold upd
  rw [if_neg h]

theorem lookup_map_aux (g : Client → Client) (hg : ∀ c, (g c).id = c.id)
    (l : List Client) (i : ClientId) :
    lookup (l.map g) i = (lookup l i).map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, lookup_cons]
    have he : (g x).id = x.id := hg x
    rw [he]
    by_cases h : x.id = i
    · simp [h]
    · simp [h, ih]

theorem lookup_map_upd (s : State) (r : Request) (l : List Client) (i : ClientId) :
    lookup (l.map (upd s r)) i = (lookup l i).map (upd s r) :=
  lookup_map_aux (upd s r) (upd_id s r) l i

theorem map_upd_ids (s : State) (r : Request) (l : List Client) :
    (l.map (upd s r)).map Client.id = l.map Client.id := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    have h : (upd s r x).id = x.id := upd_id s r x
    simp [h, ih]

theorem mem_map_id {l : List Client} {c : Client} (h : c ∈ l) :
    c.id ∈ l.map Client.id := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.map_cons]
    have hor : c = x ∨ c ∈ xs := by simpa using h
    cases hor with
    | inl heq => simp [heq]
    | inr hmem =>
      have ihm := ih hmem
      simp [ihm]

theorem lookup_of_mem_nodup {l : List Client} {c0 : Client} {i : ClientId}
    (hmem : c0 ∈ l) (hnodup : (l.map Client.id).Nodup) (hid : c0.id = i) :
    lookup l i = some c0 := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    have hpair : (∀ a' ∈ xs.map Client.id, x.id ≠ a') ∧ (xs.map Client.id).Nodup := by
      match hnodup with
      | .cons hhead htail' => exact ⟨fun a' ha h => hhead a' ha h, htail'⟩
    have hnot : x.id ∉ xs.map Client.id := by
      intro hcontra
      exact (hpair.1 _ hcontra rfl).elim
    have htail : (xs.map Client.id).Nodup := hpair.2
    have hor : c0 = x ∨ c0 ∈ xs := by simpa using hmem
    simp only [lookup_cons]
    by_cases hx : x.id = i
    · have hc0eq : c0 = x := by
        cases hor with
        | inl heq => exact heq
        | inr hmem2 =>
          exfalso
          have hmemid : c0.id ∈ xs.map Client.id := mem_map_id hmem2
          have heq2 : c0.id = x.id := by rw [hid, hx]
          rw [heq2] at hmemid
          exact hnot hmemid
      subst hc0eq
      simp [hx]
    · have hmem2 : c0 ∈ xs := by
        cases hor with
        | inl heq =>
          exfalso
          rw [heq] at hid
          exact False.elim (hx hid)
        | inr hm => exact hm
      have ihres := ih hmem2 htail
      rw [if_neg hx, ihres]

def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with clients := s.clients.map (upd s r) })
  else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_isolation : Isolation step := by
  unfold Isolation
  intro s r i hi
  by_cases hAdm : Admissible s r
  · have hclients : (step s r).2.clients = s.clients.map (upd s r) := by
      simp [step, hAdm]
    rw [hclients, lookup_map_upd]
    match hEq : lookup s.clients i with
    | none =>
      simp [hEq]
    | some c =>
      have hid : c.id = i := lookup_id hEq
      have hne : c.id ≠ r.client := by rw [hid]; exact hi
      have hupd : upd s r c = c := upd_diff _ _ _ hne
      simp [hEq, hupd]
  · have hstep : (step s r).2 = s := by simp [step, hAdm]
    rw [hstep]

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hok
  have hAdm : Admissible s r := by
    by_cases ha : Admissible s r
    · exact ha
    · exfalso
      have hstep : step s r = (.rejected, s) := by simp [step, ha]
      rw [hstep] at hok
      simp at hok
  have hwin : (step s r).2.window = s.window := by simp [step, hAdm]
  have hlim : (step s r).2.limit = s.limit := by simp [step, hAdm]
  have hclients : (step s r).2.clients = s.clients.map (upd s r) := by simp [step, hAdm]
  have hids : (step s r).2.clients.map Client.id = s.clients.map Client.id := by
    rw [hclients]
    exact map_upd_ids s r s.clients
  refine ⟨hwin, hlim, hids, ?_⟩
  intro i
  rw [hclients, lookup_map_upd]
  unfold expectedLookup
  by_cases he : i = r.client
  · rw [if_pos he]
    match hEq : lookup s.clients i with
    | none =>
      simp [hEq]
    | some c =>
      have hid : c.id = i := lookup_id hEq
      have heq : c.id = r.client := by rw [hid, he]
      have hupd : upd s r c = advance s c r.time := upd_same _ _ _ heq
      simp [hEq, hupd]
  · rw [if_neg he]
    match hEq : lookup s.clients i with
    | none =>
      simp [hEq]
    | some c =>
      have hid : c.id = i := lookup_id hEq
      have hne : c.id ≠ r.client := by rw [hid]; exact he
      have hupd : upd s r c = c := upd_diff _ _ _ hne
      simp [hEq, hupd]

theorem req_reset : ResetRule step := by
  unfold ResetRule
  intro s r hok c hlook
  have hAdm : Admissible s r := by
    by_cases ha : Admissible s r
    · exact ha
    · exfalso
      have hstep : step s r = (.rejected, s) := by simp [step, ha]
      rw [hstep] at hok
      simp at hok
  have hclients : (step s r).2.clients = s.clients.map (upd s r) := by simp [step, hAdm]
  have heq : c.id = r.client := lookup_id hlook
  have hupd : upd s r c = advance s c r.time := upd_same _ _ _ heq
  have hafter : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
    rw [hclients, lookup_map_upd, hlook]
    simp [hupd]
  refine ⟨advance s c r.time, hafter, ?_, ?_⟩
  · intro hle
    unfold advance windowStart windowCount
    simp [hle]
  · intro hlt
    have hle : ¬ (c.start + s.window ≤ r.time) := by omega
    unfold advance windowStart windowCount
    simp [hle]

theorem req_window_bound : WindowBound step := by
  unfold WindowBound
  intro s r hbound c hmem
  by_cases hAdm : Admissible s r
  · have hclients : (step s r).2.clients = s.clients.map (upd s r) := by simp [step, hAdm]
    have hlim : (step s r).2.limit = s.limit := by simp [step, hAdm]
    rw [hlim]
    rw [hclients] at hmem
    obtain ⟨c0, hinc0, heqc0⟩ := List.mem_map.mp hmem
    rw [← heqc0]
    have hle0 : c0.count ≤ s.limit := hbound c0 hinc0
    by_cases heq : c0.id = r.client
    · have hnodup : (s.clients.map Client.id).Nodup := hAdm.1
      have hadmits : Admits s r.time (lookup s.clients r.client) := hAdm.2
      cases hlk : lookup s.clients r.client with
      | none =>
        rw [hlk] at hadmits
        unfold Admits at hadmits
        exact False.elim hadmits
      | some cstar =>
        rw [hlk] at hadmits
        unfold Admits at hadmits
        have hpair : cstar.start ≤ r.time ∧ windowCount s cstar r.time < s.limit := hadmits
        have hlook0 : lookup s.clients r.client = some c0 :=
          lookup_of_mem_nodup hinc0 hnodup heq
        have heqc : c0 = cstar := by
          rw [hlook0] at hlk
          exact Option.some_inj.mp hlk
        subst heqc
        have hupd_eq : upd s r c0 = advance s c0 r.time := upd_same _ _ _ heq
        rw [hupd_eq]
        have hwc : windowCount s c0 r.time < s.limit := hpair.2
        have hcount : (advance s c0 r.time).count = windowCount s c0 r.time + 1 := rfl
        rw [hcount]
        omega
    · have hupd_eq : upd s r c0 = c0 := upd_diff _ _ _ heq
      rw [hupd_eq]
      exact hle0
  · have hstep : (step s r).2 = s := by simp [step, hAdm]
    rw [hstep] at hmem ⊢
    exact hbound c hmem

end FixedWindow
