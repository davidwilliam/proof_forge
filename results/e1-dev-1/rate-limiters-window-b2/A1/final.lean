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

def fooTest : Nat := 1

theorem fooTest2 : 1 = 1 := rfl

theorem advance_id_test : (1 : Nat) = 1 := rfl

theorem myLemA (n : Nat) : n = n := rfl

theorem myLemB : (1 : Nat) = 1 := rfl

theorem advId (s : State) (c : Client) (t : Nat) : (advance s c t).id = c.id := rfl

theorem lookupMapPreserve (f : Client -> Client) (hf : forall c, (f c).id = c.id) (l : List Client) (i : ClientId) : lookup (l.map f) i = (lookup l i).map f := by induction l with | nil => rfl | cons x xs ih => simp only [List.map_cons, lookup_cons, hf] ; by_cases hx : x.id = i ; simp [hx] ; simp [hx, ih]

theorem mapIdPreserveAux (f : Client → Client) (hf : ∀ c, (f c).id = c.id) (l : List Client) : (l.map f).map Client.id = l.map Client.id := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, hf, ih]

theorem testNodupAux (a : Nat) (l : List Nat) : List.Nodup (a :: l) → a ∉ l ∧ List.Nodup l := by
  intro h
  simp [List.nodup_cons] at h
  exact h
#check List.nodup_cons
#check List.mem_map

theorem tmpUniqTest (l : List Client) : True := by
  induction l with
  | nil => trivial
  | cons x xs ih => trivial

theorem tmpUniqTest2 (l : List Client) (c : Client) (h : c ∈ l) : True := by
  induction l with
  | nil => trivial
  | cons hd tl ih =>
    have hhd : hd = hd := rfl
    trivial

theorem inspectNodup (hd : Client) (tl : List Client) (hN : ((hd :: tl).map Client.id).Nodup) : True := by
  simp only [List.map_cons] at hN
  have h := (List.nodup_cons.mp hN)
  guard_hyp h : _ ∧ _
  trivial

theorem req_reset_aux_test1 (s : State) (r : Request) (h : (step s r).1 = .ok) : Admissible s r := by
  by_cases hAdm : Admissible s r
  · exact hAdm
  · have hrej : (step s r).1 = .rejected := by simp [step, hAdm]
    rw [hrej] at h
    contradiction

theorem req_reset_proof2 : ResetRule step := by
  intro s r h_ok c hlook
  have hAdm : Admissible s r := req_reset_aux_test1 s r h_ok
  have hstep2 : (step s r).2.clients = s.clients.map (fun cc => if cc.id = r.client then advance s cc r.time else cc) := by
    simp [step, hAdm]
  have hf : ∀ cc : Client, ((if cc.id = r.client then advance s cc r.time else cc).id = cc.id) := by
    intro cc
    by_cases hc : cc.id = r.client
    · simp [hc, advId]
    · simp [hc]
  have hmap := lookupMapPreserve (fun cc => (if cc.id = r.client then advance s cc r.time else cc)) hf s.clients r.client
  have hcId : c.id = r.client := lookup_id hlook
  have hgoal : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
    rw [hstep2, hmap, hlook]
    simp [hcId]
  refine ⟨advance s c r.time, hgoal, ?_, ?_⟩
  · intro hexp
    have hs : windowStart s c r.time = r.time := by unfold windowStart; simp [hexp]
    have hc0 : windowCount s c r.time = 0 := by unfold windowCount; simp [hexp]
    unfold advance
    simp [hs, hc0]
  · intro hlt
    have hexp_neg : ¬ (c.start + s.window ≤ r.time) := by omega
    have hs : windowStart s c r.time = c.start := by unfold windowStart; simp [hexp_neg]
    have hc0 : windowCount s c r.time = c.count := by unfold windowCount; simp [hexp_neg]
    unfold advance
    simp [hs, hc0]

theorem req_reset_dup : ResetRule step := req_reset_proof2

theorem req_reset_fix : True := trivial

theorem mem_lookup_eq_aux4 (l : List Client) : (l.map Client.id).Nodup → ∀ (c : Client), c ∈ l → ∀ (c0 : Client), lookup l c.id = some c0 → c = c0 := by
  induction l with
  | nil => intro hN c hm; simp at hm
  | cons hd tl ih =>
    intro hN c hm c0 hlook
    simp only [List.map_cons, List.nodup_cons] at hN
    obtain ⟨hNotMem, hNtl⟩ := hN
    simp at hm
    rw [lookup_cons] at hlook
    by_cases hhd : hd.id = c.id
    · simp [hhd] at hlook
      subst hlook
      rcases hm with rfl | hmem2
      · rfl
      · exfalso
        apply hNotMem
        have hmemId : c.id ∈ tl.map Client.id := List.mem_map.mpr ⟨c, hmem2, rfl⟩
        rw [← hhd] at hmemId
        exact hmemId
    · simp [hhd] at hlook
      rcases hm with heq | hmem2
      · exfalso; apply hhd; rw [heq]
      · exact ih hNtl c hmem2 c0 hlook

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_isolation : Isolation step := by
  intro s r i hne
  unfold step
  by_cases hAdm : Admissible s r
  · simp only [hAdm, ↓reduceIte]
    have hf : ∀ c : Client, ((if c.id = r.client then advance s c r.time else c).id = c.id) := by
      intro c
      by_cases hc : c.id = r.client
      · simp [hc, advId]
      · simp [hc]
    have hmap := lookupMapPreserve (fun c => (if c.id = r.client then advance s c r.time else c)) hf s.clients i
    have h_eq : (lookup s.clients i).map (fun c => (if c.id = r.client then advance s c r.time else c)) = lookup s.clients i := by
      cases hlook : lookup s.clients i with
      | none => rfl
      | some c =>
        have hcId : c.id = i := lookup_id hlook
        have hcc : ¬ (c.id = r.client) := by
          intro hcon
          apply hne
          rw [hcId] at hcon
          exact hcon
        simp [hcc]
    exact hmap.trans h_eq
  · simp [hAdm]

theorem req_reset : ResetRule step := req_reset_proof2

theorem req_effects : Effects step := by
  intro s r h_ok
  by_cases hAdm : Admissible s r
  · have hstep : step s r = (.ok, { s with clients := s.clients.map (fun c => (if c.id = r.client then advance s c r.time else c)) }) := by simp [step, hAdm]
    have h2 : (step s r).2.clients = s.clients.map (fun c => (if c.id = r.client then advance s c r.time else c)) := by rw [hstep]
    have hf : ∀ c, ((if c.id = r.client then advance s c r.time else c).id = c.id) := by
      intro c
      by_cases hc : c.id = r.client
      · simp [hc, advId]
      · simp [hc]
    have hmap : ∀ i, lookup (s.clients.map (fun c => (if c.id = r.client then advance s c r.time else c))) i = (lookup s.clients i).map (fun c => (if c.id = r.client then advance s c r.time else c)) :=
      fun i => lookupMapPreserve _ hf s.clients i
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hstep]
    · rw [hstep]
    · rw [h2]
      exact mapIdPreserveAux _ hf s.clients
    · intro i
      rw [h2, hmap]
      unfold expectedLookup
      by_cases hi : i = r.client
      · subst hi
        simp only [ite_true]
        cases hlook : lookup s.clients r.client with
        | none => rfl
        | some c =>
          have hcId : c.id = r.client := lookup_id hlook
          simp [hcId]
      · simp only [hi, ↓reduceIte]
        cases hlook : lookup s.clients i with
        | none => rfl
        | some c =>
          have hcId : c.id = i := lookup_id hlook
          have hcc : ¬ (c.id = r.client) := by
            intro hcon
            apply hi
            rw [← hcId, hcon]
          simp [hcc]
  · exfalso
    have hrej : (step s r).1 = .rejected := by simp [step, hAdm]
    rw [hrej] at h_ok
    contradiction

theorem req_window_bound : WindowBound step := by
  intro s r hBound c' hmem'
  by_cases hAdm : Admissible s r
  · have hstep2c : (step s r).2.clients = s.clients.map (fun c => if c.id = r.client then advance s c r.time else c) := by simp [step, hAdm]
    have hstep2l : (step s r).2.limit = s.limit := by simp [step, hAdm]
    rw [hstep2l]
    rw [hstep2c] at hmem'
    obtain ⟨c, hcMem, hcEq⟩ := List.mem_map.mp hmem'
    have hNodup : (s.clients.map Client.id).Nodup := hAdm.1
    have hAdmits : Admits s r.time (lookup s.clients r.client) := hAdm.2
    by_cases hcId : c.id = r.client
    · cases hlc : lookup s.clients r.client with
      | none =>
        exfalso
        have hnone := (lookup_eq_none (l := s.clients) (i := r.client)).mp hlc
        exact hnone c hcMem hcId
      | some c0 =>
        have hAdm0 : c0.start ≤ r.time ∧ windowCount s c0 r.time < s.limit := by
          rw [hlc] at hAdmits
          exact hAdmits
        have hlookc : lookup s.clients c.id = some c0 := by
          rw [hcId]
          exact hlc
        have hcEq0 : c = c0 := mem_lookup_eq_aux4 s.clients hNodup c hcMem c0 hlookc
        have hc'eq : c' = advance s c r.time := by simpa [hcId] using hcEq.symm
        rw [hc'eq]
        show (advance s c r.time).count ≤ s.limit
        unfold advance
        simp only
        have hlt : windowCount s c r.time < s.limit := by rw [hcEq0]; exact hAdm0.2
        omega
    · have hc'eq : c' = c := by simpa [hcId] using hcEq.symm
      rw [hc'eq]
      exact hBound c hcMem
  · have h2 : (step s r).2 = s := by simp [step, hAdm]
    rw [h2] at hmem'
    rw [h2]
    exact hBound c' hmem'

end FixedWindow
