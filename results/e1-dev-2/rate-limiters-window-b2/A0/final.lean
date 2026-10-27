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
      if c.id = r.client then advance s c r.time else c })
  else (.rejected, s)

private theorem f_id (s : State) (r : Request) (c : Client) :
    (if c.id = r.client then advance s c r.time else c).id = c.id := by
  by_cases h : c.id = r.client <;> simp [h, advance]

private theorem ids_preserved (s : State) (r : Request) (l : List Client) :
    ((l.map fun c => if c.id = r.client then advance s c r.time else c).map Client.id) =
      l.map Client.id := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [f_id s r c, ih]

private theorem lookup_other (s : State) (r : Request) (l : List Client) (i : ClientId)
    (hne : i ≠ r.client) :
    lookup ((l.map fun c => if c.id = r.client then advance s c r.time else c)) i =
      lookup l i := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons]
    by_cases hci : c.id = i
    · have hcr : c.id ≠ r.client := fun hcon => hne (hci.symm.trans hcon)
      have hFc : (if c.id = r.client then advance s c r.time else c) = c :=
        if_neg hcr
      have hcond : (if c.id = r.client then advance s c r.time else c).id = i := by
        rw [hFc, hci]
      have e1 : lookup ((if c.id = r.client then advance s c r.time else c) ::
          List.map (fun c => if c.id = r.client then advance s c r.time else c) cs) i =
          some c := by rw [lookup_cons, if_pos hcond, hFc]
      have e2 : lookup (c :: cs) i = some c := by rw [lookup_cons, if_pos hci]
      rw [e1, e2]
    · have hcondNeg : (if c.id = r.client then advance s c r.time else c).id ≠ i := by
        rw [f_id s r c]; exact hci
      have e1 : lookup ((if c.id = r.client then advance s c r.time else c) ::
          List.map (fun c => if c.id = r.client then advance s c r.time else c) cs) i =
          lookup (List.map (fun c => if c.id = r.client then advance s c r.time else c) cs) i := by
        rw [lookup_cons, if_neg hcondNeg]
      have e2 : lookup (c :: cs) i = lookup cs i := by
        rw [lookup_cons, if_neg hci]
      rw [e1, e2, ih]

private theorem lookup_self (s : State) (r : Request) (l : List Client) :
    lookup ((l.map fun c => if c.id = r.client then advance s c r.time else c)) r.client =
      (lookup l r.client).map fun c => advance s c r.time := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons]
    by_cases hcr : c.id = r.client
    · have hFc : (if c.id = r.client then advance s c r.time else c) =
          advance s c r.time := if_pos hcr
      have hadv : (advance s c r.time).id = r.client := by simp [advance, hcr]
      have hcond : (if c.id = r.client then advance s c r.time else c).id = r.client := by
        rw [hFc]; exact hadv
      have e1 : lookup ((if c.id = r.client then advance s c r.time else c) ::
          List.map (fun c => if c.id = r.client then advance s c r.time else c) cs) r.client =
          some (advance s c r.time) := by rw [lookup_cons, if_pos hcond, hFc]
      have e2 : lookup (c :: cs) r.client = some c := by rw [lookup_cons, if_pos hcr]
      rw [e1, e2]
      rfl
    · have hFc : (if c.id = r.client then advance s c r.time else c) = c :=
        if_neg hcr
      have hcondNeg : (if c.id = r.client then advance s c r.time else c).id ≠ r.client := by
        rw [f_id s r c]; exact hcr
      have e1 : lookup ((if c.id = r.client then advance s c r.time else c) ::
          List.map (fun c => if c.id = r.client then advance s c r.time else c) cs) r.client =
          lookup (List.map (fun c => if c.id = r.client then advance s c r.time else c) cs) r.client := by
        rw [lookup_cons, if_neg hcondNeg]
      have e2 : lookup (c :: cs) r.client = lookup cs r.client := by
        rw [lookup_cons, if_neg hcr]
      rw [e1, e2, ih]

private theorem lookup_unique (l : List Client) :
    (l.map Client.id).Nodup → ∀ (i : ClientId) (c0 : Client),
      lookup l i = some c0 → ∀ (x : Client), x ∈ l → x.id = i → x = c0 := by
  induction l with
  | nil =>
    intro _ i c0 hlook x hmem hid
    simp [lookup_nil] at hlook
  | cons y ys ih =>
    intro hNodup i c0 hlook x hmem hid
    simp only [List.map_cons] at hNodup
    rw [List.nodup_cons] at hNodup
    obtain ⟨hnotin, hNodupTail⟩ := hNodup
    have hlookU := lookup_cons y ys i
    rw [hlookU] at hlook
    by_cases hy : y.id = i
    · simp [hy] at hlook
      subst hlook
      have hdisj : x = y ∨ x ∈ ys := List.mem_cons.mp hmem
      cases hdisj with
      | inl hxy => exact hxy
      | inr hmemTail =>
        exfalso
        have hmapMem : x.id ∈ ys.map Client.id := List.mem_map_of_mem hmemTail
        have hxy : x.id = y.id := by rw [hid, hy]
        have hyIn : y.id ∈ ys.map Client.id := by rw [← hxy]; exact hmapMem
        exact hnotin hyIn
    · simp [hy] at hlook
      have hdisj : x = y ∨ x ∈ ys := List.mem_cons.mp hmem
      cases hdisj with
      | inl hxy =>
        exfalso
        rw [hxy] at hid
        exact hy hid
      | inr hmemTail =>
        exact ih hNodupTail i c0 hlook x hmemTail hid

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
  by_cases h : Admissible s r
  · have h2 : (step s r).2.clients =
        s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
      unfold step; simp [h]
    rw [h2]
    exact lookup_other s r s.clients i hne
  · have h2 : (step s r).2.clients = s.clients := by
      unfold step; simp [h]
    rw [h2]

theorem req_reset : ResetRule step := by
  intro s r hok c hlook
  by_cases hAdm : Admissible s r
  · have hmap : (step s r).2.clients =
        s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
      unfold step; simp [hAdm]
    have hlook2 : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
      rw [hmap, lookup_self s r s.clients, hlook]
      rfl
    refine ⟨advance s c r.time, hlook2, ?_, ?_⟩
    · intro hexp
      unfold advance windowStart windowCount
      simp [hexp]
    · intro hnexp
      have hle : ¬ c.start + s.window ≤ r.time := by omega
      unfold advance windowStart windowCount
      simp [hle]
  · exfalso
    have hrej : (step s r).1 = .rejected := by
      unfold step; simp [hAdm]
    rw [hrej] at hok
    cases hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hAdm : Admissible s r
  · have hmap : (step s r).2.clients =
        s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
      unfold step; simp [hAdm]
    have hwin : (step s r).2.window = s.window := by
      unfold step; simp [hAdm]
    have hlim : (step s r).2.limit = s.limit := by
      unfold step; simp [hAdm]
    have hids : (step s r).2.clients.map Client.id = s.clients.map Client.id := by
      rw [hmap]; exact ids_preserved s r s.clients
    refine ⟨hwin, hlim, hids, ?_⟩
    intro i
    rw [hmap]
    show lookup (List.map _ _) i = expectedLookup s r i
    unfold expectedLookup
    by_cases hi : i = r.client
    · subst hi
      simp only [ite_true]
      exact lookup_self s r s.clients
    · simp only [hi, ↓reduceIte]
      exact lookup_other s r s.clients i hi
  · exfalso
    have hrej : (step s r).1 = .rejected := by
      unfold step; simp [hAdm]
    rw [hrej] at hok
    cases hok

theorem req_window_bound : WindowBound step := by
  intro s r hall c hmem
  by_cases hAdm : Admissible s r
  · have hmap : (step s r).2.clients =
        s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
      unfold step; simp [hAdm]
    have hlim : (step s r).2.limit = s.limit := by
      unfold step; simp [hAdm]
    rw [hlim]
    rw [hmap] at hmem
    obtain ⟨c0, hmem0, hfc⟩ := List.mem_map.mp hmem
    have hle0 : c0.count ≤ s.limit := hall c0 hmem0
    by_cases heq : c0.id = r.client
    · have hfeq : (if c0.id = r.client then advance s c0 r.time else c0) =
          advance s c0 r.time := if_pos heq
      have hcEq : c = advance s c0 r.time := by rw [← hfeq]; exact hfc.symm
      rw [hcEq]
      obtain ⟨hNodup, hAdmits⟩ := hAdm
      cases hlk : lookup s.clients r.client with
      | none =>
        have hF : Admits s r.time (lookup s.clients r.client) := hAdmits
        rw [hlk] at hF
        cases hF
      | some c1 =>
        have hF : Admits s r.time (some c1) := by rw [← hlk]; exact hAdmits
        unfold Admits at hF
        obtain ⟨_, hlt1⟩ := hF
        have hEq : c0 = c1 := lookup_unique s.clients hNodup r.client c1 hlk c0 hmem0 heq
        have hlt : windowCount s c0 r.time < s.limit := by rw [hEq]; exact hlt1
        have hcount : (advance s c0 r.time).count = windowCount s c0 r.time + 1 := by
          simp [advance]
        rw [hcount]
        omega
    · have hfeq : (if c0.id = r.client then advance s c0 r.time else c0) = c0 :=
        if_neg heq
      have hcEq : c = c0 := by rw [← hfeq]; exact hfc.symm
      rw [hcEq]
      exact hle0
  · have heq : (step s r).2 = s := by
      unfold step; simp [hAdm]
    rw [heq] at hmem ⊢
    exact hall c hmem

end FixedWindow
