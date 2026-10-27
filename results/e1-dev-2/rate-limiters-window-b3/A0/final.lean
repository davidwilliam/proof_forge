import FixedWindow.Spec
import FixedWindow.Lemmas
namespace FixedWindow

instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance

def step : Impl := fun s r =>
  if (s.clients.map Client.id).Nodup then
    match lookup s.clients r.client with
    | some c =>
      if c.start ≤ r.time ∧ windowCount s c r.time < s.limit then
        (.ok, { s with clients := s.clients.map fun x =>
          if x.id = r.client then advance s x r.time else x })
      else (.rejected, s)
    | none => (.rejected, s)
  else (.rejected, s)

def upd (s : State) (r : Request) (x : Client) : Client :=
  if x.id = r.client then advance s x r.time else x

theorem upd_id (s : State) (r : Request) (x : Client) : (upd s r x).id = x.id := by
  unfold upd
  by_cases h : x.id = r.client
  · rw [if_pos h]
    rfl
  · rw [if_neg h]

theorem upd_eq_advance (s : State) (r : Request) (x : Client) (h : x.id = r.client) :
    upd s r x = advance s x r.time := by
  unfold upd
  rw [if_pos h]

theorem upd_eq_self (s : State) (r : Request) (x : Client) (h : x.id ≠ r.client) :
    upd s r x = x := by
  unfold upd
  rw [if_neg h]

theorem lookup_map_aux (f : Client → Client) (hf : ∀ x, (f x).id = x.id)
    (l : List Client) (i : ClientId) :
    lookup (List.map f l) i = Option.map f (lookup l i) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, lookup_cons]
    have hff : (f x).id = x.id := hf x
    by_cases h : x.id = i
    · have h2 : (f x).id = i := by rw [hff, h]
      simp [h, h2, ih]
    · have h2 : (f x).id ≠ i := by rw [hff]; exact h
      simp [h, h2, ih]

theorem lookup_upd (s : State) (r : Request) (i : ClientId) :
    lookup (List.map (upd s r) s.clients) i =
      Option.map (upd s r) (lookup s.clients i) :=
  lookup_map_aux (upd s r) (upd_id s r) s.clients i

theorem map_ids_upd (s : State) (r : Request) (l : List Client) :
    (List.map (upd s r) l).map Client.id = l.map Client.id := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map]
    have h := upd_id s r x
    rw [h, ih]

theorem map_ids_upd_state (s : State) (r : Request) :
    (List.map (upd s r) s.clients).map Client.id = s.clients.map Client.id :=
  map_ids_upd s r s.clients

theorem mem_eq_of_id_eq (l : List Client) :
    (l.map Client.id).Nodup → ∀ {x y : Client}, x ∈ l → y ∈ l → x.id = y.id → x = y := by
  induction l with
  | nil =>
    intro _ x y hx _ _
    simp at hx
  | cons hd tl ih =>
    intro hN x y hx hy hId
    simp only [List.map] at hN
    rw [List.nodup_cons] at hN
    obtain ⟨hNotMem, hNtail⟩ := hN
    have hx' : x = hd ∨ x ∈ tl := by simpa using hx
    have hy' : y = hd ∨ y ∈ tl := by simpa using hy
    cases hx' with
    | inl hxEq =>
      cases hy' with
      | inl hyEq => rw [hxEq, hyEq]
      | inr hyMem =>
        have hMemId : y.id ∈ List.map Client.id tl :=
          List.mem_map.mpr ⟨y, hyMem, rfl⟩
        rw [hxEq] at hId
        rw [← hId] at hMemId
        exact absurd hMemId hNotMem
    | inr hxMem =>
      cases hy' with
      | inl hyEq =>
        have hMemId : x.id ∈ List.map Client.id tl :=
          List.mem_map.mpr ⟨x, hxMem, rfl⟩
        rw [hyEq] at hId
        rw [hId] at hMemId
        exact absurd hMemId hNotMem
      | inr hyMem =>
        exact ih hNtail hxMem hyMem hId

theorem lookup_upd_eq_expected (s : State) (r : Request) (i : ClientId) :
    lookup (List.map (upd s r) s.clients) i = expectedLookup s r i := by
  have hMap := lookup_upd s r i
  rw [hMap]
  unfold expectedLookup
  by_cases hIi : i = r.client
  · rw [if_pos hIi]
    subst hIi
    cases hEq : lookup s.clients r.client with
    | none =>
      simp
    | some c =>
      simp
      have hcId : c.id = r.client := lookup_id hEq
      rw [upd_eq_advance s r c hcId]
  · rw [if_neg hIi]
    cases hEq : lookup s.clients i with
    | none =>
      simp
    | some c =>
      simp
      have hcId : c.id = i := lookup_id hEq
      have hNe : c.id ≠ r.client := by
        rw [hcId]
        exact hIi
      rw [upd_eq_self s r c hNe]

theorem step_ok_eq (s : State) (r : Request)
    (hNodup : (s.clients.map Client.id).Nodup)
    (c : Client) (hL : lookup s.clients r.client = some c)
    (hCond : c.start ≤ r.time ∧ windowCount s c r.time < s.limit) :
    step s r = (.ok, { s with clients := List.map (upd s r) s.clients }) := by
  unfold step upd
  simp [hNodup, hL, hCond]

theorem step_rej_of_nodup (s : State) (r : Request)
    (h : ¬ (s.clients.map Client.id).Nodup) :
    step s r = (.rejected, s) := by
  unfold step
  simp [h]

theorem step_rej_of_none (s : State) (r : Request)
    (hNodup : (s.clients.map Client.id).Nodup)
    (hL : lookup s.clients r.client = none) :
    step s r = (.rejected, s) := by
  unfold step
  simp [hNodup, hL]

theorem step_rej_of_cond (s : State) (r : Request)
    (hNodup : (s.clients.map Client.id).Nodup)
    (c : Client) (hL : lookup s.clients r.client = some c)
    (hCond : ¬ (c.start ≤ r.time ∧ windowCount s c r.time < s.limit)) :
    step s r = (.rejected, s) := by
  unfold step
  simp [hNodup, hL, hCond]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hAdm
  unfold Admissible at hAdm
  obtain ⟨hNodup, hAdmits⟩ := hAdm
  cases hL : lookup s.clients r.client with
  | none =>
    rw [hL] at hAdmits
    exact absurd hAdmits (by simp [Admits])
  | some c =>
    rw [hL] at hAdmits
    unfold Admits at hAdmits
    have hStep := step_ok_eq s r hNodup c hL hAdmits
    rw [hStep]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hNAdm
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · cases hL : lookup s.clients r.client with
    | none =>
      exact step_rej_of_none s r hNodup hL
    | some c =>
      by_cases hCond : c.start ≤ r.time ∧ windowCount s c r.time < s.limit
      · have hAdm : Admissible s r := by
          unfold Admissible
          refine ⟨hNodup, ?_⟩
          rw [hL]
          unfold Admits
          exact hCond
        exact absurd hAdm hNAdm
      · exact step_rej_of_cond s r hNodup c hL hCond
  · exact step_rej_of_nodup s r hNodup

theorem req_isolation : Isolation step := by
  intro s r i hNe
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · cases hL : lookup s.clients r.client with
    | none =>
      rw [step_rej_of_none s r hNodup hL]
    | some c =>
      by_cases hCond : c.start ≤ r.time ∧ windowCount s c r.time < s.limit
      · rw [step_ok_eq s r hNodup c hL hCond]
        simp only
        have hEq := lookup_upd_eq_expected s r i
        unfold expectedLookup at hEq
        rw [if_neg hNe] at hEq
        exact hEq
      · rw [step_rej_of_cond s r hNodup c hL hCond]
  · rw [step_rej_of_nodup s r hNodup]

theorem req_reset : ResetRule step := by
  intro s r hOk c0 hLook
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · cases hLc : lookup s.clients r.client with
    | none =>
      rw [step_rej_of_none s r hNodup hLc] at hOk
      contradiction
    | some d =>
      by_cases hCond : d.start ≤ r.time ∧ windowCount s d r.time < s.limit
      · have hCD : c0 = d := Option.some_inj.mp (hLook.symm.trans hLc)
        subst hCD
        have hCond0 : c0.start ≤ r.time ∧ windowCount s c0 r.time < s.limit := hCond
        have hLc0 : lookup s.clients r.client = some c0 := hLc
        have hStep := step_ok_eq s r hNodup c0 hLc0 hCond0
        have hcId : c0.id = r.client := lookup_id hLc0
        have h1 : upd s r c0 = advance s c0 r.time :=
          upd_eq_advance s r c0 hcId
        have h2 : Option.map (upd s r) (some c0) = some (advance s c0 r.time) := by
          simp only [Option.map_some, h1]
        have hMap := lookup_upd s r r.client
        rw [hLc0] at hMap
        rw [h2] at hMap
        have hLookAfter : lookup ({ s with clients := List.map (upd s r) s.clients } : State).clients r.client
            = some (advance s c0 r.time) := hMap
        rw [hStep]
        simp only
        refine ⟨advance s c0 r.time, hLookAfter, ?_, ?_⟩
        · intro hExp
          have hs : windowStart s c0 r.time = r.time := by
            unfold windowStart
            simp [hExp]
          have hc : windowCount s c0 r.time = 0 := by
            unfold windowCount
            simp [hExp]
          unfold advance
          rw [hs, hc]
          exact ⟨rfl, rfl⟩
        · intro hLt
          have hNot : ¬ c0.start + s.window ≤ r.time := Nat.not_le_of_gt hLt
          have hs : windowStart s c0 r.time = c0.start := by
            unfold windowStart
            simp [hNot]
          have hc : windowCount s c0 r.time = c0.count := by
            unfold windowCount
            simp [hNot]
          unfold advance
          rw [hs, hc]
          exact ⟨rfl, rfl⟩
      · rw [step_rej_of_cond s r hNodup d hLc hCond] at hOk
        contradiction
  · rw [step_rej_of_nodup s r hNodup] at hOk
    contradiction

theorem req_effects : Effects step := by
  intro s r hOk
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · cases hL : lookup s.clients r.client with
    | none =>
      rw [step_rej_of_none s r hNodup hL] at hOk
      contradiction
    | some c =>
      by_cases hCond : c.start ≤ r.time ∧ windowCount s c r.time < s.limit
      · have hStep := step_ok_eq s r hNodup c hL hCond
        rw [hStep]
        exact ⟨rfl, rfl, map_ids_upd_state s r, fun i => lookup_upd_eq_expected s r i⟩
      · rw [step_rej_of_cond s r hNodup c hL hCond] at hOk
        contradiction
  · rw [step_rej_of_nodup s r hNodup] at hOk
    contradiction

theorem req_window_bound : WindowBound step := by
  intro s r hBound c hMem
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · cases hL : lookup s.clients r.client with
    | none =>
      rw [step_rej_of_none s r hNodup hL] at hMem ⊢
      simp only at hMem ⊢
      exact hBound c hMem
    | some d =>
      by_cases hCond : d.start ≤ r.time ∧ windowCount s d r.time < s.limit
      · rw [step_ok_eq s r hNodup d hL hCond] at hMem ⊢
        simp only at hMem ⊢
        obtain ⟨x, hxMem, hxEq⟩ := List.mem_map.mp hMem
        unfold upd at hxEq
        by_cases hx : x.id = r.client
        · rw [if_pos hx] at hxEq
          have hdMem : d ∈ s.clients := lookup_mem hL
          have hdId : d.id = r.client := lookup_id hL
          have hIdEq : x.id = d.id := by rw [hx, hdId]
          have hxIsD : x = d := mem_eq_of_id_eq s.clients hNodup hxMem hdMem hIdEq
          rw [hxIsD] at hxEq
          rw [← hxEq]
          simp only [advance]
          obtain ⟨_, hLt⟩ := hCond
          exact Nat.succ_le_of_lt hLt
        · rw [if_neg hx] at hxEq
          rw [← hxEq]
          exact hBound x hxMem
      · rw [step_rej_of_cond s r hNodup d hL hCond] at hMem ⊢
        simp only at hMem ⊢
        exact hBound c hMem
  · rw [step_rej_of_nodup s r hNodup] at hMem ⊢
    simp only at hMem ⊢
    exact hBound c hMem

end FixedWindow
