import Reversal.Spec
import Reversal.Lemmas

namespace Reversal

instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance

instance instDecidableValid (s : State) (c : Command) : Decidable (Valid s c) := by
  cases c with
  | post e => unfold Valid; infer_instance
  | reverse i => unfold Valid ValidReverse; infer_instance

/-- Add `amt` to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

/-- Post every line, first to last. -/
def postLines : List Line → (AccountId → Int) → (AccountId → Int)
  | [], bal => bal
  | l :: ls, bal => postLines ls (adjust bal l.1 l.2)

/-- The same lines with every amount negated. -/
def negate (ls : List Line) : List Line := ls.map (fun l => (l.1, -l.2))

/-- State after posting `e`. -/
def postState (s : State) (e : Entry) : State :=
  { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }

/-- State after reversing the stored entry `e` with ID `i`. -/
def revState (s : State) (i : EntryId) (e : Entry) : State :=
  { s with balance := postLines (negate e.lines) s.balance, reversed := i :: s.reversed }

def refStep : Impl := fun s c =>
  match c with
  | .post e => if ValidPost s e then (.ok, postState s e) else (.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | some e => if i ∈ s.reversed then (.rejected, s) else (.ok, revState s i e)
    | none => (.rejected, s)

/-! ## Facts about lines and the journal -/

theorem postLines_eq : ∀ (ls : List Line) (bal : AccountId → Int) (a : AccountId),
    postLines ls bal a = bal a + netOf ls a := by
  intro ls
  induction ls with
  | nil => intro bal a; simp [postLines, netOf]
  | cons l ls ih =>
    intro bal a
    simp only [postLines, ih, adjust, netOf, sumOver_cons]
    by_cases h : a = l.1
    · subst h; simp; omega
    · have : l.1 ≠ a := fun h' => h h'.symm
      simp [h, this]

theorem netOf_negate (ls : List Line) (a : AccountId) : netOf (negate ls) a = - netOf ls a := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [negate, List.map_cons, netOf, sumOver_cons] at ih ⊢
    rw [ih]
    by_cases h : l.1 = a <;> simp [h] <;> omega

theorem findEntry_spec : ∀ {j : List Entry} {i : EntryId} {e : Entry},
    findEntry j i = some e → e ∈ j ∧ e.id = i := by
  intro j
  induction j with
  | nil => intro i e h; simp [findEntry] at h
  | cons x xs ih =>
    intro i e h
    simp only [findEntry] at h
    by_cases hx : x.id = i
    · simp [hx] at h; subst h; exact ⟨by simp, hx⟩
    · simp [hx] at h
      have := ih h
      exact ⟨by simp [this.1], this.2⟩

theorem findEntry_none : ∀ {j : List Entry} {i : EntryId}, findEntry j i = none → i ∉ ids j := by
  intro j
  induction j with
  | nil => intro i _; simp [ids]
  | cons x xs ih =>
    intro i h
    simp only [findEntry] at h
    by_cases hx : x.id = i
    · simp [hx] at h
    · simp only [hx, ite_false] at h
      have := ih h
      simp only [ids, List.map_cons, List.mem_cons, not_or] at this ⊢
      exact ⟨fun h' => hx h'.symm, this⟩

theorem findEntry_last {j : List Entry} {e : Entry} (h : e.id ∉ ids j) :
    findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil => simp [findEntry]
  | cons x xs ih =>
    simp only [ids, List.map_cons, List.mem_cons, not_or] at h
    simp only [List.cons_append, findEntry, Ne.symm h.1, ite_false]
    exact ih h.2

theorem sumOver_zero {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Summing the net effect of the lines over the universe gives the sum of the lines. -/
theorem sum_netOf {accts : List AccountId} (hnd : accts.Nodup) : ∀ (ls : List Line),
    (∀ l ∈ ls, l.1 ∈ accts) → sumOver accts (netOf ls) = lineSum ls := by
  intro ls
  induction ls with
  | nil => intro _; exact sumOver_zero accts
  | cons l ls ih =>
    intro hk
    have h1 : netOf (l :: ls) = fun a => (if a = l.1 then l.2 else 0) + netOf ls a := by
      funext a
      simp only [netOf, sumOver_cons]
      by_cases h : a = l.1
      · subst h; simp
      · have : l.1 ≠ a := fun h' => h h'.symm
        simp [h, this]
    rw [h1, sumOver_add, sumOver_ite_eq hnd, ih (fun x hx => hk x (by simp [hx]))]
    simp [lineSum, hk l (by simp)]

/-- Marking the entry `e` with ID `i` as reversed removes exactly its net from the active
sum. -/
theorem active_reverse (R R' : List EntryId) (i : EntryId) (e : Entry) (a : AccountId)
    (hR : ∀ x, x ∈ R' ↔ x = i ∨ x ∈ R) (hi : i ∉ R) : ∀ (j : List Entry),
    (ids j).Nodup → findEntry j i = some e →
    sumOver j (fun x => if x.id ∈ R' then 0 else netOf x.lines a)
      = sumOver j (fun x => if x.id ∈ R then 0 else netOf x.lines a) - netOf e.lines a := by
  intro j
  induction j with
  | nil => intro _ h; simp [findEntry] at h
  | cons x xs ih =>
    intro hnd hf
    simp only [ids, List.map_cons, List.nodup_cons] at hnd
    simp only [findEntry] at hf
    simp only [sumOver_cons]
    by_cases hx : x.id = i
    · simp only [hx, ite_true, Option.some.injEq] at hf
      subst hf
      have hrest : sumOver xs (fun y => if y.id ∈ R' then 0 else netOf y.lines a)
          = sumOver xs (fun y => if y.id ∈ R then 0 else netOf y.lines a) := by
        apply sumOver_congr
        intro y hy
        have hyi : y.id ≠ i := by
          intro h'
          apply hnd.1
          rw [hx.trans h'.symm]
          exact List.mem_map_of_mem hy
        have : (y.id ∈ R') ↔ (y.id ∈ R) := by rw [hR]; simp [hyi]
        simp only [this]
      have h1 : x.id ∈ R' := (hR _).mpr (Or.inl hx)
      have h2 : x.id ∉ R := hx ▸ hi
      simp only [h1, h2, ite_true, ite_false, hrest]
      omega
    · simp only [hx, ite_false] at hf
      have : (x.id ∈ R') ↔ (x.id ∈ R) := by rw [hR]; simp [hx]
      simp only [this, ih hnd.2 hf]
      omega

/-! ## The refStep function case by case -/

theorem post_valid {s : State} {e : Entry} (h : ValidPost s e) :
    refStep s (.post e) = (.ok, postState s e) := by
  simp [refStep, h]

theorem post_invalid {s : State} {e : Entry} (h : ¬ ValidPost s e) :
    refStep s (.post e) = (.rejected, s) := by
  simp [refStep, h]

theorem rev_valid {s : State} {i : EntryId} {e : Entry} (hf : findEntry s.journal i = some e)
    (hi : i ∉ s.reversed) : refStep s (.reverse i) = (.ok, revState s i e) := by
  simp [refStep, hf, hi]

theorem rev_invalid {s : State} {i : EntryId} (h : ¬ ValidReverse s i) :
    refStep s (.reverse i) = (.rejected, s) := by
  cases hf : findEntry s.journal i with
  | none => simp [refStep, hf]
  | some e =>
    have hmem : i ∈ ids s.journal := by
      have := findEntry_spec hf
      rw [← this.2]; exact List.mem_map_of_mem this.1
    have hi : i ∈ s.reversed := by
      by_cases hi : i ∈ s.reversed
      · exact hi
      · exact absurd ⟨hmem, hi⟩ h
    simp [refStep, hf, hi]

theorem ok_post {s : State} {e : Entry} (h : (refStep s (.post e)).1 = .ok) : ValidPost s e := by
  by_cases hv : ValidPost s e
  · exact hv
  · rw [post_invalid hv] at h; cases h

theorem ok_rev {s : State} {i : EntryId} (h : (refStep s (.reverse i)).1 = .ok) :
    ValidReverse s i := by
  by_cases hv : ValidReverse s i
  · exact hv
  · rw [rev_invalid hv] at h; cases h

theorem rev_entry {s : State} {i : EntryId} (h : ValidReverse s i) :
    ∃ e, findEntry s.journal i = some e := by
  cases hf : findEntry s.journal i with
  | none => exact absurd h.1 (findEntry_none hf)
  | some e => exact ⟨e, rfl⟩

/-- Every refStep either leaves the state unchanged, posts a valid entry, or reverses a stored
entry. -/
theorem step_cases (s : State) (c : Command) :
    (refStep s c).2 = s ∨
    (∃ e, c = .post e ∧ ValidPost s e ∧ (refStep s c).2 = postState s e) ∨
    (∃ i e, c = .reverse i ∧ findEntry s.journal i = some e ∧ i ∉ s.reversed ∧
      (refStep s c).2 = revState s i e) := by
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · exact Or.inr (Or.inl ⟨e, rfl, hv, by rw [post_valid hv]⟩)
    · exact Or.inl (by rw [post_invalid hv])
  | reverse i =>
    by_cases hv : ValidReverse s i
    · obtain ⟨e, hf⟩ := rev_entry hv
      exact Or.inr (Or.inr ⟨i, e, rfl, hf, hv.2, by rw [rev_valid hf hv.2]⟩)
    · exact Or.inl (by rw [rev_invalid hv])

theorem ok_cases {s : State} {c : Command} (h : (refStep s c).1 = .ok) :
    (∃ e, c = .post e ∧ ValidPost s e ∧ (refStep s c).2 = postState s e) ∨
    (∃ i e, c = .reverse i ∧ findEntry s.journal i = some e ∧ i ∉ s.reversed ∧
      (refStep s c).2 = revState s i e) := by
  cases c with
  | post e =>
    have hv := ok_post h
    exact Or.inl ⟨e, rfl, hv, by rw [post_valid hv]⟩
  | reverse i =>
    have hv := ok_rev h
    obtain ⟨e, hf⟩ := rev_entry hv
    exact Or.inr ⟨i, e, rfl, hf, hv.2, by rw [rev_valid hf hv.2]⟩

/-! ## Requirements -/

theorem ref_req_post_succeeds : PostSucceeds refStep := by
  intro s e h; rw [post_valid h]

theorem ref_req_reverse_succeeds : ReverseSucceeds refStep := by
  intro s i h
  obtain ⟨e, hf⟩ := rev_entry h
  rw [rev_valid hf h.2]

theorem ref_req_invalid_noop : InvalidNoop refStep := by
  intro s c h
  cases c with
  | post e => exact post_invalid h
  | reverse i => exact rev_invalid h

theorem ref_req_post_effects : PostEffects refStep := by
  intro s e h
  rw [post_valid (ok_post h)]
  exact ⟨rfl, rfl, rfl, rfl, fun a => postLines_eq _ _ a⟩

theorem ref_req_reverse_effects : ReverseEffects refStep := by
  intro s i e h hf
  rw [rev_valid hf (ok_rev h).2]
  refine ⟨rfl, rfl, rfl, fun x => by simp [revState], fun a => ?_⟩
  simp only [revState]
  rw [postLines_eq, netOf_negate]
  omega

theorem ref_req_reverse_once : ReverseOnce refStep := by
  intro s i h
  have hv := ok_rev h
  obtain ⟨e, hf⟩ := rev_entry hv
  rw [rev_valid hf hv.2]
  apply rev_invalid
  intro h'
  exact h'.2 (by simp [revState])

theorem ref_req_roundtrip : RoundTrip refStep := by
  intro s e h
  have hv := ok_post h
  rw [post_valid hv]
  have hf : findEntry (postState s e).journal e.id = some e := findEntry_last hv.2.2.2.2.1
  have hi : e.id ∉ (postState s e).reversed := hv.2.2.2.2.2
  rw [rev_valid hf hi]
  refine ⟨rfl, ?_⟩
  funext a
  simp only [revState, postState]
  rw [postLines_eq, postLines_eq, netOf_negate]
  omega

theorem ref_req_trial_balance : TrialBalance refStep := by
  intro s c hw h
  rcases ok_cases h with ⟨e, _, hv, hs⟩ | ⟨i, e, _, hf, _, hs⟩
  · rw [hs]
    unfold total
    simp only [postState]
    rw [sumOver_congr _ _ _ (fun a _ => postLines_eq e.lines s.balance a), sumOver_add,
      sum_netOf hw.1 e.lines hv.2.1, hv.2.2.2.1]
    omega
  · rw [hs]
    have he := (hw.2.2.2 e (findEntry_spec hf).1)
    unfold total
    simp only [revState]
    rw [sumOver_congr _ _ _ (fun a _ => postLines_eq (negate e.lines) s.balance a),
      sumOver_add, sumOver_congr _ _ _ (fun a _ => netOf_negate e.lines a)]
    have : sumOver s.accounts (fun a => - netOf e.lines a) = - sumOver s.accounts (netOf e.lines) := by
      have := sumOver_sub s.accounts (fun _ => (0 : Int)) (netOf e.lines)
      simp only [sumOver_zero] at this
      simpa using this
    rw [this, sum_netOf hw.1 e.lines he.1, he.2]
    omega

theorem ref_req_well_formed : StaysWellFormed refStep := by
  intro s c hw
  obtain ⟨hacc, hids, hrev, hent⟩ := hw
  rcases step_cases s c with hs | ⟨e, _, hv, hs⟩ | ⟨i, e, _, hf, _, hs⟩
  · rw [hs]; exact ⟨hacc, hids, hrev, hent⟩
  · rw [hs]
    simp only [postState, WellFormed, ids, List.map_append, List.map_cons, List.map_nil]
    refine ⟨hacc, ?_, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hids, by simp, ?_⟩
      intro x hx y hy hxy
      simp at hy
      subst hxy; subst hy
      exact hv.2.2.2.2.1 hx
    · intro x hx
      exact List.mem_append_left _ (hrev x hx)
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hent x hx
      · simp at hx; subst hx; exact ⟨hv.2.1, hv.2.2.2.1⟩
  · rw [hs]
    simp only [revState, WellFormed]
    refine ⟨hacc, hids, ?_, hent⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with hx | hx
    · subst hx
      have := findEntry_spec hf
      rw [← this.2]; exact List.mem_map_of_mem this.1
    · exact hrev x hx

theorem ref_req_consistent : StaysConsistent refStep := by
  intro s c hw hc
  rcases step_cases s c with hs | ⟨e, _, hv, hs⟩ | ⟨i, e, _, hf, hi, hs⟩
  · rw [hs]; exact hc
  · rw [hs]
    intro a
    show postLines e.lines s.balance a = s.opening a +
      sumOver (s.journal ++ [e]) (fun x => if x.id ∈ s.reversed then 0 else netOf x.lines a)
    rw [postLines_eq, hc a, sumOver_append]
    unfold activeNet
    simp [hv.2.2.2.2.2]
    omega
  · rw [hs]
    intro a
    show postLines (negate e.lines) s.balance a = s.opening a +
      sumOver s.journal (fun x => if x.id ∈ i :: s.reversed then 0 else netOf x.lines a)
    rw [postLines_eq, netOf_negate, hc a]
    unfold activeNet
    rw [active_reverse s.reversed (i :: s.reversed) i e a (fun x => by simp) hi s.journal hw.2.1 hf]
    omega

/-! Attack: the proved definition is the reference, but compiled code re-posts the entry on
a reversal. -/

/-- Compiled replacement. -/
def fastStep : Impl := fun s c =>
  match c with
  | .post e => refStep s (.post e)
  | .reverse i =>
    match findEntry s.journal i with
    | some e =>
      if i ∈ s.reversed then (.rejected, s)
      else (.ok, { s with balance := postLines e.lines s.balance, reversed := i :: s.reversed })
    | none => (.rejected, s)

@[implemented_by fastStep]
def step : Impl := refStep

theorem req_post_succeeds    : PostSucceeds step := ref_req_post_succeeds
theorem req_reverse_succeeds : ReverseSucceeds step := ref_req_reverse_succeeds
theorem req_invalid_noop     : InvalidNoop step := ref_req_invalid_noop
theorem req_post_effects     : PostEffects step := ref_req_post_effects
theorem req_reverse_effects  : ReverseEffects step := ref_req_reverse_effects
theorem req_reverse_once     : ReverseOnce step := ref_req_reverse_once
theorem req_roundtrip        : RoundTrip step := ref_req_roundtrip
theorem req_trial_balance    : TrialBalance step := ref_req_trial_balance
theorem req_well_formed      : StaysWellFormed step := ref_req_well_formed
theorem req_consistent       : StaysConsistent step := ref_req_consistent

end Reversal
