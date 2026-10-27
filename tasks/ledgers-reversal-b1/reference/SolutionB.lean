import Reversal.Spec
import Reversal.Lemmas
/-!
# Reference solution B (hidden from agents)

Closed-form balance updates, Boolean validation, `List.find?` lookup, and reversed IDs
appended at the end of the list.
-/

namespace Reversal

instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance

/-- Boolean form of the posting check. -/
def postOk (s : State) (e : Entry) : Bool :=
  !e.lines.isEmpty && e.lines.all (fun l => s.accounts.contains l.1 && l.2 != 0) &&
  decide (lineSum e.lines = 0) && !(ids s.journal).contains e.id && !s.reversed.contains e.id

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if postOk s e then
      (.ok, { accounts := s.accounts, opening := s.opening,
              balance := fun a => s.balance a + netOf e.lines a,
              journal := s.journal ++ [e], reversed := s.reversed })
    else (.rejected, s)
  | .reverse i =>
    match s.journal.find? (fun x => x.id == i) with
    | none => (.rejected, s)
    | some e =>
      if s.reversed.contains i then (.rejected, s)
      else (.ok, { accounts := s.accounts, opening := s.opening,
                   balance := fun a => s.balance a - netOf e.lines a,
                   journal := s.journal, reversed := s.reversed ++ [i] })

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


theorem find_eq : ∀ (j : List Entry) (i : EntryId),
    j.find? (fun x => x.id == i) = findEntry j i := by
  intro j
  induction j with
  | nil => intro i; rfl
  | cons x xs ih =>
    intro i
    by_cases h : x.id = i
    · simp [List.find?, findEntry, h]
    · have hb : (x.id == i) = false := by simp [h]
      simp [List.find?, findEntry, h, hb, ih]

theorem postOk_iff (s : State) (e : Entry) : postOk s e = true ↔ ValidPost s e := by
  simp only [postOk, ValidPost, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨h1, fun l hl => (h2 l hl).1, fun l hl => (h2 l hl).2, h3, ?_, ?_⟩
    · simpa using h4
    · simpa using h5
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨⟨⟨h1, fun l hl => ⟨h2 l hl, h3 l hl⟩⟩, h4⟩, ?_⟩, ?_⟩
    · simpa using h5
    · simpa using h6

/-- State after posting `e`. -/
def postState (s : State) (e : Entry) : State :=
  { accounts := s.accounts, opening := s.opening,
    balance := fun a => s.balance a + netOf e.lines a,
    journal := s.journal ++ [e], reversed := s.reversed }

/-- State after reversing the stored entry `e` with ID `i`. -/
def revState (s : State) (i : EntryId) (e : Entry) : State :=
  { accounts := s.accounts, opening := s.opening,
    balance := fun a => s.balance a - netOf e.lines a,
    journal := s.journal, reversed := s.reversed ++ [i] }

theorem post_valid {s : State} {e : Entry} (h : ValidPost s e) :
    step s (.post e) = (.ok, postState s e) := by
  simp [step, (postOk_iff s e).mpr h, postState]

theorem post_invalid {s : State} {e : Entry} (h : ¬ ValidPost s e) :
    step s (.post e) = (.rejected, s) := by
  have : postOk s e = false := by
    cases hc : postOk s e
    · rfl
    · exact absurd ((postOk_iff s e).mp hc) h
  simp [step, this]

theorem rev_valid {s : State} {i : EntryId} {e : Entry} (hf : findEntry s.journal i = some e)
    (hi : i ∉ s.reversed) : step s (.reverse i) = (.ok, revState s i e) := by
  simp [step, find_eq, hf, hi, revState]

theorem rev_invalid {s : State} {i : EntryId} (h : ¬ ValidReverse s i) :
    step s (.reverse i) = (.rejected, s) := by
  cases hf : findEntry s.journal i with
  | none => simp [step, find_eq, hf]
  | some e =>
    have hmem : i ∈ ids s.journal := by
      have := findEntry_spec hf
      rw [← this.2]; exact List.mem_map_of_mem this.1
    have hi : i ∈ s.reversed := by
      by_cases hi : i ∈ s.reversed
      · exact hi
      · exact absurd ⟨hmem, hi⟩ h
    simp [step, find_eq, hf, hi]

theorem ok_post {s : State} {e : Entry} (h : (step s (.post e)).1 = .ok) : ValidPost s e := by
  by_cases hv : ValidPost s e
  · exact hv
  · rw [post_invalid hv] at h; cases h

theorem ok_rev {s : State} {i : EntryId} (h : (step s (.reverse i)).1 = .ok) :
    ValidReverse s i := by
  by_cases hv : ValidReverse s i
  · exact hv
  · rw [rev_invalid hv] at h; cases h

theorem rev_entry {s : State} {i : EntryId} (h : ValidReverse s i) :
    ∃ e, findEntry s.journal i = some e := by
  cases hf : findEntry s.journal i with
  | none => exact absurd h.1 (findEntry_none hf)
  | some e => exact ⟨e, rfl⟩

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h; rw [post_valid h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  obtain ⟨e, hf⟩ := rev_entry h
  rw [rev_valid hf h.2]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c with
  | post e => exact post_invalid h
  | reverse i => exact rev_invalid h

theorem req_post_effects : PostEffects step := by
  intro s e h
  rw [post_valid (ok_post h)]
  exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e h hf
  rw [rev_valid hf (ok_rev h).2]
  exact ⟨rfl, rfl, rfl, fun x => by simp [revState, or_comm], fun _ => rfl⟩

theorem req_reverse_once : ReverseOnce step := by
  intro s i h
  have hv := ok_rev h
  obtain ⟨e, hf⟩ := rev_entry hv
  rw [rev_valid hf hv.2]
  apply rev_invalid
  intro h'
  exact h'.2 (by simp [revState])

theorem req_roundtrip : RoundTrip step := by
  intro s e h
  have hv := ok_post h
  rw [post_valid hv]
  have hf : findEntry (postState s e).journal e.id = some e := findEntry_last hv.2.2.2.2.1
  have hi : e.id ∉ (postState s e).reversed := hv.2.2.2.2.2
  rw [rev_valid hf hi]
  refine ⟨rfl, ?_⟩
  funext a
  simp [revState, postState]

theorem req_trial_balance : TrialBalance step := by
  intro s c hw h
  cases c with
  | post e =>
    have hv := ok_post h
    rw [post_valid hv]
    show sumOver s.accounts (fun a => s.balance a + netOf e.lines a) = sumOver s.accounts s.balance
    rw [sumOver_add, sum_netOf hw.1 e.lines hv.2.1, hv.2.2.2.1]
    omega
  | reverse i =>
    have hv := ok_rev h
    obtain ⟨e, hf⟩ := rev_entry hv
    rw [rev_valid hf hv.2]
    have he := hw.2.2.2 e (findEntry_spec hf).1
    show sumOver s.accounts (fun a => s.balance a - netOf e.lines a) = sumOver s.accounts s.balance
    rw [sumOver_sub, sum_netOf hw.1 e.lines he.1, he.2]
    omega

theorem req_well_formed : StaysWellFormed step := by
  intro s c hw
  obtain ⟨hacc, hids, hrev, hent⟩ := hw
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · rw [post_valid hv]
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
    · rw [post_invalid hv]; exact ⟨hacc, hids, hrev, hent⟩
  | reverse i =>
    by_cases hv : ValidReverse s i
    · obtain ⟨e, hf⟩ := rev_entry hv
      rw [rev_valid hf hv.2]
      refine ⟨hacc, hids, ?_, hent⟩
      intro x hx
      simp only [revState, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact hrev x hx
      · subst hx; exact hv.1
    · rw [rev_invalid hv]; exact ⟨hacc, hids, hrev, hent⟩

theorem req_consistent : StaysConsistent step := by
  intro s c hw hc
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · rw [post_valid hv]
      intro a
      show s.balance a + netOf e.lines a = s.opening a +
        sumOver (s.journal ++ [e]) (fun x => if x.id ∈ s.reversed then 0 else netOf x.lines a)
      rw [hc a, sumOver_append]
      unfold activeNet
      simp [hv.2.2.2.2.2]
      omega
    · rw [post_invalid hv]; exact hc
  | reverse i =>
    by_cases hv : ValidReverse s i
    · obtain ⟨e, hf⟩ := rev_entry hv
      rw [rev_valid hf hv.2]
      intro a
      show s.balance a - netOf e.lines a = s.opening a +
        sumOver s.journal (fun x => if x.id ∈ s.reversed ++ [i] then 0 else netOf x.lines a)
      rw [hc a]
      unfold activeNet
      rw [active_reverse s.reversed (s.reversed ++ [i]) i e a (fun x => by simp [or_comm]) hv.2
        s.journal hw.2.1 hf]
      omega
    · rw [rev_invalid hv]; exact hc

end Reversal
