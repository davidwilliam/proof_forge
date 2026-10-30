import ProofForgeFin
/-!
# Demonstration: the requirements of `ledgers-reversal-b3` with `ProofForgeFin.Machine.Journal`

The specification definitions below are copied without change from
`tasks/ledgers-reversal-b3/spec/Reversal/Spec.lean`, and the implementation (`adjust`,
`postLines`, `negate`, `postState`, `revState`, `step`) from
`tasks/ledgers-reversal-b3/reference/SolutionA.lean`. The task files are not imported or
modified.

The reference solution proves the ten requirements with its own facts about lines (`postLines_eq`,
`netOf_negate`, `sumOver_zero`, `sum_netOf`) and about reversal marks (`active_reverse`, an
induction over the journal), on top of the `sumOver` lemmas of the task's `Reversal/Lemmas.lean`.
Here those facts are library theorems: `Journal.post_negate_apply` (REQ-REVERSE-EFFECTS),
`Journal.post_post_negate` (REQ-ROUNDTRIP), `Journal.trial_balance_post` with
`Journal.Known.negate` and `Journal.Balanced.negate` (REQ-TRIAL-BALANCE) and `Journal.sumOver_mark`
(REQ-CONSISTENT). What remains is specific to the implementation: the journal lookup `findEntry`
and the case analysis of `step`.
-/

namespace ProofForgeFinDemo.Machine.ReversalB3

open ProofForgeFin ProofForgeFin.Machine

/-! ## Copied from `spec/Reversal/Spec.lean` -/

abbrev AccountId := Nat
abbrev EntryId := Nat

/-- One journal line: an account and a signed amount in cents. -/
abbrev Line := AccountId × Int

/-- A journal entry. An account may appear on several lines. -/
structure Entry where
  id    : EntryId
  lines : List Line

/-- Ledger state: a fixed account universe, opening balances, current balances, the journal
of posted entries (oldest first), and the IDs of reversed entries. -/
structure State where
  accounts : List AccountId
  opening  : AccountId → Int
  balance  : AccountId → Int
  journal  : List Entry
  reversed : List EntryId

/-- A command posts a new entry or reverses a posted entry by ID. -/
inductive Command where
  | post (e : Entry)
  | reverse (i : EntryId)

inductive Outcome where
  | ok
  | rejected
  deriving DecidableEq, Repr

/-- An implementation returns an outcome and the next state. -/
abbrev Impl := State → Command → Outcome × State

/-- Sum of an integer-valued function over a list. -/
def sumOver {α : Type} (l : List α) (f : α → Int) : Int :=
  l.foldr (fun a acc => f a + acc) 0

/-- Trial balance: the sum of all balances over the account universe. -/
def total (s : State) : Int := sumOver s.accounts s.balance

/-- Sum of the amounts on a list of lines. -/
def lineSum (ls : List Line) : Int := sumOver ls (·.2)

/-- Net amount the lines post to account `a`. -/
def netOf (ls : List Line) (a : AccountId) : Int :=
  sumOver ls (fun l => if l.1 = a then l.2 else 0)

/-- The IDs of the journal entries, in journal order. -/
def ids (j : List Entry) : List EntryId := j.map (·.id)

/-- The first journal entry with ID `i`, if any. -/
def findEntry : List Entry → EntryId → Option Entry
  | [], _ => none
  | e :: es, i => if e.id = i then some e else findEntry es i

/-- Net amount that the entries not yet reversed post to account `a`. -/
def activeNet (s : State) (a : AccountId) : Int :=
  sumOver s.journal (fun e => if e.id ∈ s.reversed then 0 else netOf e.lines a)

/-- Structural invariant: distinct accounts, distinct journal IDs, only journal IDs are
marked reversed, and every journal entry is balanced and touches only known accounts. -/
def WellFormed (s : State) : Prop :=
  s.accounts.Nodup ∧
  (ids s.journal).Nodup ∧
  (∀ i ∈ s.reversed, i ∈ ids s.journal) ∧
  (∀ e ∈ s.journal, (∀ l ∈ e.lines, l.1 ∈ s.accounts) ∧ lineSum e.lines = 0)

/-- Every balance equals its opening balance plus the net of the entries not reversed. -/
def Consistent (s : State) : Prop :=
  ∀ a, s.balance a = s.opening a + activeNet s a

/-- The conditions under which posting an entry must succeed. -/
def ValidPost (s : State) (e : Entry) : Prop :=
  e.lines ≠ [] ∧
  (∀ l ∈ e.lines, l.1 ∈ s.accounts) ∧
  (∀ l ∈ e.lines, l.2 ≠ 0) ∧
  lineSum e.lines = 0 ∧
  e.id ∉ ids s.journal ∧
  e.id ∉ s.reversed

/-- The conditions under which reversing entry `i` must succeed. -/
def ValidReverse (s : State) (i : EntryId) : Prop :=
  i ∈ ids s.journal ∧ i ∉ s.reversed

/-- The conditions under which a command must succeed. -/
def Valid (s : State) : Command → Prop
  | .post e => ValidPost s e
  | .reverse i => ValidReverse s i

/-- REQ-POST-SUCCEEDS: every valid posting succeeds. -/
def PostSucceeds (step : Impl) : Prop :=
  ∀ s e, ValidPost s e → (step s (.post e)).1 = .ok

/-- REQ-REVERSE-SUCCEEDS: every valid reversal succeeds. -/
def ReverseSucceeds (step : Impl) : Prop :=
  ∀ s i, ValidReverse s i → (step s (.reverse i)).1 = .ok

/-- REQ-INVALID-NOOP: every invalid command is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s c, ¬ Valid s c → step s c = (.rejected, s)

/-- REQ-POST-EFFECTS: a successful posting appends the entry to the journal, adds the net
of its lines to each balance, and changes nothing else. -/
def PostEffects (step : Impl) : Prop :=
  ∀ s e, (step s (.post e)).1 = .ok →
    (step s (.post e)).2.accounts = s.accounts ∧
    (step s (.post e)).2.opening = s.opening ∧
    (step s (.post e)).2.journal = s.journal ++ [e] ∧
    (step s (.post e)).2.reversed = s.reversed ∧
    ∀ a, (step s (.post e)).2.balance a = s.balance a + netOf e.lines a

/-- REQ-REVERSE-EFFECTS: a successful reversal of the entry `e` with ID `i` keeps the
journal, marks exactly `i` as newly reversed, subtracts the net of `e`'s lines from each
balance, and changes nothing else. -/
def ReverseEffects (step : Impl) : Prop :=
  ∀ s i e, (step s (.reverse i)).1 = .ok → findEntry s.journal i = some e →
    (step s (.reverse i)).2.accounts = s.accounts ∧
    (step s (.reverse i)).2.opening = s.opening ∧
    (step s (.reverse i)).2.journal = s.journal ∧
    (∀ x, x ∈ (step s (.reverse i)).2.reversed ↔ x = i ∨ x ∈ s.reversed) ∧
    ∀ a, (step s (.reverse i)).2.balance a = s.balance a - netOf e.lines a

/-- REQ-REVERSE-ONCE: after a successful reversal, reversing the same ID again is rejected
and leaves the state unchanged. -/
def ReverseOnce (step : Impl) : Prop :=
  ∀ s i, (step s (.reverse i)).1 = .ok →
    step (step s (.reverse i)).2 (.reverse i) = (.rejected, (step s (.reverse i)).2)

/-- REQ-ROUNDTRIP: right after a successful posting, reversing the posted entry succeeds and
restores every balance to its value before the posting. -/
def RoundTrip (step : Impl) : Prop :=
  ∀ s e, (step s (.post e)).1 = .ok →
    (step (step s (.post e)).2 (.reverse e.id)).1 = .ok ∧
    (step (step s (.post e)).2 (.reverse e.id)).2.balance = s.balance

/-- REQ-TRIAL-BALANCE: in a well-formed state, every successful command keeps the sum of
all balances unchanged. -/
def TrialBalance (step : Impl) : Prop :=
  ∀ s c, WellFormed s → (step s c).1 = .ok → total (step s c).2 = total s

/-- REQ-WELL-FORMED: every command keeps a well-formed state well-formed. -/
def StaysWellFormed (step : Impl) : Prop :=
  ∀ s c, WellFormed s → WellFormed (step s c).2

/-- REQ-CONSISTENT: in a well-formed state, every command keeps each balance equal to its
opening balance plus the net of the entries not reversed. -/
def StaysConsistent (step : Impl) : Prop :=
  ∀ s c, WellFormed s → Consistent s → Consistent (step s c).2

/-! ## Copied from `reference/SolutionA.lean`: the implementation -/

instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance

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

def step : Impl := fun s c =>
  match c with
  | .post e => if ValidPost s e then (.ok, postState s e) else (.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | some e => if i ∈ s.reversed then (.rejected, s) else (.ok, revState s i e)
    | none => (.rejected, s)

/-! ## The task's definitions are the library's -/

/-- The task's `sumOver` is the library's. -/
theorem sumOver_eq {α : Type} : @sumOver α = @Ledger.sumOver α := rfl

/-- The task's posting loop is the library's `post`. -/
theorem postLines_eq (ls : List Line) (bal : AccountId → Int) :
    postLines ls bal = Machine.Journal.post bal ls := by
  rw [← Machine.Journal.postLines_eq_post]
  induction ls generalizing bal with
  | nil => rfl
  | cons l ls ih => exact ih _

/-- The task's `netOf` is the library's. -/
theorem netOf_eq (ls : List Line) (a : AccountId) : Machine.Journal.netOf ls a = netOf ls a := rfl

/-- The task's reversing entry is the library's. -/
theorem negate_eq (ls : List Line) : negate ls = Machine.Journal.negate ls := rfl

/-! ## The journal lookup (specific to the task) -/

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
      exact ⟨by simp [(ih h).1], (ih h).2⟩

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

/-! ## The step function case by case (specific to the implementation) -/

theorem post_valid {s : State} {e : Entry} (h : ValidPost s e) :
    step s (.post e) = (.ok, postState s e) := by simp [step, h]

theorem post_invalid {s : State} {e : Entry} (h : ¬ ValidPost s e) :
    step s (.post e) = (.rejected, s) := by simp [step, h]

theorem rev_valid {s : State} {i : EntryId} {e : Entry} (hf : findEntry s.journal i = some e)
    (hi : i ∉ s.reversed) : step s (.reverse i) = (.ok, revState s i e) := by simp [step, hf, hi]

theorem rev_invalid {s : State} {i : EntryId} (h : ¬ ValidReverse s i) :
    step s (.reverse i) = (.rejected, s) := by
  cases hf : findEntry s.journal i with
  | none => simp [step, hf]
  | some e =>
    have hmem : i ∈ ids s.journal := (findEntry_spec hf).2 ▸ List.mem_map_of_mem (findEntry_spec hf).1
    have hi : i ∈ s.reversed := Classical.byContradiction fun hi => h ⟨hmem, hi⟩
    simp [step, hf, hi]

theorem ok_post {s : State} {e : Entry} (h : (step s (.post e)).1 = .ok) : ValidPost s e :=
  Classical.byContradiction fun hv => by rw [post_invalid hv] at h; cases h

theorem ok_rev {s : State} {i : EntryId} (h : (step s (.reverse i)).1 = .ok) : ValidReverse s i :=
  Classical.byContradiction fun hv => by rw [rev_invalid hv] at h; cases h

theorem rev_entry {s : State} {i : EntryId} (h : ValidReverse s i) :
    ∃ e, findEntry s.journal i = some e := by
  cases hf : findEntry s.journal i with
  | none => exact absurd h.1 (findEntry_none hf)
  | some e => exact ⟨e, rfl⟩

theorem step_cases (s : State) (c : Command) :
    (step s c).2 = s ∨
    (∃ e, c = .post e ∧ ValidPost s e ∧ (step s c).2 = postState s e) ∨
    (∃ i e, c = .reverse i ∧ findEntry s.journal i = some e ∧ i ∉ s.reversed ∧
      (step s c).2 = revState s i e) := by
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

theorem ok_cases {s : State} {c : Command} (h : (step s c).1 = .ok) :
    (∃ e, c = .post e ∧ ValidPost s e ∧ (step s c).2 = postState s e) ∨
    (∃ i e, c = .reverse i ∧ findEntry s.journal i = some e ∧ i ∉ s.reversed ∧
      (step s c).2 = revState s i e) := by
  rcases step_cases s c with hs | h1 | h2
  · cases c with
    | post e => exact Or.inl ⟨e, rfl, ok_post h, by rw [post_valid (ok_post h)]⟩
    | reverse i =>
      obtain ⟨e, hf⟩ := rev_entry (ok_rev h)
      exact Or.inr ⟨i, e, rfl, hf, (ok_rev h).2, by rw [rev_valid hf (ok_rev h).2]⟩
  · exact Or.inl h1
  · exact Or.inr h2

/-! ## Requirements, with the library -/

theorem req_post_succeeds : PostSucceeds step := fun s e h => by rw [post_valid h]

theorem req_reverse_succeeds : ReverseSucceeds step := fun s i h => by
  obtain ⟨e, hf⟩ := rev_entry h; rw [rev_valid hf h.2]

theorem req_invalid_noop : InvalidNoop step := fun _ c h => by
  cases c with
  | post e => exact post_invalid h
  | reverse i => exact rev_invalid h

theorem req_post_effects : PostEffects step := fun s e h => by
  rw [post_valid (ok_post h)]
  exact ⟨rfl, rfl, rfl, rfl, fun a => by simp only [postState, postLines_eq]; rfl⟩

theorem req_reverse_effects : ReverseEffects step := fun s i e h hf => by
  rw [rev_valid hf (ok_rev h).2]
  refine ⟨rfl, rfl, rfl, fun x => by simp [revState], fun a => ?_⟩
  simp only [revState, postLines_eq]
  exact Machine.Journal.post_negate_apply _ _ a

theorem req_reverse_once : ReverseOnce step := fun s i h => by
  obtain ⟨e, hf⟩ := rev_entry (ok_rev h)
  rw [rev_valid hf (ok_rev h).2]
  exact rev_invalid (fun h' => h'.2 (by simp [revState]))

theorem req_roundtrip : RoundTrip step := fun s e h => by
  have hv := ok_post h
  rw [post_valid hv, rev_valid (s := postState s e) (findEntry_last hv.2.2.2.2.1) hv.2.2.2.2.2]
  refine ⟨rfl, ?_⟩
  simp only [revState, postState, postLines_eq]
  exact Machine.Journal.post_post_negate _ _

theorem req_trial_balance : TrialBalance step := fun s c hw h => by
  unfold total; rw [sumOver_eq]
  rcases ok_cases h with ⟨e, _, hv, hs⟩ | ⟨i, e, _, hf, _, hs⟩
  · rw [hs]; simp only [postState, postLines_eq]
    exact Machine.Journal.trial_balance_post hw.1 _ hv.2.1 hv.2.2.2.1
  · rw [hs]; simp only [revState, postLines_eq]
    have he := hw.2.2.2 e (findEntry_spec hf).1
    exact Machine.Journal.trial_balance_post hw.1 _ (Machine.Journal.Known.negate (l := s.accounts) he.1)
      (Machine.Journal.Balanced.negate he.2)

theorem req_well_formed : StaysWellFormed step := by
  intro s c hw
  obtain ⟨hacc, hids, hrev, hent⟩ := hw
  rcases step_cases s c with hs | ⟨e, _, hv, hs⟩ | ⟨i, e, _, hf, _, hs⟩
  · rw [hs]; exact ⟨hacc, hids, hrev, hent⟩
  · rw [hs]
    simp only [postState, WellFormed, ids, List.map_append, List.map_cons, List.map_nil]
    refine ⟨hacc, ?_, fun x hx => List.mem_append_left _ (hrev x hx), fun x hx => ?_⟩
    · rw [List.nodup_append]
      refine ⟨hids, by simp, fun x hx y hy hxy => ?_⟩
      simp at hy; subst hxy; subst hy; exact hv.2.2.2.2.1 hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hent x hx
      · simp at hx; subst hx; exact ⟨hv.2.1, hv.2.2.2.1⟩
  · rw [hs]
    refine ⟨hacc, hids, fun x hx => ?_, hent⟩
    rcases List.mem_cons.mp hx with hx | hx
    · subst hx; exact (findEntry_spec hf).2 ▸ List.mem_map_of_mem (findEntry_spec hf).1
    · exact hrev x hx

theorem req_consistent : StaysConsistent step := by
  intro s c hw hc
  rcases step_cases s c with hs | ⟨e, _, hv, hs⟩ | ⟨i, e, _, hf, hi, hs⟩
  · rw [hs]; exact hc
  · rw [hs]
    intro a
    simp only [postState, activeNet, postLines_eq, Machine.Journal.post_apply, netOf_eq, sumOver_eq,
      Ledger.sumOver_append, Ledger.sumOver_cons, Ledger.sumOver_nil, hv.2.2.2.2.2, ite_false]
    rw [hc a]; unfold activeNet; rw [sumOver_eq]; omega
  · rw [hs]
    intro a
    simp only [revState, activeNet, postLines_eq, negate_eq, sumOver_eq]
    rw [Machine.Journal.post_negate_apply, hc a, Machine.Journal.sumOver_mark (fun x : Entry => x.id)
      (fun x : Entry => netOf x.lines a) (R := s.reversed) (fun x => List.mem_cons) hi hw.2.1
      (findEntry_spec hf).1 (findEntry_spec hf).2]
    unfold activeNet; rw [sumOver_eq, netOf_eq]; omega

end ProofForgeFinDemo.Machine.ReversalB3
