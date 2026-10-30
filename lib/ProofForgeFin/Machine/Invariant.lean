import ProofForgeFin.Machine.Record
/-!
# Invariant engineering

Proofs about state machines stand or fall with the invariant. `ProofForgeFin.Seq` has the
induction principles; this module has the means of building invariants.

* Conjunctions: `AllOf Is` (every invariant of a list), `Preserves.allOf`, and
  `Preserves.mutual` (two properties proved preserved together, each using the other).
* Strengthening: `Preserves.under` (an invariant that is preserved only in the presence of
  another one), `Preserves.of_iff` (replacing an invariant by an equivalent one).
* Ghost history: invariants `I s hist` relating the state to the operations performed so far
  (`run_hist_invariant`), and the prefix form over the trace of one fixed operation list
  (`run_take_hist_invariant`).
* Per-key invariants: `Frame view step touched` says an operation changes `view s j` only for the
  keys it touches. A property of every key is preserved when every operation re-establishes it on
  the keys it touches (`Frame.preserves_forall`, `FrameOne.preserves_forall`); keys no operation of
  a run touches keep their value (`Frame.run_untouched`). `frameOne_of_upd` and
  `frameOne_of_upd_or` derive the frame property from a step that updates one key with
  `Ledger.upd`, possibly under a condition (a refused operation changes nothing).
* `forallKey_preserves`: the general per-key form for properties `P j s` of the whole state, with a
  frame lemma for the other keys as hypothesis.
-/

namespace ProofForgeFin.Machine

open ProofForgeFin.Seq (Preserves run_invariant)

universe u v w x

variable {σ : Type u} {α : Type v}

/-! ## Conjunctions -/

/-- Every property of the list `Is` holds of `s`. -/
def AllOf (Is : List (σ → Prop)) (s : σ) : Prop := ∀ I ∈ Is, I s

/-- No properties: always true. -/
@[simp] theorem allOf_nil (s : σ) : AllOf [] s := fun _ h => absurd h List.not_mem_nil

/-- `AllOf` of `I :: Is` is `I` and `AllOf Is`. -/
@[simp] theorem allOf_cons (I : σ → Prop) (Is : List (σ → Prop)) (s : σ) :
    AllOf (I :: Is) s ↔ I s ∧ AllOf Is s := by
  unfold AllOf; simp

/-- When every property of the list is preserved, their conjunction is. -/
theorem Preserves.allOf {step : σ → α → σ} {Is : List (σ → Prop)}
    (h : ∀ I ∈ Is, Preserves step I) : Preserves step (AllOf Is) :=
  fun s a hs I hI => h I hI s a (hs I hI)

/-- When every property of the list is preserved on the states where all of them hold, their
conjunction is preserved: each component may use the others. -/
theorem Preserves.allOf_under {step : σ → α → σ} {Is : List (σ → Prop)}
    (h : ∀ I ∈ Is, ∀ s a, AllOf Is s → I (step s a)) : Preserves step (AllOf Is) :=
  fun s a hs I hI => h I hI s a hs

/-- Mutual induction: two properties preserved together, each step using both. -/
theorem Preserves.mutual {step : σ → α → σ} {I J : σ → Prop}
    (hI : ∀ s a, I s → J s → I (step s a)) (hJ : ∀ s a, I s → J s → J (step s a)) :
    Preserves step (fun s => I s ∧ J s) :=
  fun s a h => ⟨hI s a h.1 h.2, hJ s a h.1 h.2⟩

/-- Relative invariant: `I` is preserved on states satisfying the invariant `J`, so `I ∧ J` is an
invariant. -/
theorem Preserves.under {step : σ → α → σ} {I J : σ → Prop} (hJ : Preserves step J)
    (hI : ∀ s a, J s → I s → I (step s a)) : Preserves step (fun s => I s ∧ J s) :=
  fun s a h => ⟨hI s a h.2 h.1, hJ s a h.2⟩

/-- An invariant can be replaced by an equivalent property. -/
theorem Preserves.of_iff {step : σ → α → σ} {I J : σ → Prop} (h : Preserves step I)
    (hIJ : ∀ s, I s ↔ J s) : Preserves step J :=
  fun s a hs => (hIJ _).mp (h s a ((hIJ s).mpr hs))

/-- A property true of every state is an invariant. -/
theorem Preserves.of_forall {step : σ → α → σ} {I : σ → Prop} (h : ∀ s, I s) : Preserves step I :=
  fun _ _ _ => h _

/-- The left component of a preserved conjunction holds after every run. -/
theorem run_invariant_left {step : σ → α → σ} {I J : σ → Prop}
    (h : Preserves step (fun s => I s ∧ J s)) {s : σ} (hI : I s) (hJ : J s) (ops : List α) :
    I (Seq.run step s ops) :=
  (run_invariant (I := fun s => I s ∧ J s) h ⟨hI, hJ⟩ ops).1

/-! ## Ghost history -/

/-- Invariants relative to the history: when `I s hist` relates the state to the operations
performed so far and every operation extends it, it holds after every run with the history
extended by the run's operations. -/
theorem run_hist_invariant {step : σ → α → σ} {I : σ → List α → Prop}
    (h : ∀ s hist a, I s hist → I (step s a) (hist ++ [a])) {s : σ} {hist : List α}
    (h0 : I s hist) (ops : List α) : I (Seq.run step s ops) (hist ++ ops) := by
  induction ops generalizing s hist with
  | nil => simpa using h0
  | cons a as ih =>
    have := ih (h s hist a h0)
    rwa [List.append_assoc, List.singleton_append] at this

/-- The form from the start of the history: `I init []` and every step extends it, so the state
after `ops` is related to `ops`. -/
theorem run_hist_invariant_nil {step : σ → α → σ} {I : σ → List α → Prop}
    (h : ∀ s hist a, I s hist → I (step s a) (hist ++ [a])) {s : σ} (h0 : I s [])
    (ops : List α) : I (Seq.run step s ops) ops := by
  simpa using run_hist_invariant h h0 ops

/-- The prefix form: along one fixed list of operations, the state after the first `k`
operations is related to those `k` operations, for every `k`. -/
theorem run_take_hist_invariant {step : σ → α → σ} {I : σ → List α → Prop}
    (h : ∀ s hist a, I s hist → I (step s a) (hist ++ [a])) {s : σ} (h0 : I s [])
    (ops : List α) (k : Nat) : I (Seq.run step s (ops.take k)) (ops.take k) :=
  run_hist_invariant_nil h h0 _

/-- A history invariant whose steps need only the history to be a prefix of the full list of
operations: the operation applied after the prefix `ops.take k` is `ops[k]`. -/
theorem run_take_hist_invariant_of_prefix {step : σ → α → σ} {I : σ → List α → Prop}
    {ops : List α} (h : ∀ k (hk : k < ops.length) s, I s (ops.take k) →
      I (step s ops[k]) (ops.take (k + 1))) {s : σ} (h0 : I s []) :
    ∀ k, k ≤ ops.length → I (Seq.run step s (ops.take k)) (ops.take k) := by
  intro k
  induction k with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk
    have hk' : k < ops.length := by omega
    have e : ops.take (k + 1) = ops.take k ++ [ops[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk']; rfl
    rw [e, Seq.run_snoc, ← e]
    exact h k hk' _ (ih (by omega))

/-! ## Per-key invariants and frames -/

section Frame

variable {κ : Type w} {β : Type x}

/-- The operation `a` changes `view s j` only for the keys `j` of `touched a`. -/
def Frame (view : σ → κ → β) (step : σ → α → σ) (touched : α → List κ) : Prop :=
  ∀ s a j, j ∉ touched a → view (step s a) j = view s j

/-- The operation `a` changes `view s j` only for the key `key a`. -/
def FrameOne (view : σ → κ → β) (step : σ → α → σ) (key : α → κ) : Prop :=
  ∀ s a j, j ≠ key a → view (step s a) j = view s j

/-- A one-key frame is a frame with one touched key. -/
theorem FrameOne.frame {view : σ → κ → β} {step : σ → α → σ} {key : α → κ}
    (h : FrameOne view step key) : Frame view step (fun a => [key a]) :=
  fun s a j hj => h s a j (fun e => hj (e ▸ List.mem_singleton_self _))

/-- A property of every key is preserved when every operation re-establishes it on the keys it
touches (the other keys keep their value). -/
theorem Frame.preserves_forall {view : σ → κ → β} {step : σ → α → σ} {touched : α → List κ}
    (hf : Frame view step touched) {P : κ → β → Prop}
    (h : ∀ s a, (∀ j, P j (view s j)) → ∀ k ∈ touched a, P k (view (step s a) k)) :
    Preserves step (fun s => ∀ j, P j (view s j)) := by
  intro s a hs j
  by_cases hj : j ∈ touched a
  · exact h s a hs j hj
  · rw [hf s a j hj]; exact hs j

/-- The one-key form: an operation that re-establishes the property at its key preserves it at
every key. -/
theorem FrameOne.preserves_forall {view : σ → κ → β} {step : σ → α → σ} {key : α → κ}
    (hf : FrameOne view step key) {P : κ → β → Prop}
    (h : ∀ s a, (∀ j, P j (view s j)) → P (key a) (view (step s a) (key a))) :
    Preserves step (fun s => ∀ j, P j (view s j)) :=
  hf.frame.preserves_forall (fun s a hs k hk => by
    rw [List.mem_singleton] at hk; subst hk; exact h s a hs)

/-- A key that no operation of a run touches keeps its value. -/
theorem Frame.run_untouched {view : σ → κ → β} {step : σ → α → σ} {touched : α → List κ}
    (hf : Frame view step touched) {j : κ} {ops : List α} (h : ∀ a ∈ ops, j ∉ touched a)
    (s : σ) : view (Seq.run step s ops) j = view s j :=
  Seq.run_eq_of_mem (fun s => view s j) (fun t a ha => hf t a j (h a ha)) s

/-- The one-key form: a key different from the key of every operation of the run keeps its value. -/
theorem FrameOne.run_untouched {view : σ → κ → β} {step : σ → α → σ} {key : α → κ}
    (hf : FrameOne view step key) {j : κ} {ops : List α} (h : ∀ a ∈ ops, j ≠ key a) (s : σ) :
    view (Seq.run step s ops) j = view s j :=
  Seq.run_eq_of_mem (fun s => view s j) (fun t a ha => hf t a j (h a ha)) s

/-- A step that writes the view at one key with `Ledger.upd` has the one-key frame property. -/
theorem frameOne_of_upd [DecidableEq κ] {view : σ → κ → β} {step : σ → α → σ} {key : α → κ}
    (g : σ → α → β) (h : ∀ s a, view (step s a) = Ledger.upd (view s) (key a) (g s a)) :
    FrameOne view step key := by
  intro s a j hj; rw [h]; exact Ledger.upd_ne _ _ hj

/-- A step that either leaves the view unchanged (a refused operation) or writes it at one key
has the one-key frame property. -/
theorem frameOne_of_upd_or [DecidableEq κ] {view : σ → κ → β} {step : σ → α → σ} {key : α → κ}
    (h : ∀ s a, view (step s a) = view s ∨ ∃ v, view (step s a) = Ledger.upd (view s) (key a) v) :
    FrameOne view step key := by
  intro s a j hj
  rcases h s a with e | ⟨v, e⟩
  · rw [e]
  · rw [e]; exact Ledger.upd_ne _ _ hj

/-- A step that changes the view only at keys satisfying a condition on the operation, for
example "the accounts named by the entry". -/
theorem frame_of_pointwise {view : σ → κ → β} {step : σ → α → σ} {touched : α → List κ}
    (h : ∀ s a j, j ∉ touched a → view (step s a) j = view s j) : Frame view step touched := h

end Frame

/-- Per-key invariants of the whole state: `P j s` for every key `j`. When every operation
preserves `P j` for every key other than its own (the frame lemma) and re-establishes `P` at its
own key from `P` at every key, `P` holds at every key after every run. -/
theorem forallKey_preserves {κ : Type w} {step : σ → α → σ} {key : α → κ} {P : κ → σ → Prop}
    (hother : ∀ s a j, j ≠ key a → P j s → P j (step s a))
    (hkey : ∀ s a, (∀ j, P j s) → P (key a) (step s a)) : Preserves step (fun s => ∀ j, P j s) := by
  intro s a hs j
  by_cases hj : j = key a
  · subst hj; exact hkey s a hs
  · exact hother s a j hj (hs j)

/-- The form with a list of touched keys. -/
theorem forallKey_preserves_touched {κ : Type w} {step : σ → α → σ} {touched : α → List κ}
    {P : κ → σ → Prop} (hother : ∀ s a j, j ∉ touched a → P j s → P j (step s a))
    (hkey : ∀ s a, (∀ j, P j s) → ∀ k ∈ touched a, P k (step s a)) :
    Preserves step (fun s => ∀ j, P j s) := by
  intro s a hs j
  by_cases hj : j ∈ touched a
  · exact hkey s a hs j hj
  · exact hother s a j hj (hs j)

end ProofForgeFin.Machine
