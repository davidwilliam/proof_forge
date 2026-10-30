import ProofForgeFin.Machine.Record
/-!
# Trace properties, commuting operations and atomic batches

Safety requirements over runs, without liveness: a property holds in every state a run passes
through, a bad state is never reached, a property stays true once it holds, a field changes at
most once, a quantity never decreases along a run. And two facts about the order of operations:
commuting operations give the same final state in any order, and an atomic batch either applies
every operation or reverts entirely.

* `Always step P s ops`: `P` holds on every state of the trace; `Never` is `Always` of the
  negation. `always_iff_take` states it as "after every prefix"; `always_append` splits it.
* `stable_after`: a preserved property that holds after the first `i` operations holds after the
  first `j` for every `j ≥ i`; `run_take_rel` and `run_take_mono`: a relation (an order) that every
  operation establishes holds between any two states of a run, earlier to later.
* `changes view step s ops`: the number of operations of the run that change `view`. A field
  that is final once set changes at most once (`changes_le_one_of_final`, with the forms for a
  write-once `Option` and a flag); a monotone counter changes at most as often as it grows
  (`changes_le_of_mono`).
* `Commute step a b`: `a` then `b` equals `b` then `a`. When the operations of a list commute
  pairwise, every permutation gives the same final state (`run_perm`).
* `batch step s ops`: the atomic batch of a partial step, the result of `runAll` or `s` unchanged
  when an operation fails (`batch_eq_or`); a batch fails exactly when some operation fails on the
  state its prefix reaches (`runAll_eq_none_iff`); invariants of the operations are invariants of
  batches (`batch_invariant`).
-/

namespace ProofForgeFin.Machine

open ProofForgeFin.Seq (Preserves run_invariant trace_invariant skip runAll Reachable)

universe u v w

variable {σ : Type u} {α : Type v}

/-! ## Always and never -/

/-- `P` holds on every state the run of `ops` from `s` passes through, first and last included. -/
def Always (step : σ → α → σ) (P : σ → Prop) (s : σ) (ops : List α) : Prop :=
  ∀ t ∈ Seq.trace step s ops, P t

/-- No state the run passes through satisfies `P`. -/
def Never (step : σ → α → σ) (P : σ → Prop) (s : σ) (ops : List α) : Prop :=
  Always step (fun t => ¬ P t) s ops

/-- A preserved property that holds at the start holds always. -/
theorem always_of_preserves {step : σ → α → σ} {P : σ → Prop} (h : Preserves step P) {s : σ}
    (h0 : P s) (ops : List α) : Always step P s ops :=
  trace_invariant h h0 ops

/-- A bad state is never reached when a preserved property excludes it and holds at the start. -/
theorem never_of_preserves {step : σ → α → σ} {P I : σ → Prop} (h : Preserves step I)
    (hI : ∀ t, I t → ¬ P t) {s : σ} (h0 : I s) (ops : List α) : Never step P s ops :=
  fun t ht => hI t (trace_invariant h h0 ops t ht)

/-- `Always` over no operations is the property of the start. -/
@[simp] theorem always_nil (step : σ → α → σ) (P : σ → Prop) (s : σ) :
    Always step P s [] ↔ P s := by
  simp [Always]

/-- `Always` over `a :: as`: the start, and always from the state after `a`. -/
theorem always_cons (step : σ → α → σ) (P : σ → Prop) (s : σ) (a : α) (as : List α) :
    Always step P s (a :: as) ↔ P s ∧ Always step P (step s a) as := by
  simp [Always]

/-- `Always` over a concatenation: always over the first part, then always from the state it
reaches. -/
theorem always_append (step : σ → α → σ) (P : σ → Prop) (s : σ) (as bs : List α) :
    Always step P s (as ++ bs) ↔ Always step P s as ∧ Always step P (Seq.run step s as) bs := by
  induction as generalizing s with
  | nil =>
    simp only [List.nil_append, always_nil, Seq.run_nil]
    constructor
    · intro h; exact ⟨h _ (Seq.self_mem_trace _ _ _), h⟩
    · exact fun h => h.2
  | cons a as ih =>
    simp only [List.cons_append, always_cons, Seq.run_cons, ih]
    constructor
    · exact fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩
    · exact fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩

/-- `Always` is "after every prefix of the operations". -/
theorem always_iff_take (step : σ → α → σ) (P : σ → Prop) (s : σ) (ops : List α) :
    Always step P s ops ↔ ∀ k, P (Seq.run step s (ops.take k)) := by
  constructor
  · intro h k; exact h _ (Seq.run_take_mem_trace step s ops k)
  · intro h t ht
    obtain ⟨k, rfl⟩ := Seq.exists_take_of_mem_trace step s ops ht
    exact h k

/-- The property holds at the end of the run. -/
theorem Always.run {step : σ → α → σ} {P : σ → Prop} {s : σ} {ops : List α}
    (h : Always step P s ops) : P (Seq.run step s ops) :=
  h _ (Seq.run_mem_trace step s ops)

/-- The property holds at the start of the run. -/
theorem Always.start {step : σ → α → σ} {P : σ → Prop} {s : σ} {ops : List α}
    (h : Always step P s ops) : P s :=
  h _ (Seq.self_mem_trace step s ops)

/-- `Always` is monotone in the property. -/
theorem Always.mono {step : σ → α → σ} {P Q : σ → Prop} {s : σ} {ops : List α}
    (h : Always step P s ops) (hPQ : ∀ t, P t → Q t) : Always step Q s ops :=
  fun t ht => hPQ t (h t ht)

/-- `Always` of a conjunction. -/
theorem always_and (step : σ → α → σ) (P Q : σ → Prop) (s : σ) (ops : List α) :
    Always step (fun t => P t ∧ Q t) s ops ↔ Always step P s ops ∧ Always step Q s ops :=
  ⟨fun h => ⟨fun t ht => (h t ht).1, fun t ht => (h t ht).2⟩,
    fun ⟨h1, h2⟩ t ht => ⟨h1 t ht, h2 t ht⟩⟩

/-! ## Along a run -/

/-- The state after the first `j` operations is reached from the state after the first `i ≤ j`
by the operations in between. -/
theorem run_take_of_le (step : σ → α → σ) (s : σ) (ops : List α) {i j : Nat} (hij : i ≤ j) :
    Seq.run step s (ops.take j) =
      Seq.run step (Seq.run step s (ops.take i)) ((ops.drop i).take (j - i)) := by
  rw [← Seq.run_append]
  congr 1
  have : j = i + (j - i) := by omega
  conv => lhs; rw [this]
  exact List.take_add

/-- Stability: a preserved property that holds after the first `i` operations holds after the
first `j` operations for every `j ≥ i`. "Once filled, always filled." -/
theorem stable_after {step : σ → α → σ} {P : σ → Prop} (h : Preserves step P) {s : σ}
    {ops : List α} {i j : Nat} (hi : P (Seq.run step s (ops.take i))) (hij : i ≤ j) :
    P (Seq.run step s (ops.take j)) := by
  rw [run_take_of_le step s ops hij]; exact run_invariant h hi _

/-- A reflexive, transitive relation that every operation establishes holds from any earlier
state of a run to any later one. -/
theorem run_take_rel {step : σ → α → σ} {R : σ → σ → Prop} (hrefl : ∀ s, R s s)
    (htrans : ∀ x y z, R x y → R y z → R x z) (hstep : ∀ s a, R s (step s a)) (s : σ)
    (ops : List α) {i j : Nat} (hij : i ≤ j) :
    R (Seq.run step s (ops.take i)) (Seq.run step s (ops.take j)) := by
  rw [run_take_of_le step s ops hij]; exact Seq.run_rel hrefl htrans hstep _ _

/-- A quantity that no operation lowers is monotone along a run. -/
theorem run_take_mono {step : σ → α → σ} (P : σ → Nat) (h : ∀ s a, P s ≤ P (step s a)) (s : σ)
    (ops : List α) {i j : Nat} (hij : i ≤ j) :
    P (Seq.run step s (ops.take i)) ≤ P (Seq.run step s (ops.take j)) :=
  run_take_rel (R := fun x y => P x ≤ P y) (fun _ => Nat.le_refl _)
    (fun _ _ _ h1 h2 => Nat.le_trans h1 h2) h s ops hij

/-- A quantity that no operation raises is antitone along a run. -/
theorem run_take_anti {step : σ → α → σ} (P : σ → Nat) (h : ∀ s a, P (step s a) ≤ P s) (s : σ)
    (ops : List α) {i j : Nat} (hij : i ≤ j) :
    P (Seq.run step s (ops.take j)) ≤ P (Seq.run step s (ops.take i)) :=
  run_take_rel (R := fun x y => P y ≤ P x) (fun _ => Nat.le_refl _)
    (fun _ _ _ h1 h2 => Nat.le_trans h2 h1) h s ops hij

/-! ## Counting changes -/

section Changes

variable {β : Type w} [DecidableEq β]

/-- The number of operations of the run that change `view`. -/
def changes (view : σ → β) (step : σ → α → σ) : σ → List α → Nat
  | _, [] => 0
  | s, a :: as => (if view (step s a) = view s then 0 else 1) + changes view step (step s a) as

/-- No operations, no changes. -/
@[simp] theorem changes_nil (view : σ → β) (step : σ → α → σ) (s : σ) :
    changes view step s [] = 0 := rfl

/-- The change of the first operation, then the changes of the rest. -/
theorem changes_cons (view : σ → β) (step : σ → α → σ) (s : σ) (a : α) (as : List α) :
    changes view step s (a :: as) =
      (if view (step s a) = view s then 0 else 1) + changes view step (step s a) as := rfl

/-- The changes over a concatenation. -/
theorem changes_append (view : σ → β) (step : σ → α → σ) (s : σ) (as bs : List α) :
    changes view step s (as ++ bs) =
      changes view step s as + changes view step (Seq.run step s as) bs := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih => rw [List.cons_append, changes_cons, changes_cons, ih, Seq.run_cons]; omega

/-- At most one change per operation. -/
theorem changes_le_length (view : σ → β) (step : σ → α → σ) (s : σ) (ops : List α) :
    changes view step s ops ≤ ops.length := by
  induction ops generalizing s with
  | nil => simp
  | cons a as ih => rw [changes_cons, List.length_cons]; have := ih (step s a); split <;> omega

/-- Operations that never change the view make no changes. -/
theorem changes_eq_zero {view : σ → β} {step : σ → α → σ} {ops : List α}
    (h : ∀ a ∈ ops, ∀ t, view (step t a) = view t) (s : σ) : changes view step s ops = 0 := by
  induction ops generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [changes_cons, h a (by simp), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    simp

/-- A view whose value is final once it satisfies `D` makes no changes from a state where it
does. -/
theorem changes_eq_zero_of_final {view : σ → β} {step : σ → α → σ} {D : β → Prop}
    (hD : ∀ s a, D (view s) → view (step s a) = view s) {s : σ} (hs : D (view s))
    (ops : List α) : changes view step s ops = 0 := by
  induction ops generalizing s with
  | nil => rfl
  | cons a as ih =>
    have e := hD s a hs
    rw [changes_cons, e, ih (e ▸ hs)]
    simp

/-- At most one change: when the view is final once it satisfies `D` and every change leads to a
value satisfying `D`, a run changes the view at most once. -/
theorem changes_le_one_of_final {view : σ → β} {step : σ → α → σ} {D : β → Prop}
    (hD : ∀ s a, D (view s) → view (step s a) = view s)
    (hchg : ∀ s a, view (step s a) ≠ view s → D (view (step s a))) (s : σ) (ops : List α) :
    changes view step s ops ≤ 1 := by
  induction ops generalizing s with
  | nil => simp
  | cons a as ih =>
    rw [changes_cons]
    split
    · exact Nat.zero_add _ ▸ ih (step s a)
    · next h => rw [changes_eq_zero_of_final hD (hchg s a h)]; omega

/-- A write-once field (an `Option` that no operation changes once it is set) is set at most once
along any run. -/
theorem changes_le_one_of_writeOnce {β : Type w} [DecidableEq β] {view : σ → Option β}
    {step : σ → α → σ} (h : ∀ s a, view s ≠ none → view (step s a) = view s) (s : σ)
    (ops : List α) : changes view step s ops ≤ 1 :=
  changes_le_one_of_final (D := fun v => v ≠ none) h
    (fun s a hne hnone => by
      have hs : view s ≠ none := fun e => hne (by rw [hnone, e])
      exact hne (h s a hs)) s ops

/-- A flag that stays set once set (a reversed mark, a filled status) changes at most once along
any run. -/
theorem changes_le_one_of_flag {view : σ → Bool} {step : σ → α → σ}
    (h : ∀ s a, view s = true → view (step s a) = true) (s : σ) (ops : List α) :
    changes view step s ops ≤ 1 :=
  changes_le_one_of_final (D := fun v => v = true)
    (fun s a hs => by rw [h s a hs, hs])
    (fun s a hne => by
      cases hv : view (step s a)
      · cases hs : view s
        · exact absurd (hv.trans hs.symm) hne
        · exact absurd (h s a hs) (by rw [hv]; decide)
      · rfl) s ops

/-- A counter that no operation lowers changes at most as many times as it grows. -/
theorem changes_le_of_mono {step : σ → α → σ} (P : σ → Nat) (h : ∀ s a, P s ≤ P (step s a))
    (s : σ) (ops : List α) : changes P step s ops + P s ≤ P (Seq.run step s ops) := by
  induction ops generalizing s with
  | nil => simp
  | cons a as ih =>
    rw [changes_cons, Seq.run_cons]
    have h1 := ih (step s a)
    have h2 := h s a
    split
    · omega
    · next hne => have : P s < P (step s a) := Nat.lt_of_le_of_ne h2 (Ne.symm hne); omega

/-- A counter that no operation lowers and that stays at most `B` changes at most `B - P s` times
along a run from `s`. -/
theorem changes_le_of_bounded {step : σ → α → σ} (P : σ → Nat) (h : ∀ s a, P s ≤ P (step s a))
    {B : Nat} (s : σ) (ops : List α) (hB : P (Seq.run step s ops) ≤ B) :
    changes P step s ops ≤ B - P s := by
  have := changes_le_of_mono P h s ops; omega

end Changes

/-! ## Commuting operations -/

/-- `a` then `b` gives the same state as `b` then `a`, from every state. -/
def Commute (step : σ → α → σ) (a b : α) : Prop := ∀ s, step (step s a) b = step (step s b) a

/-- Commutation is symmetric. -/
theorem Commute.symm {step : σ → α → σ} {a b : α} (h : Commute step a b) : Commute step b a :=
  fun s => (h s).symm

/-- Every operation commutes with itself. -/
theorem Commute.refl (step : σ → α → σ) (a : α) : Commute step a a := fun _ => rfl

/-- Swapping two adjacent commuting operations does not change the final state. -/
theorem run_swap {step : σ → α → σ} {a b : α} (h : Commute step a b) (s : σ) (l : List α) :
    Seq.run step s (a :: b :: l) = Seq.run step s (b :: a :: l) := by
  simp only [Seq.run_cons, h s]

/-- Reordering: when the operations of a list commute pairwise, every permutation of the list
gives the same final state. -/
theorem run_perm {step : σ → α → σ} {ops ops' : List α} (hp : ops.Perm ops')
    (h : ∀ a ∈ ops, ∀ b ∈ ops, Commute step a b) (s : σ) :
    Seq.run step s ops = Seq.run step s ops' := by
  induction hp generalizing s with
  | nil => rfl
  | cons x _ ih =>
    rw [Seq.run_cons, Seq.run_cons]
    exact ih (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) _
  | swap x y l =>
    exact (run_swap (h x (by simp) y (by simp)) s l).symm
  | trans h₁₂ _ ih₁ ih₂ =>
    rw [ih₁ h s]
    exact ih₂ (fun a ha b hb => h a (h₁₂.mem_iff.mpr ha) b (h₁₂.mem_iff.mpr hb)) s

/-- When every two operations commute, every reordering gives the same final state. -/
theorem run_perm_of_forall {step : σ → α → σ} (h : ∀ a b, Commute step a b) {ops ops' : List α}
    (hp : ops.Perm ops') (s : σ) : Seq.run step s ops = Seq.run step s ops' :=
  run_perm hp (fun a _ b _ => h a b) s

/-- An operation that commutes with every operation of a run can be moved to its end. -/
theorem run_step_comm {step : σ → α → σ} {a : α} {ops : List α}
    (h : ∀ b ∈ ops, Commute step a b) (s : σ) :
    Seq.run step (step s a) ops = step (Seq.run step s ops) a := by
  induction ops generalizing s with
  | nil => rfl
  | cons b bs ih =>
    rw [Seq.run_cons, h b (by simp) s, ih (fun c hc => h c (List.mem_cons_of_mem _ hc)), Seq.run_cons]

/-- Operations that act on disjoint parts of a product state commute: a step that changes only
the first component and one that changes only the second. -/
theorem commute_of_independent {β : Type w} {step : σ × β → α → σ × β} {a b : α}
    (fa : σ → σ) (gb : β → β) (ha : ∀ p, step p a = (fa p.1, p.2))
    (hb : ∀ p, step p b = (p.1, gb p.2)) : Commute step a b := by
  intro p; rw [ha, hb, hb, ha]

/-! ## Atomic batches -/

section Batch

/-- An atomic batch of a partial step: the result of applying every operation when all succeed,
and the unchanged state when one fails. -/
def batch (step : σ → α → Option σ) (s : σ) (ops : List α) : σ := (runAll step s ops).getD s

/-- A batch whose operations all succeed has the result of the atomic run. -/
theorem batch_of_some {step : σ → α → Option σ} {s t : σ} {ops : List α}
    (h : runAll step s ops = some t) : batch step s ops = t := by
  simp [batch, h]

/-- A batch with a failing operation reverts entirely. -/
theorem batch_of_none {step : σ → α → Option σ} {s : σ} {ops : List α}
    (h : runAll step s ops = none) : batch step s ops = s := by
  simp [batch, h]

/-- All or nothing: a batch either leaves the state unchanged with the atomic run failing, or
is the result of the successful atomic run. -/
theorem batch_eq_or (step : σ → α → Option σ) (s : σ) (ops : List α) :
    (runAll step s ops = none ∧ batch step s ops = s) ∨
      runAll step s ops = some (batch step s ops) := by
  cases h : runAll step s ops with
  | none => exact Or.inl ⟨rfl, batch_of_none h⟩
  | some t => exact Or.inr (by rw [batch_of_some h])

/-- An atomic run fails exactly when some operation fails on the state its prefix reaches. -/
theorem runAll_eq_none_iff (step : σ → α → Option σ) (s : σ) (ops : List α) :
    runAll step s ops = none ↔
      ∃ pre a post t, ops = pre ++ a :: post ∧ runAll step s pre = some t ∧ step t a = none := by
  induction ops generalizing s with
  | nil =>
    simp only [Seq.runAll_nil, reduceCtorEq, false_iff]
    rintro ⟨pre, a, post, t, h, _⟩
    cases pre <;> cases h
  | cons a as ih =>
    constructor
    · intro h
      simp only [runAll] at h
      split at h
      · next s₁ h₁ =>
        obtain ⟨pre, b, post, t, e, h2, h3⟩ := (ih s₁).mp h
        refine ⟨a :: pre, b, post, t, by simp [e], ?_, h3⟩
        simp only [runAll, h₁]; exact h2
      · next h₁ => exact ⟨[], a, as, s, rfl, rfl, h₁⟩
    · rintro ⟨pre, b, post, t, e, h2, h3⟩
      cases pre with
      | nil =>
        cases e; cases h2
        simp [runAll, h3]
      | cons c pre =>
        cases e
        obtain ⟨s₁, h₁, h₂⟩ := Seq.runAll_cons_eq_some h2
        simp only [runAll, h₁]
        exact (ih s₁).mpr ⟨pre, b, post, t, rfl, h₂, h3⟩

/-- A failing prefix makes the whole atomic run fail. -/
theorem runAll_append_of_none {step : σ → α → Option σ} {s : σ} {as : List α}
    (h : runAll step s as = none) (bs : List α) : runAll step s (as ++ bs) = none := by
  rw [Seq.runAll_append, h]; rfl

/-- A successful atomic run gives the same state as running each operation and skipping
refusals (none occur). -/
theorem run_skip_of_runAll {step : σ → α → Option σ} {s t : σ} {ops : List α}
    (h : runAll step s ops = some t) : Seq.run (skip step) s ops = t := by
  induction ops generalizing s with
  | nil => cases h; rfl
  | cons a as ih =>
    obtain ⟨s₁, h₁, h₂⟩ := Seq.runAll_cons_eq_some h
    rw [Seq.run_cons]
    have : skip step s a = s₁ := by simp [skip, h₁]
    rw [this]; exact ih h₂

/-- Every invariant of the operations is an invariant of batches. -/
theorem batch_invariant {step : σ → α → Option σ} {I : σ → Prop}
    (hI : ∀ s a s', I s → step s a = some s' → I s') {s : σ} (h0 : I s) (ops : List α) :
    I (batch step s ops) := by
  rcases batch_eq_or step s ops with ⟨_, e⟩ | e
  · rw [e]; exact h0
  · exact Seq.runAll_invariant hI h0 e

/-- Batches as a step: every invariant of the operations holds after any sequence of batches. -/
theorem run_batch_invariant {step : σ → α → Option σ} {I : σ → Prop}
    (hI : ∀ s a s', I s → step s a = some s' → I s') {s : σ} (h0 : I s) (batches : List (List α)) :
    I (Seq.run (batch step) s batches) :=
  run_invariant (step := batch step) (I := I) (fun _ ops ht => batch_invariant hI ht ops) h0 batches

/-- A reflexive, transitive relation that every successful operation establishes holds between
the state before and after a batch. -/
theorem batch_rel {step : σ → α → Option σ} {R : σ → σ → Prop} (hrefl : ∀ s, R s s)
    (htrans : ∀ x y z, R x y → R y z → R x z) (hstep : ∀ s a s', step s a = some s' → R s s')
    (s : σ) (ops : List α) : R s (batch step s ops) := by
  rcases batch_eq_or step s ops with ⟨_, e⟩ | e
  · rw [e]; exact hrefl s
  · exact Seq.runAll_rel hrefl htrans hstep e

/-- The state after a batch is reachable from the state before. -/
theorem batch_reachable {step : σ → α → Option σ} {init s : σ} (h : Reachable step init s)
    (ops : List α) : Reachable step init (batch step s ops) := by
  rcases batch_eq_or step s ops with ⟨_, e⟩ | e
  · rw [e]; exact h
  · exact Seq.reachable_of_runAll h e

end Batch

end ProofForgeFin.Machine
