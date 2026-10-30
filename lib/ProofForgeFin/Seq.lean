import ProofForgeFin.Rounding
/-!
# Runs of operations and invariants over every reachable state

Financial requirements are rarely about one call. They are about every state a system can reach:
"no account holds bad debt after any sequence of operations", "a share is never worth less after
any later operations", "rewards credited never exceed rewards emitted since the upgrade". This
module fixes the shapes such statements take and proves the induction principles once.

* `run step s ops`: the state after applying `step` to each operation in order. A refused call
  that leaves the state unchanged is modelled with `skip`.
* `trace step s ops`: every state a run passes through, first and last included.
* `runAll step s ops`: a run of a partial step that fails as a whole when one operation fails
  (an atomic batch).
* `Reachable step init`: the states reachable from `init` by successful operations.
* `accum next f g ops`: an accumulator computed from the operations alone, with a ghost state `g`
  updated by `next` (for example COMP emitted, which depends on the speeds set by earlier
  operations).

The theorems: invariants hold after every run and on every state of a trace; strengthening an
invariant; invariants relative to another invariant; relations that chain along a run
(transitive relations, and relations that are transitive only through states satisfying a
condition, such as share value with outstanding shares); bounds of the form
`P (run step s ops) ≤ P s + (ops.map f).sum` and its ghost form with `accum`; and the passage
from a bound on a scaled potential to a bound on an amount.
-/

namespace ProofForgeFin.Seq

universe u v w

variable {σ : Type u} {α : Type v} {γ : Type w}

/-! ## Runs -/

/-- The state after applying `step` to each operation of `ops` in order, starting from `s`. -/
def run (step : σ → α → σ) : σ → List α → σ
  | s, [] => s
  | s, a :: as => run step (step s a) as

/-- A run of no operations leaves the state unchanged. -/
@[simp] theorem run_nil (step : σ → α → σ) (s : σ) : run step s [] = s := rfl

/-- A run of `a :: as` applies `a` and then runs `as`. -/
@[simp] theorem run_cons (step : σ → α → σ) (s : σ) (a : α) (as : List α) :
    run step s (a :: as) = run step (step s a) as := rfl

/-- Running two lists of operations is running their concatenation. -/
theorem run_append (step : σ → α → σ) (s : σ) (as bs : List α) :
    run step s (as ++ bs) = run step (run step s as) bs := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => exact ih (step s a)

/-- The last operation of a run is applied to the state the earlier ones reach. -/
theorem run_snoc (step : σ → α → σ) (s : σ) (as : List α) (a : α) :
    run step s (as ++ [a]) = step (run step s as) a := by
  rw [run_append]; rfl

/-- `run` is a left fold. -/
theorem run_eq_foldl (step : σ → α → σ) (s : σ) (as : List α) : run step s as = as.foldl step s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => exact ih (step s a)

/-- Every state a run passes through: `s`, then the state after each operation. -/
def trace (step : σ → α → σ) : σ → List α → List σ
  | s, [] => [s]
  | s, a :: as => s :: trace step (step s a) as

/-- The trace of no operations is the start alone. -/
@[simp] theorem trace_nil (step : σ → α → σ) (s : σ) : trace step s [] = [s] := rfl

/-- The trace of `a :: as` is the start followed by the trace from the state after `a`. -/
@[simp] theorem trace_cons (step : σ → α → σ) (s : σ) (a : α) (as : List α) :
    trace step s (a :: as) = s :: trace step (step s a) as := rfl

/-- A run passes through one more state than it has operations. -/
theorem length_trace (step : σ → α → σ) (s : σ) (as : List α) :
    (trace step s as).length = as.length + 1 := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- The first state of a trace is the start. -/
theorem self_mem_trace (step : σ → α → σ) (s : σ) (as : List α) : s ∈ trace step s as := by
  cases as <;> simp

/-- The last state of a trace is the state the run reaches. -/
theorem run_mem_trace (step : σ → α → σ) (s : σ) (as : List α) : run step s as ∈ trace step s as := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih => exact List.mem_cons_of_mem _ (ih (step s a))

/-- The trace of the remaining operations is part of the trace. -/
theorem trace_step_subset (step : σ → α → σ) (s : σ) (a : α) (as : List α) {t : σ}
    (h : t ∈ trace step (step s a) as) : t ∈ trace step s (a :: as) :=
  List.mem_cons_of_mem _ h

/-- The state after a prefix of the operations lies on the trace. -/
theorem run_take_mem_trace (step : σ → α → σ) (s : σ) (as : List α) (k : Nat) :
    run step s (as.take k) ∈ trace step s as := by
  induction as generalizing s k with
  | nil => simp
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ k => exact List.mem_cons_of_mem _ (ih (step s a) k)

/-- Every state on the trace is the state after some prefix of the operations. -/
theorem exists_take_of_mem_trace (step : σ → α → σ) (s : σ) (as : List α) {t : σ}
    (h : t ∈ trace step s as) : ∃ k, t = run step s (as.take k) := by
  induction as generalizing s with
  | nil => exact ⟨0, by simpa using h⟩
  | cons a as ih =>
    simp only [trace_cons, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨k, hk⟩ := ih (step s a) h
      exact ⟨k + 1, by simpa using hk⟩

/-! ## Invariants -/

/-- `step` preserves `I`: from a state satisfying `I`, every operation leads to a state
satisfying `I`. -/
def Preserves (step : σ → α → σ) (I : σ → Prop) : Prop := ∀ s a, I s → I (step s a)

/-- Induction over runs: an invariant that holds at the start and that every operation preserves
holds after every sequence of operations. -/
theorem run_invariant {step : σ → α → σ} {I : σ → Prop} (hs : Preserves step I) {s : σ}
    (h0 : I s) (as : List α) : I (run step s as) := by
  induction as generalizing s with
  | nil => exact h0
  | cons a as ih => exact ih (hs s a h0)

/-- An invariant holds on every state a run passes through. -/
theorem trace_invariant {step : σ → α → σ} {I : σ → Prop} (hs : Preserves step I) {s : σ}
    (h0 : I s) (as : List α) : ∀ t ∈ trace step s as, I t := by
  induction as generalizing s with
  | nil => intro t ht; simp at ht; subst ht; exact h0
  | cons a as ih =>
    intro t ht
    simp only [trace_cons, List.mem_cons] at ht
    rcases ht with ht | ht
    · subst ht; exact h0
    · exact ih (hs s a h0) t ht

/-- Strengthening: to prove `I` after every run, prove a stronger `J` that every operation
preserves. -/
theorem run_invariant_of_imp {step : σ → α → σ} {I J : σ → Prop} (hJI : ∀ s, J s → I s)
    (hJ : Preserves step J) {s : σ} (h0 : J s) (as : List α) : I (run step s as) :=
  hJI _ (run_invariant hJ h0 as)

/-- A relative invariant: when `J` is an invariant and every operation preserves `I` on states
satisfying `J`, both hold after every run. -/
theorem run_invariant_under {step : σ → α → σ} {I J : σ → Prop} (hJ : Preserves step J)
    (hI : ∀ s a, J s → I s → I (step s a)) {s : σ} (hJ0 : J s) (hI0 : I s) (as : List α) :
    I (run step s as) ∧ J (run step s as) :=
  run_invariant (I := fun t => I t ∧ J t) (fun t a h => ⟨hI t a h.2 h.1, hJ t a h.2⟩) ⟨hI0, hJ0⟩ as

/-- The conjunction of two invariants is an invariant. -/
theorem Preserves.and {step : σ → α → σ} {I J : σ → Prop} (hI : Preserves step I)
    (hJ : Preserves step J) : Preserves step (fun s => I s ∧ J s) :=
  fun s a h => ⟨hI s a h.1, hJ s a h.2⟩

/-- A property that holds after every operation, from any state, holds after every nonempty run. -/
theorem run_of_step {step : σ → α → σ} {I : σ → Prop} (h : ∀ s a, I (step s a)) (s : σ)
    {as : List α} (hne : as ≠ []) : I (run step s as) := by
  induction as generalizing s with
  | nil => exact absurd rfl hne
  | cons a as ih =>
    cases as with
    | nil => exact h s a
    | cons b bs => exact ih (step s a) (by simp)

/-! ## Relations along runs -/

/-- A reflexive, transitive relation that every operation establishes between the state before
and after holds between the start and the end of every run. -/
theorem run_rel {step : σ → α → σ} {R : σ → σ → Prop} (hrefl : ∀ s, R s s)
    (htrans : ∀ x y z, R x y → R y z → R x z) (hstep : ∀ s a, R s (step s a)) (s : σ)
    (as : List α) : R s (run step s as) := by
  induction as generalizing s with
  | nil => exact hrefl s
  | cons a as ih => exact htrans _ _ _ (hstep s a) (ih (step s a))

/-- A relation that every operation establishes from states satisfying `C`, and that composes
through intermediate states satisfying `C`, holds between the start and the end of every run
whose trace stays in `C`. Share value is the example: `assets / supply` cannot fall, but the
cross-multiplied comparison composes only through states with outstanding shares. -/
theorem run_rel_of_trace {step : σ → α → σ} {R : σ → σ → Prop} {C : σ → Prop}
    (hrefl : ∀ s, R s s) (htrans : ∀ x y z, R x y → R y z → C y → R x z)
    (hstep : ∀ s a, C s → R s (step s a)) (s : σ) (as : List α)
    (hC : ∀ t ∈ trace step s as, C t) : R s (run step s as) := by
  induction as generalizing s with
  | nil => exact hrefl s
  | cons a as ih =>
    have h0 : C s := hC s (self_mem_trace _ _ _)
    have h1 : ∀ t ∈ trace step (step s a) as, C t := fun t ht => hC t (trace_step_subset _ _ _ _ ht)
    have h2 : C (step s a) := h1 _ (self_mem_trace _ _ _)
    exact htrans _ _ _ (hstep s a h0) (ih (step s a) h1) h2

/-- A quantity that no operation lowers is at least its start value after every run. -/
theorem run_ge {step : σ → α → σ} (P : σ → Nat) (h : ∀ s a, P s ≤ P (step s a)) (s : σ)
    (as : List α) : P s ≤ P (run step s as) :=
  run_rel (R := fun x y => P x ≤ P y) (fun _ => Nat.le_refl _)
    (fun _ _ _ h1 h2 => Nat.le_trans h1 h2) h s as

/-- A quantity that no operation raises is at most its start value after every run. -/
theorem run_le {step : σ → α → σ} (P : σ → Nat) (h : ∀ s a, P (step s a) ≤ P s) (s : σ)
    (as : List α) : P (run step s as) ≤ P s :=
  run_rel (R := fun x y => P y ≤ P x) (fun _ => Nat.le_refl _)
    (fun _ _ _ h1 h2 => Nat.le_trans h2 h1) h s as

/-! ## Accumulated bounds -/

/-- Conservation: a quantity that every operation leaves unchanged is unchanged by every run. -/
theorem run_eq_of_step_eq {β : Type w} {step : σ → α → σ} (P : σ → β)
    (h : ∀ s a, P (step s a) = P s) (s : σ) (as : List α) : P (run step s as) = P s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => rw [run_cons, ih, h]

/-- Flows: when every operation changes a quantity by exactly `f a`, a run changes it by the sum. -/
theorem run_eq_add_sum {step : σ → α → σ} (P : σ → Nat) (f : α → Nat)
    (h : ∀ s a, P (step s a) = P s + f a) (s : σ) (as : List α) :
    P (run step s as) = P s + (as.map f).sum := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih => rw [run_cons, ih, h]; simp [Nat.add_assoc]

/-- Conservation for the operations of one list: a quantity that each operation of `as` leaves
unchanged is unchanged by the run of `as` (the operations of the list may satisfy conditions,
such as naming accounts of the ledger, that other operations do not). -/
theorem run_eq_of_mem {β : Type w} {step : σ → α → σ} (P : σ → β) {as : List α}
    (h : ∀ s a, a ∈ as → P (step s a) = P s) (s : σ) : P (run step s as) = P s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [run_cons, ih (fun t b hb => h t b (List.mem_cons_of_mem _ hb)), h s a (by simp)]

/-- Invariants for the operations of one list: a property that each operation of `as` preserves
holds after the run of `as`. -/
theorem run_invariant_of_mem {step : σ → α → σ} {I : σ → Prop} {as : List α}
    (h : ∀ s a, a ∈ as → I s → I (step s a)) {s : σ} (h0 : I s) : I (run step s as) := by
  induction as generalizing s with
  | nil => exact h0
  | cons a as ih =>
    exact ih (fun t b hb => h t b (List.mem_cons_of_mem _ hb)) (h s a (by simp) h0)

/-- Accumulated bound: when every operation raises a quantity by at most `f a`, a run raises it
by at most the sum of `f` over the operations. -/
theorem run_le_add_sum {step : σ → α → σ} (P : σ → Nat) (f : α → Nat)
    (h : ∀ s a, P (step s a) ≤ P s + f a) (s : σ) (as : List α) :
    P (run step s as) ≤ P s + (as.map f).sum := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih =>
    have h1 := ih (step s a)
    have h2 := h s a
    simp only [run_cons, List.map_cons, List.sum_cons]
    omega

/-- The accumulated bound for steps that respect it only on states satisfying an invariant. -/
theorem run_le_add_sum_of_inv {step : σ → α → σ} {I : σ → Prop} (hI : Preserves step I)
    (P : σ → Nat) (f : α → Nat) (h : ∀ s a, I s → P (step s a) ≤ P s + f a) {s : σ} (h0 : I s)
    (as : List α) : P (run step s as) ≤ P s + (as.map f).sum := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih =>
    have h1 := ih (hI s a h0)
    have h2 := h s a h0
    simp only [run_cons, List.map_cons, List.sum_cons]
    omega

/-! ## Ghost accumulators -/

/-- A total computed from the operations alone. The ghost state `g` is updated by `next` after
each operation and `f g a` is the contribution of `a` given the ghost state before it. For COMP
rewards `g` is the pair of speeds, `next` applies `setSpeeds`, and `f g a` is the COMP emitted by
`a` at speeds `g`. -/
def accum (next : γ → α → γ) (f : γ → α → Nat) : γ → List α → Nat
  | _, [] => 0
  | g, a :: as => f g a + accum next f (next g a) as

/-- No operations contribute nothing. -/
@[simp] theorem accum_nil (next : γ → α → γ) (f : γ → α → Nat) (g : γ) : accum next f g [] = 0 := rfl

/-- The contribution of `a` at the current ghost state, then the rest from the next one. -/
@[simp] theorem accum_cons (next : γ → α → γ) (f : γ → α → Nat) (g : γ) (a : α) (as : List α) :
    accum next f g (a :: as) = f g a + accum next f (next g a) as := rfl

/-- The total over a concatenation: the total of the first part, then the total of the second
part from the ghost state the first part reaches. -/
theorem accum_append (next : γ → α → γ) (f : γ → α → Nat) (g : γ) (as bs : List α) :
    accum next f g (as ++ bs) = accum next f g as + accum next f (run next g as) bs := by
  induction as generalizing g with
  | nil => simp
  | cons a as ih => simp [ih, Nat.add_assoc]

/-- Without a ghost state the total is a sum. -/
theorem accum_const (f : α → Nat) (g : γ) (as : List α) :
    accum (fun g _ => g) (fun _ a => f a) g as = (as.map f).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- Invariant with a running total: if `Inv g e s` relates the ghost state `g`, the total `e`
accumulated so far and the state `s`, and every operation carries it to the next ghost state,
the total plus the operation's contribution, and the next state, then it holds after every run
with the total `e + accum next f g ops`. With `Inv g e s := Q s ≤ Q₀ + e ∧ J g s` this is the
statement "credited ≤ initial + emitted so far". -/
theorem run_total_invariant {step : σ → α → σ} {next : γ → α → γ} {f : γ → α → Nat}
    (Inv : γ → Nat → σ → Prop) (h : ∀ g e s a, Inv g e s → Inv (next g a) (e + f g a) (step s a))
    {g : γ} {e : Nat} {s : σ} (h0 : Inv g e s) (as : List α) :
    Inv (run next g as) (e + accum next f g as) (run step s as) := by
  induction as generalizing g e s with
  | nil => simpa using h0
  | cons a as ih =>
    have := ih (h g e s a h0)
    simpa [Nat.add_assoc] using this

/-- Accumulated bound with a ghost state: when an invariant `I g s` relates the ghost state and
the state, every operation preserves it, and every operation raises `P` by at most `f g a`, a run
raises `P` by at most the ghost total, and the invariant holds at the end. -/
theorem run_le_accum {step : σ → α → σ} {next : γ → α → γ} {f : γ → α → Nat}
    (I : γ → σ → Prop) (P : σ → Nat) (hI : ∀ g s a, I g s → I (next g a) (step s a))
    (hP : ∀ g s a, I g s → P (step s a) ≤ P s + f g a) {g : γ} {s : σ} (h0 : I g s)
    (as : List α) :
    P (run step s as) ≤ P s + accum next f g as ∧ I (run next g as) (run step s as) := by
  induction as generalizing g s with
  | nil => simpa using h0
  | cons a as ih =>
    have h1 := ih (hI g s a h0)
    have h2 := hP g s a h0
    simp only [run_cons, accum_cons]
    exact ⟨by omega, h1.2⟩

/-- The scaled form: when every operation raises a potential `P` by at most `c * f g a` (for
reward indices, `c` is the index scale `1e36`), a run raises it by at most `c` times the ghost
total. -/
theorem run_le_scaled_accum {step : σ → α → σ} {next : γ → α → γ} {f : γ → α → Nat}
    (I : γ → σ → Prop) (P : σ → Nat) (c : Nat) (hI : ∀ g s a, I g s → I (next g a) (step s a))
    (hP : ∀ g s a, I g s → P (step s a) ≤ P s + c * f g a) {g : γ} {s : σ} (h0 : I g s)
    (as : List α) :
    P (run step s as) ≤ P s + c * accum next f g as ∧ I (run next g as) (run step s as) := by
  induction as generalizing g s with
  | nil => simpa using h0
  | cons a as ih =>
    have h1 := ih (hI g s a h0)
    have h2 := hP g s a h0
    simp only [run_cons, accum_cons, Nat.mul_add]
    exact ⟨by omega, h1.2⟩

/-- From a scaled potential to an amount. Suppose `Q s * c ≤ P s` on every state satisfying the
invariant (the amount credited, at scale `c`, is covered by the potential), every operation
raises `P` by at most `c * f g a`, and at the start `P s ≤ B * c + R`. Then after every run
`Q ≤ B + accum + R / c`: the remainder `R` (for example rewards owed and not yet indexed, at scale
`c`) is rounded down once. This is the shape of a reward bound "credited never exceeds what was
held and owed at the start plus what was emitted since". -/
theorem run_bound_via_potential {step : σ → α → σ} {next : γ → α → γ} {f : γ → α → Nat}
    (I : γ → σ → Prop) (P Q : σ → Nat) {c B R : Nat} (hc : 0 < c)
    (hI : ∀ g s a, I g s → I (next g a) (step s a))
    (hP : ∀ g s a, I g s → P (step s a) ≤ P s + c * f g a)
    (hQ : ∀ g s, I g s → Q s * c ≤ P s) {g : γ} {s : σ} (h0 : I g s) (hstart : P s ≤ B * c + R)
    (as : List α) : Q (run step s as) ≤ B + accum next f g as + R / c := by
  obtain ⟨h1, h2⟩ := run_le_scaled_accum I P c hI hP h0 as
  have h3 := hQ _ _ h2
  apply le_add_div_of_mul_le hc
  rw [Nat.add_mul, Nat.mul_comm (accum next f g as) c]
  omega

/-- Running the ghost state and the state together: the pair after a run is the pair of runs. -/
theorem run_pair (step : σ → α → σ) (next : γ → α → γ) (g : γ) (s : σ) (as : List α) :
    run (fun p a => (next p.1 a, step p.2 a)) (g, s) as = (run next g as, run step s as) := by
  induction as generalizing g s with
  | nil => rfl
  | cons a as ih => exact ih (next g a) (step s a)

/-! ## Partial steps -/

/-- A step that refuses an operation (`none`) leaves the state unchanged: a reverted call. -/
def skip (step : σ → α → Option σ) : σ → α → σ := fun s a => (step s a).getD s

/-- A property preserved by every successful operation is preserved by `skip`. -/
theorem skip_preserves {step : σ → α → Option σ} {I : σ → Prop}
    (h : ∀ s a s', I s → step s a = some s' → I s') : Preserves (skip step) I := by
  intro s a hs
  unfold skip
  cases e : step s a with
  | none => exact hs
  | some s' => exact h s a s' hs e

/-- A relation that every successful operation establishes, and that is reflexive, holds between
the state before and after `skip`. -/
theorem skip_rel {step : σ → α → Option σ} {R : σ → σ → Prop} (hrefl : ∀ s, R s s)
    (h : ∀ s a s', step s a = some s' → R s s') (s : σ) (a : α) : R s (skip step s a) := by
  unfold skip
  cases e : step s a with
  | none => exact hrefl s
  | some s' => exact h s a s' e

/-- An atomic run of a partial step: the operations are applied in order and the run fails as a
whole (`none`) when one of them fails. -/
def runAll (step : σ → α → Option σ) : σ → List α → Option σ
  | s, [] => some s
  | s, a :: as =>
    match step s a with
    | some s' => runAll step s' as
    | none => none

/-- An atomic run of no operations succeeds with the start. -/
@[simp] theorem runAll_nil (step : σ → α → Option σ) (s : σ) : runAll step s [] = some s := rfl

/-- A successful run of `a :: as`: `a` succeeds and the rest succeeds from the state it leaves. -/
theorem runAll_cons_eq_some {step : σ → α → Option σ} {s s' : σ} {a : α} {as : List α}
    (h : runAll step s (a :: as) = some s') : ∃ s₁, step s a = some s₁ ∧ runAll step s₁ as = some s' := by
  simp only [runAll] at h
  split at h
  · rename_i s₁ h₁; exact ⟨s₁, h₁, h⟩
  · cases h

/-- Running two lists of operations atomically is running their concatenation atomically. -/
theorem runAll_append (step : σ → α → Option σ) (s : σ) (as bs : List α) :
    runAll step s (as ++ bs) = (runAll step s as).bind (fun t => runAll step t bs) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append, runAll]
    split
    · exact ih _
    · rfl

/-- A total step run atomically always succeeds, with the result of `run`. -/
theorem runAll_some (step : σ → α → σ) (s : σ) (as : List α) :
    runAll (fun t a => some (step t a)) s as = some (run step s as) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => exact ih (step s a)

/-- Invariants of atomic runs: a property preserved by every successful operation holds after
every successful run. -/
theorem runAll_invariant {step : σ → α → Option σ} {I : σ → Prop}
    (hI : ∀ s a s', I s → step s a = some s' → I s') {s s' : σ} (h0 : I s) {as : List α}
    (h : runAll step s as = some s') : I s' := by
  induction as generalizing s with
  | nil => cases h; exact h0
  | cons a as ih =>
    obtain ⟨s₁, h₁, h₂⟩ := runAll_cons_eq_some h
    exact ih (hI s a s₁ h0 h₁) h₂

/-- Relations along atomic runs: a reflexive, transitive relation that every successful operation
establishes holds between the start and the result of every successful run (a batch of swaps
never lowers a pool's value when no single swap does). -/
theorem runAll_rel {step : σ → α → Option σ} {R : σ → σ → Prop} (hrefl : ∀ s, R s s)
    (htrans : ∀ x y z, R x y → R y z → R x z) (hstep : ∀ s a s', step s a = some s' → R s s')
    {s s' : σ} {as : List α} (h : runAll step s as = some s') : R s s' := by
  induction as generalizing s with
  | nil => cases h; exact hrefl _
  | cons a as ih =>
    obtain ⟨s₁, h₁, h₂⟩ := runAll_cons_eq_some h
    exact htrans _ _ _ (hstep s a s₁ h₁) (ih h₂)

/-- The relation form for steps that establish it only from states satisfying an invariant. -/
theorem runAll_rel_of_inv {step : σ → α → Option σ} {R : σ → σ → Prop} {I : σ → Prop}
    (hrefl : ∀ s, R s s) (htrans : ∀ x y z, R x y → R y z → R x z)
    (hI : ∀ s a s', I s → step s a = some s' → I s')
    (hstep : ∀ s a s', I s → step s a = some s' → R s s')
    {s s' : σ} (h0 : I s) {as : List α} (h : runAll step s as = some s') : R s s' := by
  induction as generalizing s with
  | nil => cases h; exact hrefl _
  | cons a as ih =>
    obtain ⟨s₁, h₁, h₂⟩ := runAll_cons_eq_some h
    exact htrans _ _ _ (hstep s a s₁ h0 h₁) (ih (hI s a s₁ h0 h₁) h₂)

/-! ## Reachable states -/

/-- The states reachable from `init` by any sequence of successful operations. -/
inductive Reachable (step : σ → α → Option σ) (init : σ) : σ → Prop
  /-- The initial state is reachable. -/
  | init : Reachable step init init
  /-- A successful operation from a reachable state reaches its result. -/
  | step {s s' : σ} (a : α) : Reachable step init s → step s a = some s' → Reachable step init s'

/-- Induction over reachable states: a property of the initial state that every successful
operation preserves holds in every reachable state. -/
theorem Reachable.invariant {step : σ → α → Option σ} {init : σ} {I : σ → Prop} (h0 : I init)
    (hI : ∀ s a s', I s → step s a = some s' → I s') {s : σ} (h : Reachable step init s) : I s := by
  induction h with
  | init => exact h0
  | step a _ hs ih => exact hI _ a _ ih hs

/-- Strengthening over reachable states. -/
theorem Reachable.invariant_of_imp {step : σ → α → Option σ} {init : σ} {I J : σ → Prop}
    (hJI : ∀ s, J s → I s) (h0 : J init) (hJ : ∀ s a s', J s → step s a = some s' → J s')
    {s : σ} (h : Reachable step init s) : I s :=
  hJI s (h.invariant h0 hJ)

/-- The end of a successful atomic run from `init` is reachable. -/
theorem reachable_of_runAll {step : σ → α → Option σ} {init : σ} :
    ∀ {s : σ} {as : List α}, Reachable step init s → ∀ {s' : σ}, runAll step s as = some s' →
      Reachable step init s'
  | s, [], h, _, e => by cases e; exact h
  | s, a :: as, h, _, e => by
    obtain ⟨s₁, h₁, h₂⟩ := runAll_cons_eq_some e
    exact reachable_of_runAll (Reachable.step a h h₁) h₂

/-- Every reachable state is the result of a successful atomic run from `init`. -/
theorem exists_runAll_of_reachable {step : σ → α → Option σ} {init : σ} {s : σ}
    (h : Reachable step init s) : ∃ as, runAll step init as = some s := by
  induction h with
  | init => exact ⟨[], rfl⟩
  | step a _ hs ih =>
    obtain ⟨as, has⟩ := ih
    refine ⟨as ++ [a], ?_⟩
    rw [runAll_append, has]
    simp [runAll, hs]

/-- Reachability is exactly the existence of a successful run. -/
theorem reachable_iff {step : σ → α → Option σ} {init s : σ} :
    Reachable step init s ↔ ∃ as, runAll step init as = some s :=
  ⟨exists_runAll_of_reachable, fun ⟨_, h⟩ => reachable_of_runAll Reachable.init h⟩

/-- For a step with refusals modelled by `skip`, the state after any run is reachable. -/
theorem reachable_run_skip {step : σ → α → Option σ} {init : σ} :
    ∀ {s : σ} (as : List α), Reachable step init s → Reachable step init (run (skip step) s as)
  | _, [], h => h
  | s, a :: as, h => by
    apply reachable_run_skip as
    unfold skip
    cases e : step s a with
    | none => exact h
    | some s' => exact Reachable.step a h e

end ProofForgeFin.Seq
