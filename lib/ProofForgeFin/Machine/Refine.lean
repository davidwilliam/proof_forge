import ProofForgeFin.Machine.Record
/-!
# Refinement and simulation

Many requirements compare an implementation with a specification: the specification computes
the truth from the events (the shares actually executed, the sum of an account's log entries),
and the implementation keeps its own counters (a cumulative quantity per order, a cached
balance). The implementation is correct when its counters always equal the specification's
recomputed values. This module proves the transfer principles once.

* `Simulates abs impl spec`: every implementation step maps, under the abstraction function
  `abs`, to the specification step (a commuting square). Then every run maps to the
  specification run (`Simulates.run`), every specification invariant holds of the abstraction of
  every implementation state (`Simulates.invariant`), and simulations compose
  (`Simulates.comp`). `SimulatesOn` assumes the square only on states satisfying an
  implementation invariant; `SimulatesBy` maps one implementation operation to a list of
  specification operations (none for an internal step, several for a batch).
* `ForwardSim R impl spec`: a relation preserved by corresponding steps. It holds after every
  pair of runs (`ForwardSim.run`), transfers specification properties (`ForwardSim.transfer`),
  composes (`ForwardSim.comp`), and can be strengthened by an invariant (`ForwardSim.and_inv`).
  `ForwardSimOpt` is the form for partial steps; every reachable implementation state is related
  to a reachable specification state (`ForwardSimOpt.reachable`).
* Steps with outputs: `couple impl obs` runs an implementation that returns its next state and
  an output together with an observer that records the output into the specification's facts
  (the shape of `advance` in `rc-knight-router`). `SimulatesOut` adds equality of outputs, and
  `outputs` collects the outputs of a run.
* Cached fields: `cache_run` (a cache that matches the specification view is kept matching by
  every step), `cache_log_invariant` (a cache kept next to an append-only log equals the fold of
  the log), and the running-total forms `run_cache_add` and `run_cache_add_key`.
* `withHistory`: a run that also records its operations, for invariants stated over the history.
-/

namespace ProofForgeFin.Machine

open ProofForgeFin.Seq (Preserves Reachable run_invariant run_eq_add_sum)

universe u v w x

variable {σ : Type u} {τ : Type v} {α : Type w}

/-! ## Functional simulation -/

/-- `impl` simulates `spec` under the abstraction function `abs`: the abstraction of the state
after an implementation step is the specification step from the abstraction. -/
def Simulates (abs : σ → τ) (impl : σ → α → σ) (spec : τ → α → τ) : Prop :=
  ∀ s a, abs (impl s a) = spec (abs s) a

/-- Every implementation run maps to the specification run from the abstraction of the start. -/
theorem Simulates.run {abs : σ → τ} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : Simulates abs impl spec) (s : σ) (ops : List α) :
    abs (Seq.run impl s ops) = Seq.run spec (abs s) ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons a as ih => rw [Seq.run_cons, ih, h, Seq.run_cons]

/-- Every state an implementation run passes through maps to the corresponding state of the
specification run. -/
theorem Simulates.trace {abs : σ → τ} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : Simulates abs impl spec) (s : σ) (ops : List α) :
    (Seq.trace impl s ops).map abs = Seq.trace spec (abs s) ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons a as ih => rw [Seq.trace_cons, Seq.trace_cons, List.map_cons, ih, h s a]

/-- Invariant transfer: every invariant of the specification holds of the abstraction of every
state an implementation run reaches. -/
theorem Simulates.invariant {abs : σ → τ} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : Simulates abs impl spec) {I : τ → Prop} (hI : Preserves spec I) {s : σ} (h0 : I (abs s))
    (ops : List α) : I (abs (Seq.run impl s ops)) := by
  rw [h.run]; exact run_invariant hI h0 ops

/-- Property transfer: a property of every specification run from `abs s` holds of the
abstraction of every implementation run from `s`, whether or not it is inductive. -/
theorem Simulates.transfer {abs : σ → τ} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : Simulates abs impl spec) {P : τ → Prop} {s : σ} (hP : ∀ ops, P (Seq.run spec (abs s) ops))
    (ops : List α) : P (abs (Seq.run impl s ops)) := by
  rw [h.run]; exact hP ops

/-- The identity simulation. -/
theorem Simulates.refl (step : σ → α → σ) : Simulates id step step := fun _ _ => rfl

/-- Simulations compose: an implementation of a refinement of the specification simulates the
specification under the composite abstraction. -/
theorem Simulates.comp {υ : Type x} {f : σ → τ} {g : τ → υ} {impl : σ → α → σ}
    {mid : τ → α → τ} {spec : υ → α → υ} (h₁ : Simulates f impl mid) (h₂ : Simulates g mid spec) :
    Simulates (fun s => g (f s)) impl spec := by
  intro s a; show g (f (impl s a)) = spec (g (f s)) a; rw [h₁, h₂]

/-- An implementation that simulates two specifications simulates their product. -/
theorem Simulates.pair {υ : Type x} {f : σ → τ} {g : σ → υ} {impl : σ → α → σ}
    {spec₁ : τ → α → τ} {spec₂ : υ → α → υ} (h₁ : Simulates f impl spec₁)
    (h₂ : Simulates g impl spec₂) :
    Simulates (fun s => (f s, g s)) impl (fun p a => (spec₁ p.1 a, spec₂ p.2 a)) := by
  intro s a; show (f (impl s a), g (impl s a)) = _; rw [h₁, h₂]

/-- A simulation that holds on the states satisfying an implementation invariant `J`. -/
def SimulatesOn (J : σ → Prop) (abs : σ → τ) (impl : σ → α → σ) (spec : τ → α → τ) : Prop :=
  ∀ s a, J s → abs (impl s a) = spec (abs s) a

/-- A simulation on an invariant maps every run from a state satisfying the invariant. -/
theorem SimulatesOn.run {J : σ → Prop} {abs : σ → τ} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : SimulatesOn J abs impl spec) (hJ : Preserves impl J) {s : σ} (h0 : J s) (ops : List α) :
    abs (Seq.run impl s ops) = Seq.run spec (abs s) ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons a as ih => rw [Seq.run_cons, ih (hJ s a h0), h s a h0, Seq.run_cons]

/-- Invariant transfer for a simulation on an invariant. -/
theorem SimulatesOn.invariant {J : σ → Prop} {abs : σ → τ} {impl : σ → α → σ}
    {spec : τ → α → τ} (h : SimulatesOn J abs impl spec) (hJ : Preserves impl J) {I : τ → Prop}
    (hI : Preserves spec I) {s : σ} (hJ0 : J s) (h0 : I (abs s)) (ops : List α) :
    I (abs (Seq.run impl s ops)) := by
  rw [h.run hJ hJ0]; exact run_invariant hI h0 ops

/-- Every simulation is a simulation on any invariant. -/
theorem Simulates.on {abs : σ → τ} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : Simulates abs impl spec) (J : σ → Prop) : SimulatesOn J abs impl spec :=
  fun s a _ => h s a

/-! ## Operations mapped to lists of specification operations -/

/-- Each implementation operation `a` corresponds to the specification operations `f a`: none
for an internal step that the specification does not see (stuttering), several for a batch. -/
def SimulatesBy {β : Type x} (abs : σ → τ) (impl : σ → α → σ) (spec : τ → β → τ)
    (f : α → List β) : Prop :=
  ∀ s a, abs (impl s a) = Seq.run spec (abs s) (f a)

/-- An implementation run maps to the specification run of the concatenated operations. -/
theorem SimulatesBy.run {β : Type x} {abs : σ → τ} {impl : σ → α → σ} {spec : τ → β → τ}
    {f : α → List β} (h : SimulatesBy abs impl spec f) (s : σ) (ops : List α) :
    abs (Seq.run impl s ops) = Seq.run spec (abs s) (ops.flatMap f) := by
  induction ops generalizing s with
  | nil => rfl
  | cons a as ih => rw [Seq.run_cons, ih, h, List.flatMap_cons, Seq.run_append]

/-- A one-to-one simulation is a simulation by singletons. -/
theorem Simulates.by_singleton {abs : σ → τ} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : Simulates abs impl spec) : SimulatesBy abs impl spec (fun a => [a]) :=
  fun s a => h s a

/-- Invariant transfer through a simulation by lists. -/
theorem SimulatesBy.invariant {β : Type x} {abs : σ → τ} {impl : σ → α → σ} {spec : τ → β → τ}
    {f : α → List β} (h : SimulatesBy abs impl spec f) {I : τ → Prop} (hI : Preserves spec I)
    {s : σ} (h0 : I (abs s)) (ops : List α) : I (abs (Seq.run impl s ops)) := by
  rw [h.run]; exact run_invariant hI h0 _

/-! ## Relational forward simulation -/

/-- A relation between implementation and specification states that corresponding steps
preserve. -/
def ForwardSim (R : σ → τ → Prop) (impl : σ → α → σ) (spec : τ → α → τ) : Prop :=
  ∀ s t a, R s t → R (impl s a) (spec t a)

/-- A forward simulation holds after every pair of corresponding runs. -/
theorem ForwardSim.run {R : σ → τ → Prop} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : ForwardSim R impl spec) {s : σ} {t : τ} (h0 : R s t) (ops : List α) :
    R (Seq.run impl s ops) (Seq.run spec t ops) := by
  induction ops generalizing s t with
  | nil => exact h0
  | cons a as ih => exact ih (h s t a h0)

/-- Property transfer: when `R s t` and a specification property `I` give an implementation
property `J`, every property of the specification runs from `t` gives `J` after every
implementation run from `s`. -/
theorem ForwardSim.transfer {R : σ → τ → Prop} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : ForwardSim R impl spec) {s : σ} {t : τ} (h0 : R s t) {I : τ → Prop} {J : σ → Prop}
    (hspec : ∀ ops, I (Seq.run spec t ops)) (hIJ : ∀ s t, R s t → I t → J s) (ops : List α) :
    J (Seq.run impl s ops) :=
  hIJ _ _ (h.run h0 ops) (hspec ops)

/-- Forward simulations compose through an intermediate model. -/
theorem ForwardSim.comp {υ : Type x} {R : σ → τ → Prop} {S : τ → υ → Prop} {impl : σ → α → σ}
    {mid : τ → α → τ} {spec : υ → α → υ} (h₁ : ForwardSim R impl mid) (h₂ : ForwardSim S mid spec) :
    ForwardSim (fun s u => ∃ t, R s t ∧ S t u) impl spec :=
  fun s u a ⟨t, hr, hs⟩ => ⟨mid t a, h₁ s t a hr, h₂ t u a hs⟩

/-- A forward simulation strengthened by an implementation invariant. -/
theorem ForwardSim.and_inv {R : σ → τ → Prop} {impl : σ → α → σ} {spec : τ → α → τ}
    {J : σ → Prop} (h : ∀ s t a, J s → R s t → R (impl s a) (spec t a)) (hJ : Preserves impl J) :
    ForwardSim (fun s t => R s t ∧ J s) impl spec :=
  fun s t a ⟨hr, hj⟩ => ⟨h s t a hj hr, hJ s a hj⟩

/-- A functional simulation is the forward simulation of the graph of the abstraction. -/
theorem Simulates.forwardSim {abs : σ → τ} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : Simulates abs impl spec) : ForwardSim (fun s t => abs s = t) impl spec := by
  intro s t a e; subst e; exact h s a

/-- A forward simulation whose relation is the graph of a function is a functional simulation. -/
theorem ForwardSim.simulates {abs : σ → τ} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : ForwardSim (fun s t => abs s = t) impl spec) : Simulates abs impl spec :=
  fun s a => h s (abs s) a rfl

/-! ## Partial steps -/

/-- Forward simulation for partial steps: every successful implementation step from related
states is matched by a successful specification step to a related state. -/
def ForwardSimOpt (R : σ → τ → Prop) (impl : σ → α → Option σ) (spec : τ → α → Option τ) :
    Prop :=
  ∀ s t a s', R s t → impl s a = some s' → ∃ t', spec t a = some t' ∧ R s' t'

/-- A successful atomic implementation run is matched by a successful atomic specification run. -/
theorem ForwardSimOpt.runAll {R : σ → τ → Prop} {impl : σ → α → Option σ}
    {spec : τ → α → Option τ} (h : ForwardSimOpt R impl spec) {ops : List α} :
    ∀ {s : σ} {t : τ} {s' : σ}, R s t → Seq.runAll impl s ops = some s' →
      ∃ t', Seq.runAll spec t ops = some t' ∧ R s' t' := by
  induction ops with
  | nil => intro s t s' h0 e; cases e; exact ⟨t, rfl, h0⟩
  | cons a as ih =>
    intro s t s' h0 e
    obtain ⟨s₁, h₁, h₂⟩ := Seq.runAll_cons_eq_some e
    obtain ⟨t₁, ht₁, hr₁⟩ := h s t a s₁ h0 h₁
    obtain ⟨t', ht', hr'⟩ := ih hr₁ h₂
    exact ⟨t', by simp only [Seq.runAll, ht₁]; exact ht', hr'⟩

/-- Every reachable implementation state is related to a reachable specification state. -/
theorem ForwardSimOpt.reachable {R : σ → τ → Prop} {impl : σ → α → Option σ}
    {spec : τ → α → Option τ} (h : ForwardSimOpt R impl spec) {si : σ} {ti : τ} (h0 : R si ti)
    {s : σ} (hs : Reachable impl si s) : ∃ t, Reachable spec ti t ∧ R s t := by
  induction hs with
  | init => exact ⟨ti, Reachable.init, h0⟩
  | step a _ he ih =>
    obtain ⟨t, ht, hr⟩ := ih
    obtain ⟨t', ht', hr'⟩ := h _ t a _ hr he
    exact ⟨t', Reachable.step a ht ht', hr'⟩

/-- Invariant transfer over reachable states: a property of every reachable specification state
gives, through the relation, a property of every reachable implementation state. -/
theorem ForwardSimOpt.invariant {R : σ → τ → Prop} {impl : σ → α → Option σ}
    {spec : τ → α → Option τ} (h : ForwardSimOpt R impl spec) {si : σ} {ti : τ} (h0 : R si ti)
    {I : τ → Prop} {J : σ → Prop} (hI : ∀ t, Reachable spec ti t → I t)
    (hIJ : ∀ s t, R s t → I t → J s) {s : σ} (hs : Reachable impl si s) : J s := by
  obtain ⟨t, ht, hr⟩ := h.reachable h0 hs
  exact hIJ s t hr (hI t ht)

/-- A total simulation gives a partial one for the steps that always succeed. -/
theorem ForwardSim.toOpt {R : σ → τ → Prop} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : ForwardSim R impl spec) :
    ForwardSimOpt R (fun s a => some (impl s a)) (fun t a => some (spec t a)) := by
  intro s t a s' hr e
  cases e
  exact ⟨spec t a, rfl, h s t a hr⟩

/-! ## Steps with outputs -/

section Outputs

variable {β : Type x}

/-- An implementation that returns its next state and an output, run together with an observer
that updates the specification's record of the facts from the operation and the output. This is
the shape of `advance` in `rc-knight-router`: the router returns its state and the child orders
it sends, and the specification records them. -/
def couple (impl : σ → α → σ × β) (obs : τ → α → β → τ) (p : σ × τ) (a : α) : σ × τ :=
  ((impl p.1 a).1, obs p.2 a (impl p.1 a).2)

/-- The implementation part of a coupled step. -/
@[simp, machine_simps] theorem couple_fst (impl : σ → α → σ × β) (obs : τ → α → β → τ)
    (p : σ × τ) (a : α) : (couple impl obs p a).1 = (impl p.1 a).1 := rfl

/-- The specification part of a coupled step. -/
@[simp, machine_simps] theorem couple_snd (impl : σ → α → σ × β) (obs : τ → α → β → τ)
    (p : σ × τ) (a : α) : (couple impl obs p a).2 = obs p.2 a (impl p.1 a).2 := rfl

/-- The implementation part of a coupled run is the run of the implementation alone. -/
theorem run_couple_fst (impl : σ → α → σ × β) (obs : τ → α → β → τ) (p : σ × τ) (ops : List α) :
    (Seq.run (couple impl obs) p ops).1 = Seq.run (fun s a => (impl s a).1) p.1 ops :=
  (Simulates.run (abs := Prod.fst) (fun _ _ => rfl) p ops)

/-- A relation between the implementation state and the specification's facts that every
coupled step preserves holds after every coupled run. -/
theorem run_couple_invariant {impl : σ → α → σ × β} {obs : τ → α → β → τ} {R : σ → τ → Prop}
    (h : ∀ s t a, R s t → R (impl s a).1 (obs t a (impl s a).2)) {p : σ × τ} (h0 : R p.1 p.2)
    (ops : List α) : R (Seq.run (couple impl obs) p ops).1 (Seq.run (couple impl obs) p ops).2 :=
  run_invariant (I := fun q : σ × τ => R q.1 q.2) (fun q a hq => h q.1 q.2 a hq) h0 ops

/-- The outputs of a run, in order. -/
def outputs (step : σ → α → σ × β) : σ → List α → List β
  | _, [] => []
  | s, a :: as => (step s a).2 :: outputs step (step s a).1 as

/-- No operations, no outputs. -/
@[simp, machine_simps] theorem outputs_nil (step : σ → α → σ × β) (s : σ) :
    outputs step s [] = [] := rfl

/-- The output of the first operation, then the outputs of the rest. -/
@[simp, machine_simps] theorem outputs_cons (step : σ → α → σ × β) (s : σ) (a : α) (as : List α) :
    outputs step s (a :: as) = (step s a).2 :: outputs step (step s a).1 as := rfl

/-- `impl` refines `spec` with equal outputs: the abstraction of the next state is the
specification's next state and the outputs are equal. -/
def SimulatesOut (abs : σ → τ) (impl : σ → α → σ × β) (spec : τ → α → τ × β) : Prop :=
  ∀ s a, abs (impl s a).1 = (spec (abs s) a).1 ∧ (impl s a).2 = (spec (abs s) a).2

/-- A refinement with equal outputs is a simulation of the state parts. -/
theorem SimulatesOut.simulates {abs : σ → τ} {impl : σ → α → σ × β} {spec : τ → α → τ × β}
    (h : SimulatesOut abs impl spec) :
    Simulates abs (fun s a => (impl s a).1) (fun t a => (spec t a).1) :=
  fun s a => (h s a).1

/-- A refinement with equal outputs produces the specification's outputs on every run. -/
theorem SimulatesOut.outputs {abs : σ → τ} {impl : σ → α → σ × β} {spec : τ → α → τ × β}
    (h : SimulatesOut abs impl spec) (s : σ) (ops : List α) :
    Machine.outputs impl s ops = Machine.outputs spec (abs s) ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons a as ih => rw [outputs_cons, outputs_cons, ih, (h s a).1, (h s a).2]

end Outputs

/-! ## Cached fields -/

section Cache

variable {γ : Type x}

/-- A cache that matches the specification's view and that every step keeps matching (assuming
it matched before) matches after every run. With `cache` an implementation counter and `view`
the specification's recomputed total, this is "the counter always equals the truth". -/
theorem cache_run {abs : σ → τ} {impl : σ → α → σ} {spec : τ → α → τ}
    (h : Simulates abs impl spec) {cache : σ → γ} {view : τ → γ}
    (hstep : ∀ s a, cache s = view (abs s) → cache (impl s a) = view (spec (abs s) a)) {s : σ}
    (h0 : cache s = view (abs s)) (ops : List α) :
    cache (Seq.run impl s ops) = view (Seq.run spec (abs s) ops) := by
  rw [← h.run]
  exact run_invariant (I := fun s => cache s = view (abs s))
    (fun s a hs => by
      show cache (impl s a) = view (abs (impl s a)); rw [h s a]; exact hstep s a hs) h0 ops

/-- A view of an event log computed by a left fold extends over a list of events. -/
theorem view_append_list {view : List α → γ} {g : γ → α → γ}
    (hview : ∀ log a, view (log ++ [a]) = g (view log) a) (log xs : List α) :
    view (log ++ xs) = Seq.run g (view log) xs := by
  induction xs generalizing log with
  | nil => simp
  | cons a as ih => rw [← List.singleton_append, ← List.append_assoc, ih, hview]; rfl

/-- A cache kept next to an append-only log. Suppose the specification view of a log is a left
fold (`view (log ++ [a]) = g (view log) a`) and every step either leaves both the log and the
cache unchanged or appends events to the log and folds the same events into the cache. Then the
cache equals the view of the log in every state of every run, as soon as it does at the start. -/
theorem cache_log_invariant {impl : σ → α → σ} {cache : σ → γ} {log : σ → List τ}
    {view : List τ → γ} {g : γ → τ → γ} (hview : ∀ l a, view (l ++ [a]) = g (view l) a)
    (hstep : ∀ s a, ∃ xs, log (impl s a) = log s ++ xs ∧ cache (impl s a) = Seq.run g (cache s) xs) :
    Preserves impl (fun s => cache s = view (log s)) := by
  intro s a hs
  obtain ⟨xs, hl, hc⟩ := hstep s a
  rw [hl, hc, view_append_list hview, hs]

/-- The single-event form: every step leaves the log and the cache unchanged or appends one event
to the log and folds it into the cache. -/
theorem cache_log_invariant' {impl : σ → α → σ} {cache : σ → γ} {log : σ → List τ}
    {view : List τ → γ} {g : γ → τ → γ} (hview : ∀ l a, view (l ++ [a]) = g (view l) a)
    (hstep : ∀ s a, (log (impl s a) = log s ∧ cache (impl s a) = cache s) ∨
      ∃ x, log (impl s a) = log s ++ [x] ∧ cache (impl s a) = g (cache s) x) :
    Preserves impl (fun s => cache s = view (log s)) := by
  apply cache_log_invariant hview
  intro s a
  rcases hstep s a with ⟨hl, hc⟩ | ⟨x, hl, hc⟩
  · exact ⟨[], by simp [hl], hc⟩
  · exact ⟨[x], hl, hc⟩

end Cache

/-- A running total: when every step adds `d a` to a natural-number counter, the counter after a
run is the start value plus the sum over the operations. -/
theorem run_cache_add {impl : σ → α → σ} (cache : σ → Nat) (d : α → Nat)
    (h : ∀ s a, cache (impl s a) = cache s + d a) (s : σ) (ops : List α) :
    cache (Seq.run impl s ops) = cache s + (ops.map d).sum :=
  run_eq_add_sum cache d h s ops

/-- A per-key running total with signed amounts: when every step adds `d a k` to the counter of
every key `k`, the counter of `k` after a run is its start value plus the sum of `d · k` over the
operations. With `d a k := if k = a.account then a.amount else 0` this is the cached balance of
an entry log. -/
theorem run_cache_add_key {κ : Type x} {impl : σ → α → σ} (cache : σ → κ → Int)
    (d : α → κ → Int) (h : ∀ s a k, cache (impl s a) k = cache s k + d a k) (s : σ)
    (ops : List α) (k : κ) :
    cache (Seq.run impl s ops) k = cache s k + Ledger.sumOver ops (fun a => d a k) := by
  induction ops generalizing s with
  | nil => simp
  | cons a as ih => rw [Seq.run_cons, ih, h, Ledger.sumOver_cons]; omega

/-! ## Runs that record their history -/

/-- A step that also records the operation in a history (oldest first). -/
def withHistory (step : σ → α → σ) (p : σ × List α) (a : α) : σ × List α := (step p.1 a, p.2 ++ [a])

/-- A run with history: the state of the run and the history extended by the operations. -/
theorem run_withHistory (step : σ → α → σ) (s : σ) (h : List α) (ops : List α) :
    Seq.run (withHistory step) (s, h) ops = (Seq.run step s ops, h ++ ops) := by
  induction ops generalizing s h with
  | nil => simp
  | cons a as ih => rw [Seq.run_cons]; simp only [withHistory]; rw [ih]; simp

/-- The history is the abstraction of a simulation: a run with history maps to the specification
run that only appends to the log. -/
theorem withHistory_simulates (step : σ → α → σ) :
    Simulates Prod.snd (withHistory step) (fun h a => h ++ [a]) := fun _ _ => rfl

end ProofForgeFin.Machine
