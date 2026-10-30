import ProofForgeFin.Machine.Record
/-!
# Idempotent operations keyed by an identifier

Payment and ledger APIs make a request idempotent by a client-chosen identifier: the first
request with an identifier takes effect, and every later request with the same identifier
changes nothing ("posting twice equals posting once"). `keyed key step` wraps any step function
with the set of identifiers already seen.

* `keyed_keyed`: applying the same operation twice is applying it once; `keyed_resubmit`: a later
  operation with an identifier already seen is ignored whatever its other fields are.
* `run_keyed_twice`: replaying a whole log a second time changes nothing; `run_keyed_of_seen`:
  a run of operations whose identifiers were all seen changes nothing.
* `run_keyed_fst`: the state after a run with resubmissions is the state after running only the
  first occurrence of every identifier (`fresh`); `run_keyed_of_nodup`: with distinct new
  identifiers, the wrapper is invisible.
* `keyed_preserves`: every invariant of the step is an invariant of the wrapped step.

The wrapped state is a pair `(state, seen)`. A task state that keeps the posted identifiers as a
field maps to this pair by an abstraction function (see `ProofForgeFin.Machine.Refine`).
-/

namespace ProofForgeFin.Machine

universe u v w

variable {σ : Type u} {α : Type v} {ι : Type w} [DecidableEq ι]

/-- `step` made idempotent by the identifier `key a`: an operation whose identifier was already
seen leaves the state unchanged; otherwise it is applied and its identifier recorded. -/
def keyed (key : α → ι) (step : σ → α → σ) (p : σ × List ι) (a : α) : σ × List ι :=
  if key a ∈ p.2 then p else (step p.1 a, key a :: p.2)

/-- An operation with an identifier already seen changes nothing. -/
theorem keyed_of_mem (key : α → ι) (step : σ → α → σ) {p : σ × List ι} {a : α} (h : key a ∈ p.2) :
    keyed key step p a = p := by
  simp [keyed, h]

/-- An operation with a new identifier is applied and its identifier recorded. -/
theorem keyed_of_not_mem (key : α → ι) (step : σ → α → σ) {p : σ × List ι} {a : α}
    (h : key a ∉ p.2) : keyed key step p a = (step p.1 a, key a :: p.2) := by
  simp [keyed, h]

/-- The identifiers seen after an operation: its own and the earlier ones. -/
theorem mem_keyed_seen (key : α → ι) (step : σ → α → σ) (p : σ × List ι) (a : α) (x : ι) :
    x ∈ (keyed key step p a).2 ↔ x = key a ∨ x ∈ p.2 := by
  unfold keyed; split
  · next h => constructor
              · exact Or.inr
              · rintro (rfl | hx)
                · exact h
                · exact hx
  · simp

/-- After an operation its identifier is seen. -/
theorem key_mem_keyed (key : α → ι) (step : σ → α → σ) (p : σ × List ι) (a : α) :
    key a ∈ (keyed key step p a).2 :=
  (mem_keyed_seen key step p a (key a)).mpr (Or.inl rfl)

/-- Idempotence: applying an operation twice is applying it once. -/
@[simp] theorem keyed_keyed (key : α → ι) (step : σ → α → σ) (p : σ × List ι) (a : α) :
    keyed key step (keyed key step p a) a = keyed key step p a :=
  keyed_of_mem key step (key_mem_keyed key step p a)

/-- A resubmission is ignored whatever its other fields are: after `a`, an operation `b` with the
same identifier changes nothing. -/
theorem keyed_resubmit (key : α → ι) (step : σ → α → σ) (p : σ × List ι) {a b : α}
    (h : key b = key a) : keyed key step (keyed key step p a) b = keyed key step p a :=
  keyed_of_mem key step (h ▸ key_mem_keyed key step p a)

/-- The identifiers seen never shrink along a run. -/
theorem mem_run_keyed_of_mem (key : α → ι) (step : σ → α → σ) {p : σ × List ι} {x : ι}
    (h : x ∈ p.2) (ops : List α) : x ∈ (Seq.run (keyed key step) p ops).2 := by
  induction ops generalizing p with
  | nil => exact h
  | cons a as ih => exact ih ((mem_keyed_seen key step p a x).mpr (Or.inr h))

/-- After a run, the identifier of every operation of the run is seen. -/
theorem key_mem_run_keyed (key : α → ι) (step : σ → α → σ) (p : σ × List ι) {ops : List α}
    {a : α} (ha : a ∈ ops) : key a ∈ (Seq.run (keyed key step) p ops).2 := by
  induction ops generalizing p with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with e | e
    · subst e; exact mem_run_keyed_of_mem key step (key_mem_keyed key step p a) bs
    · exact ih _ e

/-- A run of operations whose identifiers were all seen changes nothing. -/
theorem run_keyed_of_seen (key : α → ι) (step : σ → α → σ) {p : σ × List ι} {ops : List α}
    (h : ∀ a ∈ ops, key a ∈ p.2) : Seq.run (keyed key step) p ops = p := by
  induction ops with
  | nil => rfl
  | cons a as ih =>
    rw [Seq.run_cons, keyed_of_mem key step (h a (by simp))]
    exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- Appending operations whose identifiers already occur earlier in the run, or were seen before
it, changes nothing. -/
theorem run_keyed_append_of_seen (key : α → ι) (step : σ → α → σ) (p : σ × List ι)
    {ops ops' : List α} (h : ∀ b ∈ ops', key b ∈ p.2 ∨ ∃ a ∈ ops, key a = key b) :
    Seq.run (keyed key step) p (ops ++ ops') = Seq.run (keyed key step) p ops := by
  rw [Seq.run_append]
  apply run_keyed_of_seen
  intro b hb
  rcases h b hb with h1 | ⟨a, ha, e⟩
  · exact mem_run_keyed_of_mem key step h1 ops
  · exact e ▸ key_mem_run_keyed key step p ha

/-- Replaying a whole log a second time changes nothing. -/
@[simp] theorem run_keyed_twice (key : α → ι) (step : σ → α → σ) (p : σ × List ι) (ops : List α) :
    Seq.run (keyed key step) p (ops ++ ops) = Seq.run (keyed key step) p ops :=
  run_keyed_append_of_seen key step p (fun b hb => Or.inr ⟨b, hb, rfl⟩)

/-- The operations of `ops` that take effect after the identifiers `seen`: the first occurrence
of every identifier not in `seen`. -/
def fresh (key : α → ι) : List ι → List α → List α
  | _, [] => []
  | seen, a :: as => if key a ∈ seen then fresh key seen as else a :: fresh key (key a :: seen) as

/-- The state after a run with resubmissions is the state after running only the operations that
take effect. -/
theorem run_keyed_fst (key : α → ι) (step : σ → α → σ) (s : σ) (seen : List ι) (ops : List α) :
    (Seq.run (keyed key step) (s, seen) ops).1 = Seq.run step s (fresh key seen ops) := by
  induction ops generalizing s seen with
  | nil => rfl
  | cons a as ih =>
    rw [Seq.run_cons]
    by_cases h : key a ∈ seen
    · rw [keyed_of_mem key step (p := (s, seen)) h, ih]; simp [fresh, h]
    · rw [keyed_of_not_mem key step (p := (s, seen)) h, ih]; simp [fresh, h]

/-- The identifiers seen after a run: those of the operations that took effect, latest first,
then the earlier ones. -/
theorem run_keyed_snd (key : α → ι) (step : σ → α → σ) (s : σ) (seen : List ι) (ops : List α) :
    (Seq.run (keyed key step) (s, seen) ops).2 = (fresh key seen ops).reverse.map key ++ seen := by
  induction ops generalizing s seen with
  | nil => rfl
  | cons a as ih =>
    rw [Seq.run_cons]
    by_cases h : key a ∈ seen
    · rw [keyed_of_mem key step (p := (s, seen)) h, ih]; simp [fresh, h]
    · rw [keyed_of_not_mem key step (p := (s, seen)) h, ih]; simp [fresh, h]

/-- The operations that take effect are operations of the run. -/
theorem mem_of_mem_fresh (key : α → ι) {seen : List ι} {ops : List α} {a : α}
    (h : a ∈ fresh key seen ops) : a ∈ ops := by
  induction ops generalizing seen with
  | nil => simp [fresh] at h
  | cons b bs ih =>
    simp only [fresh] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with e | e
      · exact e ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih e)

/-- The operations that take effect have distinct identifiers, none of them seen before. -/
theorem fresh_keys (key : α → ι) (seen : List ι) (ops : List α) :
    ((fresh key seen ops).map key).Nodup ∧ ∀ a ∈ fresh key seen ops, key a ∉ seen := by
  induction ops generalizing seen with
  | nil => simp [fresh]
  | cons b bs ih =>
    simp only [fresh]
    split
    · exact ih seen
    · next h =>
      obtain ⟨h1, h2⟩ := ih (key b :: seen)
      refine ⟨?_, ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, h1⟩
        obtain ⟨c, hc, e⟩ := List.mem_map.mp hm
        exact h2 c hc (e ▸ List.mem_cons_self)
      · intro a ha
        rcases List.mem_cons.mp ha with e | e
        · exact e ▸ h
        · exact fun hm => h2 a e (List.mem_cons_of_mem _ hm)

/-- With distinct identifiers none of which was seen, every operation takes effect. -/
theorem fresh_of_nodup (key : α → ι) {seen : List ι} {ops : List α} (hnd : (ops.map key).Nodup)
    (hnew : ∀ a ∈ ops, key a ∉ seen) : fresh key seen ops = ops := by
  induction ops generalizing seen with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [fresh, hnew a (by simp), ite_false]
    congr 1
    apply ih hnd.2
    intro b hb hm
    rcases List.mem_cons.mp hm with e | e
    · exact hnd.1 (e ▸ List.mem_map_of_mem hb)
    · exact hnew b (List.mem_cons_of_mem _ hb) e

/-- With distinct new identifiers the idempotence wrapper is invisible. -/
theorem run_keyed_of_nodup (key : α → ι) (step : σ → α → σ) (s : σ) {seen : List ι}
    {ops : List α} (hnd : (ops.map key).Nodup) (hnew : ∀ a ∈ ops, key a ∉ seen) :
    (Seq.run (keyed key step) (s, seen) ops).1 = Seq.run step s ops := by
  rw [run_keyed_fst, fresh_of_nodup key hnd hnew]

/-- Every invariant of the step is an invariant of the wrapped step. -/
theorem keyed_preserves (key : α → ι) {step : σ → α → σ} {I : σ → Prop}
    (h : Seq.Preserves step I) : Seq.Preserves (keyed key step) (fun p => I p.1) := by
  intro p a hp
  unfold keyed; split
  · exact hp
  · exact h p.1 a hp

/-- Distinct seen identifiers stay distinct. -/
theorem keyed_seen_nodup (key : α → ι) (step : σ → α → σ) :
    Seq.Preserves (keyed key step) (fun p => p.2.Nodup) := by
  intro p a hp
  unfold keyed; split
  · exact hp
  · next h => exact List.nodup_cons.mpr ⟨h, hp⟩

end ProofForgeFin.Machine
