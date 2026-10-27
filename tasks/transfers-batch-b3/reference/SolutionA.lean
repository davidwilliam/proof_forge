import Batch.Spec
import Batch.Lemmas
/-!
# Reference solution A (build team; hidden from agents)

Loop implementation: walk the legs in order against running balances, debiting and
crediting with a two-step update, and abort the whole batch at the first inadmissible leg.
-/

namespace Batch

/-- Add `amt` (possibly negative) to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

/-- Debit the source, then credit the target. -/
def move (bal : AccountId → Int) (l : Leg) : AccountId → Int :=
  adjust (adjust bal l.source (-(l.amount : Int))) l.target l.amount

/-- Boolean admission check of one leg against running balances. -/
def admit (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && l.source != l.target && s.accounts.contains l.source &&
  s.accounts.contains l.target && decide ((l.amount : Int) ≤ bal l.source + s.limit l.source)

/-- Final balances, or `none` if some leg is inadmissible when reached. -/
def run (s : State) : (AccountId → Int) → List Leg → Option (AccountId → Int)
  | bal, [] => some bal
  | bal, l :: ls => if admit s bal l then run s (move bal l) ls else none

/-- Batch-level admission check. -/
def header (s : State) (r : Request) : Bool :=
  decide s.accounts.Nodup && !r.legs.isEmpty && !decide (r.batchId ∈ s.applied)

def step : Impl := fun s r =>
  if header s r then
    match run s s.balance r.legs with
    | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
    | none => (.rejected, s)
  else (.rejected, s)

theorem move_eq (bal : AccountId → Int) (l : Leg) : move bal l = shift bal l := by
  funext a
  unfold move adjust shift
  grind

theorem admit_iff (s : State) (bal : AccountId → Int) (l : Leg) :
    admit s bal l = true ↔ LegOk s bal l := by
  simp only [admit, LegOk, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    List.contains_iff_mem]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, by omega⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, by omega⟩

theorem header_iff (s : State) (r : Request) :
    header s r = true ↔ s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied := by
  simp only [header, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, List.isEmpty_eq_false_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem run_iff (s : State) : ∀ (ls : List Leg) (bal : AccountId → Int),
    (LegsOk s bal ls → run s bal ls = some (applyLegs bal ls)) ∧
    (¬ LegsOk s bal ls → run s bal ls = none) := by
  intro ls
  induction ls with
  | nil => intro bal; exact ⟨fun _ => rfl, fun h => absurd trivial h⟩
  | cons l ls ih =>
    intro bal
    have hcons : LegsOk s bal (l :: ls) ↔ LegOk s bal l ∧ LegsOk s (shift bal l) ls := Iff.rfl
    by_cases hl : LegOk s bal l
    · have ha : admit s bal l = true := (admit_iff s bal l).mpr hl
      have hrun : run s bal (l :: ls) = run s (shift bal l) ls := by
        simp only [run, ha, ite_true, move_eq]
      rw [hrun, hcons]
      exact ⟨fun h => (ih _).1 h.2, fun h => (ih _).2 (fun h' => h ⟨hl, h'⟩)⟩
    · have ha : admit s bal l = false := by
        cases hb : admit s bal l
        · rfl
        · exact absurd ((admit_iff s bal l).mp hb) hl
      have hrun : run s bal (l :: ls) = none := by simp only [run, ha]; rfl
      rw [hrun, hcons]
      exact ⟨fun h => absurd h.1 hl, fun _ => rfl⟩

theorem step_of_valid {s : State} {r : Request} (h : ValidBatch s r) :
    step s r = (.ok, { s with balance := applyLegs s.balance r.legs,
                              applied := r.batchId :: s.applied }) := by
  have hh : header s r = true := (header_iff s r).mpr ⟨h.1, h.2.1, h.2.2.1⟩
  have hr := (run_iff s r.legs s.balance).1 h.2.2.2
  simp only [step, hh, ite_true, hr]

theorem step_of_invalid {s : State} {r : Request} (h : ¬ ValidBatch s r) :
    step s r = (.rejected, s) := by
  by_cases hh : header s r = true
  · have ⟨h1, h2, h3⟩ := (header_iff s r).mp hh
    have hl : ¬ LegsOk s s.balance r.legs := fun hl => h ⟨h1, h2, h3, hl⟩
    have hr := (run_iff s r.legs s.balance).2 hl
    simp only [step, hh, ite_true, hr]
  · have hf : header s r = false := by simpa using hh
    simp only [step, hf]
    rfl

theorem ok_valid {s : State} {r : Request} (h : (step s r).1 = .ok) : ValidBatch s r := by
  by_cases hv : ValidBatch s r
  · exact hv
  · rw [step_of_invalid hv] at h; cases h

/-! ## Facts about the specified balances -/

theorem sum_shift (s : State) (bal : AccountId → Int) (l : Leg) (hnd : s.accounts.Nodup)
    (hl : LegOk s bal l) : sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  unfold shift
  rw [sumOver_add (f := fun a => bal a - (if a = l.source then (l.amount : Int) else 0)),
    sumOver_sub, sumOver_ite_eq hnd, sumOver_ite_eq hnd]
  simp [hl.2.2.1, hl.2.2.2.1]

theorem sum_applyLegs (s : State) (hnd : s.accounts.Nodup) :
    ∀ (ls : List Leg) (bal : AccountId → Int), LegsOk s bal ls →
      sumOver s.accounts (applyLegs bal ls) = sumOver s.accounts bal := by
  intro ls
  induction ls with
  | nil => intro bal _; rfl
  | cons l ls ih =>
    intro bal h
    show sumOver s.accounts (applyLegs (shift bal l) ls) = _
    rw [ih _ h.2, sum_shift s bal l hnd h.1]

theorem limits_shift (s : State) (bal : AccountId → Int) (l : Leg) (hl : LegOk s bal l)
    (hw : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a := by
  intro a ha
  have h0 := hw a ha
  have hlim := hl.2.2.2.2
  unfold shift
  by_cases hs : a = l.source
  · subst hs; simp [hl.2.1]; omega
  · by_cases ht : a = l.target
    · subst ht; simp [hs]; omega
    · simp [hs, ht]; omega

theorem limits_applyLegs (s : State) :
    ∀ (ls : List Leg) (bal : AccountId → Int), LegsOk s bal ls →
      (∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) →
      ∀ k, ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ applyLegs bal (ls.take k) a := by
  intro ls
  induction ls with
  | nil => intro bal _ hw k a ha; simpa [applyLegs] using hw a ha
  | cons l ls ih =>
    intro bal h hw k a ha
    cases k with
    | zero => simpa [applyLegs] using hw a ha
    | succ k =>
      show -(s.limit a : Int) ≤ applyLegs (shift bal l) (ls.take k) a
      exact ih _ h.2 (limits_shift s bal l h.1 hw) k a ha

/-! ## Requirements -/

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h; rw [step_of_valid h]

theorem req_atomicity : Atomicity step := by
  intro s r h; exact step_of_invalid h

theorem req_single_leg : SingleLeg step := by
  intro s r l hl hok
  have hv := ok_valid hok
  have hleg : LegOk s s.balance l := by
    have := hv.2.2.2; rw [hl] at this; exact this.1
  have hne : l.source ≠ l.target := hleg.2.1
  rw [step_of_valid hv, hl]
  constructor
  · simp [applyLegs, shift, hne]
  · simp [applyLegs, shift, Ne.symm hne]

theorem req_effects : Effects step := by
  intro s r hok
  rw [step_of_valid (ok_valid hok)]
  exact ⟨rfl, rfl, fun _ => rfl⟩

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv := ok_valid hok
  rw [step_of_valid hv]
  refine ⟨fun x => by simp, ?_⟩
  apply step_of_invalid
  intro h'
  exact h'.2.2.1 (by simp)

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv := ok_valid hok
  rw [step_of_valid hv]
  exact sum_applyLegs s hv.1 r.legs s.balance hv.2.2.2

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hw
  by_cases hv : ValidBatch s r
  · have hk := limits_applyLegs s r.legs s.balance hv.2.2.2 hw
    refine ⟨?_, fun _ => hk⟩
    rw [step_of_valid hv]
    intro a ha
    have := hk r.legs.length a ha
    rwa [List.take_length] at this
  · rw [step_of_invalid hv]
    exact ⟨hw, fun h => by cases h⟩

end Batch
