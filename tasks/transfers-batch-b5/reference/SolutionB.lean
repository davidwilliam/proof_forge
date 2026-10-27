import Batch.Spec
import Batch.Lemmas
/-!
# Reference solution B (build team; hidden from agents)

Check-then-apply implementation: decide admissibility of the whole batch first, then
compute the final balances directly.
-/

namespace Batch

instance instDecidableLegOk (s : State) (bal : AccountId → Int) (l : Leg) :
    Decidable (LegOk s bal l) := by
  unfold LegOk; infer_instance

def decLegsOk (s : State) : (bal : AccountId → Int) → (ls : List Leg) → Decidable (LegsOk s bal ls)
  | _, [] => isTrue trivial
  | bal, l :: ls =>
    match instDecidableLegOk s bal l, decLegsOk s (shift bal l) ls with
    | isTrue h1, isTrue h2 => isTrue ⟨h1, h2⟩
    | isFalse h1, _ => isFalse (fun h => h1 h.1)
    | _, isFalse h2 => isFalse (fun h => h2 h.2)

instance instDecidableLegsOk (s : State) (bal : AccountId → Int) (ls : List Leg) :
    Decidable (LegsOk s bal ls) := decLegsOk s bal ls

instance instDecidableValidBatch (s : State) (r : Request) : Decidable (ValidBatch s r) := by
  unfold ValidBatch; infer_instance

def step : Impl := fun s r =>
  if ValidBatch s r then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else
    (.rejected, s)

theorem step_of_valid {s : State} {r : Request} (h : ValidBatch s r) :
    step s r =
      (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
  simp [step, h]

theorem step_of_invalid {s : State} {r : Request} (h : ¬ ValidBatch s r) :
    step s r = (.rejected, s) := by
  simp [step, h]

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
