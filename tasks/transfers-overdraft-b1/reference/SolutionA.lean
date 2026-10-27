import Transfer.Spec
import Transfer.Lemmas
/-!
# Reference solution A (build team; hidden from agents)

Two-phase implementation: check the request field by field, debit the source, then credit
the target.
-/

namespace Transfer

/-- Add `amt` (possibly negative) to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

/-- Boolean admission check. -/
def admits (s : State) (r : Request) : Bool :=
  decide s.accounts.Nodup && decide (0 < r.amount) && r.source != r.target &&
  s.accounts.contains r.source && s.accounts.contains r.target &&
  s.auth r.requester r.source &&
  decide ((r.amount : Int) ≤ s.balance r.source + s.limit r.source) &&
  !decide (r.txId ∈ s.applied)

theorem admits_iff (s : State) (r : Request) : admits s r = true ↔ ValidTransfer s r := by
  simp only [admits, ValidTransfer, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    List.contains_iff_mem, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, by omega, h8⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, by omega⟩, h8⟩

def step : Impl := fun s r =>
  if admits s r then
    let debited := adjust s.balance r.source (-(r.amount : Int))
    (.ok, { s with balance := adjust debited r.target r.amount,
                   applied := r.txId :: s.applied })
  else
    (.rejected, s)

theorem new_balance (s : State) (r : Request) :
    adjust (adjust s.balance r.source (-(r.amount : Int))) r.target r.amount
      = expectedBalance s r := by
  funext a
  unfold adjust expectedBalance
  grind

theorem step_of_valid {s : State} {r : Request} (h : ValidTransfer s r) :
    step s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
  have h' := (admits_iff s r).mpr h
  simp only [step, h', ite_true, new_balance]

theorem step_of_invalid {s : State} {r : Request} (h : ¬ ValidTransfer s r) :
    step s r = (.rejected, s) := by
  have h' : admits s r = false := by
    cases hb : admits s r
    · rfl
    · exact absurd ((admits_iff s r).mp hb) h
  simp only [step, h']
  rfl

theorem ok_valid {s : State} {r : Request} (h : (step s r).1 = .ok) : ValidTransfer s r := by
  by_cases hv : ValidTransfer s r
  · exact hv
  · rw [step_of_invalid hv] at h; cases h

theorem next_balance {s : State} {r : Request} (hok : (step s r).1 = .ok) (a : AccountId) :
    (step s r).2.balance a = expectedBalance s r a := by
  rw [step_of_valid (ok_valid hok)]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h; rw [step_of_valid h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h; exact step_of_invalid h

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  exact (ok_valid hok).2.2.2.2.2.1

theorem req_debit_credit : DebitCredit step := by
  intro s r hok
  have hne : r.source ≠ r.target := (ok_valid hok).2.2.1
  rw [next_balance hok, next_balance hok]
  constructor
  · simp [expectedBalance, hne]
  · simp [expectedBalance, Ne.symm hne]

theorem req_effects : Effects step := by
  intro s r hok
  refine ⟨?_, ?_, ?_, next_balance hok⟩ <;> rw [step_of_valid (ok_valid hok)]

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv := ok_valid hok
  rw [step_of_valid hv]
  refine ⟨fun x => by simp, ?_⟩
  apply step_of_invalid
  intro h'
  exact h'.2.2.2.2.2.2.2 (by simp)

theorem req_limit : LimitRespected step := by
  intro s r hw
  by_cases hv : ValidTransfer s r
  · have hok : (step s r).1 = .ok := by rw [step_of_valid hv]
    have hacc : (step s r).2.accounts = s.accounts := by rw [step_of_valid hv]
    have hlimit : (step s r).2.limit = s.limit := by rw [step_of_valid hv]
    intro a ha
    rw [hacc] at ha
    rw [hlimit, next_balance hok]
    have h0 := hw a ha
    have hlim := hv.2.2.2.2.2.2.1
    unfold expectedBalance
    by_cases hs : a = r.source
    · subst hs; simp [hv.2.2.1]; omega
    · by_cases ht : a = r.target
      · subst ht; simp [hs]; omega
      · simp [hs, ht]; omega
  · rw [step_of_invalid hv]; exact hw

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv := ok_valid hok
  have hacc : (step s r).2.accounts = s.accounts := by rw [step_of_valid hv]
  unfold total
  rw [hacc, sumOver_congr _ _ _ (fun a _ => next_balance hok a)]
  unfold expectedBalance
  rw [sumOver_add (f := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)),
    sumOver_sub, sumOver_ite_eq hv.1, sumOver_ite_eq hv.1]
  simp [hv.2.2.2.1, hv.2.2.2.2.1]

end Transfer
