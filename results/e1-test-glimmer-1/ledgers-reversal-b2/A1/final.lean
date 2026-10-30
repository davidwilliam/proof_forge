import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance

instance instDecidableValidReverse (s : State) (i : EntryId) : Decidable (ValidReverse s i) := by
  unfold ValidReverse; infer_instance

/-- Add `amt` to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

/-- Post every line, first to last. -/
def postLines : List Line → (AccountId → Int) → (AccountId → Int)
  | [], bal => bal
  | l :: ls, bal => postLines ls (adjust bal l.1 l.2)

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if h : ValidPost s e then
      (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] })
    else (.rejected, s)
  | .reverse i =>
    if h : ValidReverse s i then
      match findEntry s.journal i with
      | some e =>
        (.ok, { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                       reversed := i :: s.reversed })
      | none => (.rejected, s) -- unreachable under ValidReverse
    else (.rejected, s)

theorem adjust_cancel (bal : AccountId → Int) (a : AccountId) (amt : Int) :
    adjust (adjust bal a amt) a (-amt) = bal := by
  funext b
  dsimp [adjust]
  by_cases hb : b = a
  · subst hb; simp; omega
  · simp [hb]

theorem sumOver_adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) (accounts : List AccountId) (hnd : accounts.Nodup) :
    sumOver accounts (adjust bal a amt) = sumOver accounts bal + (if a ∈ accounts then amt else 0) := by
  unfold adjust
  have : (fun acc => if acc = a then bal acc + amt else bal acc) = (fun acc => bal acc + (if acc = a then amt else 0)) := by funext x; by_cases h : x = a; simp [h]; simp [h]
  rw [this]
  have hsum : sumOver accounts (fun acc => bal acc + (if acc = a then amt else 0)) = sumOver accounts bal + sumOver accounts (fun acc => if acc = a then amt else 0) := by apply sumOver_add
  rw [hsum]
  have h2 : sumOver accounts (fun acc => if acc = a then amt else 0) = if a ∈ accounts then amt else 0 := by
    apply sumOver_ite_eq hnd a amt
  rw [h2]

theorem postLines_total (bal : AccountId → Int) (ls : List Line) (accounts : List AccountId) (hnd : accounts.Nodup) :
    sumOver accounts (postLines ls bal) = sumOver accounts bal + sumOver ls (fun l => if l.1 ∈ accounts then l.2 else 0) := by
  induction ls generalizing bal with
  | nil => simp [postLines]
  | cons l ls ih =>
    simp [postLines]
    have h1 : sumOver accounts (adjust bal l.1 l.2) = sumOver accounts bal + (if l.1 ∈ accounts then l.2 else 0) := by
      apply sumOver_adjust bal l.1 l.2 accounts hnd
    have h2 : sumOver accounts (postLines ls (adjust bal l.1 l.2)) = sumOver accounts (adjust bal l.1 l.2) + sumOver ls (fun l' => if l'.1 ∈ accounts then l'.2 else 0) := by
      apply ih
    rw [h2, h1]
    omega

theorem adjust_eq (bal : AccountId → Int) (a : AccountId) (amt : Int) (b : AccountId) :
    adjust bal a amt b = bal b + if b = a then amt else 0 := by
  unfold adjust
  by_cases h : b = a
  · subst h; simp
  · simp [h]

theorem req_post_succeeds : PostSucceeds step := by
  intro s e hvp
  unfold step
  simp [hvp]

theorem req_reverse_succeeds : ReverseSucceeds step := sorry

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    simp [step]
    by_cases hvp : ValidPost s e
    · have : Valid s (Command.post e) := by simp [Valid, hvp]
      exact absurd this h
    · simp [hvp]
  | reverse i =>
    simp [step]
    by_cases hvr : ValidReverse s i
    · have : Valid s (Command.reverse i) := by simp [Valid, hvr]
      exact absurd this h
    · simp [hvr]

theorem req_post_effects     : PostEffects step := sorry

theorem req_reverse_effects  : ReverseEffects step := sorry

theorem req_reverse_once     : ReverseOnce step := sorry

theorem req_roundtrip        : RoundTrip step := sorry

theorem req_trial_balance    : TrialBalance step := sorry

theorem req_well_formed      : StaysWellFormed step := sorry

theorem req_consistent       : StaysConsistent step := sorry

end Reversal
