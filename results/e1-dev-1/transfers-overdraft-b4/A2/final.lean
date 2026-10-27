import Transfer.Spec
import Transfer.Lemmas
namespace Transfer
/-- Admission check for a transfer request. -/
def admissible (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧
  0 < r.amount ∧
  r.source ≠ r.target ∧
  r.source ∈ s.accounts ∧
  r.target ∈ s.accounts ∧
  s.auth r.requester r.source = true ∧
  -(s.limit r.source : Int) ≤ s.balance r.source - r.amount ∧
  r.txId ∉ s.applied

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (admissible s r) := by
  unfold admissible; infer_instance

def step : Impl := fun s r =>
  if admissible s r then
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_debit_credit_aux2 : DebitCredit step := by
  intro s r h
  by_cases hc : admissible s r
  · have hstep : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by unfold step; simp [hc]
    obtain ⟨_, _, hne, _, _, _, _, _⟩ := hc
    rw [hstep]
    constructor
    · simp [hne]
    · simp [Ne.symm hne]
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [hc]
    rw [hrej] at h
    contradiction

theorem mytest1 : (2 : Int) + 0 = 2 := by simp

theorem mytest2 : (2 : Int) - 0 = 2 := by simp

theorem probe_add_zero (a : Int) : a + 0 = a := by simp

theorem probe_sub_zero (a : Int) : a - 0 = a := by simp

theorem probe_if (x y : Nat) (h : x ≠ y) (c d : Int) : (if x = y then c else d) = d := by simp [h]

theorem probe_rw (s : State) (r : Request) (hc : admissible s r) :
    (step s r).2.accounts = s.accounts := by
  unfold step
  simp [hc]

theorem req_limit_aux_probe (s : State) (r : Request) (a : AccountId) (hne : r.source ≠ r.target) (has : a = r.source) :
    (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0)) =
    (s.balance r.source - (r.amount : Int)) := by
  subst has
  simp [hne]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have h' : admissible s r := h
  show (step s r).1 = .ok
  unfold step
  simp [h']

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have h' : ¬ admissible s r := h
  show step s r = (.rejected, s)
  unfold step
  simp [h']

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hc : admissible s r
  · obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hc
    exact hauth
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [hc]
    rw [hrej] at h
    contradiction

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  by_cases hc : admissible s r
  · have hstep : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by unfold step; simp [hc]
    obtain ⟨_, _, hne, _, _, _, _, _⟩ := hc
    rw [hstep]
    constructor
    · simp [hne]
    · simp [Ne.symm hne]
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [hc]
    rw [hrej] at h
    contradiction

theorem req_effects : Effects step := by
  intro s r h
  by_cases hc : admissible s r
  · have hstep : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by unfold step; simp [hc]
    rw [hstep]
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro a
    rfl
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [hc]
    rw [hrej] at h
    contradiction

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hc : admissible s r
  · have hstep : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by unfold step; simp [hc]
    have h2eq : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } : State) := by rw [hstep]
    constructor
    · intro x
      rw [h2eq]
      simp
    · have hnot_rec : ¬ admissible
        ({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State) r := by
        intro hcon
        obtain ⟨_, _, _, _, _, _, _, hni⟩ := hcon
        simp at hni
      have hsr : step
        ({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State) r =
        (.rejected,
        ({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State)) := by
        unfold step; simp [hnot_rec]
      rw [h2eq]
      exact hsr
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [hc]
    rw [hrej] at hok
    contradiction

theorem req_limit : LimitRespected step := by
  intro s r hlim
  by_cases hc : admissible s r
  · have hc0 := hc
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hfloor, hni⟩ := hc
    have hstep2 : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } : State) := by unfold step; simp [hc0]
    rw [hstep2]
    intro a ha
    have ha0 : a ∈ s.accounts := ha
    have hlim_a : -(s.limit a : Int) ≤ s.balance a := hlim a ha0
    by_cases has : a = r.source
    · subst has
      show -(s.limit r.source : Int) ≤ (s.balance r.source - (if r.source = r.source then (r.amount : Int) else 0) + (if r.source = r.target then (r.amount : Int) else 0))
      simp [hne]
      exact hfloor
    · show -(s.limit a : Int) ≤ (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0))
      have h1 : (if a = r.source then (r.amount : Int) else 0) = 0 := by simp [has]
      rw [h1, probe_sub_zero]
      by_cases hat : a = r.target
      · subst hat
        simp only [if_true]
        omega
      · have h2 : (if a = r.target then (r.amount : Int) else 0) = 0 := by simp [hat]
        rw [h2, probe_add_zero]
        exact hlim_a
  · have hstep2 : (step s r).2 = s := by unfold step; simp [hc]
    rw [hstep2]
    exact hlim

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases hc : admissible s r
  · have hc0 := hc
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hfloor, hni⟩ := hc
    have h2eq : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } : State) := by unfold step; simp [hc0]
    have hacc : (step s r).2.accounts = s.accounts := by rw [h2eq]
    have hbal : (step s r).2.balance = (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0)) := by rw [h2eq]
    unfold total
    rw [hacc, hbal]
    have h1 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0))
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        + sumOver s.accounts (fun a => (if a = r.target then (r.amount : Int) else 0)) := by
      have h := sumOver_add s.accounts
        (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        (fun a => (if a = r.target then (r.amount : Int) else 0))
      have hcongr : ∀ a ∈ s.accounts,
        (s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (if a = r.target then (r.amount : Int) else 0))
        = ((fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) a
          + (fun a => (if a = r.target then (r.amount : Int) else 0)) a) := by
        intro a _; rfl
      rw [sumOver_congr _ _ _ hcongr]
      exact h
    have h2 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) :=
      sumOver_sub s.accounts s.balance (fun a => (if a = r.source then (r.amount : Int) else 0))
    rw [h1, h2]
    rw [sumOver_ite_eq hnodup r.source (r.amount : Int)]
    rw [sumOver_ite_eq hnodup r.target (r.amount : Int)]
    simp [hsrc, htgt]
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [hc]
    rw [hrej] at hok
    contradiction

end Transfer
