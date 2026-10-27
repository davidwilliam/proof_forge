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

theorem req_authorization_test2 : True := by
  have h : ∀ (s : State) (r : Request),
    (if admissible s r then (Outcome.ok : Outcome) else .rejected) = .ok →
    s.auth r.requester r.source = true := by
    intro s r hh
    by_cases hadm : admissible s r
    · obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hadm
      exact hauth
    · simp [hadm] at hh
  trivial

theorem req_auth_aux : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hadm : admissible s r
  · obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hadm
    exact hauth
  · simp [hadm] at h

theorem tmp_debug1 (s : State) (r : Request) : admissible s r ∨ ¬ admissible s r := by
  by_cases hc : admissible s r
  · exact Or.inl hc
  · exact Or.inr hc

theorem tmp_debug2 (s : State) (r : Request) (h : (step s r).1 = .ok) : True := by
  unfold step at h
  by_cases hc : admissible s r
  · trivial
  · simp [hc] at h

theorem tmp_debug6 (s : State) (r : Request) (h : (step s r).1 = .ok) : (step s r).2.balance r.source = s.balance r.source - r.amount ∧ (step s r).2.balance r.target = s.balance r.target + r.amount := by
  unfold step at h
  by_cases hc : admissible s r
  · have hne : r.source ≠ r.target := hc.2.2.1
    have hne2 : r.target ≠ r.source := fun heq => hne heq.symm
    simp [hc] at h
    unfold step
    simp [hc, hne, hne2]
  · simp [hc] at h

theorem req_effects_dbg : True := by
  have g : ∀ s r, (step s r).1 = .ok → (admissible s r) := by
    intro s r h
    unfold step at h
    by_cases hc : admissible s r
    · exact hc
    · simp [hc] at h
  trivial

theorem tmp_idem_gen (r : Request) (s2 : State) (h : ¬ admissible s2 r) : step s2 r = (.rejected, s2) := by
  unfold step
  simp [h]

theorem mytest_limit_aux : True := by trivial

theorem my_cons_helper : True := trivial

theorem cons_check_tmp2 : True := by trivial

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hadm : admissible s r := h
  unfold step
  simp [hadm]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  have hadm : ¬ admissible s r := h
  unfold step
  simp [hadm]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hadm : admissible s r
  · obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hadm
    exact hauth
  · simp [hadm] at h

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  unfold step at h
  by_cases hc : admissible s r
  · have hne : r.source ≠ r.target := hc.2.2.1
    have hne2 : r.target ≠ r.source := fun heq => hne heq.symm
    simp [hc] at h
    unfold step
    simp [hc, hne, hne2]
  · simp [hc] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hc : admissible s r
  · unfold step
    simp only [hc, ↓reduceIte]
    exact ⟨trivial, trivial, trivial, fun a => rfl⟩
  · unfold step at h
    simp only [hc, ↓reduceIte] at h
    exact absurd h (by decide)

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hc : admissible s r := by
    by_cases hcc : admissible s r
    · exact hcc
    · unfold step at hok
      simp [hcc] at hok
  have hstep : step s r = (.ok, { s with balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0), applied := r.txId :: s.applied }) := by
    unfold step
    simp [hc]
  have happ : (step s r).2.applied = r.txId :: s.applied := by
    rw [hstep]
  have hmem : r.txId ∈ (step s r).2.applied := by
    rw [happ]; simp
  have hnadm : ¬ admissible (step s r).2 r := by
    intro hcon
    obtain ⟨_, _, _, _, _, _, _, hnotin⟩ := hcon
    exact hnotin hmem
  exact ⟨by intro x; rw [happ]; simp, tmp_idem_gen r _ hnadm⟩

theorem req_limit : LimitRespected step := by
  intro s r hlim
  by_cases hc : admissible s r
  · have hc0 := hc
    obtain ⟨_, hpos, hne, _, _, _, hsrc_lim, _⟩ := hc
    have hstep2 : (step s r).2 = ({ s with balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0), applied := r.txId :: s.applied } : State) := by
      unfold step
      simp [hc0]
    intro a ha
    have ha' : a ∈ s.accounts := by rw [hstep2] at ha; simpa using ha
    have hold : -((s.limit a : Int)) ≤ s.balance a := hlim a ha'
    have hbal : (step s r).2.balance a = s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0) := by rw [hstep2]
    have hlim' : (step s r).2.limit a = s.limit a := by rw [hstep2]
    rw [hlim', hbal]
    by_cases has : a = r.source
    · subst has
      rw [if_pos rfl, if_neg hne]
      omega
    · by_cases hat : a = r.target
      · subst hat
        rw [if_neg has, if_pos rfl]
        have hnn : (0 : Int) ≤ (r.amount : Int) := by exact_mod_cast Nat.zero_le _
        omega
      · rw [if_neg has, if_neg hat]
        omega
  · have hstep2 : (step s r).2 = s := by unfold step; simp [hc]
    rw [hstep2]
    exact hlim

theorem req_conservation : Conserves step := by
  intro s r hok
  have hc : admissible s r := by
    by_cases hcc : admissible s r
    · exact hcc
    · unfold step at hok
      simp [hcc] at hok
  have hc0 := hc
  obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hlimsrc, hnotin⟩ := hc
  have hstep2 : (step s r).2 = ({ s with balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0), applied := r.txId :: s.applied } : State) := by
    unfold step
    simp [hc0]
  have hacc : (step s r).2.accounts = s.accounts := by rw [hstep2]
  unfold total
  rw [hacc]
  rw [hstep2]
  simp only
  have hSA : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodup r.source (r.amount : Int)
    rw [h]
    simp [hsrc]
  have hTA : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodup r.target (r.amount : Int)
    rw [h]
    simp [htgt]
  have hdecomp : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) + sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) := by
    have e1 : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0))
        = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (if a = r.target then (r.amount : Int) else 0)) := rfl
    rw [e1, sumOver_add]
    congr 1
    exact sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
  rw [hdecomp, hSA, hTA]
  omega

end Transfer
