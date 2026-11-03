import Grants.Spec
namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin
  infer_instance

def step : Impl := fun s r =>
  if _ : ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

private theorem step_ok_iff (s : State) (r : Request) :
    (step s r).1 = .ok ↔ ValidCommand s r := by
  unfold step
  constructor
  · intro h
    by_cases hv : ValidCommand s r
    · exact hv
    · simp [hv] at h
  · intro h
    simp [h]

private theorem step_rejected_iff (s : State) (r : Request) :
    (step s r) = (.rejected, s) ↔ ¬ ValidCommand s r := by
  unfold step
  constructor
  · intro heq hn
    simp [hn] at heq
  · intro hn
    simp [hn]

private theorem step_eq_okState (s : State) (r : Request) (h : ValidCommand s r) :
    step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
  unfold step
  simp [h]

private theorem expectedHas_others (s : State) (r : Request) (u : UserId) (q : Role)
    (h : u ≠ r.target ∨ q ≠ r.role) : expectedHas s r u q = s.has u q := by
  unfold expectedHas
  have hn : ¬ (u = r.target ∧ q = r.role) := by
    intro hc
    rcases h with h1 | h1
    · exact h1 hc.1
    · exact h1 hc.2
  simp [hn]

private theorem expectedHas_ne (s : State) (r : Request) (u : UserId) (q : Role)
    (h : ¬ (u = r.target ∧ q = r.role)) : expectedHas s r u q = s.has u q := by
  unfold expectedHas
  simp [h]

private theorem expectedHas_target (s : State) (r : Request) :
    expectedHas s r r.target r.role = decide (r.op = .grant) := by
  unfold expectedHas
  simp

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : AdminOnly step := by
  intro s r hOk
  have hV : ValidCommand s r := (step_ok_iff s r).mp hOk
  unfold ValidCommand at hV
  rcases hV with ⟨h1, h2, h3, _⟩
  exact ⟨h1, h3⟩

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hOk hGrant
  have hV : ValidCommand s r := (step_ok_iff s r).mp hOk
  unfold ValidCommand at hV
  rcases hV with ⟨_, _, _, hG, _⟩
  exact (hG hGrant).1

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hOk u q hNe
  have hV : ValidCommand s r := (step_ok_iff s r).mp hOk
  have heq := step_eq_okState s r hV
  have h2 : (step s r).2.has u q = (expectedHas s r) u q := by
    rw [heq]
  rw [h2]
  exact expectedHas_others s r u q hNe

theorem req_effects : Effects step := by
  intro s r hOk
  have hV : ValidCommand s r := (step_ok_iff s r).mp hOk
  have heq := step_eq_okState s r hV
  constructor
  · rw [heq]
  · intro u q
    have h2 : (step s r).2.has u q = expectedHas s r u q := by rw [heq]
    exact h2

theorem req_idempotency : Idempotent step := by
  intro s r hOk
  have hV : ValidCommand s r := (step_ok_iff s r).mp hOk
  have heq := step_eq_okState s r hV
  have hStep2 : step (step s r).2 r = (.rejected, (step s r).2) := by
    rw [heq]
    apply (step_rejected_iff _ _).mpr
    intro hV2
    unfold ValidCommand at hV hV2
    rcases hV with ⟨_, _, _, hG1, hR1⟩
    rcases hV2 with ⟨_, _, _, hG2, hR2⟩
    cases hop : r.op with
    | grant =>
      have h2 := hG2 hop
      have hExp : expectedHas s r r.target r.role = true := by
        rw [expectedHas_target]; simp [hop]
      have hExpFalse : expectedHas s r r.target r.role = false := h2.2
      rw [hExp] at hExpFalse
      contradiction
    | revoke =>
      have h2 := hR2 hop
      have hExp : expectedHas s r r.target r.role = false := by
        rw [expectedHas_target]; simp [hop]
      have hExpTrue : expectedHas s r r.target r.role = true := h2.1
      rw [hExp] at hExpTrue
      contradiction
  exact hStep2

theorem req_last_admin : KeepsAdmin step := by
  intro s r hExists
  by_cases hV : ValidCommand s r
  · have heq := step_eq_okState s r hV
    have hg : (step s r).2.users = s.users := by rw [heq]
    have hg2 : ∀ u q, (step s r).2.has u q = expectedHas s r u q := by intro u q; rw [heq]
    rcases hExists with ⟨w, hwMem, hwAdmin⟩
    unfold ValidCommand OtherAdmin at hV
    rcases hV with ⟨_, _, _, hG, hR⟩
    by_cases hRevAdmin : r.op = .revoke ∧ r.target = w ∧ r.role = .admin
    · have hOther : OtherAdmin s r.target := by
        have hTmp := hR hRevAdmin.1
        exact hTmp.2 hRevAdmin.2.2
      unfold OtherAdmin at hOther
      rcases hOther with ⟨v, hvMem, hvNe, hvAdmin⟩
      refine ⟨v, ?_, ?_⟩
      · rw [hg]; exact hvMem
      · rw [hg2]
        have hOthers : expectedHas s r v .admin = s.has v .admin := by
          apply expectedHas_others; left; exact hvNe
        rw [hOthers, hvAdmin]
    · refine ⟨w, ?_, ?_⟩
      · rw [hg]; exact hwMem
      · rw [hg2]
        by_cases hEq : w = r.target ∧ .admin = r.role
        · have hEq1 := hEq.1
          have hEq2 := hEq.2
          have hExpEq : expectedHas s r w .admin = decide (r.op = .grant) := by
            have h1 : expectedHas s r w .admin = expectedHas s r r.target r.role := by
              rw [hEq1, ← hEq2]
            rw [h1, expectedHas_target]
          rw [hExpEq]
          have hNotRevoke : r.op ≠ .revoke := by
            intro hRr
            exact hRevAdmin ⟨hRr, hEq1.symm, hEq2.symm⟩
          cases hrp : r.op with
          | grant => simp [hrp]
          | revoke => exact absurd hrp hNotRevoke
        · have hOthers := expectedHas_ne s r w .admin hEq
          rw [hOthers, hwAdmin]
  · have heq : step s r = (.rejected, s) := (step_rejected_iff s r).mpr hV
    have hg : (step s r).2 = s := by rw [heq]
    rw [hg]
    exact hExists

end Grants
