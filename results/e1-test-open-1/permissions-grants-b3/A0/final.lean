import Grants.Spec

namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin
  infer_instance

def step : Impl := fun s r =>
  if _h : ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

private theorem valid_of_ok {s : State} {r : Request} (hok : (step s r).1 = .ok) : ValidCommand s r := by
  unfold step at hok
  split at hok
  · assumption
  · contradiction

private theorem step_eq_of_valid {s : State} {r : Request} (hV : ValidCommand s r) :
    step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
  unfold step
  simp [hV]

private theorem step_eq_of_invalid {s : State} {r : Request} (hN : ¬ ValidCommand s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [hN]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hV
  have hEq := step_eq_of_valid (s:=s) (r:=r) hV
  simp [hEq]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hN
  exact step_eq_of_invalid hN

theorem req_authorization : AdminOnly step := by
  intro s r hok
  have hV := valid_of_ok hok
  unfold ValidCommand at hV
  rcases hV with ⟨hMemActor, _hMemTarget, hAdmin, _hg, _hr⟩
  exact ⟨hMemActor, hAdmin⟩

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hGrant
  have hV := valid_of_ok hok
  unfold ValidCommand at hV
  rcases hV with ⟨_, _, _, hg, _⟩
  exact (hg hGrant).left

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hNe
  have hV := valid_of_ok hok
  have hEq := step_eq_of_valid hV
  have hHas : (step s r).2.has u q = expectedHas s r u q := by
    rw [hEq]
  rw [hHas]
  unfold expectedHas
  have hCond : ¬ (u = r.target ∧ q = r.role) := by
    intro hC
    rcases hC with ⟨h1, h2⟩
    rcases hNe with h | h
    · exact h h1
    · exact h h2
  simp [hCond]

theorem req_effects : Effects step := by
  intro s r hok
  have hV := valid_of_ok hok
  have hEq := step_eq_of_valid hV
  constructor
  · simp [hEq]
  · intro u q
    have hHas : (step s r).2.has u q = expectedHas s r u q := by rw [hEq]
    exact hHas

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hV := valid_of_ok hok
  have hEq := step_eq_of_valid hV
  have hHas' : ∀ u q, (step s r).2.has u q = expectedHas s r u q := by
    intro u q
    rw [hEq]
  have hInvalid : ¬ ValidCommand (step s r).2 r := by
    intro hV2
    unfold ValidCommand at hV2
    rcases hV2 with ⟨_hMemA2, _hMemT2, _hAdm2, hg2, hr2⟩
    have hExpTarget : (step s r).2.has r.target r.role = decide (r.op = .grant) := by
      rw [hHas' r.target r.role]
      unfold expectedHas
      simp
    cases hop : r.op with
    | grant =>
      have hNeed : (step s r).2.has r.target r.role = false := by
        have := (hg2 hop).right
        exact this
      have hTrue : decide (r.op = .grant) = true := by simp [hop]
      rw [hTrue] at hExpTarget
      rw [hExpTarget] at hNeed
      contradiction
    | revoke =>
      have hNeed : (step s r).2.has r.target r.role = true := by
        have := (hr2 hop).left
        exact this
      have hFalse : decide (r.op = .grant) = false := by simp [hop]
      rw [hFalse] at hExpTarget
      rw [hExpTarget] at hNeed
      contradiction
  exact step_eq_of_invalid hInvalid

theorem req_last_admin : KeepsAdmin step := by
  intro s r hEx
  rcases hEx with ⟨w, hwMem, hwHas⟩
  by_cases hV : ValidCommand s r
  · have hEq := step_eq_of_valid hV
    have hUsers' : (step s r).2.users = s.users := by rw [hEq]
    have hHas' : ∀ u q, (step s r).2.has u q = expectedHas s r u q := by
      intro u q; rw [hEq]
    have hOther : ∃ u ∈ (step s r).2.users, (step s r).2.has u .admin = true := by
      cases hop : r.op with
      | grant =>
        have hwHas' : (step s r).2.has w .admin = true := by
          rw [hHas' w .admin]
          unfold expectedHas
          by_cases hCond : w = r.target ∧ (Role.admin = r.role)
          · have hDec : decide (r.op = .grant) = true := by simp [hop]
            simp [hCond, hDec]
          · simp [hCond, hwHas]
        exact ⟨w, by rw [hUsers']; exact hwMem, hwHas'⟩
      | revoke =>
        by_cases hRoleAdmin : r.role = .admin
        · by_cases hWTarget : w = r.target
          · have hOtherAdmin : OtherAdmin s r.target := by
              unfold ValidCommand at hV
              rcases hV with ⟨_, _, _, _, hr⟩
              have hr' := hr hop
              exact hr'.right hRoleAdmin
            unfold OtherAdmin at hOtherAdmin
            rcases hOtherAdmin with ⟨v, hvMem, hvNe, hvHas⟩
            have hvHas' : (step s r).2.has v .admin = true := by
              rw [hHas' v .admin]
              unfold expectedHas
              have hCond : ¬ (v = r.target ∧ (Role.admin = r.role)) := by
                intro hC
                rcases hC with ⟨h1, _h2⟩
                exact hvNe h1
              simp [hCond, hvHas]
            exact ⟨v, by rw [hUsers']; exact hvMem, hvHas'⟩
          · have hwHas' : (step s r).2.has w .admin = true := by
              rw [hHas' w .admin]
              unfold expectedHas
              have hCond : ¬ (w = r.target ∧ (Role.admin = r.role)) := by
                intro hC
                rcases hC with ⟨h1, _⟩
                exact hWTarget h1
              simp [hCond, hwHas]
            exact ⟨w, by rw [hUsers']; exact hwMem, hwHas'⟩
        · have hwHas' : (step s r).2.has w .admin = true := by
            rw [hHas' w .admin]
            unfold expectedHas
            have hCond : ¬ (w = r.target ∧ (Role.admin = r.role)) := by
              intro hC
              rcases hC with ⟨_, h2⟩
              exact hRoleAdmin h2.symm
            simp [hCond, hwHas]
          exact ⟨w, by rw [hUsers']; exact hwMem, hwHas'⟩
    exact hOther
  · have hEq := step_eq_of_invalid hV
    rw [hEq]
    exact ⟨w, hwMem, hwHas⟩

end Grants
