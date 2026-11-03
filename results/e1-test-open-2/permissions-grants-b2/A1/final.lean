import Grants.Spec

namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin
  infer_instance

def step : Impl := fun s r =>
  if ValidCommand s r then
    (.ok, { users := s.users, has := fun u q => expectedHas s r u q })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hV
  show (step s r).1 = .ok
  unfold step
  simp [hV]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hN
  show step s r = (.rejected, s)
  unfold step
  simp [hN]

theorem req_authorization : AdminOnly step := by
  intro s r hOk
  show r.actor ∈ s.users ∧ s.has r.actor .admin = true
  by_cases hV : ValidCommand s r
  · obtain ⟨h1, h2, h3, _, _⟩ := hV
    exact ⟨h1, h3⟩
  · unfold step at hOk
    simp [hV] at hOk

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hOk hOp
  show r.actor ≠ r.target
  by_cases hV : ValidCommand s r
  · obtain ⟨_, _, _, hG, _⟩ := hV
    exact (hG hOp).1
  · unfold step at hOk
    simp [hV] at hOk

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hOk u q hNeq
  show (step s r).2.has u q = s.has u q
  by_cases hV : ValidCommand s r
  · have hStep : (step s r).2 = { users := s.users, has := fun u q => expectedHas s r u q } := by
      unfold step; simp [hV]
    rw [hStep]
    show expectedHas s r u q = s.has u q
    unfold expectedHas
    have hcond : ¬ (u = r.target ∧ q = r.role) := by
      intro ⟨hu, hq⟩
      rcases hNeq with h | h
      · exact h hu
      · exact h hq
    simp [hcond]
  · unfold step at hOk
    simp [hV] at hOk

theorem req_effects : Effects step := by
  intro s r hOk
  show (step s r).2.users = s.users ∧ ∀ u q, (step s r).2.has u q = expectedHas s r u q
  by_cases hV : ValidCommand s r
  · have hStep : (step s r).2 = { users := s.users, has := fun u q => expectedHas s r u q } := by
      unfold step; simp [hV]
    constructor
    · rw [hStep]
    · intro u q; rw [hStep]
  · unfold step at hOk
    simp [hV] at hOk

theorem req_idempotency : Idempotent step := by
  intro s r hOk
  show step (step s r).2 r = (.rejected, (step s r).2)
  by_cases hV : ValidCommand s r
  · have hStep2 : (step s r).2 = ({ users := s.users, has := fun u q => expectedHas s r u q } : State) := by
      unfold step; simp [hV]
    have hNot : ¬ ValidCommand (step s r).2 r := by
      rw [hStep2]
      intro hV2
      obtain ⟨_, _, _, hG, hRv⟩ := hV
      obtain ⟨_, _, _, hG2, hR2⟩ := hV2
      cases hop : r.op with
      | grant =>
        have hg2 := hG2 hop
        have hIsTrue : expectedHas s r r.target r.role = true := by
          unfold expectedHas; simp [hop]
        simp [hIsTrue] at hg2
      | revoke =>
        have hr2 := hR2 hop
        have hIsFalse : expectedHas s r r.target r.role = false := by
          unfold expectedHas; simp [hop]
        simp [hIsFalse] at hr2
    have hStepUnfold : step (step s r).2 r = (if ValidCommand (step s r).2 r then (.ok, { users := (step s r).2.users, has := fun u q => expectedHas (step s r).2 r u q }) else (.rejected, (step s r).2)) := by
      unfold step; rfl
    rw [hStepUnfold, if_neg hNot]
  · unfold step at hOk
    simp [hV] at hOk

theorem req_last_admin : KeepsAdmin step := by
  intro s r hEx
  show ∃ u ∈ (step s r).2.users, (step s r).2.has u .admin = true
  by_cases hV : ValidCommand s r
  · have hStep : (step s r).2 = ({ users := s.users, has := fun u q => expectedHas s r u q } : State) := by
      unfold step; simp [hV]
    rw [hStep]
    simp only
    obtain ⟨hMemA, hMemT, hAdmA, hG, hRv⟩ := hV
    cases hop : r.op with
    | grant =>
      obtain ⟨w, hwMem, hwAdmin⟩ := hEx
      refine ⟨w, hwMem, ?_⟩
      show expectedHas s r w .admin = true
      unfold expectedHas
      simp only [hop, decide_true]
      by_cases hwEq : w = r.target ∧ Role.admin = r.role
      · simp [hwEq]
      · simp [hwEq, hwAdmin]
    | revoke =>
      by_cases hRole : r.role = Role.admin
      · have hr := hRv hop
        have hOA : OtherAdmin s r.target := hr.2 hRole
        obtain ⟨v, hvMem, hvNe, hvAdmin⟩ := hOA
        refine ⟨v, hvMem, ?_⟩
        show expectedHas s r v .admin = true
        unfold expectedHas
        simp only [hop, decide_false]
        have hNeConj : ¬ (v = r.target ∧ Role.admin = r.role) := by
          intro ⟨h1, h2⟩
          exact hvNe h1
        simp [hNeConj, hvAdmin]
      · obtain ⟨w, hwMem, hwAdmin⟩ := hEx
        refine ⟨w, hwMem, ?_⟩
        show expectedHas s r w .admin = true
        unfold expectedHas
        simp only [hop, decide_false]
        by_cases hwEq : w = r.target ∧ Role.admin = r.role
        · obtain ⟨hw1, hw2⟩ := hwEq
          exact absurd hw2.symm hRole
        · simp [hwEq, hwAdmin]
  · unfold step
    simp [hV]
    exact hEx

end Grants
