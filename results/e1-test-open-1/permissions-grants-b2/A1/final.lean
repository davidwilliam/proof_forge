import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance
def step : Impl := fun s r =>
  if h : ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

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
  have hDec : Decidable (ValidCommand s r) := instDecidableValidCommand s r
  by_cases hV : ValidCommand s r
  · exact ⟨hV.1, hV.2.2.1⟩
  · have heq : step s r = (.rejected, s) := by
      unfold step
      simp [hV]
    have h1 : (step s r).1 = .rejected := by
      simp [heq]
    rw [h1] at hOk
    contradiction

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hOk hGrant
  have hDec : Decidable (ValidCommand s r) := instDecidableValidCommand s r
  by_cases hV : ValidCommand s r
  · have h1 := hV.2.2.2.1 hGrant
    exact h1.1
  · have heq : step s r = (.rejected, s) := by
      unfold step
      simp [hV]
    have h1 : (step s r).1 = .rejected := by simp [heq]
    rw [h1] at hOk
    contradiction

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hOk u q hNe
  have hDec : Decidable (ValidCommand s r) := instDecidableValidCommand s r
  by_cases hV : ValidCommand s r
  · have hStep : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
      unfold step; simp [hV]
    have hHas : (step s r).2.has u q = expectedHas s r u q := by
      rw [hStep]
    rw [hHas]
    unfold expectedHas
    split
    · next h =>
      exfalso
      have hNot : ¬(u = r.target ∧ q = r.role) := by
        intro hConj
        rcases hNe with h1 | h2
        · exact h1 hConj.1
        · exact h2 hConj.2
      exact hNot h
    · rfl
  · have heq : step s r = (.rejected, s) := by
      unfold step; simp [hV]
    have h1 : (step s r).1 = .rejected := by simp [heq]
    rw [h1] at hOk
    contradiction

theorem req_effects : Effects step := by
  intro s r hOk
  have hDec : Decidable (ValidCommand s r) := instDecidableValidCommand s r
  by_cases hV : ValidCommand s r
  · have hStep : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
      unfold step; simp [hV]
    constructor
    · have hUsers : (step s r).2.users = s.users := by rw [hStep]
      exact hUsers
    · intro u q
      have hHas : (step s r).2.has u q = expectedHas s r u q := by rw [hStep]
      exact hHas
  · have heq : step s r = (.rejected, s) := by unfold step; simp [hV]
    have h1 : (step s r).1 = .rejected := by simp [heq]
    rw [h1] at hOk
    contradiction

theorem req_idempotency : Idempotent step := by
  intro s r hOk
  have hDec : Decidable (ValidCommand s r) := instDecidableValidCommand s r
  by_cases hV : ValidCommand s r
  · have hStep : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step; simp [hV]
    have hS2_eq : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by rw [hStep]
    have hNotValid : ¬ ValidCommand (step s r).2 r := by
      rw [hS2_eq]
      intro hV2
      cases hOp : r.op with
      | grant =>
        have h2 := hV2.2.2.2.1 hOp
        have hHasFalse2 : (({ users := s.users, has := expectedHas s r } : State).has r.target r.role) = false := h2.2
        unfold expectedHas at hHasFalse2
        simp [hOp] at hHasFalse2
      | revoke =>
        have h2 := hV2.2.2.2.2 hOp
        have hHasTrue2 : (({ users := s.users, has := expectedHas s r } : State).has r.target r.role) = true := h2.1
        unfold expectedHas at hHasTrue2
        simp [hOp] at hHasTrue2
    have hStep2 : step (step s r).2 r = (.rejected, (step s r).2) := by
      unfold step
      exact dif_neg hNotValid
    exact hStep2
  · have heq : step s r = (.rejected, s) := by unfold step; simp [hV]
    have h1 : (step s r).1 = .rejected := by simp [heq]
    rw [h1] at hOk
    contradiction

theorem req_last_admin : KeepsAdmin step := by
  intro s r hExists
  have hDec : Decidable (ValidCommand s r) := instDecidableValidCommand s r
  by_cases hV : ValidCommand s r
  · have hStep : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step; simp [hV]
    have hS2_users : (step s r).2.users = s.users := by rw [hStep]
    have hS2_has : ∀ u q, (step s r).2.has u q = expectedHas s r u q := by
      intro u q; rw [hStep]
    cases hOp : r.op with
    | grant =>
      rcases hExists with ⟨u, huMem, huAdmin⟩
      by_cases hUT : u = r.target ∧ (Role.admin = r.role)
      · have hExp : expectedHas s r u .admin = true := by
          unfold expectedHas
          simp [hUT.1, hUT.2, hOp]
        have hNew : (step s r).2.has u .admin = true := by rw [hS2_has u .admin, hExp]
        exact ⟨u, by rw [hS2_users]; exact huMem, hNew⟩
      · have hNe : ¬(u = r.target ∧ (Role.admin = r.role)) := hUT
        have hExp : expectedHas s r u .admin = s.has u .admin := by
          unfold expectedHas
          split
          · next h =>
            have hEq : u = r.target ∧ .admin = r.role := by
              rcases h with ⟨h1, h2⟩
              exact ⟨h1, h2.symm ▸ rfl⟩
            exact absurd hEq hNe
          · rfl
        have hNew : (step s r).2.has u .admin = true := by
          rw [hS2_has u .admin, hExp, huAdmin]
        exact ⟨u, by rw [hS2_users]; exact huMem, hNew⟩
    | revoke =>
      by_cases hRoleAdmin : r.role = .admin
      · have hOther := (hV.2.2.2.2 hOp).2 hRoleAdmin
        rcases hOther with ⟨v, hvMem, hvNe, hvAdmin⟩
        have hExp : expectedHas s r v .admin = s.has v .admin := by
          unfold expectedHas
          split
          · next h =>
            rcases h with ⟨h1, _⟩
            exact absurd h1 hvNe
          · rfl
        have hNew : (step s r).2.has v .admin = true := by
          rw [hS2_has v .admin, hExp, hvAdmin]
        exact ⟨v, by rw [hS2_users]; exact hvMem, hNew⟩
      · rcases hExists with ⟨u, huMem, huAdmin⟩
        have hNe : ¬(u = r.target ∧ (Role.admin = r.role)) := by
          intro hConj
          have hEq : r.role = .admin := hConj.2.symm
          exact hRoleAdmin hEq
        have hExp : expectedHas s r u .admin = s.has u .admin := by
          unfold expectedHas
          split
          · next h =>
            rcases h with ⟨h1, h2⟩
            have hConj : u = r.target ∧ (Role.admin = r.role) := by
              constructor
              · exact h1
              · rw [h2]
            exact absurd hConj hNe
          · rfl
        have hNew : (step s r).2.has u .admin = true := by
          rw [hS2_has u .admin, hExp, huAdmin]
        exact ⟨u, by rw [hS2_users]; exact huMem, hNew⟩
  · have heq : step s r = (.rejected, s) := by unfold step; simp [hV]
    have hUsers : (step s r).2 = s := by simp [heq]
    rcases hExists with ⟨u, huMem, huAdmin⟩
    have huMem2 : u ∈ (step s r).2.users := by rw [hUsers]; exact huMem
    have huAdmin2 : (step s r).2.has u .admin = true := by rw [hUsers]; exact huAdmin
    exact ⟨u, huMem2, huAdmin2⟩

end Grants
