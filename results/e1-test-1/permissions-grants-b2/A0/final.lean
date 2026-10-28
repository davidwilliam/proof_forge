import Grants.Spec
namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance

def step : Impl := fun s r =>
  if ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have heq : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
    unfold step; simp [h]
  simp [heq]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have heq : step s r = (.rejected, s) := by
    unfold step; simp [h]
  exact heq

theorem req_authorization : AdminOnly step := by
  intro s r hok
  by_cases h : ValidCommand s r
  · obtain ⟨hA, _, hAd, _, _⟩ := h
    exact ⟨hA, hAd⟩
  · have heq : step s r = (.rejected, s) := by
      unfold step; simp [h]
    have h1 : (step s r).1 = Outcome.rejected := by rw [heq]
    have hc : Outcome.rejected = Outcome.ok := Eq.trans h1.symm hok
    have hne : Outcome.rejected ≠ Outcome.ok := by decide
    exact absurd hc hne

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hop
  by_cases h : ValidCommand s r
  · obtain ⟨_, _, _, hG, _⟩ := h
    exact (hG hop).1
  · have heq : step s r = (.rejected, s) := by
      unfold step; simp [h]
    have h1 : (step s r).1 = Outcome.rejected := by rw [heq]
    have hc : Outcome.rejected = Outcome.ok := Eq.trans h1.symm hok
    have hne : Outcome.rejected ≠ Outcome.ok := by decide
    exact absurd hc hne

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hor
  by_cases h : ValidCommand s r
  · have heq : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step; simp [h]
    have hhas : (step s r).2.has u q = expectedHas s r u q := by rw [heq]
    have hne : ¬ (u = r.target ∧ q = r.role) := by
      intro hc
      obtain ⟨hu, hq⟩ := hc
      cases hor with
      | inl hnu => exact hnu hu
      | inr hnq => exact hnq hq
    have hexp : expectedHas s r u q = s.has u q := by unfold expectedHas; simp [hne]
    rw [hhas, hexp]
  · have heq : step s r = (.rejected, s) := by
      unfold step; simp [h]
    have h1 : (step s r).1 = Outcome.rejected := by rw [heq]
    have hc : Outcome.rejected = Outcome.ok := Eq.trans h1.symm hok
    have hne : Outcome.rejected ≠ Outcome.ok := by decide
    exact absurd hc hne

theorem req_effects : Effects step := by
  intro s r hok
  by_cases h : ValidCommand s r
  · have heq : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step; simp [h]
    constructor
    · simp [heq]
    · intro u q
      have hhas : (step s r).2.has u q = expectedHas s r u q := by rw [heq]
      rw [hhas]
  · have heq : step s r = (.rejected, s) := by
      unfold step; simp [h]
    have h1 : (step s r).1 = Outcome.rejected := by rw [heq]
    have hc : Outcome.rejected = Outcome.ok := Eq.trans h1.symm hok
    have hne : Outcome.rejected ≠ Outcome.ok := by decide
    exact absurd hc hne

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hV : ValidCommand s r := by
    by_cases h : ValidCommand s r
    · exact h
    · have heq : step s r = (.rejected, s) := by
        unfold step; simp [h]
      have h1 : (step s r).1 = Outcome.rejected := by rw [heq]
      have hc : Outcome.rejected = Outcome.ok := Eq.trans h1.symm hok
      have hne : Outcome.rejected ≠ Outcome.ok := by decide
      exact absurd hc hne
  have heq1 : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
    unfold step; simp [hV]
  have hExp : expectedHas s r r.target r.role = decide (r.op = Op.grant) := by unfold expectedHas; simp
  have hS : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by rw [heq1]
  have hOpCases : ∀ (o : Op), o = Op.grant ∨ o = Op.revoke := by
    intro o; cases o; exact Or.inl rfl; exact Or.inr rfl
  have hNot2 : ¬ ValidCommand ({ users := s.users, has := expectedHas s r } : State) r := by
    intro hV2
    obtain ⟨_, _, _, hG2, hR2⟩ := hV2
    by_cases hOp : r.op = Op.grant
    · have hF : ({ users := s.users, has := expectedHas s r } : State).has r.target r.role = false :=
        (hG2 hOp).2
      have hEq : ({ users := s.users, has := expectedHas s r } : State).has r.target r.role = decide (r.op = Op.grant) := hExp
      have hDec : decide (r.op = Op.grant) = true := by simp [hOp]
      rw [hDec] at hEq
      have hc : (true : Bool) = false := Eq.trans hEq.symm hF
      have hne : (true : Bool) ≠ false := by decide
      exact absurd hc hne
    · have hRev : r.op = Op.revoke := by
        have hc := hOpCases r.op
        cases hc with
        | inl h => exact absurd h hOp
        | inr h => exact h
      have hT : ({ users := s.users, has := expectedHas s r } : State).has r.target r.role = true :=
        (hR2 hRev).1
      have hEq : ({ users := s.users, has := expectedHas s r } : State).has r.target r.role = decide (r.op = Op.grant) := hExp
      have hDec : decide (r.op = Op.grant) = false := by simp [hOp]
      rw [hDec] at hEq
      have hc : (true : Bool) = false := Eq.trans hT.symm hEq
      have hne : (true : Bool) ≠ false := by decide
      exact absurd hc hne
  have hStep2 : step ({ users := s.users, has := expectedHas s r } : State) r =
      (.rejected, ({ users := s.users, has := expectedHas s r } : State)) := by
    unfold step; simp [hNot2]
  rw [hS]
  exact hStep2

theorem req_last_admin : KeepsAdmin step := by
  intro s r hEx
  by_cases hV : ValidCommand s r
  · have heq : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step; simp [hV]
    have hS : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by rw [heq]
    rw [hS]
    obtain ⟨hMemA, hMemT, hAdm, hG, hR⟩ := hV
    have hOpCases : ∀ (o : Op), o = Op.grant ∨ o = Op.revoke := by
      intro o; cases o; exact Or.inl rfl; exact Or.inr rfl
    by_cases hOp : r.op = Op.grant
    · by_cases hRole : r.role = Role.admin
      · refine ⟨r.target, hMemT, ?_⟩
        have h1 : expectedHas s r r.target Role.admin = true := by
          unfold expectedHas
          have hcond : (r.target = r.target ∧ Role.admin = r.role) := ⟨rfl, Eq.symm hRole⟩
          simp [hcond, hOp]
        exact h1
      · refine ⟨r.actor, hMemA, ?_⟩
        have hne : ¬ (r.actor = r.target ∧ Role.admin = r.role) := by
          intro hc
          exact hRole hc.2.symm
        have h1 : expectedHas s r r.actor Role.admin = s.has r.actor Role.admin := by
          unfold expectedHas; simp [hne]
        show expectedHas s r r.actor Role.admin = true
        rw [h1]; exact hAdm
    · have hRev : r.op = Op.revoke := by
        have hc := hOpCases r.op
        cases hc with
        | inl h => exact absurd h hOp
        | inr h => exact h
      by_cases hRole : r.role = Role.admin
      · have hOther : OtherAdmin s r.target := (hR hRev).2 hRole
        obtain ⟨v, hvMem, hvNe, hvAdm⟩ := hOther
        refine ⟨v, hvMem, ?_⟩
        have hne : ¬ (v = r.target ∧ Role.admin = r.role) := fun hc => hvNe hc.1
        have h1 : expectedHas s r v Role.admin = s.has v Role.admin := by
          unfold expectedHas; simp [hne]
        show expectedHas s r v Role.admin = true
        rw [h1]; exact hvAdm
      · refine ⟨r.actor, hMemA, ?_⟩
        have hne : ¬ (r.actor = r.target ∧ Role.admin = r.role) := by
          intro hc
          exact hRole hc.2.symm
        have h1 : expectedHas s r r.actor Role.admin = s.has r.actor Role.admin := by
          unfold expectedHas; simp [hne]
        show expectedHas s r r.actor Role.admin = true
        rw [h1]; exact hAdm
  · have heq : step s r = (.rejected, s) := by
      unfold step; simp [hV]
    have hS : (step s r).2 = s := by rw [heq]
    rw [hS]
    exact hEx

end Grants
