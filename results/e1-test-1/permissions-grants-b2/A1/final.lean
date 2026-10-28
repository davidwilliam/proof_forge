import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance
def step : Impl := fun s r =>
  if _h : ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

theorem req_valid_succeeds  : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization   : AdminOnly step := by
  intro s r hok
  by_cases hv : ValidCommand s r
  · exact ⟨hv.1, hv.2.2.1⟩
  · exfalso
    have hre : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [hre] at hok
    cases hok

theorem req_no_self_grant   : NoSelfGrant step := by
  intro s r hok hop
  by_cases hv : ValidCommand s r
  · exact (hv.2.2.2.1 hop).1
  · exfalso
    have hre : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [hre] at hok
    cases hok

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hne
  by_cases hv : ValidCommand s r
  · have h2 : (step s r).2 = { users := s.users, has := expectedHas s r } := by
      unfold step
      simp [hv]
    rw [h2]
    simp only
    unfold expectedHas
    have hcond : ¬ (u = r.target ∧ q = r.role) := by
      cases hne with
      | inl h => exact fun ⟨hu, _⟩ => h hu
      | inr h => exact fun ⟨_, hq⟩ => h hq
    simp [hcond]
  · exfalso
    have hre : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [hre] at hok
    cases hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : ValidCommand s r
  · have hst : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step
      simp [hv]
    rw [hst]
    constructor
    · rfl
    · intro u q
      rfl
  · exfalso
    have hre : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [hre] at hok
    cases hok

theorem req_idempotency     : Idempotent step := by
  intro s r hok
  by_cases hv : ValidCommand s r
  · have hst : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step
      simp [hv]
    have h2eq : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by rw [hst]
    have hnvalid : ¬ ValidCommand (step s r).2 r := by
      rw [h2eq]
      intro hc
      cases hop : r.op with
      | grant =>
        have hcond2 := hc.2.2.2.1 hop
        have hfalse : (({ users := s.users, has := expectedHas s r } : State).has r.target r.role) = false := hcond2.2
        unfold expectedHas at hfalse
        simp [hop] at hfalse
      | revoke =>
        have hcond2 := hc.2.2.2.2 hop
        have htrue : (({ users := s.users, has := expectedHas s r } : State).has r.target r.role) = true := hcond2.1
        unfold expectedHas at htrue
        simp [hop] at htrue
    exact req_invalid_noop _ _ hnvalid
  · exfalso
    have hre : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [hre] at hok
    cases hok

theorem req_last_admin      : KeepsAdmin step := by
  intro s r hex
  by_cases hv : ValidCommand s r
  · obtain ⟨u0, hu0mem, hu0adm⟩ := hex
    have hactor_mem : r.actor ∈ s.users := hv.1
    have hactor_adm : s.has r.actor .admin = true := hv.2.2.1
    have hst2 : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by
      unfold step
      simp [hv]
    rw [hst2]
    simp only
    cases hop : r.op with
    | grant =>
      refine ⟨r.actor, hactor_mem, ?_⟩
      show expectedHas s r r.actor .admin = true
      unfold expectedHas
      have hne : ¬ (r.actor = r.target ∧ (.admin : Role) = r.role) := by
        have hdiff : r.actor ≠ r.target := (hv.2.2.2.1 hop).1
        intro ⟨heq, _⟩
        exact hdiff heq
      simp [hne, hactor_adm]
    | revoke =>
      by_cases hrole : r.role = .admin
      · -- need other admin
        have hcond := hv.2.2.2.2 hop
        have htrue : s.has r.target r.role = true := hcond.1
        have hother : OtherAdmin s r.target := hcond.2 hrole
        obtain ⟨v, hvmem, hne, hvadmin⟩ := hother
        refine ⟨v, hvmem, ?_⟩
        show expectedHas s r v .admin = true
        unfold expectedHas
        have hnc : ¬ (v = r.target ∧ (.admin : Role) = r.role) := by
          intro ⟨heq, _⟩
          exact hne heq
        simp [hnc, hvadmin]
      · refine ⟨r.actor, hactor_mem, ?_⟩
        show expectedHas s r r.actor .admin = true
        unfold expectedHas
        have hnc : ¬ (r.actor = r.target ∧ (.admin : Role) = r.role) := by
          intro ⟨_, hq⟩
          exact hrole hq.symm
        simp [hnc, hactor_adm]
  · have hst : step s r = (.rejected, s) := req_invalid_noop s r hv
    have h2eq : (step s r).2 = s := by rw [hst]
    rw [h2eq]
    exact hex

end Grants
