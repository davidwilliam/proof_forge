import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance
def step : Impl := fun s r =>
  if ValidCommand s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

theorem req_last_admin_aux : KeepsAdmin step := by
  intro s r hex
  obtain ⟨u0, hu0mem, hu0admin⟩ := hex
  by_cases hvc : ValidCommand s r
  · have hs : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step
      simp [hvc]
    obtain ⟨hactor_mem, htarget_mem, hactor_admin, hgrant, hrevoke⟩ := hvc
    cases hop : r.op with
    | grant =>
      have hne : r.actor ≠ r.target := (hgrant hop).1
      refine ⟨r.actor, ?_, ?_⟩
      · have hU : (step s r).2.users = s.users := by rw [hs]
        rw [hU]; exact hactor_mem
      · have hH : (step s r).2.has r.actor .admin = expectedHas s r r.actor .admin := by rw [hs]
        rw [hH]
        unfold expectedHas
        have hneg : ¬ (r.actor = r.target ∧ Role.admin = r.role) :=
          fun h2 => hne h2.1
        simp [hneg, hactor_admin]
    | revoke =>
      by_cases hrole : r.role = .admin
      · have hrev := hrevoke hop
        have hother : OtherAdmin s r.target := hrev.2 hrole
        unfold OtherAdmin at hother
        obtain ⟨v, hvmem, hvne, hvadmin⟩ := hother
        refine ⟨v, ?_, ?_⟩
        · have hU : (step s r).2.users = s.users := by rw [hs]
          rw [hU]; exact hvmem
        · have hH : (step s r).2.has v .admin = expectedHas s r v .admin := by rw [hs]
          rw [hH]
          unfold expectedHas
          have hneg : ¬ (v = r.target ∧ Role.admin = r.role) :=
            fun h2 => hvne h2.1
          simp [hneg, hvadmin]
      · refine ⟨u0, ?_, ?_⟩
        · have hU : (step s r).2.users = s.users := by rw [hs]
          rw [hU]; exact hu0mem
        · have hH : (step s r).2.has u0 .admin = expectedHas s r u0 .admin := by rw [hs]
          rw [hH]
          unfold expectedHas
          have hneg : ¬ (u0 = r.target ∧ Role.admin = r.role) := by
            intro h2
            exact hrole h2.2.symm
          simp [hneg, hu0admin]
  · have hs : step s r = (.rejected, s) := by
      unfold step
      simp [hvc]
    refine ⟨u0, ?_, ?_⟩
    · have hU : (step s r).2 = s := by rw [hs]
      rw [hU]; exact hu0mem
    · have hU : (step s r).2 = s := by rw [hs]
      rw [hU]; exact hu0admin

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization   : AdminOnly step := by
  intro s r hok
  by_cases hvc : ValidCommand s r
  · exact ⟨hvc.1, hvc.2.2.1⟩
  · unfold step at hok
    simp [hvc] at hok

theorem req_no_self_grant   : NoSelfGrant step := by
  intro s r hok hop
  by_cases hvc : ValidCommand s r
  · exact (hvc.2.2.2.1 hop).1
  · unfold step at hok
    simp [hvc] at hok

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hne
  by_cases hvc : ValidCommand s r
  · unfold step at hok ⊢
    simp [hvc] at hok ⊢
    unfold expectedHas
    have hneg : ¬ (u = r.target ∧ q = r.role) := by
      cases hne with
      | inl h => exact fun h2 => h h2.1
      | inr h => exact fun h2 => h h2.2
    simp [hneg]
  · unfold step at hok
    simp [hvc] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hvc : ValidCommand s r
  · have hs : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step
      simp [hvc]
    rw [hs]
    exact ⟨rfl, fun u q => rfl⟩
  · have hs : step s r = (.rejected, s) := by
      unfold step
      simp [hvc]
    rw [hs] at hok
    simp at hok

theorem req_idempotency     : Idempotent step := by
  intro s r hok
  by_cases hvc : ValidCommand s r
  · have hs : step s r = (.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
      unfold step
      simp [hvc]
    rw [hs]
    suffices hnov : ¬ ValidCommand ({ users := s.users, has := expectedHas s r } : State) r by
      have hstep : step ({ users := s.users, has := expectedHas s r } : State) r =
        (.rejected, ({ users := s.users, has := expectedHas s r } : State)) := by
        unfold step
        simp [hnov]
      exact hstep
    intro hvc2
    obtain ⟨hactor_mem, htarget_mem, hactor_admin, hgrant, hrevoke⟩ := hvc
    obtain ⟨hactor_mem2, htarget_mem2, hactor_admin2, hgrant2, hrevoke2⟩ := hvc2
    cases hop : r.op with
    | grant =>
      have hg2 := hgrant2 hop
      have hhas : (expectedHas s r r.target r.role) = true := by
        unfold expectedHas
        simp [hop]
      have hfalse : ({ users := s.users, has := expectedHas s r } : State).has r.target r.role = false := hg2.2
      simp at hfalse
      rw [hhas] at hfalse
      simp at hfalse
    | revoke =>
      have hr2 := hrevoke2 hop
      have hhas : (expectedHas s r r.target r.role) = false := by
        unfold expectedHas
        simp [hop]
      have htrue : ({ users := s.users, has := expectedHas s r } : State).has r.target r.role = true := hr2.1
      simp at htrue
      rw [hhas] at htrue
      simp at htrue
  · unfold step at hok
    simp [hvc] at hok

theorem req_last_admin : KeepsAdmin step := req_last_admin_aux

end Grants
