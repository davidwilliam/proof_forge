import Grants.Spec
namespace Grants

def otherAdmin (s : State) (u : UserId) : Bool :=
  s.users.any (fun v => v != u && s.has v .admin)

def isValid (s : State) (r : Request) : Bool :=
  s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin &&
    match r.op with
    | .grant => (r.actor != r.target) && !s.has r.target r.role
    | .revoke => s.has r.target r.role && (r.role != .admin || otherAdmin s r.target)

def step : Impl := fun s r =>
  if isValid s r then
    (.ok, { users := s.users, has := expectedHas s r })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hv
  have hval : isValid s r = true := by
    unfold isValid otherAdmin
    obtain ⟨ha_mem, ht_mem, ha_admin, hgrant, hrevoke⟩ := hv
    have h1 : (s.users.contains r.actor) = true := by simp [List.contains_eq_mem, ha_mem]
    have h2 : (s.users.contains r.target) = true := by simp [List.contains_eq_mem, ht_mem]
    have h3 : (s.has r.actor .admin) = true := ha_admin
    simp only [h1, h2, h3, Bool.true_and]
    cases hop : r.op with
    | grant =>
      have hg := hgrant hop
      obtain ⟨hne, hfalse⟩ := hg
      have hne_b : (r.actor != r.target) = true := by simp [hne]
      have hf : ((!s.has r.target r.role)) = true := by simp [hfalse]
      simp only [hne_b, hf, Bool.true_and]
    | revoke =>
      have hr := hrevoke hop
      obtain ⟨htrue, hadmin_imp⟩ := hr
      have ht : (s.has r.target r.role) = true := htrue
      simp only [ht, Bool.true_and]
      cases hrole : r.role with
      | admin =>
        have hother := hadmin_imp hrole
        obtain ⟨v, hv_mem, hv_ne, hv_admin⟩ := hother
        have key : s.users.any (fun v => v != r.target && s.has v .admin) = true := by
          rw [List.any_eq_true]
          refine ⟨v, hv_mem, ?_⟩
          simp [hv_ne, hv_admin]
        simp [hrole, key]
      | editor =>
        rfl
      | viewer =>
        rfl
  unfold step
  simp [hval]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hnot
  unfold step
  have hval_false : isValid s r = false := by
    by_cases h : isValid s r = true
    · exfalso
      apply hnot
      -- build ValidCommand from h
      unfold isValid at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨hca, hct⟩, hadm⟩, hrest⟩ := h
      refine ⟨of_decide_eq_true hca, of_decide_eq_true hct, hadm, ?_, ?_⟩
      · intro hop
        cases hc : r.op
        · simp only [hop] at hrest
          simp only [Bool.and_eq_true] at hrest
          obtain ⟨hne2, hnothas⟩ := hrest
          exact ⟨of_decide_eq_true hne2, by simp at hnothas; exact hnothas⟩
        · exfalso; rw [hc] at hop; contradiction
      · intro hop
        cases hc : r.op
        · exfalso; rw [hc] at hop; contradiction
        · simp only [hc] at hrest
          simp only [Bool.and_eq_true] at hrest
          obtain ⟨hhas, hcond⟩ := hrest
          refine ⟨hhas, ?_⟩
          intro hrole
          have hcond' : (r.role != .admin || otherAdmin s r.target) = true := hcond
          rw [hrole] at hcond'
          simp at hcond'
          unfold otherAdmin at hcond'
          rw [List.any_eq_true] at hcond'
          obtain ⟨v, hv_mem, hv_b⟩ := hcond'
          have hv_and : (v != r.target && s.has v .admin) = true := hv_b
          rw [Bool.and_eq_true] at hv_and
          obtain ⟨hv_ne_b, hv_adm⟩ := hv_and
          have hv_ne : v ≠ r.target := by
            intro heq; simp [heq] at hv_ne_b
          exact ⟨v, hv_mem, hv_ne, hv_adm⟩
    · cases heq : isValid s r
      · rfl
      · simp_all
  simp [hval_false]

theorem req_authorization : AdminOnly step := by
  intro s r hok
  unfold step at hok
  by_cases hv : isValid s r = true
  · simp [hv] at hok
    unfold isValid at hv
    simp only [Bool.and_eq_true] at hv
    obtain ⟨⟨⟨hca, hct⟩, hadm⟩, _⟩ := hv
    constructor
    · exact of_decide_eq_true hca
    · exact hadm
  · simp [hv] at hok

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hop
  unfold step at hok
  by_cases hv : isValid s r = true
  · simp [hv] at hok
    unfold isValid at hv
    simp only [Bool.and_eq_true] at hv
    obtain ⟨⟨⟨hca, hct⟩, hadm⟩, hrest⟩ := hv
    rw [hop] at hrest
    simp only [Bool.and_eq_true] at hrest
    obtain ⟨hne, _⟩ := hrest
    exact of_decide_eq_true hne
  · simp [hv] at hok

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hneq
  unfold step at hok ⊢
  by_cases hv : isValid s r = true
  · simp [hv] at hok ⊢
    unfold expectedHas
    by_cases heq : (u = r.target ∧ q = r.role)
    · obtain ⟨hu, hq⟩ := heq
      subst hu; subst hq
      simp at hneq
    · simp [heq]
  · simp [hv] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : isValid s r = true
  · have h1 : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by unfold step; simp [hv]
    have husers : (step s r).2.users = s.users := by rw [h1]
    have hhas : ∀ u q, (step s r).2.has u q = expectedHas s r u q := by intro u q; rw [h1]
    exact ⟨husers, hhas⟩
  · exfalso; unfold step at hok; simp [hv] at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv : isValid s r = true := by
    by_cases h : isValid s r = true
    · exact h
    · have hfalse : isValid s r = false := by
        cases heq : isValid s r
        · rfl
        · simp_all
      unfold step at hok; simp [hfalse] at hok
  have hstep_eq : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by
    unfold step; simp [hv]
  have h_after_invalid : isValid { users := s.users, has := expectedHas s r } r = false := by
    have h1 : s.users.contains r.actor = true := by
      unfold isValid at hv; simp only [Bool.and_eq_true] at hv; obtain ⟨⟨⟨ha, _⟩, _⟩, _⟩ := hv; exact ha
    have h2 : s.users.contains r.target = true := by
      unfold isValid at hv; simp only [Bool.and_eq_true] at hv; obtain ⟨⟨⟨_, ht⟩, _⟩, _⟩ := hv; exact ht
    cases hop : r.op with
    | grant =>
      have hexp_true : (expectedHas s r) r.target r.role = true := by unfold expectedHas; simp [hop]
      unfold isValid
      simp only [h1, h2, hop, hexp_true]
      simp only [Bool.not_true, Bool.false_and, Bool.and_false]
    | revoke =>
      have hexp_false : (expectedHas s r) r.target r.role = false := by unfold expectedHas; simp [hop]
      unfold isValid
      simp only [h1, h2, hop, hexp_false, Bool.false_and, Bool.and_false]
  have hstep2 : step (step s r).2 r = (.rejected, (step s r).2) := by
    rw [hstep_eq]
    unfold step
    simp [h_after_invalid]
  exact hstep2

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  obtain ⟨w, hw_mem, hw_admin⟩ := hex
  by_cases hv : isValid s r = true
  · have h_step_eq : step s r = (.ok, { users := s.users, has := expectedHas s r }) := by unfold step; simp [hv]
    have h_users_eq : (step s r).2.users = s.users := by rw [h_step_eq]
    have h_has_eq : ∀ u q, (step s r).2.has u q = expectedHas s r u q := by intro u q; rw [h_step_eq]
    -- Helper to show target ∈ s.users
    have ht_mem : r.target ∈ s.users := by
      unfold isValid at hv
      simp only [Bool.and_eq_true] at hv
      obtain ⟨⟨⟨_, ht⟩, _⟩, _⟩ := hv
      exact of_decide_eq_true ht
    by_cases hop : r.op = .grant
    · -- grant preserves admins
      -- decide if w is the affected pair
      by_cases heq : w = r.target ∧ Role.admin = r.role
      · obtain ⟨hwt, hra⟩ := heq
        -- w is target with admin role, grant makes it true
        have hwa : (step s r).2.has w .admin = true := by
          rw [h_has_eq]; simp [expectedHas, hwt, ←hra, hop]
        exact ⟨w, by rw [h_users_eq]; exact hw_mem, hwa⟩
      · have hwa : (step s r).2.has w .admin = true := by
          rw [h_has_eq, expectedHas, if_neg heq, hw_admin]
        exact ⟨w, by rw [h_users_eq]; exact hw_mem, hwa⟩
    · have hop_rev : r.op = .revoke := by cases h : r.op with | grant => contradiction | revoke => rfl
      by_cases hrole : r.role = .admin
      · -- revoking admin: need other admin
        have h_other : otherAdmin s r.target = true := by
          unfold isValid at hv
          simp only [Bool.and_eq_true] at hv
          obtain ⟨⟨⟨_, _⟩, _⟩, hrest⟩ := hv
          rw [hop_rev] at hrest
          simp only [Bool.and_eq_true] at hrest
          obtain ⟨_, hcond⟩ := hrest
          rw [hrole] at hcond
          simp at hcond
          exact hcond
        unfold otherAdmin at h_other
        rw [List.any_eq_true] at h_other
        obtain ⟨v, hv_mem, hv_b⟩ := h_other
        rw [Bool.and_eq_true] at hv_b
        obtain ⟨hv_ne_b, hv_adm⟩ := hv_b
        have hv_ne : v ≠ r.target := by intro heq; simp [heq] at hv_ne_b
        have hv_has_after : (step s r).2.has v .admin = true := by
          rw [h_has_eq]
          unfold expectedHas
          have heq : ¬ (v = r.target ∧ Role.admin = r.role) := by
            intro h; obtain ⟨hv_eq, _⟩ := h
            exact hv_ne hv_eq
          simp [heq, hv_adm]
        exact ⟨v, by rw [h_users_eq]; exact hv_mem, hv_has_after⟩
      · -- revoking non-admin leaves w admin
        have hw_after : (step s r).2.has w .admin = true := by
          rw [h_has_eq]; unfold expectedHas
          have heq : ¬ (w = r.target ∧ Role.admin = r.role) := by
            intro h; obtain ⟨_, hq⟩ := h
            exact hrole hq.symm
          simp [heq, hw_admin]
        exact ⟨w, by rw [h_users_eq]; exact hw_mem, hw_after⟩
  · have hfalse : isValid s r = false := by cases heq : isValid s r <;> simp_all
    have hstep : step s r = (.rejected, s) := by unfold step; simp [hfalse]
    have h2 : (step s r).2 = s := by rw [hstep]
    rw [h2]
    exact ⟨w, hw_mem, hw_admin⟩

end Grants
