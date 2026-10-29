import Grants.Spec

namespace Grants

def otherAdminBool (s : State) (target : UserId) : Bool :=
  s.users.any (fun v => decide (v ≠ target) && s.has v .admin)

def validBool (s : State) (r : Request) : Bool :=
  decide (r.actor ∈ s.users) && decide (r.target ∈ s.users) &&
    s.has r.actor .admin &&
    (match r.op with
     | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
     | .revoke => s.has r.target r.role &&
         (decide (r.role ≠ .admin) || otherAdminBool s r.target))

def step : Impl := fun s r =>
  if validBool s r then
    (Outcome.ok, { users := s.users, has := fun u q => expectedHas s r u q })
  else
    (Outcome.rejected, s)

def foo := 1

theorem my_test_lemma : True := trivial

theorem my_probe2 : True := trivial

theorem my_probe3 : List.any [1,2] (fun x => decide (x = 1)) = true := rfl

theorem my_test_lemma2 : True := trivial

theorem otherAdmin_aux1 (s : State) (t : UserId) : OtherAdmin s t ↔ ∃ v ∈ s.users, v ≠ t ∧ s.has v .admin = true := by rfl

theorem probe_bool1 : ∀ (a b : Bool), ((a && b) = true ↔ a = true ∧ b = true) := by intro a b; cases a <;> cases b <;> simp

theorem probe_bool2 (a b : Bool) (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all

theorem probe_dec1 (p : Prop) [d : Decidable p] (h : decide p = true) : p := of_decide_eq_true h

theorem probe_dec2 (a b : Bool) : ((a && b) = true → a = true) := fun h => by cases a <;> cases b <;> simp_all

theorem probe_dec3 (l : List Nat) (x : Nat) : decide (x ∈ l) = true → x ∈ l := fun h => of_decide_eq_true h

theorem aux_and_left (a b : Bool) (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all

theorem aux_and_right (a b : Bool) (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp_all

theorem aux_valid_actor_mem (s : State) (r : Request) (hv : validBool s r = true) : r.actor ∈ s.users := by
  unfold validBool at hv
  have h1 := aux_and_left _ _ hv
  have h2 := aux_and_left _ _ h1
  have h3 := aux_and_left _ _ h2
  exact of_decide_eq_true h3

theorem aux_valid_actor_admin (s : State) (r : Request) (hv : validBool s r = true) : s.has r.actor Role.admin = true := by
  unfold validBool at hv
  have h1 := aux_and_left _ _ hv
  have h2 := aux_and_right _ _ h1
  exact h2

theorem aux_ok_valid (s : State) (r : Request) (h : (step s r).1 = Outcome.ok) : validBool s r = true := by
  cases hvb : validBool s r with
  | true => rfl
  | false =>
    have hstep : (step s r).1 = Outcome.rejected := by
      unfold step
      simp [hvb]
    rw [hstep] at h
    contradiction

theorem aux_grant_ne (s : State) (r : Request) (hv : validBool s r = true) (hop : r.op = Op.grant) : r.actor ≠ r.target := by
  unfold validBool at hv
  have hD := aux_and_right _ _ hv
  have hD2 : (decide (r.actor ≠ r.target) && !(s.has r.target r.role)) = true := by
    simpa [hop] using hD
  have hleft := aux_and_left _ _ hD2
  exact of_decide_eq_true hleft

theorem aux_target_mem2 (s : State) (r : Request) (hv : validBool s r = true) : r.target ∈ s.users := by
  unfold validBool at hv
  have h1 := aux_and_left _ _ hv
  have h2 := aux_and_left _ _ h1
  have h4 := aux_and_right _ _ h2
  exact of_decide_eq_true h4

theorem aux_valid_has_target_grant2 (s : State) (r : Request) (hv : validBool s r = true) (hop : r.op = Op.grant) : s.has r.target r.role = false := by
  unfold validBool at hv
  have hD := aux_and_right _ _ hv
  have hD2 : (decide (r.actor ≠ r.target) && !(s.has r.target r.role)) = true := by simpa [hop] using hD
  have hr := aux_and_right _ _ hD2
  cases hs : s.has r.target r.role with
  | true => simp [hs] at hr
  | false => rfl

theorem aux_valid_has_target_revoke2 (s : State) (r : Request) (hv : validBool s r = true) (hop : r.op = Op.revoke) : s.has r.target r.role = true := by
  unfold validBool at hv
  have hD := aux_and_right _ _ hv
  have hD2 : (s.has r.target r.role && (decide (r.role ≠ Role.admin) || otherAdminBool s r.target)) = true := by simpa [hop] using hD
  exact aux_and_left _ _ hD2

theorem lem_exp_target2 (s : State) (r : Request) : expectedHas s r r.target r.role = decide (r.op = Op.grant) := by
  unfold expectedHas
  simp

theorem aux_step_rej (s' : State) (r : Request) (h : validBool s' r = false) : step s' r = (Outcome.rejected, s') := by
  unfold step
  simp [h]

theorem aux_otherAdmin_of_bool (s : State) (t : UserId) (h : otherAdminBool s t = true) :
    ∃ v ∈ s.users, v ≠ t ∧ s.has v .admin = true := by
  unfold otherAdminBool at h
  rw [List.any_eq_true] at h
  obtain ⟨v, hmem, hp⟩ := h
  have h1 : decide (v ≠ t) = true := aux_and_left _ _ hp
  have h2 : s.has v .admin = true := aux_and_right _ _ hp
  exact ⟨v, hmem, of_decide_eq_true h1, h2⟩

#check aux_otherAdmin_of_bool

theorem aux_revoke_otherAdmin (s : State) (r : Request) (hv : validBool s r = true)
    (hop : r.op = Op.revoke) (hrole : r.role = Role.admin) :
    otherAdminBool s r.target = true := by
  unfold validBool at hv
  have hD := aux_and_right _ _ hv
  have hD2 : (s.has r.target r.role && (decide (r.role ≠ Role.admin) || otherAdminBool s r.target)) = true := by
    simpa [hop] using hD
  have hright := aux_and_right _ _ hD2
  have hdec : decide (r.role ≠ Role.admin) = false := by
    simp [hrole]
  simp [hdec] at hright
  exact hright

theorem aux_expected_other (s : State) (r : Request) (u : UserId) (q : Role)
    (h : u ≠ r.target) : expectedHas s r u q = s.has u q := by
  unfold expectedHas
  simp [h]

theorem aux_expected_other2 (s : State) (r : Request) (u : UserId) (q : Role)
    (h : q ≠ r.role) : expectedHas s r u q = s.has u q := by
  unfold expectedHas
  simp [h]

theorem aux_otherAdmin_of_exists (s : State) (t : UserId)
    (h : ∃ v ∈ s.users, v ≠ t ∧ s.has v .admin = true) :
    otherAdminBool s t = true := by
  unfold otherAdminBool
  rw [List.any_eq_true]
  obtain ⟨v, hmem, hne, hadm⟩ := h
  exact ⟨v, hmem, by simp [hne, hadm]⟩

theorem probe_valid_rw (s : State) (r : Request) (hactor_mem : r.actor ∈ s.users) :
    decide (r.actor ∈ s.users) = true := decide_eq_true hactor_mem

theorem probe_cases_op (s : State) (r : Request) : True := by
  cases hop : r.op with
  | grant =>
    have h1 : validBool s r = (decide (r.actor ∈ s.users) && decide (r.target ∈ s.users) && s.has r.actor .admin && (decide (r.actor ≠ r.target) && !(s.has r.target r.role))) := by
      unfold validBool
      simp [hop]
    trivial
  | revoke => trivial

theorem probe_and_true : ((true && true && true && (true && true) : Bool) = true) := by simp

theorem probe_and_true2 (a : Bool) (h : a = true) : ((a && true : Bool) = true) := by simp [h]

theorem aux_valid_of_bool (s : State) (r : Request) (hv : validBool s r = true) : ValidCommand s r := by
  unfold ValidCommand
  refine ⟨aux_valid_actor_mem s r hv, aux_target_mem2 s r hv, aux_valid_actor_admin s r hv, ?_, ?_⟩
  · intro hop
    exact ⟨aux_grant_ne s r hv hop, aux_valid_has_target_grant2 s r hv hop⟩
  · intro hop
    refine ⟨aux_valid_has_target_revoke2 s r hv hop, ?_⟩
    intro hrole
    have hbool := aux_revoke_otherAdmin s r hv hop hrole
    exact aux_otherAdmin_of_bool s r.target hbool

theorem req_valid_succeeds  : ValidSucceeds step := by
  intro s r hval
  unfold ValidCommand at hval
  obtain ⟨hactor_mem, htarget_mem, hactor_admin, hgrant, hrevoke⟩ := hval
  have ha1 : decide (r.actor ∈ s.users) = true := decide_eq_true hactor_mem
  have ht1 : decide (r.target ∈ s.users) = true := decide_eq_true htarget_mem
  have hadm : s.has r.actor Role.admin = true := hactor_admin
  have hvb : validBool s r = true := by
    cases hop : r.op with
    | grant =>
      have hg := hgrant hop
      obtain ⟨hne, hnot⟩ := hg
      have hne1 : decide (r.actor ≠ r.target) = true := decide_eq_true hne
      have hnot1 : (!(s.has r.target r.role)) = true := by simp [hnot]
      have h2 : validBool s r = (decide (r.actor ∈ s.users) && decide (r.target ∈ s.users) && s.has r.actor .admin && (decide (r.actor ≠ r.target) && !(s.has r.target r.role))) := by
        unfold validBool
        simp [hop]
      simp [h2, ha1, ht1, hadm, hne1, hnot1]
    | revoke =>
      have hr := hrevoke hop
      obtain ⟨hhas, hlast⟩ := hr
      have hhas1 : s.has r.target r.role = true := hhas
      have h2 : validBool s r = (decide (r.actor ∈ s.users) && decide (r.target ∈ s.users) && s.has r.actor .admin && (s.has r.target r.role && (decide (r.role ≠ Role.admin) || otherAdminBool s r.target))) := by
        unfold validBool
        simp [hop]
      by_cases hrole : r.role = Role.admin
      · have hOA : OtherAdmin s r.target := hlast hrole
        have hbool := aux_otherAdmin_of_exists s r.target hOA
        have hdec : decide (r.role ≠ Role.admin) = false := by simp [hrole]
        simp [h2, ha1, ht1, hadm, hhas1, hdec, hbool]
      · have hdec : decide (r.role ≠ Role.admin) = true := decide_eq_true hrole
        simp [h2, ha1, ht1, hadm, hhas1, hdec]
  unfold step
  simp [hvb]

theorem req_invalid_noop    : InvalidNoop step := by
  intro s r hInv
  have hvf : validBool s r = false := by
    cases h : validBool s r with
    | true => exfalso; exact hInv (aux_valid_of_bool s r h)
    | false => rfl
  have hstep : step s r = (Outcome.rejected, s) := aux_step_rej s r hvf
  exact hstep

theorem req_authorization   : AdminOnly step := by
  intro s r h
  have hv := aux_ok_valid s r h
  exact ⟨aux_valid_actor_mem s r hv, aux_valid_actor_admin s r hv⟩

theorem req_no_self_grant   : NoSelfGrant step := by
  intro s r hok hop
  have hv := aux_ok_valid s r hok
  exact aux_grant_ne s r hv hop

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hne
  have hv := aux_ok_valid s r hok
  have hEq : step s r = (Outcome.ok, ({ users := s.users, has := fun u q => expectedHas s r u q } : State)) := by
    unfold step
    simp [hv]
  have h2 : (step s r).2.has u q = expectedHas s r u q := by
    rw [hEq]
  have hneg : ¬ (u = r.target ∧ q = r.role) := by
    intro hcon
    cases hne with
    | inl hne => exact hne hcon.1
    | inr hne => exact hne hcon.2
  have hexp : expectedHas s r u q = s.has u q := by
    unfold expectedHas
    simp [hneg]
  rw [h2, hexp]

theorem req_effects : Effects step := by
  intro s r hok
  have hv := aux_ok_valid s r hok
  have hst : step s r = (Outcome.ok, ({ users := s.users, has := fun u q => expectedHas s r u q } : State)) := by
    unfold step
    simp [hv]
  constructor
  · have : (step s r).2.users = s.users := by rw [hst]
    exact this
  · intro u q
    have : (step s r).2.has u q = expectedHas s r u q := by rw [hst]
    exact this

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv := aux_ok_valid s r hok
  have hst : step s r = (Outcome.ok, ({ users := s.users, has := fun u q => expectedHas s r u q } : State)) := by
    unfold step
    simp [hv]
  have hs2 : (step s r).2 = ({ users := s.users, has := fun u q => expectedHas s r u q } : State) := by rw [hst]
  have hv2false : validBool ({ users := s.users, has := fun u q => expectedHas s r u q } : State) r = false := by
    cases hop : r.op with
    | grant =>
      have hhas : (({ users := s.users, has := fun u q => expectedHas s r u q } : State)).has r.target r.role = true := by
        show expectedHas s r r.target r.role = true
        rw [lem_exp_target2]
        simp [hop]
      cases h2 : validBool ({ users := s.users, has := fun u q => expectedHas s r u q } : State) r with
      | false => rfl
      | true =>
        have hfalse := aux_valid_has_target_grant2 _ _ h2 hop
        rw [hhas] at hfalse
        contradiction
    | revoke =>
      have hhas : (({ users := s.users, has := fun u q => expectedHas s r u q } : State)).has r.target r.role = false := by
        show expectedHas s r r.target r.role = false
        rw [lem_exp_target2]
        simp [hop]
      cases h2 : validBool ({ users := s.users, has := fun u q => expectedHas s r u q } : State) r with
      | false => rfl
      | true =>
        have htrue := aux_valid_has_target_revoke2 _ _ h2 hop
        rw [hhas] at htrue
        contradiction
  have hstep2 : step ({ users := s.users, has := fun u q => expectedHas s r u q } : State) r
      = (Outcome.rejected, ({ users := s.users, has := fun u q => expectedHas s r u q } : State)) :=
    aux_step_rej _ _ hv2false
  have hfin : step (step s r).2 r = (Outcome.rejected, (step s r).2) := by
    rw [hs2, hstep2]
  exact hfin

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  obtain ⟨w, hwmem, hwadmin⟩ := hex
  cases hvb : validBool s r with
  | false =>
    have hstep : step s r = (Outcome.rejected, s) := aux_step_rej s r hvb
    have h2 : (step s r).2 = s := by rw [hstep]
    have : ∃ u ∈ (step s r).2.users, (step s r).2.has u .admin = true := by
      rw [h2]
      exact ⟨w, hwmem, hwadmin⟩
    exact this
  | true =>
    have hst : step s r = (Outcome.ok, ({ users := s.users, has := fun u q => expectedHas s r u q } : State)) := by
      unfold step
      simp [hvb]
    have h2eq : (step s r).2 = ({ users := s.users, has := fun u q => expectedHas s r u q } : State) := by rw [hst]
    suffices h : ∃ u ∈ s.users, expectedHas s r u Role.admin = true by
      obtain ⟨u, humem, hu⟩ := h
      exact ⟨u, by rw [h2eq]; exact humem, by rw [h2eq]; exact hu⟩
    cases hop : r.op with
    | grant =>
      refine ⟨w, hwmem, ?_⟩
      unfold expectedHas
      by_cases hcond : w = r.target ∧ Role.admin = r.role
      · simp [hcond, hop]
      · simp [hcond, hwadmin]
    | revoke =>
      by_cases hrole : r.role = Role.admin
      · by_cases hwt : w = r.target
        · have hOA := aux_revoke_otherAdmin s r hvb hop hrole
          obtain ⟨v, hvmem, hne, hvadmin⟩ := aux_otherAdmin_of_bool s r.target hOA
          refine ⟨v, hvmem, ?_⟩
          have heq : expectedHas s r v Role.admin = s.has v Role.admin := by
            unfold expectedHas
            have hneg : ¬ (v = r.target ∧ Role.admin = r.role) := by
              intro hcon
              exact hne hcon.1
            simp [hneg, hvadmin]
          rw [heq, hvadmin]
        · refine ⟨w, hwmem, ?_⟩
          have heq : expectedHas s r w Role.admin = s.has w Role.admin := by
            unfold expectedHas
            have hneg : ¬ (w = r.target ∧ Role.admin = r.role) := by
              intro hcon
              exact hwt hcon.1
            simp [hneg]
          rw [heq]
          exact hwadmin
      · refine ⟨w, hwmem, ?_⟩
        have heq : expectedHas s r w Role.admin = s.has w Role.admin := by
          unfold expectedHas
          have hneg : ¬ (w = r.target ∧ Role.admin = r.role) := by
            intro hcon
            exact hrole hcon.2.symm
          simp [hneg]
        rw [heq]
        exact hwadmin

end Grants
