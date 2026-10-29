import Grants.Spec

namespace Grants

def otherAdminExists (users : List UserId) (has : UserId → Role → Bool) (u : UserId) : Bool :=
  users.any (fun v => decide (v ≠ u) && has v .admin)

def validBool (s : State) (r : Request) : Bool :=
  decide (r.actor ∈ s.users) && decide (r.target ∈ s.users) && s.has r.actor .admin &&
    (match r.op with
     | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
     | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminExists s.users s.has r.target))

def step : Impl := fun s r =>
  if validBool s r then (Outcome.ok, { users := s.users, has := expectedHas s r })
  else (Outcome.rejected, s)

theorem t1 : True := trivial
#check @List.any
#check @List.any_eq_true
#check @decide_eq_true

theorem tLem : True := trivial
#print List.any

theorem tProbe_any_nil : List.any ([] : List Nat) (fun _ => true) = false := by simp

theorem tProbe_any_cons : True := trivial
#check List.any_cons

theorem otherAdminExists_of_OtherAdmin (s : State) (u : UserId)
    (h : OtherAdmin s u) : otherAdminExists s.users s.has u = true := by
  unfold OtherAdmin at h
  obtain ⟨v, hmem, hne, hadm⟩ := h
  unfold otherAdminExists
  rw [List.any_eq_true]
  exact ⟨v, hmem, by simp [decide_eq_true hne, hadm]⟩

theorem otherAdminExists_true_imp (s : State) (u : UserId)
    (h : otherAdminExists s.users s.has u = true) : OtherAdmin s u := by
  unfold otherAdminExists at h
  rw [List.any_eq_true] at h
  obtain ⟨v, hmem, hv⟩ := h
  simp at hv
  obtain ⟨hne, hadm⟩ := hv
  exact ⟨v, hmem, hne, hadm⟩

#check otherAdminExists_true_imp

theorem probe_and : forall (a b : Bool), (a && b) = true -> a = true /\ b = true := by
  intro a b h
  cases a <;> cases b <;> simp_all

#check probe_and
#check Bool.and_eq_true
#check decide_eq_true
#check decide_eq_true_eq

theorem probe_not_true (b : Bool) (h : (!b) = true) : b = false := by
  cases b <;> simp_all

theorem probe_or_true (a b : Bool) (h : (a || b) = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all

theorem probe_has_false (b : Bool) (h : (!b) = true) : b = false := probe_not_true b h

#check Bool.not_eq_true
#check of_decide_eq_true
#check ne_of_beq_false

theorem probe_shape2 (s : State) (r : Request) (hop : r.op = .grant)
    (h : validBool s r = true) : r.actor ∈ s.users := by
  unfold validBool at h
  rw [hop] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp at h1
  exact h1

theorem probe_grant_simp (s : State) (r : Request) (hne : r.actor ≠ r.target) (hf : s.has r.target r.role = false) :
    ((decide (r.actor ≠ r.target) && !(s.has r.target r.role)) = true) := by
  simp [hne, hf]

theorem req_effects_aux_test : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases hb : validBool s r = true
  · simp [hb]
  · simp [hb] at hok

theorem idem_helper_valid_true (s : State) (r : Request) (h : validBool s r = true) :
    r.actor ∈ s.users ∧ r.target ∈ s.users ∧ s.has r.actor .admin = true := by
  unfold validBool at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp at h1 h2
  exact ⟨h1, h2, h3⟩

theorem idem_helper_grant (s : State) (r : Request) (h : validBool s r = true) (hop : r.op = .grant) :
    r.actor ≠ r.target ∧ s.has r.target r.role = false := by
  unfold validBool at h
  rw [hop] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨hne, hfalse⟩ := h4
  have hne' : r.actor ≠ r.target := of_decide_eq_true hne
  have hfalse' : s.has r.target r.role = false := by
    cases hh : s.has r.target r.role <;> simp_all
  exact ⟨hne', hfalse'⟩

theorem idem_helper_revoke_has (s : State) (r : Request) (h : validBool s r = true) (hop : r.op = .revoke) :
    s.has r.target r.role = true := by
  unfold validBool at h
  rw [hop] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨hhas, _⟩ := h4
  exact hhas

theorem expectedHas_target (s : State) (r : Request) :
    expectedHas s r r.target r.role = decide (r.op = .grant) := by
  unfold expectedHas
  simp

theorem expectedHas_target_grant (s : State) (r : Request) (hop : r.op = .grant) :
    expectedHas s r r.target r.role = true := by
  rw [expectedHas_target, hop]
  simp

theorem expectedHas_target_revoke (s : State) (r : Request) (hop : r.op = .revoke) :
    expectedHas s r r.target r.role = false := by
  rw [expectedHas_target]
  have h : ¬ (r.op = .grant) := by rw [hop]; simp
  simp [h]

theorem validBool_after_grant_false (s : State) (r : Request) (hop : r.op = .grant) :
    validBool { users := s.users, has := expectedHas s r } r = false := by
  unfold validBool
  simp only [hop]
  have hexp : expectedHas s r r.target r.role = true := expectedHas_target_grant s r hop
  simp [hexp]

theorem validBool_after_revoke_false (s : State) (r : Request) (hop : r.op = .revoke) :
    validBool { users := s.users, has := expectedHas s r } r = false := by
  unfold validBool
  simp only [hop]
  have hexp : expectedHas s r r.target r.role = false := expectedHas_target_revoke s r hop
  simp [hexp]

theorem idem_probe1 (s : State) (r : Request) (hb : validBool s r = true) :
    (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := by
  simp [step, hb]

theorem idem_probe2 (s : State) (r : Request) (hb : validBool s r = true) :
    step s r = (Outcome.ok, ({ users := s.users, has := expectedHas s r } : State)) := by
  simp [step, hb]

theorem idem_probe3 (s2 : State) (r : Request) (hnb : validBool s2 r = false) :
    (fun s r => if validBool s r then (Outcome.ok, ({ users := s.users, has := expectedHas s r } : State)) else (Outcome.rejected, s)) s2 r = (Outcome.rejected, s2) := by
  simp [hnb]

theorem idem_probe4 (s2 : State) (r : Request) (hnb : validBool s2 r = false) :
    step s2 r = (Outcome.rejected, s2) := by
  unfold step
  simp [hnb]

theorem probe_last_grant_true (s : State) (r : Request) (hop : r.op = .grant)
    (u0 : UserId) (hcond : u0 = r.target ∧ Role.admin = r.role) :
    expectedHas s r u0 Role.admin = true := by
  unfold expectedHas
  simp [hcond, hop]

theorem probe_last_grant_false (s : State) (r : Request) (u0 : UserId)
    (ha0 : s.has u0 Role.admin = true) (hcond : ¬ (u0 = r.target ∧ Role.admin = r.role)) :
    expectedHas s r u0 Role.admin = true := by
  unfold expectedHas
  simp [hcond, ha0]

theorem probe_last_grant_rw2 (s : State) (r : Request) (hop : r.op = Op.grant)
    (u0 : UserId) (hm0 : u0 ∈ s.users) (ha0 : s.has u0 Role.admin = true)
    (h2 : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State)) :
    ∃ u ∈ (step s r).2.users, (step s r).2.has u Role.admin = true := by
  refine ⟨u0, ?_, ?_⟩
  · rw [h2]; exact hm0
  · rw [h2]
    show expectedHas s r u0 Role.admin = true
    by_cases hcond : (u0 = r.target ∧ Role.admin = r.role)
    · unfold expectedHas
      rw [if_pos hcond, hop]
      rfl
    · unfold expectedHas
      rw [if_neg hcond, ha0]

theorem probe_debug_revoke3 (s : State) (r : Request)
    (hb : validBool s r = true) (hop : r.op = Op.revoke) (hro : r.role = Role.admin) :
    otherAdminExists s.users s.has r.target = true := by
  have hb2 : validBool s r = true := hb
  unfold validBool at hb2
  rw [hop] at hb2
  -- hb2 : decide ... && ... = true
  have hAnd : ∀ (a b : Bool), (a && b) = true → b = true := by
    intro a b h; cases a <;> cases b <;> simp_all
  have hOr : ∀ (a b : Bool), (a || b) = true → a = false → b = true := by
    intro a b h ha; cases a <;> cases b <;> simp_all
  have htail : (decide (r.role ≠ Role.admin) || otherAdminExists s.users s.has r.target) = true := by
    have h1 := hAnd _ _ hb2
    exact hAnd _ _ h1
  have hdec : decide (r.role ≠ Role.admin) = false := by simp [hro]
  exact hOr _ _ htail hdec

theorem probe_decide_mem (s : State) (r : Request) (hact : r.actor ∈ s.users) : decide (r.actor ∈ s.users) = true := by simp [hact]

theorem probe_decide_ne (a b : Nat) (h : a ≠ b) : decide (a ≠ b) = true := by simp [h]

theorem probe_decide_role (q : Role) (h : q ≠ .admin) : decide (q ≠ .admin) = true := by simp [h]

theorem probe_valid_grant_shape (s : State) (r : Request) (h1 : decide (r.actor ∈ s.users) = true) (h2 : decide (r.target ∈ s.users) = true) (h3 : s.has r.actor .admin = true) (h4 : decide (r.actor ≠ r.target) = true) (h5 : (!(s.has r.target r.role)) = true) (hop : r.op = .grant) : validBool s r = true := by unfold validBool; simp [hop, h1, h2, h3, h4, h5]

theorem probe_rw_valid_revoke (s : State) (r : Request) (h1 : decide (r.actor ∈ s.users) = true) (h2 : decide (r.target ∈ s.users) = true) (hadm : s.has r.actor .admin = true) (htrue : s.has r.target r.role = true) (hor : (decide (r.role ≠ .admin) || otherAdminExists s.users s.has r.target) = true) (hop : r.op = .revoke) : validBool s r = true := by
  unfold validBool
  rw [hop, h1, h2, hadm, htrue, hor]
  rfl

theorem probe_rw_valid_grant (s : State) (r : Request) (h1 : decide (r.actor ∈ s.users) = true) (h2 : decide (r.target ∈ s.users) = true) (hadm : s.has r.actor .admin = true) (hne_b : decide (r.actor ≠ r.target) = true) (hnot : (!(s.has r.target r.role)) = true) (hop : r.op = .grant) : validBool s r = true := by
  unfold validBool
  rw [hop, h1, h2, hadm, hne_b, hnot]
  rfl

theorem probe_hor_admin2 (s : State) (r : Request) (hrole : r.role = .admin) (hother : otherAdminExists s.users s.has r.target = true) : (decide (r.role ≠ .admin) || otherAdminExists s.users s.has r.target) = true := by
  have hdec : decide (r.role ≠ .admin) = false := by simp [hrole]
  simp [hdec, hother]

theorem probe_hor_notadmin2 (s : State) (r : Request) (hrole : r.role ≠ .admin) : (decide (r.role ≠ .admin) || otherAdminExists s.users s.has r.target) = true := by
  have hne_b : decide (r.role ≠ .admin) = true := by simp [hrole]
  simp [hne_b]

theorem validBool_of_ValidCommand_aux3 (s : State) (r : Request) (h : ValidCommand s r) : validBool s r = true := by
  unfold ValidCommand at h
  obtain ⟨hact, htgt, hadm, hgrant, hrevoke⟩ := h
  have h1 : decide (r.actor ∈ s.users) = true := by simp [hact]
  have h2 : decide (r.target ∈ s.users) = true := by simp [htgt]
  cases hop : r.op with
  | grant =>
    have hg := hgrant hop
    obtain ⟨hne, hfalse⟩ := hg
    have hne_b : decide (r.actor ≠ r.target) = true := by simp [hne]
    have hnot : (!(s.has r.target r.role)) = true := by simp [hfalse]
    exact probe_rw_valid_grant s r h1 h2 hadm hne_b hnot hop
  | revoke =>
    have hr := hrevoke hop
    obtain ⟨htrue, hadmImp⟩ := hr
    have hor : (decide (r.role ≠ .admin) || otherAdminExists s.users s.has r.target) = true := by
      by_cases hrole : r.role = .admin
      · have hOA := hadmImp hrole
        have hother := otherAdminExists_of_OtherAdmin s r.target hOA
        exact probe_hor_admin2 s r hrole hother
      · exact probe_hor_notadmin2 s r hrole
    exact probe_rw_valid_revoke s r h1 h2 hadm htrue hor hop

theorem probe_valid_split (s : State) (r : Request) (h : validBool s r = true) (hro : r.op = .grant) :
    (decide (r.actor ≠ r.target) && !(s.has r.target r.role)) = true := by
  unfold validBool at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [hro] at h4
  exact h4

theorem probe_cases_test (s : State) (r : Request) (h : validBool s r = true) (hop : r.op = .grant) :
    (decide (r.actor ≠ r.target) && !(s.has r.target r.role)) = true := by
  unfold validBool at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases hro : r.op with
  | grant =>
    simp only [hro] at h4
    exact h4
  | revoke =>
    simp [hro] at hop

theorem validBool_sound (s : State) (r : Request) (h : validBool s r = true) : ValidCommand s r := by
  unfold validBool at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hact : r.actor ∈ s.users := of_decide_eq_true h1
  have htgt : r.target ∈ s.users := of_decide_eq_true h2
  refine ⟨hact, htgt, h3, ?_, ?_⟩
  · intro hop
    cases hro : r.op with
    | revoke => simp [hro] at hop
    | grant =>
      simp only [hro] at h4
      rw [Bool.and_eq_true] at h4
      obtain ⟨hne_b, hnot⟩ := h4
      have hne : r.actor ≠ r.target := of_decide_eq_true hne_b
      have hfalse : s.has r.target r.role = false := by cases hh : s.has r.target r.role <;> simp_all
      exact ⟨hne, hfalse⟩
  · intro hop
    cases hro : r.op with
    | grant => simp [hro] at hop
    | revoke =>
      simp only [hro] at h4
      rw [Bool.and_eq_true] at h4
      obtain ⟨hhas, hor⟩ := h4
      refine ⟨hhas, ?_⟩
      intro hrole
      have hdec_false : decide (r.role ≠ .admin) = false := by simp [hrole]
      have hother_true : otherAdminExists s.users s.has r.target = true := by simp [hdec_false] at hor; exact hor
      exact otherAdminExists_true_imp s r.target hother_true

theorem probe_last_rw (s : State) (r : Request) (hcond : (r.target = r.target ∧ Role.admin = r.role)) (hop : r.op = Op.grant) : (expectedHas s r r.target Role.admin) = true := by
  unfold expectedHas
  rw [if_pos hcond, hop]
  rfl

theorem req_valid_succeeds  : ValidSucceeds step := by
  intro s r h
  have hb := validBool_of_ValidCommand_aux3 s r h
  unfold step
  simp [hb]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  have hnb : validBool s r = false := by
    cases hb : validBool s r with
    | true => exact absurd (validBool_sound s r hb) h
    | false => rfl
  simp [hnb]

theorem req_authorization   : AdminOnly step := by
  intro s r h
  unfold step at h
  cases hb : validBool s r
  · simp [hb] at h
  · unfold validBool at hb
    simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hb
    simp at h1
    exact ⟨h1, h3⟩

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hop
  unfold step at hok
  cases hb : validBool s r
  · simp [hb] at hok
  · unfold validBool at hb
    rw [hop] at hb
    simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hb
    obtain ⟨hne, _⟩ := h4
    exact of_decide_eq_true hne

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hne
  unfold step at hok ⊢
  cases hb : validBool s r
  · simp [hb] at hok
  · simp only [hb, ↓reduceIte] at hok ⊢
    unfold expectedHas
    have hneg : ¬ (u = r.target ∧ q = r.role) := by
      intro hconj
      obtain ⟨h1, h2⟩ := hconj
      cases hne with
      | inl h => exact h h1
      | inr h => exact h h2
    simp [hneg]

theorem req_effects : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases hb : validBool s r = true
  · simp [hb]
  · simp [hb] at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hb : validBool s r = true := by
    cases hbb : validBool s r with
    | false =>
      unfold step at hok
      simp [hbb] at hok
    | true => rfl
  have h2 : (step s r).2 = ({ users := s.users, has := expectedHas s r } : State) := idem_probe1 s r hb
  have hnb : validBool (step s r).2 r = false := by
    rw [h2]
    cases hop : r.op with
    | grant => exact validBool_after_grant_false s r hop
    | revoke => exact validBool_after_revoke_false s r hop
  exact idem_probe4 _ _ hnb

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  obtain ⟨u0, hm0, ha0⟩ := hex
  unfold step
  by_cases hb : validBool s r = true
  · simp only [hb, ↓reduceIte]
    have hvc : ValidCommand s r := validBool_sound s r hb
    obtain ⟨hact, htgt, hadm, hgrant, hrevoke⟩ := hvc
    by_cases hop : r.op = .grant
    · by_cases hrole : r.role = .admin
      · refine ⟨r.target, htgt, ?_⟩
        have hcond : (r.target = r.target ∧ Role.admin = r.role) := ⟨rfl, by rw [hrole]⟩
        have h1 : expectedHas s r r.target Role.admin = decide (r.op = .grant) := by
          unfold expectedHas
          rw [if_pos hcond]
        rw [h1, hop]
        rfl
      · refine ⟨u0, hm0, ?_⟩
        unfold expectedHas
        have hneg : ¬ (u0 = r.target ∧ Role.admin = r.role) := by
          intro hconj
          obtain ⟨_, h2⟩ := hconj
          apply hrole
          rw [← h2]
        rw [if_neg hneg, ha0]
    · have hopRev : r.op = .revoke := by cases h : r.op with | grant => simp [h] at hop | revoke => rfl
      by_cases hrole : r.role = .admin
      · have hr := hrevoke hopRev
        obtain ⟨htrue, hadmImp⟩ := hr
        have hOA : OtherAdmin s r.target := hadmImp hrole
        obtain ⟨v, hmem, hne, hadmV⟩ := hOA
        refine ⟨v, hmem, ?_⟩
        unfold expectedHas
        have hneg : ¬ (v = r.target ∧ Role.admin = r.role) := by
          intro hconj
          obtain ⟨h1, _⟩ := hconj
          exact hne h1
        rw [if_neg hneg, hadmV]
      · refine ⟨u0, hm0, ?_⟩
        unfold expectedHas
        have hneg : ¬ (u0 = r.target ∧ Role.admin = r.role) := by
          intro hconj
          obtain ⟨_, h2⟩ := hconj
          apply hrole
          rw [← h2]
        rw [if_neg hneg, ha0]
  · have hbf : validBool s r = false := by cases hbb : validBool s r with | true => simp [hbb] at hb | false => rfl
    simp only [hbf]
    exact ⟨u0, hm0, ha0⟩

end Grants
