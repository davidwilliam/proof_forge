import Grants.Spec

namespace Grants

def hasOtherAdminB (s : State) (u : UserId) : Bool :=
  s.users.any (fun v => decide (v ≠ u) && s.has v .admin)

def validB (s : State) (r : Request) : Bool :=
  decide (r.actor ∈ s.users) && decide (r.target ∈ s.users) && s.has r.actor .admin &&
    match r.op with
    | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
    | .revoke =>
      s.has r.target r.role &&
        match r.role with
        | .admin => hasOtherAdminB s r.target
        | _ => true

def step : Impl := fun s r =>
  if validB s r then
    (Outcome.ok, { users := s.users, has := fun u q => expectedHas s r u q })
  else
    (Outcome.rejected, s)

def fooTest : Nat := 1

theorem fooTestThm : 1 = 1 := rfl

theorem probe_any (l : List Nat) (p : Nat → Bool) : l.any p = true ↔ ∃ x, x ∈ l ∧ p x = true := by
  exact List.any_eq_true

theorem hasOtherAdminB_true_iff3 (s : State) (u : UserId) :
    hasOtherAdminB s u = true ↔ OtherAdmin s u := by
  unfold hasOtherAdminB OtherAdmin
  rw [List.any_eq_true]
  constructor
  · intro h
    obtain ⟨w, hmem, hand⟩ := h
    have ha : (decide (w ≠ u) && s.has w Role.admin) = true := hand
    simp at ha
    obtain ⟨hne, hadm⟩ := ha
    exact ⟨w, hmem, hne, hadm⟩
  · intro h
    obtain ⟨w, hmem, hne, hadm⟩ := h
    refine ⟨w, hmem, ?_⟩
    simp [hne, hadm]

theorem validB_unfold_test (s : State) (r : Request) (h : r.op = .grant) : validB s r = (decide (r.actor ∈ s.users) && decide (r.target ∈ s.users) && s.has r.actor .admin && (decide (r.actor ≠ r.target) && !(s.has r.target r.role))) := by
  unfold validB
  rw [h]

theorem bool_probe2 (a b : Bool) (h : (a && b) = true) : a = true := by
  simp at h
  exact h.1

theorem dbg_bool (a b : Bool) (h : (a && b) = true) : a = true := by
  simp at h
  exact h.1

theorem dbg_dec (P : Prop) [Decidable P] (h : decide P = true) : P := of_decide_eq_true h

theorem dbg_mem (s : State) (actor target : UserId) (role : Role)
    (h : (decide (actor ∈ s.users) && decide (target ∈ s.users) && s.has actor Role.admin && (decide (actor ≠ target) && !(s.has target role))) = true) :
    actor ∈ s.users := by
  have h2 : (decide (actor ∈ s.users) && decide (target ∈ s.users) && s.has actor Role.admin && (decide (actor ≠ target) && !(s.has target role))) = true := h
  simp at h2
  obtain ⟨⟨⟨ha, ht⟩, had⟩, hs, hnt⟩ := h2
  exact ha

theorem bool_and_extract2 (a b : Bool) (h : (a && b) = true) : a = true := by
  simp at h
  exact h.1

theorem auth_probe2 (s : State) (r : Request) (h : validB s r = true) : r.actor ∈ s.users := by
  unfold validB at h
  cases hop : r.op
  · simp [hop] at h
    exact h.1.1.1
  · simp [hop] at h
    exact h.1.1.1

theorem auth_probe_admin (s : State) (r : Request) (h : validB s r = true) : s.has r.actor .admin = true := by
  unfold validB at h
  cases hop : r.op
  · simp [hop] at h
    exact h.1.2
  · simp [hop] at h
    exact h.1.2

theorem grant_ne_helper (s : State) (r : Request) (hv : validB s r = true) (hop : r.op = Op.grant) : r.actor ≠ r.target := by
  unfold validB at hv
  rw [hop] at hv
  simp at hv
  exact hv.2.1

theorem expectedHas_target3 (s : State) (r : Request) :
    expectedHas s r r.target r.role = decide (r.op = .grant) := by
  unfold expectedHas
  simp

#check decide (Op.grant = Op.grant)
#check (rfl : decide (Op.grant = Op.grant) = true)
#check (rfl : decide (Op.revoke = Op.grant) = false)

theorem idem_probe (s : State) (r : Request) (hv : validB s r = true) :
    (step s r).2.has r.target r.role = decide (r.op = .grant) := by
  have h1 : (step s r).2.has r.target r.role = expectedHas s r r.target r.role := by
    simp [step, hv]
  rw [h1, expectedHas_target3]

theorem idem_probe2 (s : State) (r : Request) (hv : validB s r = true) (hop : r.op = .grant) :
    (step s r).2.has r.target r.role = true := by
  have h1 := idem_probe s r hv
  rw [hop] at h1
  have h2 : decide (Op.grant = Op.grant) = true := rfl
  rw [h2] at h1
  exact h1

theorem idem_step_false (s2 : State) (r : Request) (hf : validB s2 r = false) :
    step s2 r = (Outcome.rejected, s2) := by
  unfold step
  simp [hf]

theorem idem_probe3b (s : State) (r : Request) (hv : validB s r = true) (hop : r.op = .revoke) :
    (step s r).2.has r.target r.role = false := by
  have h1 := idem_probe s r hv
  rw [hop] at h1
  have h2 : decide (Op.revoke = Op.grant) = false := rfl
  rw [h2] at h1
  exact h1

theorem idem_validB_grant_falseb (s : State) (r : Request) (hv : validB s r = true) (hop : r.op = .grant) :
    validB (step s r).2 r = false := by
  have hhas := idem_probe2 s r hv hop
  unfold validB
  rw [hop, hhas]
  simp

theorem idem_validB_revoke_falseb (s : State) (r : Request) (hv : validB s r = true) (hop : r.op = .revoke) :
    validB (step s r).2 r = false := by
  have hhas := idem_probe3b s r hv hop
  unfold validB
  rw [hop, hhas]
  cases hrole : r.role
  · simp
  · simp
  · simp

theorem otherAdmin_of_validB_revoke_admin3 (s : State) (r : Request) (hv : validB s r = true) (hop : r.op = .revoke) (hrole : r.role = .admin) : OtherAdmin s r.target := by
  unfold validB at hv
  rw [hop, hrole] at hv
  simp at hv
  exact (hasOtherAdminB_true_iff3 s r.target).mp hv.2.2

theorem step_users_eq3 (s : State) (r : Request) : (step s r).2.users = s.users := by
  unfold step
  by_cases h : validB s r = true
  · simp [h]
  · have h2 : validB s r = false := by cases hb : validB s r with | true => simp [hb] at h | false => rfl
    simp [h2]

theorem step_has_eq3 (s : State) (r : Request) (hv : validB s r = true) (u : UserId) (q : Role) : (step s r).2.has u q = expectedHas s r u q := by
  unfold step
  simp [hv]

theorem target_mem_of_validB4 (s : State) (r : Request) (hv : validB s r = true) : r.target ∈ s.users := by
  unfold validB at hv
  cases hop : r.op
  · simp [hop] at hv
    exact hv.1.1.2
  · simp [hop] at hv
    cases hrole : r.role <;> simp [hrole] at hv
    · exact hv.1.1.2
    · exact hv.1.1.2
    · exact hv.1.1.2

theorem tmp_check1 (P : Prop) [Decidable P] (h : P) : decide P = true := by simp [h]

theorem tmp_check2 (s : State) (r : Request) (h : r.actor ∈ s.users) : decide (r.actor ∈ s.users) = true := by simp [h]

theorem validB_of_ValidCommand_test2 (s : State) (r : Request) (h : ValidCommand s r) :
    validB s r = true := by
  unfold ValidCommand at h
  obtain ⟨hAmem, hTmem, hAadm, hGrant, hRevoke⟩ := h
  have e1 : decide (r.actor ∈ s.users) = true := by simp [hAmem]
  have e2 : decide (r.target ∈ s.users) = true := by simp [hTmem]
  cases hop : r.op with
  | grant =>
    have hg := hGrant hop
    obtain ⟨hne, hfalse⟩ := hg
    have e3 : decide (r.actor ≠ r.target) = true := by simp [hne]
    have e4 : (!(s.has r.target r.role)) = true := by simp [hfalse]
    unfold validB
    rw [hop]
    simp [e1, e2, hAadm, e3, e4]
  | revoke =>
    have hr := hRevoke hop
    obtain ⟨htrue, hadmin⟩ := hr
    cases hrole : r.role with
    | admin =>
      have hOther : OtherAdmin s r.target := hadmin hrole
      have eOther : hasOtherAdminB s r.target = true :=
        (hasOtherAdminB_true_iff3 s r.target).mpr hOther
      have htrue' : s.has r.target Role.admin = true := by rw [← hrole]; exact htrue
      unfold validB
      rw [hop, hrole]
      simp [e1, e2, hAadm, htrue', eOther]
    | editor =>
      have htrue' : s.has r.target Role.editor = true := by rw [← hrole]; exact htrue
      unfold validB
      rw [hop, hrole]
      simp [e1, e2, hAadm, htrue']
    | viewer =>
      have htrue' : s.has r.target Role.viewer = true := by rw [← hrole]; exact htrue
      unfold validB
      rw [hop, hrole]
      simp [e1, e2, hAadm, htrue']

theorem ValidCommand_of_validB_aux (s : State) (r : Request) (hv : validB s r = true) :
    ValidCommand s r := by
  unfold ValidCommand
  have hAmem : r.actor ∈ s.users := auth_probe2 s r hv
  have hTmem : r.target ∈ s.users := target_mem_of_validB4 s r hv
  have hAadm : s.has r.actor Role.admin = true := auth_probe_admin s r hv
  refine ⟨hAmem, hTmem, hAadm, ?_, ?_⟩
  · intro hop
    have hne := grant_ne_helper s r hv hop
    have hfalse : s.has r.target r.role = false := by
      unfold validB at hv
      rw [hop] at hv
      simp at hv
      exact hv.2.2
    exact ⟨hne, hfalse⟩
  · intro hop
    unfold validB at hv
    rw [hop] at hv
    cases hrole : r.role with
    | admin =>
      rw [hrole] at hv
      simp at hv
      have htrue : s.has r.target Role.admin = true := hv.2.1
      have hOther : OtherAdmin s r.target :=
        (hasOtherAdminB_true_iff3 s r.target).mp hv.2.2
      exact ⟨htrue, fun _ => hOther⟩
    | editor =>
      rw [hrole] at hv
      simp at hv
      exact ⟨hv.2, fun h => by cases h⟩
    | viewer =>
      rw [hrole] at hv
      simp at hv
      exact ⟨hv.2, fun h => by cases h⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hv : validB s r = true := validB_of_ValidCommand_test2 s r h
  unfold step
  simp [hv]

theorem req_invalid_noop    : InvalidNoop step := by
  intro s r hn
  have hfb : validB s r = false := by
    cases hb : validB s r with
    | true => exact absurd (ValidCommand_of_validB_aux s r hb) hn
    | false => rfl
  unfold step
  simp [hfb]

theorem req_authorization : AdminOnly step := by
  intro s r hok
  have hv : validB s r = true := by
    cases hcb : validB s r
    · have hrej : (step s r).1 = Outcome.rejected := by simp [step, hcb]
      rw [hrej] at hok
      cases hok
    · rfl
  exact ⟨auth_probe2 s r hv, auth_probe_admin s r hv⟩

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hop
  have hv : validB s r = true := by
    cases hcb : validB s r
    · have hrej : (step s r).1 = Outcome.rejected := by simp [step, hcb]
      rw [hrej] at hok
      cases hok
    · rfl
  exact grant_ne_helper s r hv hop

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hdisj
  have hv : validB s r = true := by
    cases hcb : validB s r with
    | false =>
      have hrej : (step s r).1 = Outcome.rejected := by simp [step, hcb]
      rw [hrej] at hok
      cases hok
    | true => rfl
  have h2 : (step s r).2.has u q = expectedHas s r u q := by simp [step, hv]
  rw [h2]
  unfold expectedHas
  have hcond : ¬ (u = r.target ∧ q = r.role) := by
    intro hconj
    obtain ⟨hu, hq⟩ := hconj
    cases hdisj with
    | inl hne => exact hne hu
    | inr hne => exact hne hq
  rw [if_neg hcond]

theorem req_effects : Effects step := by
  intro s r hok
  have hv : validB s r = true := by
    cases hcb : validB s r with
    | false =>
      have hrej : (step s r).1 = Outcome.rejected := by simp [step, hcb]
      rw [hrej] at hok
      cases hok
    | true => rfl
  constructor
  · simp [step, hv]
  · intro u q
    simp [step, hv]

theorem req_idempotency     : Idempotent step := by
  intro s r hok
  have hv : validB s r = true := by
    cases hcb : validB s r with
    | false =>
      have hrej : (step s r).1 = Outcome.rejected := by simp [step, hcb]
      rw [hrej] at hok
      cases hok
    | true => rfl
  cases hop : r.op with
  | grant =>
    have hfalse := idem_validB_grant_falseb s r hv hop
    exact idem_step_false (step s r).2 r hfalse
  | revoke =>
    have hfalse := idem_validB_revoke_falseb s r hv hop
    exact idem_step_false (step s r).2 r hfalse

theorem req_last_admin      : KeepsAdmin step := by
  intro s r hex
  obtain ⟨u0, hu0mem, hu0adm⟩ := hex
  by_cases hv : validB s r = true
  · have husers : (step s r).2.users = s.users := step_users_eq3 s r
    have hhas : ∀ u q, (step s r).2.has u q = expectedHas s r u q := fun u q => step_has_eq3 s r hv u q
    cases hop : r.op with
    | grant =>
      cases hrole : r.role with
      | admin =>
        have htmem : r.target ∈ s.users := target_mem_of_validB4 s r hv
        have htmem' : r.target ∈ (step s r).2.users := by rw [husers]; exact htmem
        have htrue : (step s r).2.has r.target Role.admin = true := by
          rw [hhas]
          unfold expectedHas
          have hcond : r.target = r.target ∧ Role.admin = r.role := by rw [hrole]; exact ⟨rfl, rfl⟩
          rw [if_pos hcond]
          rw [hop]
          rfl
        exact ⟨r.target, htmem', htrue⟩
      | editor =>
        have hkeep : (step s r).2.has u0 Role.admin = true := by
          rw [hhas]
          unfold expectedHas
          have hcond : ¬ (u0 = r.target ∧ Role.admin = r.role) := by
            intro hconj
            obtain ⟨_, hq⟩ := hconj
            rw [hrole] at hq
            cases hq
          rw [if_neg hcond]
          exact hu0adm
        have hu0mem' : u0 ∈ (step s r).2.users := by rw [husers]; exact hu0mem
        exact ⟨u0, hu0mem', hkeep⟩
      | viewer =>
        have hkeep : (step s r).2.has u0 Role.admin = true := by
          rw [hhas]
          unfold expectedHas
          have hcond : ¬ (u0 = r.target ∧ Role.admin = r.role) := by
            intro hconj
            obtain ⟨_, hq⟩ := hconj
            rw [hrole] at hq
            cases hq
          rw [if_neg hcond]
          exact hu0adm
        have hu0mem' : u0 ∈ (step s r).2.users := by rw [husers]; exact hu0mem
        exact ⟨u0, hu0mem', hkeep⟩
    | revoke =>
      cases hrole : r.role with
      | admin =>
        have hother := otherAdmin_of_validB_revoke_admin3 s r hv hop hrole
        obtain ⟨v, hvmem, hne, hadm⟩ := hother
        have hvmem' : v ∈ (step s r).2.users := by rw [husers]; exact hvmem
        have hkeep : (step s r).2.has v Role.admin = true := by
          rw [hhas]
          unfold expectedHas
          have hcond : ¬ (v = r.target ∧ Role.admin = r.role) := by
            intro hconj
            obtain ⟨huv, _⟩ := hconj
            exact hne huv
          rw [if_neg hcond]
          exact hadm
        exact ⟨v, hvmem', hkeep⟩
      | editor =>
        have hkeep : (step s r).2.has u0 Role.admin = true := by
          rw [hhas]
          unfold expectedHas
          have hcond : ¬ (u0 = r.target ∧ Role.admin = r.role) := by
            intro hconj
            obtain ⟨_, hq⟩ := hconj
            rw [hrole] at hq
            cases hq
          rw [if_neg hcond]
          exact hu0adm
        have hu0mem' : u0 ∈ (step s r).2.users := by rw [husers]; exact hu0mem
        exact ⟨u0, hu0mem', hkeep⟩
      | viewer =>
        have hkeep : (step s r).2.has u0 Role.admin = true := by
          rw [hhas]
          unfold expectedHas
          have hcond : ¬ (u0 = r.target ∧ Role.admin = r.role) := by
            intro hconj
            obtain ⟨_, hq⟩ := hconj
            rw [hrole] at hq
            cases hq
          rw [if_neg hcond]
          exact hu0adm
        have hu0mem' : u0 ∈ (step s r).2.users := by rw [husers]; exact hu0mem
        exact ⟨u0, hu0mem', hkeep⟩
  · have hfalse : validB s r = false := by
      cases hb : validB s r with
      | true => exact absurd hb hv
      | false => rfl
    have hstep : step s r = (Outcome.rejected, s) := by unfold step; simp [hfalse]
    have h2 : (step s r).2 = s := by rw [hstep]
    rw [h2]
    exact ⟨u0, hu0mem, hu0adm⟩

end Grants
