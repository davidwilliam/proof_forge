import Grants.Spec

namespace Grants

def otherAdminb (s : State) (u : UserId) : Bool :=
  s.users.any fun v => decide (v ≠ u) && s.has v Role.admin

def validb (s : State) (r : Request) : Bool :=
  decide (r.actor ∈ s.users) && decide (r.target ∈ s.users) && s.has r.actor Role.admin &&
    (match r.op with
     | Op.grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
     | Op.revoke =>
       s.has r.target r.role &&
         (match r.role with
          | Role.admin => otherAdminb s r.target
          | _ => true))

def step : Impl :=
  fun s r => if validb s r then (Outcome.ok, { users := s.users, has := expectedHas s r }) else (Outcome.rejected, s)

def foo := 1

theorem bar : True := trivial

theorem foo2 : List.any [true, false] id = true := by simp

theorem otherAdminb_of_mem (s : State) (u v : UserId)
    (hmem : v ∈ s.users) (hne : v ≠ u) (hhas : s.has v Role.admin = true) :
    otherAdminb s u = true := by
  unfold otherAdminb
  simp
  exact ⟨v, hmem, hne, hhas⟩

theorem otherAdminb_true_iff (s : State) (u : UserId) :
    otherAdminb s u = true ↔ OtherAdmin s u := by
  unfold otherAdminb OtherAdmin
  simp

theorem validb_true_imp_aux (s : State) (r : Request) (h : validb s r = true) :
    ValidCommand s r := by
  unfold validb at h
  cases hOp : r.op with
  | grant =>
    simp only [hOp] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨ha, ht⟩, hadm⟩, hne, hnth⟩ := h
    have hhas : s.has r.actor Role.admin = true := hadm
    have hnth2 : s.has r.target r.role = false := by
      cases hb : s.has r.target r.role <;> simp_all
    refine ⟨ha, ht, hhas, ?_, ?_⟩
    · intro _
      exact ⟨hne, hnth2⟩
    · intro hEq
      simp [hOp] at hEq
  | revoke =>
    simp only [hOp] at h
    cases hRole : r.role with
    | admin =>
      simp only [hRole] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨ha, ht⟩, hadm⟩, hhas, hother⟩ := h
      have hhasA : s.has r.actor Role.admin = true := hadm
      have hhasT : s.has r.target r.role = true := by simp [hRole] at hhas ⊢; exact hhas
      refine ⟨ha, ht, hhasA, ?_, ?_⟩
      · intro hEq
        simp [hOp] at hEq
      · intro _
        refine ⟨hhasT, ?_⟩
        intro _
        rw [otherAdminb_true_iff] at hother
        exact hother
    | editor =>
      simp only [hRole] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨ha, ht⟩, hadm⟩, hhas, _⟩ := h
      have hhasA : s.has r.actor Role.admin = true := hadm
      have hhasT : s.has r.target r.role = true := by simp [hRole] at hhas ⊢; exact hhas
      refine ⟨ha, ht, hhasA, ?_, ?_⟩
      · intro hEq
        simp [hOp] at hEq
      · intro _
        refine ⟨hhasT, ?_⟩
        intro hEq
        simp [hRole] at hEq
    | viewer =>
      simp only [hRole] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨ha, ht⟩, hadm⟩, hhas, _⟩ := h
      have hhasA : s.has r.actor Role.admin = true := hadm
      have hhasT : s.has r.target r.role = true := by simp [hRole] at hhas ⊢; exact hhas
      refine ⟨ha, ht, hhasA, ?_, ?_⟩
      · intro hEq
        simp [hOp] at hEq
      · intro _
        refine ⟨hhasT, ?_⟩
        intro hEq
        simp [hRole] at hEq

theorem validb_expected_false_aux5 (s : State) (r : Request) :
    validb { users := s.users, has := expectedHas s r } r = false := by
  cases r with
  | mk op actor target role =>
    cases op with
    | grant =>
      unfold validb expectedHas
      simp
    | revoke =>
      unfold validb expectedHas
      simp

theorem keepsAdmin_helper : KeepsAdmin step := by
  intro s r hex
  obtain ⟨w, hwmem, hwhas⟩ := hex
  by_cases hv : validb s r = true
  · have h2 : (step s r).2 = { users := s.users, has := expectedHas s r } := by
      unfold step
      simp [hv]
    have hvc := validb_true_imp_aux s r hv
    obtain ⟨ha, ht, hadm, hgrant, hrev⟩ := hvc
    cases hOp : r.op with
    | grant =>
      refine ⟨w, ?_, ?_⟩
      · rw [h2]; exact hwmem
      · rw [h2]
        unfold expectedHas
        by_cases hc : (w = r.target ∧ (Role.admin = r.role))
        · simp [hc, hOp]
        · simp [hc, hwhas]
    | revoke =>
      have hrevI := hrev hOp
      obtain ⟨hhasT, hother⟩ := hrevI
      cases hRole : r.role with
      | admin =>
        have hOA := hother hRole
        obtain ⟨v, hvmem, hne, hvhas⟩ := hOA
        refine ⟨v, ?_, ?_⟩
        · rw [h2]; exact hvmem
        · rw [h2]
          unfold expectedHas
          have hc : ¬ (v = r.target ∧ Role.admin = r.role) := by
            intro h
            exact hne h.1
          simp [hc, hvhas]
      | editor =>
        refine ⟨w, ?_, ?_⟩
        · rw [h2]; exact hwmem
        · rw [h2]
          unfold expectedHas
          have hc : ¬ (w = r.target ∧ Role.admin = r.role) := by
            simp [hRole]
          simp [hc, hwhas]
      | viewer =>
        refine ⟨w, ?_, ?_⟩
        · rw [h2]; exact hwmem
        · rw [h2]
          unfold expectedHas
          have hc : ¬ (w = r.target ∧ Role.admin = r.role) := by
            simp [hRole]
          simp [hc, hwhas]
  · have h2 : (step s r).2 = s := by
      unfold step
      simp [hv]
    refine ⟨w, ?_, ?_⟩
    · rw [h2]; exact hwmem
    · rw [h2]; exact hwhas

theorem validb_of_Valid_aux (s : State) (r : Request) (h : ValidCommand s r) :
    validb s r = true := by
  unfold ValidCommand at h
  obtain ⟨ha, ht, hadm, hgrant, hrev⟩ := h
  unfold validb
  have h1 : decide (r.actor ∈ s.users) = true := by simp [ha]
  have h2 : decide (r.target ∈ s.users) = true := by simp [ht]
  rw [h1, h2, hadm]
  simp only [Bool.true_and]
  cases hOp : r.op with
  | grant =>
    simp only [hOp]
    have hg := hgrant hOp
    obtain ⟨hne, hnth⟩ := hg
    have hd : decide (r.actor ≠ r.target) = true := by simp [hne]
    rw [hd]
    simp only [Bool.true_and]
    simp [hnth]
  | revoke =>
    simp only [hOp]
    have hr := hrev hOp
    obtain ⟨hhasT, hother⟩ := hr
    cases hRole : r.role with
    | admin =>
      simp only [hRole]
      have e1 : s.has r.target r.role = true := hhasT
      simp [hRole] at e1 ⊢
      constructor
      · exact e1
      · rw [otherAdminb_true_iff]
        have : r.role = Role.admin := by rw [hRole]
        exact hother this
    | editor =>
      simp only [hRole]
      have e1 : s.has r.target r.role = true := hhasT
      simp [hRole] at e1 ⊢
      exact e1
    | viewer =>
      simp only [hRole]
      have e1 : s.has r.target r.role = true := hhasT
      simp [hRole] at e1 ⊢
      exact e1

theorem req_valid_succeeds  : ValidSucceeds step := by
  intro s r h
  have hb : validb s r = true := validb_of_Valid_aux s r h
  unfold step
  simp [hb]

theorem req_invalid_noop    : InvalidNoop step := by
  intro s r h
  unfold step
  have hb : validb s r = false := by
    cases hval : validb s r with
    | true => exact absurd (validb_true_imp_aux s r hval) h
    | false => rfl
  simp [hb]

theorem req_authorization   : AdminOnly step := by
  intro s r h
  unfold step at h
  have hval : validb s r = true := by
    cases hv : validb s r with
    | true => rfl
    | false => simp [hv] at h
  have hvc := validb_true_imp_aux s r hval
  unfold ValidCommand at hvc
  obtain ⟨ha, ht, hadm, _, _⟩ := hvc
  exact ⟨ha, hadm⟩

theorem req_no_self_grant   : NoSelfGrant step := by
  intro s r h hop
  unfold step at h
  have hval : validb s r = true := by
    cases hv : validb s r with
    | true => rfl
    | false => simp [hv] at h
  have hvc := validb_true_imp_aux s r hval
  unfold ValidCommand at hvc
  obtain ⟨ha, ht, hadm, hgrant, hrev⟩ := hvc
  exact (hgrant hop).1

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r h u q hne
  have hval : validb s r = true := by
    cases hv : validb s r with
    | true => rfl
    | false => unfold step at h; simp [hv] at h
  have hstep2 : (step s r).2 = { users := s.users, has := expectedHas s r } := by
    unfold step; simp [hval]
  have hcond : ¬ (u = r.target ∧ q = r.role) := by
    cases hne with
    | inl hl => exact fun h => hl h.1
    | inr hr => exact fun h => hr h.2
  have heq : (step s r).2.has u q = expectedHas s r u q := by
    rw [hstep2]
  rw [heq]
  unfold expectedHas
  simp [hcond]

theorem req_effects : Effects step := by
  intro s r h
  have hval : validb s r = true := by
    cases hv : validb s r with
    | true => rfl
    | false => unfold step at h; simp [hv] at h
  have h2 : (step s r).2 = { users := s.users, has := expectedHas s r } := by
    unfold step; simp [hval]
  constructor
  · rw [h2]
  · intro u q
    rw [h2]

theorem req_idempotency     : Idempotent step := by
  intro s r h
  have hval : validb s r = true := by
    cases hv : validb s r with
    | true => rfl
    | false =>
      have hstep : step s r = (Outcome.rejected, s) := by
        unfold step
        simp [hv]
      rw [hstep] at h
      simp at h
  have hstep : step s r = (Outcome.ok, { users := s.users, has := expectedHas s r }) := by
    unfold step
    simp [hval]
  have hb : validb { users := s.users, has := expectedHas s r } r = false :=
    validb_expected_false_aux5 s r
  have hstep2 : step { users := s.users, has := expectedHas s r } r =
      (Outcome.rejected, { users := s.users, has := expectedHas s r }) := by
    unfold step
    simp [hb]
  rw [hstep]
  simp only []
  rw [hstep2]

theorem req_last_admin      : KeepsAdmin step := keepsAdmin_helper

end Grants
