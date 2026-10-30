import Grants.Spec
namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance

def otherAdminb (s : State) (t : UserId) : Bool :=
  s.users.any (fun v => v != t && s.has v .admin)

def validb (s : State) (r : Request) : Bool :=
  (s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin) &&
  match r.op with
  | .grant => decide (r.actor ≠ r.target) && !s.has r.target r.role
  | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target)

def step : Impl := fun s r =>
  if validb s r then
    (.ok, { users := s.users, has := fun u q => expectedHas s r u q })
  else
    (.rejected, s)

def dummyX : Nat := 1

def checkValidb : Bool := validb { users := [], has := fun _ _ => false } { op := .grant, actor := 0, target := 0, role := .viewer }
#check (validb)
#check (List.contains_eq_mem)

def testVal : State → Request → Bool := validb
#check (inferInstance : Decidable (1 = 1))

theorem otherAdminb_iff6 (s : State) (t : UserId) : otherAdminb s t = true ↔ OtherAdmin s t := by
  unfold otherAdminb OtherAdmin
  rw [List.any_eq_true]
  constructor
  · intro h; obtain ⟨v, hv_mem, hv_cond⟩ := h
    have hv : (v != t && s.has v .admin) = true := hv_cond
    rw [Bool.and_eq_true] at hv; obtain ⟨hneqB, hhas⟩ := hv
    have hneq : v ≠ t := by intro heq; subst heq; simp at hneqB
    exact ⟨v, hv_mem, hneq, hhas⟩
  · intro h; obtain ⟨v, hv_mem, hneq, hhas⟩ := h
    exact ⟨v, hv_mem, by simp [hneq, hhas]⟩

theorem validb_iff (s : State) (r : Request) : validb s r = true ↔ ValidCommand s r := by
  unfold validb ValidCommand
  have hca : s.users.contains r.actor = true ↔ r.actor ∈ s.users := by
    rw [List.contains_eq_mem (a := r.actor)]; simp
  have hct : s.users.contains r.target = true ↔ r.target ∈ s.users := by
    rw [List.contains_eq_mem (a := r.target)]; simp
  constructor
  · intro h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Bool.and_eq_true] at h1
    obtain ⟨h1a, h1b⟩ := h1
    rw [Bool.and_eq_true] at h1a
    obtain ⟨hcaT, hctT⟩ := h1a
    have hcaM : r.actor ∈ s.users := hca.mp hcaT
    have hctM : r.target ∈ s.users := hct.mp hctT
    have hadmin : s.has r.actor .admin = true := h1b
    refine ⟨hcaM, hctM, hadmin, ?_, ?_⟩
    · intro hgrant
      cases hop : r.op
      · have h2g : decide (r.actor ≠ r.target) && !s.has r.target r.role = true := by
          have : (match r.op with | .grant => decide (r.actor ≠ r.target) && !s.has r.target r.role | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target)) = true := h2
          rw [hop] at this
          exact this
        rw [Bool.and_eq_true] at h2g
        obtain ⟨hne, hhasF⟩ := h2g
        have hneT : r.actor ≠ r.target := of_decide_eq_true hne
        have hhasF' : s.has r.target r.role = false := by
          have : (!s.has r.target r.role) = true := hhasF
          cases hb : s.has r.target r.role <;> simp_all
        exact ⟨hneT, hhasF'⟩
      · simp [hop] at hgrant
    · intro hrev
      cases hop : r.op
      · simp [hop] at hrev
      · have h2r : s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target) = true := by
          have : (match r.op with | .grant => decide (r.actor ≠ r.target) && !s.has r.target r.role | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target)) = true := h2
          rw [hop] at this
          exact this
        rw [Bool.and_eq_true] at h2r
        obtain ⟨hhasT, hor⟩ := h2r
        exact ⟨hhasT, fun heq => by
          have hdecF : decide (r.role ≠ .admin) = false := by simp [heq]
          have : otherAdminb s r.target = true := by simp [hdecF] at hor; exact hor
          exact (otherAdminb_iff6 s r.target).mp this⟩
  · intro h
    obtain ⟨hcaM, hctM, hadmin, hgrantImp, hrevImp⟩ := h
    have hcaT : s.users.contains r.actor = true := hca.mpr hcaM
    have hctT : s.users.contains r.target = true := hct.mpr hctM
    rw [Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      constructor
      · rw [Bool.and_eq_true]
        exact ⟨hcaT, hctT⟩
      · exact hadmin
    · cases hop : r.op
      · have hg := hgrantImp hop
        obtain ⟨hne, hhasF⟩ := hg
        show (decide (r.actor ≠ r.target) && !s.has r.target r.role) = true
        rw [Bool.and_eq_true]
        constructor
        · simp [hne]
        · simp [hhasF]
      · have hr := hrevImp hop
        obtain ⟨hhasT, hother⟩ := hr
        show (s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target)) = true
        rw [Bool.and_eq_true]
        constructor
        · exact hhasT
        · by_cases heq : r.role = .admin
          · have hOA := hother heq
            have hOtherB : otherAdminb s r.target = true := (otherAdminb_iff6 s r.target).mpr hOA
            simp [heq, hOtherB]
          · simp [heq]

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds step
  intro s r hV
  have hv : validb s r = true := (validb_iff s r).mpr hV
  simp [hv]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop step
  intro s r hInv
  have hvF : validb s r = false := by
    have : validb s r = true → ValidCommand s r := fun h => (validb_iff s r).mp h
    cases hb : validb s r
    · rfl
    · exfalso; exact hInv (this hb)
  simp [hvF]

theorem req_authorization : AdminOnly step := by
  unfold AdminOnly step
  intro s r h_ok
  have h_validb : validb s r = true := by
    by_cases hv : validb s r = true
    · exact hv
    · have hv2 : validb s r = false := by cases hb : validb s r <;> simp_all
      simp [hv2] at h_ok
  have hVC := (validb_iff s r).mp h_validb
  exact ⟨hVC.1, hVC.2.2.1⟩

theorem req_no_self_grant   : NoSelfGrant step := by
  unfold NoSelfGrant step
  intro s r h_ok h_grant
  have h_validb : validb s r = true := by
    by_cases hv : validb s r = true
    · exact hv
    · have hv2 : validb s r = false := by
        cases hb : validb s r
        · rfl
        · simp_all
      simp [hv2] at h_ok
  unfold validb at h_validb
  have h_and : ((s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin) = true) ∧
    ((match r.op with | .grant => decide (r.actor ≠ r.target) && !s.has r.target r.role | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target)) = true) := by
    have h2 : ((s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin) &&
      (match r.op with | .grant => decide (r.actor ≠ r.target) && !s.has r.target r.role | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target))) = true := h_validb
    rwa [Bool.and_eq_true] at h2
  obtain ⟨_, h_match⟩ := h_and
  rw [h_grant] at h_match
  have h2 : decide (r.actor ≠ r.target) = true ∧ (!s.has r.target r.role) = true := by
    rwa [Bool.and_eq_true] at h_match
  exact of_decide_eq_true h2.1

theorem req_others_unchanged : OthersUnchanged step := by
  unfold OthersUnchanged step
  intro s r h_ok u q h_neq
  have h_validb : validb s r = true := by
    by_cases hv : validb s r = true
    · exact hv
    · have hv2 : validb s r = false := by
        cases hb : validb s r
        · rfl
        · simp_all
      simp [hv2] at h_ok
  simp [h_validb]
  -- now goal is (expectedHas ...) = s.has u q
  unfold expectedHas
  have h_cond : ¬ (u = r.target ∧ q = r.role) := by
    intro h
    rcases h with ⟨hu, hq⟩
    cases h_neq with
    | inl h1 => exact h1 hu
    | inr h1 => exact h1 hq
  simp [h_cond]

theorem req_effects : Effects step := by
  unfold Effects step
  intro s r h_ok
  have h_validb : validb s r = true := by
    by_cases hv : validb s r = true
    · exact hv
    · have hv2 : validb s r = false := by
        cases hb : validb s r
        · rfl
        · simp_all
      simp [hv2] at h_ok
  simp [h_validb]

theorem req_idempotency     : Idempotent step := by
  unfold Idempotent
  intro s r h_ok
  have h_validb : validb s r = true := by
    by_cases hv : validb s r = true
    · exact hv
    · have hv2 : validb s r = false := by
        cases hb : validb s r
        · rfl
        · simp_all
      unfold step at h_ok
      simp [hv2] at h_ok
  have h_s2 : (step s r).2 = ({ users := s.users, has := fun u q => expectedHas s r u q } : State) := by
    unfold step; simp [h_validb]
  have h_need : validb { users := s.users, has := fun u q => expectedHas s r u q } r = false := by
    cases hop : r.op
    · have h_has_new : expectedHas s r r.target r.role = true := by
        unfold expectedHas; simp [hop]
      unfold validb
      simp [hop, h_has_new]
    · have h_has_new : expectedHas s r r.target r.role = false := by
        unfold expectedHas; simp [hop]
      unfold validb
      simp [hop, h_has_new]
  have h_step2' : step { users := s.users, has := fun u q => expectedHas s r u q } r = (Outcome.rejected, { users := s.users, has := fun u q => expectedHas s r u q }) := by
    unfold step; simp [h_need]
  rw [← h_s2] at h_step2'
  exact h_step2'

theorem req_last_admin : KeepsAdmin step := by
  unfold KeepsAdmin
  intro s r hex
  by_cases hv : validb s r = true
  · have hstep : step s r = (.ok, { users := s.users, has := fun u q => expectedHas s r u q }) := by unfold step; simp [hv]
    rw [hstep]; simp only
    obtain ⟨u, hu_mem, hu_admin⟩ := hex
    cases hop : r.op
    · -- grant
      refine ⟨u, hu_mem, ?_⟩
      show expectedHas s r u .admin = true
      unfold expectedHas
      by_cases hcond : u = r.target ∧ (Role.admin = r.role)
      · simp [hcond, hop]
      · simp [hcond, hu_admin]
    · -- revoke
      by_cases hrA : r.role = .admin
      · have hotherB : otherAdminb s r.target = true := by
          have h1 : validb s r = true := hv
          -- unfold only validb and hop to avoid over-simp
          have h1' : ((s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin) && (s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target))) = true := by
            have : validb s r = ((s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin) && (s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target))) := by
              simp only [validb, hop]
            rw [this] at h1; exact h1
          rw [Bool.and_eq_true] at h1'
          obtain ⟨_, h2⟩ := h1'
          rw [Bool.and_eq_true] at h2
          obtain ⟨_, hor⟩ := h2
          have hdec : decide (r.role ≠ .admin) = false := by simp [hrA]
          simp only [hdec, Bool.false_or] at hor
          exact hor
        have hOA := (otherAdminb_iff6 s r.target).mp hotherB
        obtain ⟨v, hv_mem, hv_neq, hv_admin⟩ := hOA
        refine ⟨v, hv_mem, ?_⟩
        show expectedHas s r v .admin = true
        unfold expectedHas
        have hcond : ¬ (v = r.target ∧ Role.admin = r.role) := by intro ⟨h1,h2⟩; simp [hrA] at h2; exact hv_neq h1
        simp [hcond, hv_admin]
      · refine ⟨u, hu_mem, ?_⟩
        show expectedHas s r u .admin = true
        unfold expectedHas
        have hcond : ¬ (u = r.target ∧ Role.admin = r.role) := by intro ⟨h1,h2⟩; exact hrA h2.symm
        simp [hcond, hu_admin]
  · have hvF : validb s r = false := by cases hb : validb s r <;> simp_all
    have hstep : step s r = (Outcome.rejected, s) := by unfold step; simp [hvF]
    rw [hstep]; simp only
    exact hex

end Grants
