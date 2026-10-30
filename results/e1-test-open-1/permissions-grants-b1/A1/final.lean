import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance

def otherAdminBool (s : State) (u : UserId) : Bool :=
  s.users.any (fun v => v != u && s.has v .admin)

def validCommandBool (s : State) (r : Request) : Bool :=
  s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin &&
  match r.op with
  | .grant => (r.actor != r.target) && (!s.has r.target r.role)
  | .revoke => (s.has r.target r.role) && (decide (r.role != .admin) || otherAdminBool s r.target)

def step : Impl := fun s r =>
  if validCommandBool s r then
    (.ok, { users := s.users, has := fun u q => expectedHas s r u q })
  else
    (.rejected, s)

def dummy2 := 2
#check List.contains
#check List.any

def dummy_auth := 1

def foo_auth2 := 1

theorem and_true_imp_left' {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all

theorem and_true_imp_right' {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp_all

def bar_auth2 := 1

def tmp_auth2 := 1
#check List.contains_eq_mem

def test_lemmas_1 : Bool := true
#check List.any_eq_true
#check List.any_eq_false
#check List.contains_eq_mem -- maybe?

theorem test_any_true {α} (l : List α) (p : α → Bool) : l.any p = true ↔ ∃ x ∈ l, p x = true := by simp

theorem dummy_eq : (1 != 2) = true := by rfl
#check bne
#check bne_iff_ne
#check Ne
#check decide

theorem check_any2 : ∀ {α} (l : List α) (p : α → Bool), l.any p = true ↔ ∃ x ∈ l, p x = true := by
  intro α l p
  simp

theorem otherAdminBool_iff (s : State) (u : UserId) : otherAdminBool s u = true ↔ OtherAdmin s u := by
  unfold otherAdminBool OtherAdmin
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨v, hv_mem, hv_bool⟩
    have hv_ne : (v != u) = true := and_true_imp_left' hv_bool
    have hv_has : s.has v .admin = true := and_true_imp_right' hv_bool
    have hv_ne' : v ≠ u := by intro heq; simp [heq] at hv_ne
    exact ⟨v, hv_mem, hv_ne', hv_has⟩
  · rintro ⟨v, hv_mem, hv_ne, hv_has⟩
    refine ⟨v, hv_mem, ?_⟩
    have hv_ne_b : (v != u) = true := by simp [hv_ne]
    simp [hv_ne_b, hv_has]

theorem validCommandBool_of_ValidCommand_aux5 {s : State} {r : Request} (h : ValidCommand s r) : validCommandBool s r = true := by
  unfold ValidCommand at h
  obtain ⟨hA_mem, hT_mem, hA_admin, hGrant, hRevoke⟩ := h
  have hA_bool : s.users.contains r.actor = true := by simp [List.contains_eq_mem, hA_mem]
  have hT_bool : s.users.contains r.target = true := by simp [List.contains_eq_mem, hT_mem]
  unfold validCommandBool
  simp only [hA_bool, hT_bool, hA_admin, Bool.true_and]
  show (match r.op with | .grant => (r.actor != r.target) && (!s.has r.target r.role) | .revoke => s.has r.target r.role && (decide (r.role != Role.admin) || otherAdminBool s r.target)) = true
  cases hop : r.op
  · have hg := hGrant hop
    simp [hg.1, hg.2]
  · have hr := hRevoke hop
    have hhas : s.has r.target r.role = true := hr.1
    simp only [hhas, Bool.true_and]
    by_cases hrole : r.role = Role.admin
    · simp [hrole, (otherAdminBool_iff s r.target).mpr (hr.2 hrole)]
    · simp [hrole]

theorem validCommandBool_iff (s : State) (r : Request) : validCommandBool s r = true ↔ ValidCommand s r := by
  constructor
  · intro hv
    unfold validCommandBool at hv
    have hA_contains : s.users.contains r.actor = true := by
      revert hv; cases h1 : s.users.contains r.actor <;> cases h2 : s.users.contains r.target <;> cases h3 : s.has r.actor Role.admin <;> cases h4 : (match r.op with | .grant => (r.actor != r.target) && (!s.has r.target r.role) | .revoke => s.has r.target r.role && (decide (r.role != Role.admin) || otherAdminBool s r.target)) <;> simp_all
    have hT_contains : s.users.contains r.target = true := by
      revert hv; cases h1 : s.users.contains r.actor <;> cases h2 : s.users.contains r.target <;> cases h3 : s.has r.actor Role.admin <;> cases h4 : (match r.op with | .grant => (r.actor != r.target) && (!s.has r.target r.role) | .revoke => s.has r.target r.role && (decide (r.role != Role.admin) || otherAdminBool s r.target)) <;> simp_all
    have hA_admin : s.has r.actor Role.admin = true := by
      revert hv; cases h1 : s.users.contains r.actor <;> cases h2 : s.users.contains r.target <;> cases h3 : s.has r.actor Role.admin <;> cases h4 : (match r.op with | .grant => (r.actor != r.target) && (!s.has r.target r.role) | .revoke => s.has r.target r.role && (decide (r.role != Role.admin) || otherAdminBool s r.target)) <;> simp_all
    have hRest_true : (match r.op with | .grant => (r.actor != r.target) && (!s.has r.target r.role) | .revoke => s.has r.target r.role && (decide (r.role != Role.admin) || otherAdminBool s r.target)) = true := by
      revert hv; cases h1 : s.users.contains r.actor <;> cases h2 : s.users.contains r.target <;> cases h3 : s.has r.actor Role.admin <;> cases h4 : (match r.op with | .grant => (r.actor != r.target) && (!s.has r.target r.role) | .revoke => s.has r.target r.role && (decide (r.role != Role.admin) || otherAdminBool s r.target)) <;> simp_all
    have hA_mem : r.actor ∈ s.users := by
      have h : decide (r.actor ∈ s.users) = true := by
        have heq : s.users.contains r.actor = decide (r.actor ∈ s.users) := by simp
        rw [heq] at hA_contains; exact hA_contains
      exact of_decide_eq_true h
    have hT_mem : r.target ∈ s.users := by
      have h : decide (r.target ∈ s.users) = true := by
        have heq : s.users.contains r.target = decide (r.target ∈ s.users) := by simp
        rw [heq] at hT_contains; exact hT_contains
      exact of_decide_eq_true h
    refine ⟨hA_mem, hT_mem, hA_admin, ?_, ?_⟩
    · intro hop; rw [hop] at hRest_true
      have h1 : (r.actor != r.target) = true := and_true_imp_left' hRest_true
      have h2 : (!s.has r.target r.role) = true := and_true_imp_right' hRest_true
      have hNe : r.actor ≠ r.target := by intro heq; simp [heq] at h1
      have hNotHas : s.has r.target r.role = false := by cases hh : s.has r.target r.role <;> simp_all
      exact ⟨hNe, hNotHas⟩
    · intro hop; rw [hop] at hRest_true
      have hHas : s.has r.target r.role = true := and_true_imp_left' hRest_true
      have hOr : (decide (r.role != Role.admin) || otherAdminBool s r.target) = true := and_true_imp_right' hRest_true
      refine ⟨hHas, ?_⟩
      intro hrole; rw [hrole] at hOr
      simp at hOr
      exact (otherAdminBool_iff s r.target).mp hOr
  · exact validCommandBool_of_ValidCommand_aux5

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hV
  unfold step
  have hv : validCommandBool s r = true := validCommandBool_of_ValidCommand_aux5 hV
  simp [hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hNot
  unfold step
  have hv_false : validCommandBool s r = false := by
    cases hb : validCommandBool s r
    · rfl
    · exfalso; exact hNot ((validCommandBool_iff s r).mp hb)
  simp [hv_false]

theorem req_authorization   : AdminOnly step := by
  intro s r hOk
  unfold step at hOk
  by_cases hv : validCommandBool s r
  · unfold validCommandBool at hv
    have h1 : s.users.contains r.actor = true := by
      revert hv
      cases hca : s.users.contains r.actor <;> cases hct : s.users.contains r.target <;> cases ha : s.has r.actor Role.admin <;> cases hrest : (match r.op with | .grant => (r.actor != r.target) && (!s.has r.target r.role) | .revoke => s.has r.target r.role && (decide (r.role != Role.admin) || otherAdminBool s r.target)) <;> simp_all
    have h2 : s.has r.actor Role.admin = true := by
      revert hv
      cases hca : s.users.contains r.actor <;> cases hct : s.users.contains r.target <;> cases ha : s.has r.actor Role.admin <;> cases hrest : (match r.op with | .grant => (r.actor != r.target) && (!s.has r.target r.role) | .revoke => s.has r.target r.role && (decide (r.role != Role.admin) || otherAdminBool s r.target)) <;> simp_all
    constructor
    · rw [List.contains_eq_mem] at h1; exact of_decide_eq_true h1
    · exact h2
  · have hEq : (if validCommandBool s r then (Outcome.ok : Outcome) else .rejected) = .rejected := by simp [hv]
    have hProj : (if validCommandBool s r then (Outcome.ok, { users := s.users, has := fun u q => expectedHas s r u q }) else ((Outcome.rejected, s) : Outcome × State)).1 = (if validCommandBool s r then (Outcome.ok : Outcome) else .rejected) := by
      by_cases hv2 : validCommandBool s r <;> simp [hv2]
    rw [hProj] at hOk
    rw [hEq] at hOk
    simp at hOk

theorem req_no_self_grant   : NoSelfGrant step := by
  intro s r hOk hGrant
  unfold step at hOk
  by_cases hv : validCommandBool s r
  · unfold validCommandBool at hv
    rw [hGrant] at hv
    -- hv : (contains actor && contains target && has admin && ((actor != target) && !has...)) = true
    -- Use helper lemmas to extract
    have hRest : ((r.actor != r.target) && (!s.has r.target r.role)) = true := by
      -- need to extract rightmost conjunct after 3 associates
      -- Let's do brute case analysis on bools
      revert hv
      cases h1 : s.users.contains r.actor <;> cases h2 : s.users.contains r.target <;> cases h3 : s.has r.actor .admin <;> cases h4 : (r.actor != r.target) <;> cases h5 : (!s.has r.target r.role) <;> simp
    have hNeBool : (r.actor != r.target) = true := and_true_imp_left' hRest
    intro hEq
    simp [hEq] at hNeBool
  · have hEq : (if validCommandBool s r then (Outcome.ok : Outcome) else .rejected) = .rejected := by simp [hv]
    have hProj : (if validCommandBool s r then (Outcome.ok, { users := s.users, has := fun u q => expectedHas s r u q }) else ((Outcome.rejected, s) : Outcome × State)).1 = (if validCommandBool s r then (Outcome.ok : Outcome) else .rejected) := by
      by_cases hv2 : validCommandBool s r <;> simp [hv2]
    rw [hProj] at hOk
    rw [hEq] at hOk
    simp at hOk

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hOk u q hNe
  unfold step at hOk ⊢
  by_cases hv : validCommandBool s r = true
  · simp [hv] at hOk ⊢
    unfold expectedHas
    have hNot : ¬ (u = r.target ∧ q = r.role) := by
      intro hC
      rcases hNe with h | h
      · exact h hC.1
      · exact h hC.2
    simp [hNot]
  · simp [hv] at hOk

theorem req_effects : Effects step := by
  intro s r hOk
  unfold step at hOk ⊢
  by_cases hv : validCommandBool s r
  · simp [hv] at hOk ⊢
  · simp [hv] at hOk

theorem req_idempotency : Idempotent step := by
  intro s r hOk
  unfold step at hOk ⊢
  by_cases hv : validCommandBool s r
  · simp only [hv, ite_true] at hOk ⊢
    have hv2 : validCommandBool { users := s.users, has := fun u q => expectedHas s r u q } r = false := by
        unfold validCommandBool
        cases hop : r.op
        · have hHas' : (fun u q => expectedHas s r u q) r.target r.role = true := by
            unfold expectedHas
            rw [hop]; simp
          simp [hHas']
        · have hHas' : (fun u q => expectedHas s r u q) r.target r.role = false := by
            unfold expectedHas
            rw [hop]; simp
          simp [hHas']
    simp [hv2]
  · simp [hv] at hOk

theorem req_last_admin      : KeepsAdmin step := by
  intro s r hExists
  unfold step
  by_cases hv : validCommandBool s r
  · simp only [hv, ite_true]
    obtain ⟨w, hw_mem, hw_admin⟩ := hExists
    cases hop : r.op
    · have hNewAdminW : (expectedHas s r w .admin) = true := by
        unfold expectedHas
        by_cases heq : w = r.target ∧ (Role.admin = r.role)
        · have h1 : decide (r.op = .grant) = true := by simp [hop]
          simp [heq.1, heq.2, h1]
        · simp [heq, hw_admin]
      exact ⟨w, hw_mem, hNewAdminW⟩
    · by_cases hrole : r.role = .admin
      · have hOther : otherAdminBool s r.target = true := by
          revert hv
          simp [validCommandBool, hop, hrole]
        have hOtherProp : OtherAdmin s r.target := (otherAdminBool_iff s r.target).mp hOther
        obtain ⟨v, hv_mem, hv_ne, hv_has⟩ := hOtherProp
        have hNewAdminV : (expectedHas s r v .admin) = true := by
          unfold expectedHas
          have hneq : ¬ (v = r.target ∧ (Role.admin = r.role)) := by
            intro ⟨heq, _⟩
            exact hv_ne heq
          simp [hneq, hv_has]
        exact ⟨v, hv_mem, hNewAdminV⟩
      · have hNewAdminW : (expectedHas s r w .admin) = true := by
          unfold expectedHas
          by_cases heq : w = r.target ∧ (Role.admin = r.role)
          · exfalso; exact hrole heq.2.symm
          · simp [heq, hw_admin]
        exact ⟨w, hw_mem, hNewAdminW⟩
  · simp only [hv]
    exact hExists

end Grants
