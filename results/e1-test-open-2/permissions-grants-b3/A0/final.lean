import Grants.Spec
namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance

def otherAdminBool (s : State) (u : UserId) : Bool :=
  s.users.any (fun v => decide (v ≠ u) && s.has v .admin)

-- helper: for any Bool predicate, any = true iff exists
theorem otherAdminBool_true_iff (s : State) (u : UserId) :
    otherAdminBool s u = true ↔ OtherAdmin s u := by
  unfold otherAdminBool OtherAdmin
  rw [List.any_eq_true]
  constructor
  · intro h
    obtain ⟨v, hv_mem, hv_true⟩ := h
    have hv : decide (v ≠ u) && s.has v .admin = true := hv_true
    have h1 : decide (v ≠ u) = true := by
      cases d : decide (v ≠ u) with
      | true => rfl
      | false => simp [d] at hv
    have h2 : s.has v .admin = true := by simp [h1] at hv; exact hv
    exact ⟨v, hv_mem, of_decide_eq_true h1, h2⟩
  · intro h
    obtain ⟨v, hv_mem, hv_neq, hv_adm⟩ := h
    exact ⟨v, hv_mem, by simp [hv_neq, hv_adm]⟩

def validBool (s : State) (r : Request) : Bool :=
  decide (r.actor ∈ s.users) &&
  decide (r.target ∈ s.users) &&
  s.has r.actor .admin &&
  (match r.op with
   | .grant => decide (r.actor ≠ r.target) && decide (s.has r.target r.role = false)
   | .revoke => s.has r.target r.role && (if r.role == .admin then otherAdminBool s r.target else true))

theorem validBool_true_iff (s : State) (r : Request) :
    validBool s r = true ↔ ValidCommand s r := by
  unfold validBool ValidCommand
  constructor
  · intro h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have ha : r.actor ∈ s.users := of_decide_eq_true h1
    have ht : r.target ∈ s.users := of_decide_eq_true h2
    refine ⟨ha, ht, h3, ?_, ?_⟩
    · intro hgrant
      have h4g : (match (Op.grant : Op) with | .grant => decide (r.actor ≠ r.target) && decide (s.has r.target r.role = false) | .revoke => s.has r.target r.role && (if r.role == .admin then otherAdminBool s r.target else true)) = true := by rw [← hgrant]; exact h4
      simp only at h4g
      simpa [Bool.and_eq_true, decide_eq_true_eq] using h4g
    · intro hrev
      have h4r : (match (Op.revoke : Op) with | .grant => decide (r.actor ≠ r.target) && decide (s.has r.target r.role = false) | .revoke => s.has r.target r.role && (if r.role == .admin then otherAdminBool s r.target else true)) = true := by rw [← hrev]; exact h4
      simp only at h4r
      simp only [Bool.and_eq_true] at h4r
      obtain ⟨hhas, hother⟩ := h4r
      refine ⟨hhas, ?_⟩
      intro hrole
      have hroleB : (r.role == .admin) = true := by simp [hrole]
      have hother2 : otherAdminBool s r.target = true := by simp [hroleB] at hother; exact hother
      exact (otherAdminBool_true_iff s r.target).mp hother2
  · intro h
    obtain ⟨ha, ht, hadm, hg, hr⟩ := h
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨decide_eq_true ha, decide_eq_true ht⟩, hadm⟩, ?_⟩
    cases hop : r.op with
    | grant =>
      have hh := hg hop
      simp [hop, hh.1, hh.2]
    | revoke =>
      have hh := hr hop
      simp only [hop, Bool.and_eq_true, hh.1, true_and]
      by_cases hrole : r.role = .admin
      · have hbeq : (r.role == .admin) = true := by simp [hrole]
        simp [hbeq, (otherAdminBool_true_iff s r.target).mpr (hh.2 hrole)]
      · have hbeq : (r.role == .admin) = false := by
          cases hc : r.role with
          | admin => contradiction
          | editor => rfl
          | viewer => rfl
        simp [hbeq]

def step : Impl := fun s r =>
  match validBool s r with
  | true => (.ok, { users := s.users, has := expectedHas s r })
  | false => (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  show (step s r).1 = .ok
  unfold step
  have hv : validBool s r = true := (validBool_true_iff s r).mpr h
  simp [hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  show step s r = (.rejected, s)
  unfold step
  have hv : validBool s r = false := by
    cases hb : validBool s r with
    | true => exact absurd ((validBool_true_iff s r).mp hb) h
    | false => rfl
  simp [hv]

theorem req_authorization : AdminOnly step := by
  intro s r hok
  show r.actor ∈ s.users ∧ s.has r.actor .admin = true
  unfold step at hok
  by_cases hv : validBool s r = true
  · have hvc : ValidCommand s r := (validBool_true_iff s r).mp hv
    simp [hv] at hok; exact ⟨hvc.1, hvc.2.2.1⟩
  · simp [hv] at hok

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hgrant
  show r.actor ≠ r.target
  unfold step at hok
  by_cases hv : validBool s r = true
  · have hvc : ValidCommand s r := (validBool_true_iff s r).mp hv
    simp [hv] at hok; exact (hvc.2.2.2.1 hgrant).1
  · simp [hv] at hok

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hneq
  show (step s r).2.has u q = s.has u q
  unfold step at hok ⊢
  by_cases hv : validBool s r = true
  · simp [hv] at hok ⊢
    show expectedHas s r u q = s.has u q
    unfold expectedHas
    have hcond : ¬(u = r.target ∧ q = r.role) := by
      intro ⟨a, b⟩; rcases hneq with h1 | h2; exact h1 a; exact h2 b
    simp [hcond]
  · simp [hv] at hok

theorem req_effects : Effects step := by
  intro s r hok
  show (step s r).2.users = s.users ∧ ∀ u q, (step s r).2.has u q = expectedHas s r u q
  unfold step at hok ⊢
  by_cases hv : validBool s r = true
  · simp [hv] at hok ⊢
  · simp [hv] at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  show step (step s r).2 r = (.rejected, (step s r).2)
  unfold step at hok ⊢
  by_cases hv : validBool s r = true
  · simp [hv] at hok ⊢
    suffices validBool { users := s.users, has := expectedHas s r } r = false by simp [this]
    cases hb : validBool { users := s.users, has := expectedHas s r } r with
    | true =>
      have hvc2 : ValidCommand { users := s.users, has := expectedHas s r } r := (validBool_true_iff _ _).mp hb
      cases hop : r.op with
      | grant =>
        have hg2 := (hvc2.2.2.2.1 hop)
        have h1 : expectedHas s r r.target r.role = true := by unfold expectedHas; simp [hop]
        have h2 : expectedHas s r r.target r.role = false := hg2.2
        rw [h1] at h2; contradiction
      | revoke =>
        have hr2 := (hvc2.2.2.2.2 hop)
        have h1 : expectedHas s r r.target r.role = false := by unfold expectedHas; simp [hop]
        have h2 : expectedHas s r r.target r.role = true := hr2.1
        rw [h1] at h2; contradiction
    | false => rfl
  · simp [hv] at hok

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  show ∃ u ∈ (step s r).2.users, (step s r).2.has u .admin = true
  unfold step
  by_cases hv : validBool s r = true
  · simp [hv]
    have hvc : ValidCommand s r := (validBool_true_iff s r).mp hv
    cases hop : r.op with
    | grant =>
      obtain ⟨u, hu_mem, hu_admin⟩ := hex
      refine ⟨u, hu_mem, ?_⟩; unfold expectedHas
      by_cases heq : u = r.target ∧ Role.admin = r.role
      · obtain ⟨h1, h2⟩ := heq; subst h1; rw [← h2]; simp [hop]
      · simp [heq, hu_admin]
    | revoke =>
      by_cases hrole : r.role = .admin
      · have hother : OtherAdmin s r.target := (hvc.2.2.2.2 hop).2 hrole
        obtain ⟨v, hv_mem, hv_neq, hv_admin⟩ := hother
        refine ⟨v, hv_mem, ?_⟩; unfold expectedHas
        have hneq : ¬(v = r.target ∧ Role.admin = .admin) := by intro h; exact hv_neq h.1
        simp [hrole] at hneq ⊢; simp [hneq, hv_admin]
      · obtain ⟨u, hu_mem, hu_admin⟩ := hex
        refine ⟨u, hu_mem, ?_⟩; unfold expectedHas
        by_cases heq : u = r.target ∧ Role.admin = r.role
        · have : r.role = .admin := heq.2.symm; contradiction
        · simp [heq, hu_admin]
  · simp [hv]; exact hex

end Grants
