import Grants.Spec
namespace Grants

def otherAdminb (s : State) (u : UserId) : Bool :=
  s.users.any (fun v => decide (v ≠ u) && s.has v .admin)

def validb (s : State) (r : Request) : Bool :=
  s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin &&
  (match r.op with
   | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
   | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target))

def step : Impl := fun s r =>
  if validb s r then
    (.ok, { users := s.users, has := fun u q => expectedHas s r u q })
  else
    (.rejected, s)

theorem contains_mem_test2 (l : List Nat) (x : Nat) : l.contains x = true ↔ x ∈ l := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp_all

theorem otherAdminb_true_iff (s : State) (u : UserId) :
    otherAdminb s u = true ↔ OtherAdmin s u := by
  unfold otherAdminb OtherAdmin
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨v, hv_mem, hv_cond⟩ := h
    simp at hv_cond
    obtain ⟨hne, hhas⟩ := hv_cond
    exact ⟨v, hv_mem, hne, hhas⟩
  · rintro ⟨v, hv_mem, hne, hhas⟩
    rw [List.any_eq_true]
    exact ⟨v, hv_mem, by simp [hne, hhas]⟩

theorem validb_true_iff_aux1 (a b c d : Bool) :
    ((a && b && c && d) = true) ↔ (a = true ∧ b = true ∧ c = true ∧ d = true) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp

theorem validb_true_iff_aux2 (a b : Bool) :
    ((a && b) = true) ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

theorem validb_true_iff_aux3 (a b : Bool) :
    ((a || b) = true) ↔ (a = true ∨ b = true) := by
  cases a <;> cases b <;> simp

theorem probe_decide1 (a b : Nat) (h : decide (a ≠ b) = true) : a ≠ b := by
  exact of_decide_eq_true h

theorem probe_bool_or (a b : Bool) : ((a || b) = true) ↔ (a = true ∨ b = true) := by
  cases a <;> cases b <;> simp

theorem probe_decide_ne (r : Request) : decide (r.role ≠ .admin) = true ↔ r.role ≠ .admin := by
  simp

theorem probe_other (s : State) (u : UserId) : otherAdminb s u = true ↔ OtherAdmin s u :=
  otherAdminb_true_iff s u

theorem revoke_or_iff3 (s : State) (r : Request) :
    ((decide (r.role ≠ .admin) || otherAdminb s r.target) = true ↔
    (r.role = .admin → OtherAdmin s r.target)) := by
  constructor
  · intro h heq
    have h1 : decide (r.role ≠ .admin) = true ∨ otherAdminb s r.target = true := by
      rw [← probe_bool_or]
      exact h
    cases h1 with
    | inl hl =>
      rw [probe_decide_ne] at hl
      exact absurd heq hl
    | inr hr =>
      rw [otherAdminb_true_iff] at hr
      exact hr
  · intro h
    have h2 : decide (r.role ≠ .admin) = true ∨ otherAdminb s r.target = true := by
      by_cases heq : r.role = .admin
      · have ho : OtherAdmin s r.target := h heq
        have hob : otherAdminb s r.target = true := (otherAdminb_true_iff s r.target).mpr ho
        exact Or.inr hob
      · have hd : decide (r.role ≠ .admin) = true := by simp [heq]
        exact Or.inl hd
    rw [← probe_bool_or] at h2
    exact h2

theorem grant_part_iff3 (s : State) (r : Request) :
    ((decide (r.actor ≠ r.target) && !(s.has r.target r.role)) = true ↔
    (r.actor ≠ r.target ∧ s.has r.target r.role = false)) := by
  constructor
  · intro h
    have h2 : decide (r.actor ≠ r.target) = true ∧ (!(s.has r.target r.role)) = true := by
      have hh := (validb_true_iff_aux2 _ _).mp h
      exact hh
    obtain ⟨h1, h2⟩ := h2
    have ha : r.actor ≠ r.target := of_decide_eq_true h1
    have hb : s.has r.target r.role = false := by
      cases hs : s.has r.target r.role
      · rfl
      · simp [hs] at h2
    exact ⟨ha, hb⟩
  · rintro ⟨h1, h2⟩
    have e1 : decide (r.actor ≠ r.target) = true := by simp [h1]
    have e2 : (!(s.has r.target r.role)) = true := by simp [h2]
    exact (validb_true_iff_aux2 _ _).mpr ⟨e1, e2⟩

theorem tmp_explore : True := by trivial
#check (validb_true_iff_aux1)
#check contains_mem_test2

theorem tmp_unfold_test (s : State) (r : Request) (hv : validb s r = true) : s.users.contains r.actor = true := by
  have h : validb s r = (s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin &&
  (match r.op with
   | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
   | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target))) := by
    rfl
  rw [h] at hv
  cases hop : r.op
  · rw [hop] at hv
    simp only at hv
    exact (validb_true_iff_aux1 _ _ _ _).mp hv |>.1
  · rw [hop] at hv
    simp only at hv
    exact (validb_true_iff_aux1 _ _ _ _).mp hv |>.1

theorem tmp_step_ok_validb (s : State) (r : Request) (h : (step s r).1 = .ok) : validb s r = true := by
  unfold step at h
  by_cases hv : validb s r = true
  · exact hv
  · simp [hv] at h

theorem tmp_actor_admin (s : State) (r : Request) (hv : validb s r = true) : r.actor ∈ s.users ∧ s.has r.actor .admin = true := by
  have h : validb s r = (s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin &&
  (match r.op with
   | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
   | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target))) := by
    rfl
  rw [h] at hv
  cases hop : r.op
  · rw [hop] at hv
    simp only at hv
    obtain ⟨a1, a2, a3, a4⟩ := (validb_true_iff_aux1 _ _ _ _).mp hv
    exact ⟨(contains_mem_test2 _ _).mp a1, a3⟩
  · rw [hop] at hv
    simp only at hv
    obtain ⟨a1, a2, a3, a4⟩ := (validb_true_iff_aux1 _ _ _ _).mp hv
    exact ⟨(contains_mem_test2 _ _).mp a1, a3⟩

theorem helper_others_proof3 : OthersUnchanged step := by
  intro s r hok u q hcond
  have hv : validb s r = true := tmp_step_ok_validb s r hok
  unfold step at hok ⊢
  simp only [hv, ↓reduceIte] at hok ⊢
  show expectedHas s r u q = s.has u q
  unfold expectedHas
  have hneg : ¬ (u = r.target ∧ q = r.role) := by
    rcases hcond with h | h
    · intro hcon; exact h hcon.1
    · intro hcon; exact h hcon.2
  simp only [if_neg hneg]

theorem idem_expected_self (s : State) (r : Request) :
    expectedHas s r r.target r.role = decide (r.op = .grant) := by
  unfold expectedHas
  simp

theorem idem_probe1 (s : State) (r : Request) :
    (({ users := s.users, has := fun u q => expectedHas s r u q } : State).users.contains r.actor) = (s.users.contains r.actor) := by
  simp only

theorem idem_probe2 (s : State) (r : Request) (u : UserId) (q : Role) :
    (({ users := s.users, has := fun u q => expectedHas s r u q } : State).has u q) = (expectedHas s r u q) := by
  simp only

theorem idem_hexp_grant (s : State) (r : Request) (hop : r.op = .grant) :
    expectedHas s r r.target r.role = true := by
  rw [idem_expected_self, hop]
  simp

theorem idem_hexp_revoke (s : State) (r : Request) (hop : r.op = .revoke) :
    expectedHas s r r.target r.role = false := by
  rw [idem_expected_self, hop]
  simp

theorem idem_step_unfold_probe (s : State) (r : Request) (h : validb s r = false) :
    (step s r) = (.rejected, s) := by
  unfold step
  simp [h]

theorem idem_validb_s2_eq (s : State) (r : Request) :
    validb ({ users := s.users, has := fun u q => expectedHas s r u q } : State) r =
    (s.users.contains r.actor && s.users.contains r.target && expectedHas s r r.actor .admin &&
    (match r.op with
     | .grant => decide (r.actor ≠ r.target) && !(expectedHas s r r.target r.role)
     | .revoke => expectedHas s r r.target r.role && (decide (r.role ≠ .admin) || otherAdminb ({ users := s.users, has := fun u q => expectedHas s r u q } : State) r.target))) := by
  rfl

theorem idem_s2_false_grant (s : State) (r : Request) (hop : r.op = .grant) :
    validb ({ users := s.users, has := fun u q => expectedHas s r u q } : State) r = false := by
  rw [idem_validb_s2_eq]
  rw [hop]
  simp only
  have hexp : expectedHas s r r.target r.role = true := idem_hexp_grant s r hop
  rw [hexp]
  simp

theorem idem_s2_false_revoke (s : State) (r : Request) (hop : r.op = .revoke) :
    validb ({ users := s.users, has := fun u q => expectedHas s r u q } : State) r = false := by
  rw [idem_validb_s2_eq]
  rw [hop]
  simp only
  have hexp : expectedHas s r r.target r.role = false := idem_hexp_revoke s r hop
  rw [hexp]
  simp

theorem idem_s2_eq_test (s : State) (r : Request) (hv : validb s r = true) :
    (step s r).2 = ({ users := s.users, has := fun u q => expectedHas s r u q } : State) := by
  unfold step
  simp [hv]

theorem keepsAdmin_target_mem (s : State) (r : Request) (hvc : validb s r = true) : r.target ∈ s.users := by
  unfold validb at hvc
  cases hop : r.op with
  | grant =>
    rw [hop] at hvc
    simp only at hvc
    obtain ⟨_, h2, _, _⟩ := (validb_true_iff_aux1 _ _ _ _).mp hvc
    exact (contains_mem_test2 _ _).mp h2
  | revoke =>
    rw [hop] at hvc
    simp only at hvc
    obtain ⟨_, h2, _, _⟩ := (validb_true_iff_aux1 _ _ _ _).mp hvc
    exact (contains_mem_test2 _ _).mp h2

theorem keepsAdmin_other_of_revoke_admin (s : State) (r : Request) (hvc : validb s r = true) (hop : r.op = .revoke) (hrole : r.role = .admin) : OtherAdmin s r.target := by
  unfold validb at hvc
  rw [hop] at hvc
  simp only at hvc
  obtain ⟨_, _, _, h4⟩ := (validb_true_iff_aux1 _ _ _ _).mp hvc
  obtain ⟨_, hor⟩ := (validb_true_iff_aux2 _ _).mp h4
  have hdec : decide (r.role ≠ .admin) = false := by simp [hrole]
  have hdisj : decide (r.role ≠ .admin) = true ∨ otherAdminb s r.target = true := (validb_true_iff_aux3 _ _).mp hor
  cases hdisj with
  | inl hl => rw [hdec] at hl; contradiction
  | inr hr => exact (otherAdminb_true_iff s r.target).mp hr

theorem keepsAdmin_expected_old_of_ne_role (s : State) (r : Request) (u : UserId) (hrole : r.role ≠ .admin) : expectedHas s r u .admin = s.has u .admin := by
  unfold expectedHas
  have hneg : ¬ (u = r.target ∧ (.admin : Role) = r.role) := by
    intro hcon
    exact hrole hcon.2.symm
  simp [hneg]

theorem keepsAdmin_expected_old_of_ne_target (s : State) (r : Request) (v : UserId) (hne : v ≠ r.target) (q : Role) : expectedHas s r v q = s.has v q := by
  unfold expectedHas
  have hneg : ¬ (v = r.target ∧ q = r.role) := by
    intro hcon
    exact hne hcon.1
  simp [hneg]

theorem keepsAdmin_expected_target_admin_grant (s : State) (r : Request) (hop : r.op = .grant) (hrole : r.role = .admin) : expectedHas s r r.target .admin = true := by
  unfold expectedHas
  have hcond : (r.target = r.target ∧ (.admin : Role) = r.role) := by simp [hrole]
  simp [hcond, hop]

theorem req_valid_succeeds_aux2 : ValidSucceeds step := by
  intro s r hV
  unfold ValidCommand at hV
  obtain ⟨hAmem, hTmem, hAadm, hG, hR⟩ := hV
  have h1 : s.users.contains r.actor = true := (contains_mem_test2 _ _).mpr hAmem
  have h2 : s.users.contains r.target = true := (contains_mem_test2 _ _).mpr hTmem
  have h4 : (match r.op with
   | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
   | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target)) = true := by
    cases hOp : r.op
    · have hg := hG hOp
      simpa [hOp] using (grant_part_iff3 s r).mpr hg
    · have hr := hR hOp
      obtain ⟨hHas, hAdm⟩ := hr
      have e1 : s.has r.target r.role = true := hHas
      have e2 : (decide (r.role ≠ .admin) || otherAdminb s r.target) = true := (revoke_or_iff3 s r).mpr hAdm
      simpa [hOp] using (validb_true_iff_aux2 _ _).mpr ⟨e1, e2⟩
  have hv : validb s r = true := by
    have h := (validb_true_iff_aux1 _ _ _ _).mpr ⟨h1, h2, hAadm, h4⟩
    -- need to connect h to validb; validb unfolds to same expression
    have heq : validb s r = (s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin &&
    (match r.op with
     | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
     | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target))) := rfl
    rw [heq]
    exact h
  unfold step
  simp [hv]

theorem validb_iff_aux_ok (s : State) (r : Request) :
    validb s r = true ↔ ValidCommand s r := by
  constructor
  · intro h
    have h0 : (s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin &&
      (match r.op with
       | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
       | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target))) = true := h
    obtain ⟨a1, a2, a3, d⟩ := (validb_true_iff_aux1 _ _ _ _).mp h0
    have hm1 : r.actor ∈ s.users := (contains_mem_test2 _ _).mp a1
    have hm2 : r.target ∈ s.users := (contains_mem_test2 _ _).mp a2
    refine ⟨hm1, hm2, a3, ?_, ?_⟩
    · intro hgr
      have dGr : (match (Op.grant : Op) with
          | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
          | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target)) = true :=
        hgr ▸ d
      have dGr2 : (decide (r.actor ≠ r.target) && !(s.has r.target r.role)) = true := dGr
      exact (grant_part_iff3 s r).mp dGr2
    · intro hrev
      have dRev : (match (Op.revoke : Op) with
          | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
          | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target)) = true :=
        hrev ▸ d
      have dRev2 : (s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target)) = true := dRev
      obtain ⟨e1, e2⟩ := (validb_true_iff_aux2 _ _).mp dRev2
      exact ⟨e1, (revoke_or_iff3 s r).mp e2⟩
  · rintro ⟨hAmem, hTmem, hAadm, hG, hR⟩
    have h1 : s.users.contains r.actor = true := (contains_mem_test2 _ _).mpr hAmem
    have h2 : s.users.contains r.target = true := (contains_mem_test2 _ _).mpr hTmem
    have h01 : (s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin &&
      (match r.op with
       | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
       | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target))) = true := by
      apply (validb_true_iff_aux1 _ _ _ _).mpr
      refine ⟨h1, h2, hAadm, ?_⟩
      cases hOp : r.op
      · have hg := hG hOp
        simpa [hOp] using (grant_part_iff3 s r).mpr hg
      · have hr := hR hOp
        obtain ⟨hHas, hAdm⟩ := hr
        have e2 : (decide (r.role ≠ .admin) || otherAdminb s r.target) = true :=
          (revoke_or_iff3 s r).mpr hAdm
        have h4 : (s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target)) = true :=
          (validb_true_iff_aux2 _ _).mpr ⟨hHas, e2⟩
        simpa [hOp] using h4
    exact h01

theorem req_valid_succeeds  : ValidSucceeds step := by
  intro s r hV
  unfold ValidCommand at hV
  obtain ⟨hAmem, hTmem, hAadm, hG, hR⟩ := hV
  have h1 : s.users.contains r.actor = true := (contains_mem_test2 _ _).mpr hAmem
  have h2 : s.users.contains r.target = true := (contains_mem_test2 _ _).mpr hTmem
  have h4 : (match r.op with
   | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
   | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target)) = true := by
    cases hOp : r.op
    · have hg := hG hOp
      simpa [hOp] using (grant_part_iff3 s r).mpr hg
    · have hr := hR hOp
      obtain ⟨hHas, hAdm⟩ := hr
      have e1 : s.has r.target r.role = true := hHas
      have e2 : (decide (r.role ≠ .admin) || otherAdminb s r.target) = true := (revoke_or_iff3 s r).mpr hAdm
      simpa [hOp] using (validb_true_iff_aux2 _ _).mpr ⟨e1, e2⟩
  have hv : validb s r = true := by
    have h := (validb_true_iff_aux1 _ _ _ _).mpr ⟨h1, h2, hAadm, h4⟩
    have heq : validb s r = (s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin &&
    (match r.op with
     | .grant => decide (r.actor ≠ r.target) && !(s.has r.target r.role)
     | .revoke => s.has r.target r.role && (decide (r.role ≠ .admin) || otherAdminb s r.target))) := rfl
    rw [heq]
    exact h
  unfold step
  simp [hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hN
  have hv : validb s r = false := by
    cases hb : validb s r with
    | true => exact absurd ((validb_iff_aux_ok s r).mp hb) hN
    | false => rfl
  unfold step
  simp [hv]

theorem req_authorization : AdminOnly step := by
  intro s r h
  exact tmp_actor_admin s r (tmp_step_ok_validb s r h)

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r hok hop
  have hv := tmp_step_ok_validb s r hok
  unfold validb at hv
  rw [hop] at hv
  simp only at hv
  obtain ⟨_, _, _, hg⟩ := (validb_true_iff_aux1 _ _ _ _).mp hv
  exact ((grant_part_iff3 s r).mp hg).1

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r hok u q hcond
  have hv : validb s r = true := tmp_step_ok_validb s r hok
  unfold step at hok ⊢
  simp only [hv, ↓reduceIte] at hok ⊢
  show expectedHas s r u q = s.has u q
  unfold expectedHas
  have hneg : ¬ (u = r.target ∧ q = r.role) := by
    rcases hcond with h | h
    · intro hcon; exact h hcon.1
    · intro hcon; exact h hcon.2
  simp only [if_neg hneg]

theorem req_effects : Effects step := by
  intro s r hok
  have hv : validb s r = true := tmp_step_ok_validb s r hok
  unfold step
  simp only [hv, ↓reduceIte]
  exact ⟨trivial, fun _ _ => trivial⟩

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv : validb s r = true := tmp_step_ok_validb s r hok
  have h2eq : (step s r).2 = ({ users := s.users, has := fun u q => expectedHas s r u q } : State) :=
    idem_s2_eq_test s r hv
  cases hop : r.op with
  | grant =>
    have hf : validb (step s r).2 r = false := by
      rw [h2eq]
      exact idem_s2_false_grant s r hop
    have hs : step (step s r).2 r = (.rejected, (step s r).2) :=
      idem_step_unfold_probe _ _ hf
    exact hs
  | revoke =>
    have hf : validb (step s r).2 r = false := by
      rw [h2eq]
      exact idem_s2_false_revoke s r hop
    have hs : step (step s r).2 r = (.rejected, (step s r).2) :=
      idem_step_unfold_probe _ _ hf
    exact hs

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  obtain ⟨w, hw_mem, hw_has⟩ := hex
  cases hvc : validb s r with
  | true =>
    have hstep2 : (step s r).2 = ({ users := s.users, has := fun u q => expectedHas s r u q } : State) := by
      unfold step
      simp [hvc]
    rw [hstep2]
    simp only
    cases hop : r.op with
    | grant =>
      by_cases hrole : r.role = .admin
      · have htmem : r.target ∈ s.users := keepsAdmin_target_mem s r hvc
        have hexpt : expectedHas s r r.target .admin = true := keepsAdmin_expected_target_admin_grant s r hop hrole
        exact ⟨r.target, htmem, hexpt⟩
      · have hexpw : expectedHas s r w .admin = s.has w .admin := keepsAdmin_expected_old_of_ne_role s r w hrole
        have hw' : expectedHas s r w .admin = true := by rw [hexpw, hw_has]
        exact ⟨w, hw_mem, hw'⟩
    | revoke =>
      by_cases hrole : r.role = .admin
      · have hOA := keepsAdmin_other_of_revoke_admin s r hvc hop hrole
        obtain ⟨v, hv_mem, hv_ne, hv_has⟩ := hOA
        have hexp : expectedHas s r v .admin = s.has v .admin := keepsAdmin_expected_old_of_ne_target s r v hv_ne .admin
        have hv' : expectedHas s r v .admin = true := by rw [hexp, hv_has]
        exact ⟨v, hv_mem, hv'⟩
      · have hexpw : expectedHas s r w .admin = s.has w .admin := keepsAdmin_expected_old_of_ne_role s r w hrole
        have hw' : expectedHas s r w .admin = true := by rw [hexpw, hw_has]
        exact ⟨w, hw_mem, hw'⟩
  | false =>
    have hstep2 : (step s r).2 = s := by
      unfold step
      simp [hvc]
    rw [hstep2]
    exact ⟨w, hw_mem, hw_has⟩

end Grants
