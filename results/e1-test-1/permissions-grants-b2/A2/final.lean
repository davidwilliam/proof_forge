import Grants.Spec
namespace Grants
instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance
def isAdmin (s : State) (u : UserId) : Bool := s.users.contains u && s.has u .admin
def hasOtherAdmin (s : State) (u : UserId) : Bool :=
  s.users.any (fun v => v != u && s.has v .admin)
def step : Impl := fun s r =>
  if !(s.users.contains r.actor && s.users.contains r.target) then (.rejected, s) else
  match r.op with
  | .grant =>
    if isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role then
      (.ok, { users := s.users, has := fun u q => if u == r.target && q == r.role then true else s.has u q })
    else (.rejected, s)
  | .revoke =>
    if isAdmin s r.actor && s.has r.target r.role &&
        (r.role != .admin || hasOtherAdmin s r.target) then
      (.ok, { users := s.users, has := fun u q => if u == r.target && q == r.role then false else s.has u q })
    else (.rejected, s)

def fooTest := 1

theorem fooThm : True := trivial

theorem mem_contains_test2 (s : State) (x : UserId) : (s.users.contains x = true) ↔ x ∈ s.users := by
  rw [List.contains_eq_mem]
  simp

theorem isAdmin_eq_true (s : State) (u : UserId) : (isAdmin s u = true) ↔ (u ∈ s.users ∧ s.has u .admin = true) := by
  unfold isAdmin
  rw [Bool.and_eq_true]
  rw [mem_contains_test2]

theorem auth_probe (s : State) (r : Request) (h : (step s r).1 = .ok)
    (hc : (!(s.users.contains r.actor && s.users.contains r.target)) = true) : False := by
  simp only [step] at h
  rw [if_pos hc] at h
  simp at h

theorem auth_mem_true (s : State) (r : Request) (h : (step s r).1 = .ok) :
    (s.users.contains r.actor && s.users.contains r.target) = true := by
  by_cases hb : (s.users.contains r.actor && s.users.contains r.target) = true
  · exact hb
  · have hneg : (!(s.users.contains r.actor && s.users.contains r.target)) = true := by
      simp only [hb, Bool.not_false]
    exact (auth_probe s r h hneg).elim

theorem tmp_no_self_grant_aux : True := by
  trivial
#check (inferInstance : BEq Nat)
#check (@beq_iff_eq Nat _ _ _)

theorem tmp_check_auth_type (s : State) (r : Request) (h : (step s r).1 = .ok) : (s.users.contains r.actor && s.users.contains r.target) = true :=
  auth_mem_true s r h

theorem probe_beq1 (u v : Nat) (h : u = v) : (u == v) = true := by simp [h]

theorem probe_beq2 (u v : Nat) (h : u ≠ v) : (u == v) = false := by simp [h]

theorem probe_beq3 (q r : Role) (h : q = r) : (q == r) = true := by simp [h]

theorem probe_beq4 (q r : Role) (h : q ≠ r) : (q == r) = false := by simp [h]

theorem probe_eq_iffA (u v : Nat) : ((u == v) = true) ↔ (u = v) :=
  beq_iff_eq

theorem probe_eq_iffB (q r2 : Role) : ((q == r2) = true) ↔ (q = r2) :=
  beq_iff_eq

theorem fx_and_beq_true (u t : Nat) (q r : Role) :
    ((u == t && q == r) = true) ↔ (u = t ∧ q = r) := by
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]

theorem idem_probe1 (s : State) (r : Request) (h : (step s r).1 = .ok) :
    (s.users.contains r.actor && s.users.contains r.target) = true :=
  auth_mem_true s r h

#check List.contains_eq_mem
#check beq_iff_eq

theorem ok_mem_bool (s : State) (r : Request) (h : (step s r).1 = .ok) :
    (!(s.users.contains r.actor && s.users.contains r.target)) = false := by
  by_cases hb : (!(s.users.contains r.actor && s.users.contains r.target)) = true
  · have : (step s r).1 = .rejected := by simp only [step, hb, if_pos]
    rw [this] at h
    contradiction
  · simp at hb ⊢
    exact hb

theorem step_users_eq_all3 (s : State) (r : Request) :
    (step s r).2.users = s.users := by
  unfold step
  split
  · rfl
  · split
    · split
      · rfl
      · rfl
    · split
      · rfl
      · rfl

theorem probe_bne3 (a b : Nat) (h : (a != b) = true) : a ≠ b := by
  intro heq
  subst heq
  simp at h

theorem probe_bne4 (a b : Nat) (h : a ≠ b) : (a != b) = true := by
  simp [h]

theorem probe_bne5 (a : Nat) : (a != a) = false := by simp

theorem probe_role_bne1 (q : Role) (h : (q != .admin) = true) : q ≠ .admin := by
  intro heq
  subst heq
  simp at h

theorem probe_role_bne2 (q : Role) (h : q ≠ .admin) : (q != .admin) = true := by
  simp [h]

theorem hasOtherAdmin_exists2 (s : State) (u : UserId) (h : hasOtherAdmin s u = true) :
    ∃ v ∈ s.users, v ≠ u ∧ s.has v .admin = true := by
  unfold hasOtherAdmin at h
  rw [List.any_eq_true] at h
  obtain ⟨v, hmem, hv⟩ := h
  rw [Bool.and_eq_true] at hv
  obtain ⟨hne, hadm⟩ := hv
  exact ⟨v, hmem, probe_bne3 v u hne, hadm⟩

theorem hasOtherAdmin_of_OtherAdmin (s : State) (u : UserId)
    (h : OtherAdmin s u) : hasOtherAdmin s u = true := by
  unfold OtherAdmin at h
  unfold hasOtherAdmin
  rw [List.any_eq_true]
  obtain ⟨v, hmem, hne, hadm⟩ := h
  exact ⟨v, hmem, by rw [Bool.and_eq_true]; exact ⟨probe_bne4 v u hne, hadm⟩⟩

theorem vcb_aux (a b : Bool) (ha : a = true) (hb : b = true) : (a && b) = true := by
  simp [ha, hb]

theorem valid_contains_rw3 (s : State) (r : Request) (ha : r.actor ∈ s.users) (ht : r.target ∈ s.users) :
    (s.users.contains r.actor && s.users.contains r.target) = true := by
  have h1 : s.users.contains r.actor = true := (mem_contains_test2 s r.actor).mpr ha
  have h2 : s.users.contains r.target = true := (mem_contains_test2 s r.target).mpr ht
  rw [h1, h2, Bool.and_self]



theorem plan0_valid_isAdmin (s : State) (r : Request) (h : ValidCommand s r) :
    isAdmin s r.actor = true := by
  rw [isAdmin_eq_true]
  unfold ValidCommand at h
  obtain ⟨ha, _, hadm, _, _⟩ := h
  exact ⟨ha, hadm⟩






theorem plan0_valid_revoke_extra (s : State) (r : Request) (h : ValidCommand s r)
    (hop : r.op = .revoke) :
    (s.has r.target r.role && (r.role != .admin || hasOtherAdmin s r.target)) = true := by
  unfold ValidCommand at h
  obtain ⟨ha, ht, hadm, hgrant, hrev⟩ := h
  have hr := hrev hop
  obtain ⟨hhas, hoth⟩ := hr
  have h2 : (r.role != .admin || hasOtherAdmin s r.target) = true := by
    by_cases hrole : r.role = .admin
    · have ho : OtherAdmin s r.target := hoth hrole
      have hb : hasOtherAdmin s r.target = true := hasOtherAdmin_of_OtherAdmin s r.target ho
      simp [hb]
    · have hbne : (r.role != .admin) = true := probe_role_bne2 r.role hrole
      simp [hbne]
  simp [hhas, h2]


theorem plan0_valid_contains (s : State) (r : Request) (h : ValidCommand s r) :
    (s.users.contains r.actor && s.users.contains r.target) = true := by
  unfold ValidCommand at h
  obtain ⟨ha, ht, _, _, _⟩ := h
  exact valid_contains_rw3 s r ha ht

theorem plan0_valid_isAdmin_proof : True := trivial
#check @plan0_valid_isAdmin
#check @isAdmin_eq_true

theorem plan0_valid_isAdmin_check (s : State) (r : Request) (h : ValidCommand s r) :
    isAdmin s r.actor = true := by
  rw [isAdmin_eq_true]
  unfold ValidCommand at h
  obtain ⟨ha, _, hadm, _, _⟩ := h
  exact ⟨ha, hadm⟩

theorem plan0_hasOtherAdmin_of_otherAdmin_aux (s : State) (u : UserId)
    (h : OtherAdmin s u) : hasOtherAdmin s u = true :=
  hasOtherAdmin_of_OtherAdmin s u h

theorem plan0_hasOtherAdmin_of_otherAdmin (s : State) (u : UserId)
    (h : OtherAdmin s u) : hasOtherAdmin s u = true :=
  hasOtherAdmin_of_OtherAdmin s u h

theorem plan0_valid_grant_extra (s : State) (r : Request) (h : ValidCommand s r)
    (hop : r.op = .grant) :
    (r.actor != r.target && !s.has r.target r.role) = true := by
  unfold ValidCommand at h
  obtain ⟨ha, ht, hadm, hgrant, hrev⟩ := h
  have hg := hgrant hop
  obtain ⟨hne, hfalse⟩ := hg
  have h1 : (r.actor != r.target) = true := probe_bne4 r.actor r.target hne
  have h2 : (!s.has r.target r.role) = true := by simp [hfalse]
  simp [h1, h2]

theorem plan0_valid_revoke_extra_test (s : State) (r : Request) (h : ValidCommand s r)
    (hop : r.op = .revoke) :
    (s.has r.target r.role && (r.role != .admin || hasOtherAdmin s r.target)) = true := by
  unfold ValidCommand at h
  obtain ⟨ha, ht, hadm, hgrant, hrev⟩ := h
  have hr := hrev hop
  obtain ⟨hhas, hoth⟩ := hr
  have h2 : (r.role != .admin || hasOtherAdmin s r.target) = true := by
    by_cases hrole : r.role = .admin
    · have ho : OtherAdmin s r.target := hoth hrole
      have hb : hasOtherAdmin s r.target = true := hasOtherAdmin_of_OtherAdmin s r.target ho
      simp [hb]
    · have hbne : (r.role != .admin) = true := probe_role_bne2 r.role hrole
      simp [hbne]
  simp [hhas, h2]

theorem tmpD : ((!(true && true))) = false := by decide

theorem tmpD2 : ((!true)) = false := by rfl

theorem tmpD3 (b : Bool) (hb : b = true) : ((!b) = false) := by simp [hb]

theorem tmpNot2 (s : State) (r : Request) (hc : (s.users.contains r.actor && s.users.contains r.target) = true) : ((!(s.users.contains r.actor && s.users.contains r.target)) = false) := by rw [hc]; rfl

theorem tmpIfTest1 : ((if (false = true) then (1:Nat) else 2) = 2) := by simp

theorem tmpIfTest2 (b : Bool) (hb : b = false) : ((if b then (1:Nat) else 2) = 2) := by simp [hb]

theorem tmpIfTest3 (b : Bool) (hb : (!b) = false) : ((if !b then (1:Nat) else 2) = 2) := by simp [hb]

theorem probe_case_syntax (r : Request) : True := by
  cases h : r.op
  next =>
    trivial
  next =>
    trivial











theorem plan1_grant_ok_valid (s : State) (r : Request) (hop : r.op = .grant)
    (h : (step s r).1 = .ok) : ValidCommand s r := by
  have hF : (!(s.users.contains r.actor && s.users.contains r.target)) = false := ok_mem_bool s r h
  have hg : (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true := by
    by_cases hg2 : (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true
    · exact hg2
    · have hgF : (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = false := by simp [hg2]
      have hRej : (step s r).1 = .rejected := by simp [step, hop, hgF]
      rw [hRej] at h
      contradiction
  have hC := auth_mem_true s r h
  rw [Bool.and_eq_true] at hC
  obtain ⟨hca, hct⟩ := hC
  have ha : r.actor ∈ s.users := (mem_contains_test2 s r.actor).mp hca
  have ht : r.target ∈ s.users := (mem_contains_test2 s r.target).mp hct
  rw [Bool.and_eq_true] at hg
  obtain ⟨hg12, hg3⟩ := hg
  rw [Bool.and_eq_true] at hg12
  obtain ⟨hg1, hg2⟩ := hg12
  have hadm : s.has r.actor .admin = true := (isAdmin_eq_true s r.actor).mp hg1 |>.2
  have hne : r.actor ≠ r.target := probe_bne3 r.actor r.target hg2
  have hfalse : s.has r.target r.role = false := by simp at hg3 ⊢; exact hg3
  unfold ValidCommand
  refine ⟨ha, ht, hadm, ?_, ?_⟩
  · intro _
    exact ⟨hne, hfalse⟩
  · intro hrev
    rw [hop] at hrev
    contradiction

theorem plan1_revoke_ok_valid_aux (s : State) (r : Request) (hop : r.op = .revoke)
    (h : (step s r).1 = .ok) : ValidCommand s r := by
  have hCond : (isAdmin s r.actor && s.has r.target r.role &&
      (r.role != .admin || hasOtherAdmin s r.target)) = true := by
    by_cases hc : (isAdmin s r.actor && s.has r.target r.role &&
      (r.role != .admin || hasOtherAdmin s r.target)) = true
    · exact hc
    · have hcF : (isAdmin s r.actor && s.has r.target r.role &&
        (r.role != .admin || hasOtherAdmin s r.target)) = false := by simp [hc]
      have hRej : (step s r).1 = .rejected := by simp [step, hop, hcF]
      rw [hRej] at h
      contradiction
  have hC := auth_mem_true s r h
  rw [Bool.and_eq_true] at hC
  obtain ⟨hca, hct⟩ := hC
  have ha : r.actor ∈ s.users := (mem_contains_test2 s r.actor).mp hca
  have ht : r.target ∈ s.users := (mem_contains_test2 s r.target).mp hct
  rw [Bool.and_eq_true] at hCond
  obtain ⟨h12, h3⟩ := hCond
  rw [Bool.and_eq_true] at h12
  obtain ⟨hAdm, hHas⟩ := h12
  have hadm : s.has r.actor .admin = true := (isAdmin_eq_true s r.actor).mp hAdm |>.2
  unfold ValidCommand
  refine ⟨ha, ht, hadm, ?_, ?_⟩
  · intro hG
    rw [hop] at hG
    contradiction
  · intro _
    refine ⟨hHas, ?_⟩
    intro hRole
    have hNeF : (r.role != .admin) = false := by simp [hRole]
    have hOther : hasOtherAdmin s r.target = true := by
      rw [hNeF] at h3
      simpa using h3
    exact hasOtherAdmin_exists2 s r.target hOther

theorem plan1_revoke_ok_valid (s : State) (r : Request) (hop : r.op = .revoke)
    (h : (step s r).1 = .ok) : ValidCommand s r :=
  plan1_revoke_ok_valid_aux s r hop h

theorem plan1_ok_valid (s : State) (r : Request)
    (h : (step s r).1 = .ok) : ValidCommand s r := by
  cases hOp : r.op with
  | grant => exact plan1_grant_ok_valid s r hOp h
  | revoke => exact plan1_revoke_ok_valid s r hOp h

theorem plan1_step_eq_of_not_ok_aux5 (s : State) (r : Request)
    (h : (step s r).1 ≠ .ok) : step s r = (.rejected, s) := by
  simp only [step] at h ⊢
  by_cases hc : ((!(s.users.contains r.actor && s.users.contains r.target)) = true)
  · rw [if_pos hc] at ⊢
  · rw [if_neg hc] at h ⊢
    cases hop : r.op
    · simp only [hop] at h ⊢
      by_cases hg : ((isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true)
      · rw [if_pos hg] at h
        simp at h
      · rw [if_neg hg] at ⊢
    · simp only [hop] at h ⊢
      by_cases hr : ((isAdmin s r.actor && s.has r.target r.role &&
        (r.role != .admin || hasOtherAdmin s r.target)) = true)
      · rw [if_pos hr] at h
        simp at h
      · rw [if_neg hr] at ⊢

theorem plan1_step_eq_of_not_ok (s : State) (r : Request)
    (h : (step s r).1 ≠ .ok) : step s r = (.rejected, s) := by
  simp only [step] at h ⊢
  by_cases hc : ((!(s.users.contains r.actor && s.users.contains r.target)) = true)
  · rw [if_pos hc] at ⊢
  · rw [if_neg hc] at h ⊢
    cases hop : r.op
    · simp only [hop] at h ⊢
      by_cases hg : ((isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true)
      · rw [if_pos hg] at h
        simp at h
      · rw [if_neg hg] at ⊢
    · simp only [hop] at h ⊢
      by_cases hr : ((isAdmin s r.actor && s.has r.target r.role &&
        (r.role != .admin || hasOtherAdmin s r.target)) = true)
      · rw [if_pos hr] at h
        simp at h
      · rw [if_neg hr] at ⊢

theorem plan1_invalid_step_check (s : State) (r : Request)
    (h : ¬ ValidCommand s r) : step s r = (.rejected, s) := by
  have hne : (step s r).1 ≠ .ok := fun heq => h (plan1_ok_valid s r heq)
  exact plan1_step_eq_of_not_ok s r hne

theorem hc_derive_test4 (s : State) (r : Request)
    (hc : ¬((!(s.users.contains r.actor && s.users.contains r.target)) = true)) :
    (s.users.contains r.actor && s.users.contains r.target) = true := by
  have hc2 := hc
  simp at hc2
  obtain ⟨ha, ht⟩ := hc2
  exact valid_contains_rw3 s r ha ht

theorem hc_mem_probe (s : State) (r : Request)
    (hc : ¬((!(s.users.contains r.actor && s.users.contains r.target)) = true)) :
    r.actor ∈ s.users ∧ r.target ∈ s.users := by
  have hc2 := hc
  simp at hc2
  exact hc2



theorem plan2_revoke_ok_cond (s : State) (r : Request) (hop : r.op = .revoke)
    (h : (step s r).1 = .ok) :
    (isAdmin s r.actor && s.has r.target r.role &&
      (r.role != .admin || hasOtherAdmin s r.target)) = true := by
  by_cases hc : (isAdmin s r.actor && s.has r.target r.role &&
      (r.role != .admin || hasOtherAdmin s r.target)) = true
  · exact hc
  · have hcF : (isAdmin s r.actor && s.has r.target r.role &&
        (r.role != .admin || hasOtherAdmin s r.target)) = false := by simp [hc]
    have hRej : (step s r).1 = .rejected := by simp [step, hop, hcF]
    rw [hRej] at h
    contradiction




theorem plan2_revoke_ok_valid (s : State) (r : Request) (hop : r.op = .revoke)
    (h : (step s r).1 = .ok) : ValidCommand s r :=
  plan1_revoke_ok_valid s r hop h






theorem plan2_grant_ok_cond (s : State) (r : Request) (hop : r.op = .grant)
    (h : (step s r).1 = .ok) :
    (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true := by
  by_cases hg : (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true
  · exact hg
  · have hgF : (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = false := by simp [hg]
    have hRej : (step s r).1 = .rejected := by simp [step, hop, hgF]
    rw [hRej] at h
    contradiction

theorem plan2_revoke_ok_cond_proof (s : State) (r : Request) (hop : r.op = .revoke)
    (h : (step s r).1 = .ok) :
    (isAdmin s r.actor && s.has r.target r.role &&
      (r.role != .admin || hasOtherAdmin s r.target)) = true := by
  by_cases hc : (isAdmin s r.actor && s.has r.target r.role &&
      (r.role != .admin || hasOtherAdmin s r.target)) = true
  · exact hc
  · have hcF : (isAdmin s r.actor && s.has r.target r.role &&
        (r.role != .admin || hasOtherAdmin s r.target)) = false := by simp [hc]
    have hRej : (step s r).1 = .rejected := by simp [step, hop, hcF]
    rw [hRej] at h
    contradiction

theorem plan2_grant_ok_valid_aux2 (s : State) (r : Request) (hop : r.op = .grant)
    (h : (step s r).1 = .ok) : ValidCommand s r :=
  plan1_grant_ok_valid s r hop h

theorem plan2_grant_ok_valid (s : State) (r : Request) (hop : r.op = .grant)
    (h : (step s r).1 = .ok) : ValidCommand s r :=
  plan1_grant_ok_valid s r hop h

theorem plan2_revoke_ok_valid_helperX (s : State) (r : Request) (hop : r.op = .revoke)
    (h : (step s r).1 = .ok) : ValidCommand s r :=
  plan1_revoke_ok_valid s r hop h

theorem plan2_ok_valid (s : State) (r : Request)
    (h : (step s r).1 = .ok) : ValidCommand s r :=
  plan1_ok_valid s r h

theorem plan2_not_ok_step (s : State) (r : Request)
    (h : (step s r).1 ≠ .ok) : step s r = (.rejected, s) :=
  plan1_step_eq_of_not_ok s r h

theorem plan1_invalid_step (s : State) (r : Request)
    (h : ¬ ValidCommand s r) : step s r = (.rejected, s) := by
  have hne : (step s r).1 ≠ .ok := fun heq => h (plan1_ok_valid s r heq)
  exact plan1_step_eq_of_not_ok s r hne

theorem req_invalid_noop_helper_test : InvalidNoop step :=
  fun s r h => plan1_invalid_step s r h

theorem others_beq_false_aux (u t : UserId) (q qq : Role) (h : u ≠ t ∨ q ≠ qq) :
    ((u == t && q == qq) = false) := by
  have hiff : ((u == t && q == qq) = true) ↔ (u = t ∧ q = qq) := fx_and_beq_true u t q qq
  by_cases hb : ((u == t && q == qq) = true)
  · rw [hiff] at hb
    cases h with
    | inl hl => exact (hl hb.1).elim
    | inr hr => exact (hr hb.2).elim
  · simp [hb]

theorem plan3_expected_grant (s : State) (r : Request) (u : UserId) (q : Role)
    (hop : r.op = .grant) :
    expectedHas s r u q = (if u == r.target && q == r.role then true else s.has u q) := by
  unfold expectedHas
  simp only [hop, decide_true]
  by_cases h : u = r.target ∧ q = r.role
  · have hbeq : (u == r.target && q == r.role) = true := by
      rw [fx_and_beq_true]
      exact h
    simp [h, hbeq]
  · have hbeq : (u == r.target && q == r.role) = false := by
      by_cases hb : (u == r.target && q == r.role) = true
      · rw [fx_and_beq_true] at hb
        exact (h hb).elim
      · simp [hb]
    simp [h, hbeq]


theorem plan3_expected_revoke (s : State) (r : Request) (u : UserId) (q : Role)
    (hop : r.op = .revoke) :
    expectedHas s r u q = (if u == r.target && q == r.role then false else s.has u q) := by
  unfold expectedHas
  have hdec : decide (r.op = .grant) = false := by simp [hop]
  rw [hdec]
  by_cases h : u = r.target ∧ q = r.role
  · have hbeq : (u == r.target && q == r.role) = true := by
      rw [fx_and_beq_true]
      exact h
    simp [h, hbeq]
  · have hbeq : (u == r.target && q == r.role) = false := by
      by_cases hb : (u == r.target && q == r.role) = true
      · rw [fx_and_beq_true] at hb
        exact (h hb).elim
      · simp [hb]
    simp [h, hbeq]






theorem plan3_step_has_expected (s : State) (r : Request)
    (h : (step s r).1 = .ok) (u : UserId) (q : Role) :
    (step s r).2.has u q = expectedHas s r u q := by
  cases hop : r.op with
  | grant =>
    have hg : (step s r).2.has u q = (if u == r.target && q == r.role then true else s.has u q) := by
      have hC := auth_mem_true s r h
      rw [Bool.and_eq_true] at hC
      obtain ⟨hca, hct⟩ := hC
      have ha : r.actor ∈ s.users := (mem_contains_test2 s r.actor).mp hca
      have ht : r.target ∈ s.users := (mem_contains_test2 s r.target).mp hct
      have hCond : (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true :=
        plan2_grant_ok_cond s r hop h
      simp [step, hop, hCond, ha, ht]
    have he := plan3_expected_grant s r u q hop
    rw [hg, he]
  | revoke =>
    have hr : (step s r).2.has u q = (if u == r.target && q == r.role then false else s.has u q) := by
      have hOut : ((!(s.users.contains r.actor && s.users.contains r.target)) = false) := ok_mem_bool s r h
      have hCond : (isAdmin s r.actor && s.has r.target r.role &&
          (r.role != .admin || hasOtherAdmin s r.target)) = true :=
        plan2_revoke_ok_cond s r hop h
      simp only [step, hOut, hop, hCond] at h ⊢
      rfl
    have he := plan3_expected_revoke s r u q hop
    rw [hr, he]


theorem tmp_grant_step_has_check4 (s : State) (r : Request) (u : UserId) (q : Role)
    (hop : r.op = .grant) (h : (step s r).1 = .ok) :
    (step s r).2.has u q = (if u == r.target && q == r.role then true else s.has u q) := by
  have hC := auth_mem_true s r h
  rw [Bool.and_eq_true] at hC
  obtain ⟨hca, hct⟩ := hC
  have ha : r.actor ∈ s.users := (mem_contains_test2 s r.actor).mp hca
  have ht : r.target ∈ s.users := (mem_contains_test2 s r.target).mp hct
  have hCond : (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true :=
    plan2_grant_ok_cond s r hop h
  simp [step, hop, hCond, ha, ht]

theorem plan3_grant_step_has (s : State) (r : Request) (u : UserId) (q : Role)
    (hop : r.op = .grant) (h : (step s r).1 = .ok) :
    (step s r).2.has u q = (if u == r.target && q == r.role then true else s.has u q) := by
  have hC := auth_mem_true s r h
  rw [Bool.and_eq_true] at hC
  obtain ⟨hca, hct⟩ := hC
  have ha : r.actor ∈ s.users := (mem_contains_test2 s r.actor).mp hca
  have ht : r.target ∈ s.users := (mem_contains_test2 s r.target).mp hct
  have hCond : (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true :=
    plan2_grant_ok_cond s r hop h
  simp [step, hop, hCond, ha, ht]

theorem plan3_revoke_step_has_check (s : State) (r : Request) (u : UserId) (q : Role)
    (hop : r.op = .revoke) (h : (step s r).1 = .ok) :
    (step s r).2.has u q = (if u == r.target && q == r.role then false else s.has u q) := by
  have hOut : ((!(s.users.contains r.actor && s.users.contains r.target)) = false) := ok_mem_bool s r h
  have hCond : (isAdmin s r.actor && s.has r.target r.role &&
      (r.role != .admin || hasOtherAdmin s r.target)) = true :=
    plan2_revoke_ok_cond s r hop h
  simp only [step, hOut, hop, hCond] at h ⊢
  rfl

theorem plan3_revoke_step_has (s : State) (r : Request) (u : UserId) (q : Role)
    (hop : r.op = .revoke) (h : (step s r).1 = .ok) :
    (step s r).2.has u q = (if u == r.target && q == r.role then false else s.has u q) :=
  plan3_revoke_step_has_check s r u q hop h

theorem plan3_step_has_expected_aux (s : State) (r : Request)
    (h : (step s r).1 = .ok) (u : UserId) (q : Role) :
    (step s r).2.has u q = expectedHas s r u q := by
  cases hop : r.op with
  | grant =>
    have hg := plan3_grant_step_has s r u q hop h
    have he := plan3_expected_grant s r u q hop
    rw [hg, he]
  | revoke =>
    have hr := plan3_revoke_step_has s r u q hop h
    have he := plan3_expected_revoke s r u q hop
    rw [hr, he]

theorem req_effects_proof_tmp : Effects step := by
  unfold Effects
  intro s r h
  exact ⟨step_users_eq_all3 s r, fun u q => plan3_step_has_expected s r h u q⟩

theorem idem_grant_has_true (s : State) (r : Request) (hop : r.op = .grant)
    (h : (step s r).1 = .ok) : (step s r).2.has r.target r.role = true := by
  have hh := plan3_grant_step_has s r r.target r.role hop h
  simp at hh
  exact hh

theorem idem_revoke_has_false (s : State) (r : Request) (hop : r.op = .revoke)
    (h : (step s r).1 = .ok) : (step s r).2.has r.target r.role = false := by
  have hh := plan3_revoke_step_has s r r.target r.role hop h
  simp at hh
  exact hh

theorem vs_aux1 (s : State) (r : Request) (hOut : (!(s.users.contains r.actor && s.users.contains r.target)) = false)
    (hop : r.op = .grant)
    (hCond : (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true) :
    (step s r).1 = .ok := by
  have hOutNeg : ¬((!(s.users.contains r.actor && s.users.contains r.target)) = true) := by
    rw [hOut]; simp
  unfold step
  rw [if_neg hOutNeg, hop, if_pos hCond]

theorem vs_aux2 (s : State) (r : Request) (hOut : (!(s.users.contains r.actor && s.users.contains r.target)) = false)
    (hop : r.op = .revoke)
    (hCond : (isAdmin s r.actor && s.has r.target r.role && (r.role != .admin || hasOtherAdmin s r.target)) = true) :
    (step s r).1 = .ok := by
  have hOutNeg : ¬((!(s.users.contains r.actor && s.users.contains r.target)) = true) := by
    rw [hOut]; simp
  unfold step
  rw [if_neg hOutNeg, hop, if_pos hCond]

theorem req_valid_succeeds  : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r h
  have hC : (s.users.contains r.actor && s.users.contains r.target) = true :=
    plan0_valid_contains s r h
  have hOut : (!(s.users.contains r.actor && s.users.contains r.target)) = false :=
    tmpNot2 s r hC
  have hAdm : isAdmin s r.actor = true := plan0_valid_isAdmin s r h
  cases hop : r.op with
  | grant =>
    have hG := plan0_valid_grant_extra s r h hop
    have hCond : (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true := by
      simp [hAdm, hG]
    exact vs_aux1 s r hOut hop hCond
  | revoke =>
    have hR := plan0_valid_revoke_extra s r h hop
    have hCond : (isAdmin s r.actor && s.has r.target r.role &&
      (r.role != .admin || hasOtherAdmin s r.target)) = true := by
      simp [hAdm, hR]
    exact vs_aux2 s r hOut hop hCond

theorem req_invalid_noop : InvalidNoop step :=
  fun s r h => plan1_invalid_step s r h

theorem req_authorization   : AdminOnly step := by
  unfold AdminOnly
  intro s r h
  have hv := plan1_ok_valid s r h
  unfold ValidCommand at hv
  obtain ⟨ha, ht, hadm, _, _⟩ := hv
  exact ⟨ha, hadm⟩

theorem req_no_self_grant : NoSelfGrant step := by
  unfold NoSelfGrant
  intro s r h hop
  have hv := plan1_ok_valid s r h
  unfold ValidCommand at hv
  obtain ⟨ha, ht, hadm, hgrant, hrev⟩ := hv
  exact (hgrant hop).1

theorem req_others_unchanged : OthersUnchanged step := by
  unfold OthersUnchanged
  intro s r h u q hneq
  have hOut : ((!(s.users.contains r.actor && s.users.contains r.target)) = false) := ok_mem_bool s r h
  have hbeq : ((u == r.target && q == r.role) = false) := others_beq_false_aux u r.target q r.role hneq
  cases hop : r.op with
  | grant =>
    have hCond : (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true :=
      plan2_grant_ok_cond s r hop h
    simp only [step, hOut, hop, hCond] at h ⊢
    show (if u == r.target && q == r.role then true else s.has u q) = s.has u q
    simp [hbeq]
  | revoke =>
    have hCond : (isAdmin s r.actor && s.has r.target r.role &&
        (r.role != .admin || hasOtherAdmin s r.target)) = true :=
      plan2_revoke_ok_cond s r hop h
    simp only [step, hOut, hop, hCond] at h ⊢
    show (if u == r.target && q == r.role then false else s.has u q) = s.has u q
    simp [hbeq]

theorem req_effects : Effects step := by
  unfold Effects
  intro s r h
  exact ⟨step_users_eq_all3 s r, fun u q => plan3_step_has_expected s r h u q⟩

theorem req_idempotency  : Idempotent step := by
  unfold Idempotent
  intro s r h
  have husers : (step s r).2.users = s.users := step_users_eq_all3 s r
  have hnot : ¬ ValidCommand (step s r).2 r := by
    intro hv
    unfold ValidCommand at hv
    obtain ⟨ha, ht, hadm, hgrant, hrev⟩ := hv
    cases hop : r.op with
    | grant =>
      have hg := hgrant hop
      obtain ⟨hne, hfalse⟩ := hg
      have htrue : (step s r).2.has r.target r.role = true :=
        idem_grant_has_true s r hop h
      rw [htrue] at hfalse
      contradiction
    | revoke =>
      have hr := hrev hop
      obtain ⟨htrue2, _⟩ := hr
      have hfalse : (step s r).2.has r.target r.role = false :=
        idem_revoke_has_false s r hop h
      rw [hfalse] at htrue2
      contradiction
  have hstep := plan1_invalid_step (step s r).2 r hnot
  exact hstep

theorem req_last_admin : KeepsAdmin step := by
  unfold KeepsAdmin
  intro s r hex
  obtain ⟨w, hwmem, hwadm⟩ := hex
  by_cases hOk : (step s r).1 = .ok
  · have hValid : ValidCommand s r := plan1_ok_valid s r hOk
    have hUsers : (step s r).2.users = s.users := step_users_eq_all3 s r
    cases hop : r.op with
    | grant =>
      refine ⟨w, ?_, ?_⟩
      · rw [hUsers]; exact hwmem
      · have hAfter : (step s r).2.has w .admin = expectedHas s r w .admin :=
          plan3_step_has_expected s r hOk w .admin
        rw [hAfter]
        unfold expectedHas
        by_cases hc : w = r.target ∧ (.admin : Role) = r.role
        · simp [hc, hop]
        · simp [hc, hwadm]
    | revoke =>
      by_cases hRole : r.role = .admin
      · -- revoking admin: use other admin
        have hV : ValidCommand s r := hValid
        unfold ValidCommand at hV
        obtain ⟨ha, ht, hadm, hgrant, hrev⟩ := hV
        have hr := hrev hop
        obtain ⟨hhas, hoth⟩ := hr
        have hOA : OtherAdmin s r.target := hoth hRole
        obtain ⟨v, hvmem, hne, hvadmin⟩ := hOA
        refine ⟨v, ?_, ?_⟩
        · rw [hUsers]; exact hvmem
        · have hpres : (step s r).2.has v .admin = s.has v .admin := by
            have hh := req_others_unchanged s r hOk v .admin (Or.inl hne)
            exact hh
          rw [hpres, hvadmin]
      · -- revoking non-admin: w persists
        refine ⟨w, ?_, ?_⟩
        · rw [hUsers]; exact hwmem
        · have hAfter : (step s r).2.has w .admin = expectedHas s r w .admin :=
            plan3_step_has_expected s r hOk w .admin
          rw [hAfter]
          unfold expectedHas
          have hc : ¬ (w = r.target ∧ (.admin : Role) = r.role) := by
            intro hcon
            exact hRole hcon.2.symm
          simp [hc, hwadm]
  · have hPair : step s r = (.rejected, s) := plan1_step_eq_of_not_ok s r hOk
    have h2 : (step s r).2 = s := by rw [hPair]
    rw [h2]
    exact ⟨w, hwmem, hwadm⟩

end Grants
