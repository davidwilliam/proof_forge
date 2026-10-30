import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance
def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

/-- Depth of the most specific matching entry with effect `eff`. -/
def best (eff : Effect) (r : Request) (l : List Entry) : Option Nat :=
  (l.filter (fun e => matchesB e r && e.effect == eff)).foldl
    (fun m e => some (max (m.getD 0) (depth e))) none

def decision (l : List Entry) (r : Request) : Bool :=
  match best .allow r l, best .deny r l with
  | some _, none => true
  | some a, some d => d < a
  | none, _ => false

def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := decision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem matchesB_eq_true_iff_aux (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches
  simp

theorem aux_best_allow_some_imp_HasAllow {l : List Entry} {r : Request} {n : Nat} (h : best .allow r l = some n) : HasAllow l r := by
  unfold best at h
  have hfilter_ne : (l.filter fun e => matchesB e r && (e.effect == Effect.allow)) ≠ [] := by
    intro hnil
    simp [hnil] at h
  obtain ⟨a, ha⟩ : ∃ a, a ∈ l.filter fun e => matchesB e r && (e.effect == Effect.allow) := by
    exact List.exists_mem_of_ne_nil _ hfilter_ne
  have ha' := ha
  rw [List.mem_filter] at ha'
  obtain ⟨ha_mem, ha_b⟩ := ha'
  -- ha_b is Bool equality true
  have hm : Matches a r := (matchesB_eq_true_iff_aux a r).mp ((Bool.and_eq_true_iff.mp ha_b).1)
  have heff : a.effect = .allow := by simpa using (Bool.and_eq_true_iff.mp ha_b).2
  exact ⟨a, ha_mem, hm, heff⟩

theorem aux_decision_true_imp_HasAllow {l : List Entry} {r : Request} (h : decision l r = true) : HasAllow l r := by
  unfold decision at h
  cases ha : best .allow r l with
  | none =>
    simp [ha] at h
  | some a =>
    exact aux_best_allow_some_imp_HasAllow ha

def dummy := 0
#check List.isPrefixOf

theorem req_valid_answered     : ValidAnswered step := by
  intro s r h
  have hc : r.user ∈ s.users ∧ r.user ≠ 0 := h
  have h1 : step s r = (if decision s.entries r then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
    unfold step; simp [hc]
  rw [h1]
  simp
  intro hcontra
  cases h2 : decision s.entries r <;> simp [h2] at hcontra

theorem req_invalid_noop       : InvalidNoop step := sorry

theorem req_effects : Effects step := by
  intro s r h
  by_cases hc : r.user ∈ s.users ∧ r.user ≠ 0
  · have hstep_users : (step s r).2.users = s.users := by
      unfold step
      simp [hc]
    have hstep_entries : (step s r).2.entries = s.entries := by
      unfold step
      simp [hc]
    have hstep_log : (step s r).2.log = s.log ++ [⟨r.user, r.path, decide ((step s r).1 = .granted)⟩] := by
      have heq1 : (step s r).1 = if decision s.entries r then .granted else .denied := by
        unfold step; simp [hc]
      have heq2 : (step s r).2.log = s.log ++ [⟨r.user, r.path, decision s.entries r⟩] := by
        unfold step; simp [hc]
      rw [heq1, heq2]
      cases hd : decision s.entries r <;> simp_all
    exact ⟨hstep_users, hstep_entries, hstep_log⟩
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hc]
    rw [hstep] at h
    simp at h

theorem req_default_deny : DefaultDeny step := by
  intro s r hno hgr
  unfold step at hgr
  by_cases hc : r.user ∈ s.users ∧ r.user ≠ 0
  · simp [hc] at hgr
    have hdt : decision s.entries r = true := by
      cases hd : decision s.entries r
      · simp [hd] at hgr
      · rfl
    exact hno (aux_decision_true_imp_HasAllow hdt)
  · simp [hc] at hgr

theorem req_deny_overrides     : DenyOverrides step := sorry

theorem req_specific_allow     : SpecificAllow step := sorry

theorem req_grant_justified    : GrantJustified step := sorry

theorem req_order_independent  : OrderIndependent step := sorry

theorem req_denial_explained   : DenialExplained step := sorry

end Acl
