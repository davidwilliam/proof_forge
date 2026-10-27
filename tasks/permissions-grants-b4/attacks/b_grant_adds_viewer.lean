import Grants.Spec

namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance

/-- Set the pair `(u, q)` of a grant relation to `b`. -/
def setGrant (has : UserId → Role → Bool) (u : UserId) (q : Role) (b : Bool) :
    UserId → Role → Bool :=
  fun v p => if v = u ∧ p = q then b else has v p

def refStep : Impl := fun s r =>
  if ValidCommand s r then
    (.ok, { s with has := setGrant s.has r.target r.role (decide (r.op = .grant)) })
  else
    (.rejected, s)

theorem refStep_of_valid {s : State} {r : Request} (h : ValidCommand s r) :
    refStep s r = (.ok, { s with has := setGrant s.has r.target r.role (decide (r.op = .grant)) }) := by
  simp [refStep, h]

theorem refStep_of_invalid {s : State} {r : Request} (h : ¬ ValidCommand s r) :
    refStep s r = (.rejected, s) := by
  simp [refStep, h]

theorem ref_ok_valid {s : State} {r : Request} (h : (refStep s r).1 = .ok) : ValidCommand s r := by
  by_cases hv : ValidCommand s r
  · exact hv
  · rw [refStep_of_invalid hv] at h; cases h

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s r h; rw [refStep_of_valid h]

theorem ref_req_invalid_noop : InvalidNoop refStep := by
  intro s r h; exact refStep_of_invalid h

theorem ref_req_authorization : AdminOnly refStep := by
  intro s r h
  have hv := ref_ok_valid h
  exact ⟨hv.1, hv.2.2.1⟩

theorem ref_req_no_self_grant : NoSelfGrant refStep := by
  intro s r h hg
  exact ((ref_ok_valid h).2.2.2.1 hg).1

theorem ref_req_effects : Effects refStep := by
  intro s r h
  rw [refStep_of_valid (ref_ok_valid h)]
  exact ⟨rfl, fun u q => rfl⟩

theorem ref_req_others_unchanged : OthersUnchanged refStep := by
  intro s r h u q hne
  rw [refStep_of_valid (ref_ok_valid h)]
  simp only [setGrant]
  have : ¬ (u = r.target ∧ q = r.role) := by
    rintro ⟨h1, h2⟩; cases hne <;> contradiction
  simp [this]

theorem ref_req_idempotency : Idempotent refStep := by
  intro s r h
  have hv := ref_ok_valid h
  rw [refStep_of_valid hv]
  apply refStep_of_invalid
  intro h'
  obtain ⟨_, _, _, hg, hr⟩ := h'
  cases hop : r.op with
  | grant =>
    have := (hg hop).2
    simp [setGrant, hop] at this
  | revoke =>
    have := (hr hop).1
    simp [setGrant, hop] at this

theorem ref_req_last_admin : KeepsAdmin refStep := by
  intro s r hex
  by_cases hv : ValidCommand s r
  · rw [refStep_of_valid hv]
    obtain ⟨_, _, _, _, hr⟩ := hv
    cases hop : r.op with
    | grant =>
      obtain ⟨u, hu, ha⟩ := hex
      refine ⟨u, hu, ?_⟩
      simp only [setGrant]
      split <;> simp_all
    | revoke =>
      by_cases hrole : r.role = .admin
      · obtain ⟨v, hv, hne, ha⟩ := (hr hop).2 hrole
        refine ⟨v, hv, ?_⟩
        simp [setGrant, hne, ha]
      · obtain ⟨u, hu, ha⟩ := hex
        refine ⟨u, hu, ?_⟩
        have : ¬ (u = r.target ∧ Role.admin = r.role) := fun h => hrole h.2.symm
        simp [setGrant, this, ha]
  · rw [refStep_of_invalid hv]; exact hex


/-- Attack: every successful grant also gives the target the viewer role. -/
def touch (r : Request) (t : State) : State :=
  { t with has := fun u q => t.has u q || (u == r.target && q == .viewer && r.op == .grant) }

def step : Impl := fun s r =>
  if (refStep s r).1 = .ok then (.ok, touch r (refStep s r).2) else refStep s r

theorem step_ok {s : State} {r : Request} (h : (step s r).1 = .ok) :
    (refStep s r).1 = .ok ∧ step s r = (.ok, touch r (refStep s r).2) := by
  unfold step at *
  by_cases hk : (refStep s r).1 = .ok
  · simp [hk]
  · simp [hk] at h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, ref_req_valid_succeeds s r h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, ref_req_invalid_noop s r h]

theorem req_authorization : AdminOnly step := by
  intro s r h
  exact ref_req_authorization s r (step_ok h).1

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r h
  exact ref_req_no_self_grant s r (step_ok h).1

theorem req_others_unchanged : ∀ s r, (step s r).1 = .ok →
    ∀ u q, u ≠ r.target → (step s r).2.has u q = s.has u q := by
  intro s r h u q hu
  obtain ⟨hk, he⟩ := step_ok h
  rw [he]
  have := ref_req_others_unchanged s r hk u q (Or.inl hu)
  simp [touch, this, hu]

theorem req_effects : ∀ s r, (step s r).1 = .ok →
    (step s r).2.users = s.users ∧
    ∀ u q, q ≠ .viewer → (step s r).2.has u q = expectedHas s r u q := by
  intro s r h
  obtain ⟨hk, he⟩ := step_ok h
  obtain ⟨hu, hh⟩ := ref_req_effects s r hk
  rw [he]
  refine ⟨hu, fun u q hq => ?_⟩
  simp [touch, hh, hq]

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  unfold step
  split
  · obtain ⟨u, hu, ha⟩ := ref_req_last_admin s r hex
    exact ⟨u, hu, by simp [touch, ha]⟩
  · exact ref_req_last_admin s r hex

theorem req_idempotency : Idempotent step := by
  intro s r h
  obtain ⟨hk, he⟩ := step_ok h
  have hv := ref_ok_valid hk
  obtain ⟨_, hh⟩ := ref_req_effects s r hk
  rw [he]
  have hinv : ¬ ValidCommand (touch r (refStep s r).2) r := by
    rintro ⟨_, _, _, hg, hr⟩
    cases hop : r.op with
    | grant =>
      have h1 := (hg hop).2
      simp [touch, hh, expectedHas, hop] at h1
    | revoke =>
      have h1 := (hr hop).1
      simp [touch, hh, expectedHas, hop] at h1
  have hn : (refStep (touch r (refStep s r).2) r) = (.rejected, touch r (refStep s r).2) :=
    ref_req_invalid_noop _ r hinv
  simp [step, hn]

end Grants
