import Grants.Spec
/-!
# Reference solution B (build team; hidden from agents)

Boolean checks per operation; grant and revoke rewrite the relation separately.
-/

namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance

/-- Some admin of the universe other than `u`. -/
def otherAdminB (s : State) (u : UserId) : Bool :=
  s.users.any (fun v => v != u && s.has v .admin)

def canGrant (s : State) (r : Request) : Bool :=
  r.actor != r.target && !s.has r.target r.role

def canRevoke (s : State) (r : Request) : Bool :=
  s.has r.target r.role && (r.role != .admin || otherAdminB s r.target)

def addGrant (s : State) (u : UserId) (q : Role) : State :=
  { s with has := fun v p => s.has v p || (v == u && p == q) }

def removeGrant (s : State) (u : UserId) (q : Role) : State :=
  { s with has := fun v p => s.has v p && !(v == u && p == q) }

/-- Boolean validity check. -/
def validB (s : State) (r : Request) : Bool :=
  s.users.contains r.actor && s.users.contains r.target && s.has r.actor .admin &&
    match r.op with
    | .grant => canGrant s r
    | .revoke => canRevoke s r

/-- Apply a command that passed the check. -/
def apply (s : State) (r : Request) : State :=
  match r.op with
  | .grant => addGrant s r.target r.role
  | .revoke => removeGrant s r.target r.role

def step : Impl := fun s r =>
  if validB s r then (.ok, apply s r) else (.rejected, s)

theorem otherAdminB_iff (s : State) (u : UserId) : otherAdminB s u = true ↔ OtherAdmin s u := by
  simp [otherAdminB, OtherAdmin]

theorem validB_iff (s : State) (r : Request) : validB s r = true ↔ ValidCommand s r := by
  obtain ⟨op, a, t, q⟩ := r
  cases op <;> cases q <;>
    simp [validB, ValidCommand, canGrant, canRevoke, ← otherAdminB_iff, and_assoc]

theorem apply_eq (s : State) (r : Request) : apply s r = { s with has := expectedHas s r } := by
  obtain ⟨op, a, t, q⟩ := r
  cases op <;>
  · simp only [apply, addGrant, removeGrant, State.mk.injEq, true_and]
    funext v p
    simp only [expectedHas]
    by_cases hvp : v = t ∧ p = q
    · obtain ⟨rfl, rfl⟩ := hvp; simp
    · simp only [hvp, ite_false]
      have : (v == t && p == q) = false := by
        cases hv : v == t <;> cases hp : p == q <;> simp_all
      simp [this]

theorem step_eq (s : State) (r : Request) :
    step s r = if ValidCommand s r
      then (.ok, { s with has := expectedHas s r }) else (.rejected, s) := by
  by_cases h : ValidCommand s r
  · simp [step, (validB_iff s r).2 h, apply_eq, h]
  · have : validB s r = false := by
      cases hb : validB s r
      · rfl
      · exact absurd ((validB_iff s r).1 hb) h
    simp [step, this, h]

theorem step_of_valid {s : State} {r : Request} (h : ValidCommand s r) :
    step s r = (.ok, { s with has := expectedHas s r }) := by
  rw [step_eq]; simp [h]

theorem step_of_invalid {s : State} {r : Request} (h : ¬ ValidCommand s r) :
    step s r = (.rejected, s) := by
  rw [step_eq]; simp [h]

theorem ok_valid {s : State} {r : Request} (h : (step s r).1 = .ok) : ValidCommand s r := by
  by_cases hv : ValidCommand s r
  · exact hv
  · rw [step_of_invalid hv] at h; cases h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h; rw [step_of_valid h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h; exact step_of_invalid h

theorem req_authorization : AdminOnly step := by
  intro s r h
  have hv := ok_valid h
  exact ⟨hv.1, hv.2.2.1⟩

theorem req_no_self_grant : NoSelfGrant step := by
  intro s r h hg
  exact ((ok_valid h).2.2.2.1 hg).1

theorem req_effects : Effects step := by
  intro s r h
  rw [step_of_valid (ok_valid h)]
  exact ⟨rfl, fun u q => rfl⟩

theorem req_others_unchanged : OthersUnchanged step := by
  intro s r h u q hne
  rw [step_of_valid (ok_valid h)]
  have : ¬ (u = r.target ∧ q = r.role) := by
    rintro ⟨h1, h2⟩; cases hne <;> contradiction
  simp [expectedHas, this]

theorem req_idempotency : Idempotent step := by
  intro s r h
  have hv := ok_valid h
  rw [step_of_valid hv]
  apply step_of_invalid
  rintro ⟨_, _, _, hg, hr⟩
  cases hop : r.op with
  | grant => have := (hg hop).2; simp [expectedHas, hop] at this
  | revoke => have := (hr hop).1; simp [expectedHas, hop] at this

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  by_cases hv : ValidCommand s r
  · rw [step_of_valid hv]
    obtain ⟨_, _, _, _, hr⟩ := hv
    by_cases hdrop : r.op = .revoke ∧ r.role = .admin
    · obtain ⟨v, hv, hne, ha⟩ := (hr hdrop.1).2 hdrop.2
      exact ⟨v, hv, by simp [expectedHas, hne, ha]⟩
    · obtain ⟨u, hu, ha⟩ := hex
      refine ⟨u, hu, ?_⟩
      simp only [expectedHas]
      split
      · rename_i hp
        cases hop : r.op
        · rfl
        · exact absurd ⟨hop, hp.2.symm⟩ hdrop
      · exact ha
  · rw [step_of_invalid hv]; exact hex

end Grants
