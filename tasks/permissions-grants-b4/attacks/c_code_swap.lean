import Grants.Spec
/-!
# Reference solution A (build team; hidden from agents)

Decide validity with the specification predicate and overwrite the single pair.
-/

namespace Grants

instance instDecidableValidCommand (s : State) (r : Request) : Decidable (ValidCommand s r) := by
  unfold ValidCommand OtherAdmin; infer_instance

/-- Set the pair `(u, q)` of a grant relation to `b`. -/
def setGrant (has : UserId → Role → Bool) (u : UserId) (q : Role) (b : Bool) :
    UserId → Role → Bool :=
  fun v p => if v = u ∧ p = q then b else has v p

def isAdmin (s : State) (u : UserId) : Bool := s.users.contains u && s.has u .admin
def buggyStep : Impl := fun s r =>
  if !(s.users.contains r.actor && s.users.contains r.target) then (.rejected, s) else
  match r.op with
  | .grant =>
    if isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role then
      (.ok, { users := s.users, has := fun u q => if u == r.target && q == r.role then true else s.has u q })
    else (.rejected, s)
  | .revoke =>
    if isAdmin s r.actor && s.has r.target r.role &&
        (r.role != .admin || s.users.any (fun v => v != r.target && s.has v .admin)) then
      (.ok, { users := s.users, has := fun u q => if u == r.target then false else s.has u q })
    else (.rejected, s)

@[implemented_by buggyStep]
def step : Impl := fun s r =>
  if ValidCommand s r then
    (.ok, { s with has := setGrant s.has r.target r.role (decide (r.op = .grant)) })
  else
    (.rejected, s)

theorem step_of_valid {s : State} {r : Request} (h : ValidCommand s r) :
    step s r = (.ok, { s with has := setGrant s.has r.target r.role (decide (r.op = .grant)) }) := by
  simp [step, h]

theorem step_of_invalid {s : State} {r : Request} (h : ¬ ValidCommand s r) :
    step s r = (.rejected, s) := by
  simp [step, h]

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
  simp only [setGrant]
  have : ¬ (u = r.target ∧ q = r.role) := by
    rintro ⟨h1, h2⟩; cases hne <;> contradiction
  simp [this]

theorem req_idempotency : Idempotent step := by
  intro s r h
  have hv := ok_valid h
  rw [step_of_valid hv]
  apply step_of_invalid
  intro h'
  obtain ⟨_, _, _, hg, hr⟩ := h'
  cases hop : r.op with
  | grant =>
    have := (hg hop).2
    simp [setGrant, hop] at this
  | revoke =>
    have := (hr hop).1
    simp [setGrant, hop] at this

theorem req_last_admin : KeepsAdmin step := by
  intro s r hex
  by_cases hv : ValidCommand s r
  · rw [step_of_valid hv]
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
  · rw [step_of_invalid hv]; exact hex

end Grants
