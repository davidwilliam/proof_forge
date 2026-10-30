import Acl.Spec
import Init.Classical

namespace Acl

instance decValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) :=
  inferInstanceAs (Decidable (r.user ∈ s.users ∧ r.user ≠ 0))

noncomputable instance decPermitted (s : State) (r : Request) : Decidable (Permitted s.entries r) :=
  by classical infer_instance

noncomputable def step : Impl := fun s r =>
  if ValidQuery s r then
    if Permitted s.entries r then
      (.granted, { s with log := s.log ++ [{ user := r.user, path := r.path, granted := true }] })
    else
      (.denied , { s with log := s.log ++ [{ user := r.user, path := r.path, granted := false }] })
  else
    (.rejected, s)

theorem req_valid_answered : ValidAnswered step := by
  intro s r hv
  simp [step, hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_effects : Effects step := by
  intro s r hnr
  simp [step] at hnr ⊢
  split_ifs at hnr ⊢ with hv hp
  · constructor <;> rfl
  · constructor <;> rfl
  · cases hnr

theorem req_default_deny : DefaultDeny step := by
  intro s r hna
  by_cases hv : ValidQuery s r
  · by_cases hp : Permitted s.entries r
    · rcases hp with ⟨a, ha, ma, al, _⟩
      exact hna ⟨a, ha, ma, al⟩
    · simp [step, hv, hp]
  · simp [step, hv]

theorem req_deny_overrides : DenyOverrides step := by
  intro s r ho
  by_cases hv : ValidQuery s r
  · by_cases hp : Permitted s.entries r
    · rcases ho with ⟨d, hd, md, de, dle⟩
      rcases hp with ⟨a, ha, ma, al, alt⟩
      have h1 := dle a ha ma al
      have h2 := alt d hd md de
      omega
    · simp [step, hv, hp]
  · simp [step, hv]

theorem req_specific_allow : SpecificAllow step := by
  intro s r hv hp
  simp [step, hv, hp]

theorem req_grant_justified : GrantJustified step := by
  intro s r h
  simp [step] at h
  split_ifs at h with hv hp
  · exact hp
  · contradiction
  · contradiction

theorem req_order_independent : OrderIndependent step := by
  intro s r l hperm
  simp [step]
  split_ifs with hv
  · have hpermP : Permitted s.entries r ↔ Permitted l r := by
      constructor
      · intro hP
        rcases hP with ⟨a, ha, ma, al, forall_a⟩
        refine ⟨a, (hperm.mem_of_perm ha).mp ha, ma, al, fun d hd md de => ?⟩
        have hd' := (hperm.mem_of_perm hd).mp hd
        exact forall_a d hd' md de
      · intro hP
        rcases hP with ⟨a, ha, ma, al, forall_a⟩
        refine ⟨a, (hperm.mem_of_perm ha).mpr ha, ma, al, fun d hd md de => ?⟩
        have hd' := (hperm.mem_of_perm hd).mpr hd
        exact forall_a d hd' md de
    simp [hpermP]
  · rfl

theorem req_denial_explained : DenialExplained step := by
  intro s r hden
  simp [step] at hden
  split_ifs at hden with hv hp
  · contradiction
  · by_cases ha : HasAllow s.entries r
    · right
      by_contra hno
      rcases hno with ⟨d, hd, md, de, dle⟩
      rcases ha with ⟨a0, ha0, ma0, al0⟩
      have hperm : Permitted s.entries r := by
        refine ⟨a0, ha0, ma0, al0, fun d' hd' md' de' => ?⟩
        have h1 := dle a0 ha0 ma0 al0
        have h2 := dle d' hd' md' de'
        exact Nat.le_trans h2 h1
      exact hp hperm
    · left; exact ha
  · contradiction

end Acl
