import EulerLending.Spec
/-!
Reference solution: the Euler v1 market logic with the liquidity check added to
`donateToReserves`, as `withdraw`, `mint` and `transferFrom` already perform it. Every
operation that can lower an account's health checks that account after the update.
-/
namespace EulerLending

/-- Replace the position of account `u`. -/
def setAcct (s : St) (u : Nat) (a : Acct) : St :=
  { s with acct := fun w => if w = u then a else s.acct w }

def step : Impl := fun s op =>
  match op with
  | .deposit u x =>
    let a : Acct := ⟨(s.acct u).e + x, (s.acct u).d⟩
    if (s.acct u).d = 0 ∨ Healthy a then some { setAcct s u a with cash := s.cash + x } else none
  | .withdraw u x =>
    let a : Acct := ⟨(s.acct u).e - x, (s.acct u).d⟩
    if x ≤ (s.acct u).e ∧ x ≤ s.cash ∧ Healthy a then
      some { setAcct s u a with cash := s.cash - x } else none
  | .borrow u x =>
    let a : Acct := ⟨(s.acct u).e, (s.acct u).d + x⟩
    if x ≤ s.cash ∧ Healthy a then some { setAcct s u a with cash := s.cash - x } else none
  | .repay u x =>
    let y := min x (s.acct u).d
    some { setAcct s u ⟨(s.acct u).e, (s.acct u).d - y⟩ with cash := s.cash + y }
  | .mint u x =>
    let a : Acct := ⟨(s.acct u).e + x, (s.acct u).d + x⟩
    if Healthy a then some (setAcct s u a) else none
  | .burn u x =>
    let y := min x (s.acct u).d
    let a : Acct := ⟨(s.acct u).e - y, (s.acct u).d - y⟩
    if y ≤ (s.acct u).e ∧ Healthy a then some (setAcct s u a) else none
  | .transfer u v x =>
    let a : Acct := ⟨(s.acct u).e - x, (s.acct u).d⟩
    let b : Acct := ⟨(s.acct v).e + x, (s.acct v).d⟩
    if u ≠ v ∧ x ≤ (s.acct u).e ∧ Healthy a ∧ ((s.acct v).d = 0 ∨ Healthy b) then
      some (setAcct (setAcct s u a) v b) else none
  | .donate u x =>
    let a : Acct := ⟨(s.acct u).e - x, (s.acct u).d⟩
    if x ≤ (s.acct u).e ∧ Healthy a then
      some { setAcct s u a with reserves := s.reserves + x } else none
  | .liquidate l v r =>
    let y := liqYield (s.acct v) r
    let b : Acct := ⟨(s.acct l).e + y, (s.acct l).d + r + liqFee r⟩
    if l ≠ v ∧ ¬ Healthy (s.acct v) ∧ r ≤ maxRepay (s.acct v) ∧ Healthy b then
      some { setAcct (setAcct s v ⟨(s.acct v).e - y, (s.acct v).d - r⟩) l b with
        reserves := s.reserves + liqFee r } else none

theorem setAcct_same (s : St) (u : Nat) (a : Acct) : (setAcct s u a).acct u = a := by
  simp [setAcct]

theorem setAcct_other (s : St) (u w : Nat) (a : Acct) (h : w ≠ u) :
    (setAcct s u a).acct w = s.acct w := by
  simp [setAcct, h]

theorem healthy_mono {a b : Acct} (h : Healthy a) (hd : b.d ≤ a.d) (he : a.e ≤ b.e) :
    Healthy b := by
  unfold Healthy at *
  omega

theorem healthy_zero : Healthy ⟨0, 0⟩ := by
  unfold Healthy; decide

theorem req_honest_flow : HonestFlow step := by
  unfold HonestFlow; decide

theorem req_allowed_succeeds : AllowedSucceeds step := by
  intro s op h
  cases op <;> simp only [Allowed] at h <;> simp [step, h]

theorem req_effects : Effects step := by
  intro s op s' h
  cases op with
  | deposit u x =>
    simp only [step] at h
    split at h
    · cases h
      refine ⟨setAcct_same _ _ _, fun w hw => setAcct_other _ _ _ _ hw, rfl, rfl⟩
    · cases h
  | withdraw u x =>
    simp only [step] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨hc.1, hc.2.1, setAcct_same _ _ _, fun w hw => setAcct_other _ _ _ _ hw, rfl, rfl⟩
    · cases h
  | borrow u x =>
    simp only [step] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨hc.1, setAcct_same _ _ _, fun w hw => setAcct_other _ _ _ _ hw, rfl, rfl⟩
    · cases h
  | repay u x =>
    simp only [step] at h
    cases h
    exact ⟨setAcct_same _ _ _, fun w hw => setAcct_other _ _ _ _ hw, rfl, rfl⟩
  | mint u x =>
    simp only [step] at h
    split at h
    · cases h
      exact ⟨setAcct_same _ _ _, fun w hw => setAcct_other _ _ _ _ hw, rfl, rfl⟩
    · cases h
  | burn u x =>
    simp only [step] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨hc.1, setAcct_same _ _ _, fun w hw => setAcct_other _ _ _ _ hw, rfl, rfl⟩
    · cases h
  | transfer u v x =>
    simp only [step] at h
    split at h
    · rename_i hc
      cases h
      refine ⟨hc.1, hc.2.1, ?_, setAcct_same _ _ _, ?_, rfl, rfl⟩
      · rw [setAcct_other _ _ _ _ hc.1, setAcct_same]
      · intro w hu hv
        rw [setAcct_other _ _ _ _ hv, setAcct_other _ _ _ _ hu]
    · cases h
  | donate u x =>
    simp only [step] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨hc.1, setAcct_same _ _ _, fun w hw => setAcct_other _ _ _ _ hw, rfl, rfl⟩
    · cases h
  | liquidate l v r =>
    simp only [step] at h
    split at h
    · rename_i hc
      cases h
      refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_, setAcct_same _ _ _, ?_, rfl, rfl⟩
      · show (setAcct (setAcct s v _) l _).acct v = _
        rw [setAcct_other _ _ _ _ (Ne.symm hc.1), setAcct_same]
      · intro w hl hv
        show (setAcct (setAcct s v _) l _).acct w = _
        rw [setAcct_other _ _ _ _ hl, setAcct_other _ _ _ _ hv]
    · cases h

theorem req_actor_healthy : ActorHealthy step := by
  intro s op s' w h hw
  have he := req_effects s op s' h
  cases op with
  | deposit u x => exact hw.elim
  | repay u x => exact hw.elim
  | withdraw u x =>
    simp only [Checked] at hw; subst hw
    simp only [step] at h
    split at h
    · rename_i hc; rw [he.2.2.1]; exact hc.2.2
    · cases h
  | borrow u x =>
    simp only [Checked] at hw; subst hw
    simp only [step] at h
    split at h
    · rename_i hc; rw [he.2.1]; exact hc.2
    · cases h
  | mint u x =>
    simp only [Checked] at hw; subst hw
    simp only [step] at h
    split at h
    · rename_i hc; rw [he.1]; exact hc
    · cases h
  | burn u x =>
    simp only [Checked] at hw; subst hw
    simp only [step] at h
    split at h
    · rename_i hc; rw [he.2.1]; exact hc.2
    · cases h
  | transfer u v x =>
    simp only [Checked] at hw; subst hw
    simp only [step] at h
    split at h
    · rename_i hc; rw [he.2.2.1]; exact hc.2.2.1
    · cases h
  | donate u x =>
    simp only [Checked] at hw; subst hw
    simp only [step] at h
    split at h
    · rename_i hc; rw [he.2.1]; exact hc.2
    · cases h
  | liquidate l v r =>
    simp only [Checked] at hw; subst hw
    simp only [step] at h
    split at h
    · rename_i hc; rw [he.2.2.2.2.1]; exact hc.2.2.2
    · cases h

theorem req_stays_healthy : StaysHealthy step := by
  intro s op s' w h hw
  have hact := req_actor_healthy s op s' w h
  have he := req_effects s op s' h
  cases op with
  | deposit u x =>
    by_cases hu : w = u
    · subst hu; rw [he.1]; exact healthy_mono hw (Nat.le_refl _) (Nat.le_add_right _ _)
    · rw [he.2.1 w hu]; exact hw
  | withdraw u x =>
    by_cases hu : w = u
    · exact hact hu
    · rw [he.2.2.2.1 w hu]; exact hw
  | borrow u x =>
    by_cases hu : w = u
    · exact hact hu
    · rw [he.2.2.1 w hu]; exact hw
  | repay u x =>
    by_cases hu : w = u
    · subst hu; rw [he.1]; exact healthy_mono hw (Nat.sub_le _ _) (Nat.le_refl _)
    · rw [he.2.1 w hu]; exact hw
  | mint u x =>
    by_cases hu : w = u
    · exact hact hu
    · rw [he.2.1 w hu]; exact hw
  | burn u x =>
    by_cases hu : w = u
    · exact hact hu
    · rw [he.2.2.1 w hu]; exact hw
  | transfer u v x =>
    by_cases hu : w = u
    · exact hact hu
    · by_cases hv : w = v
      · subst hv; rw [he.2.2.2.1]; exact healthy_mono hw (Nat.le_refl _) (Nat.le_add_right _ _)
      · rw [he.2.2.2.2.1 w hu hv]; exact hw
  | donate u x =>
    by_cases hu : w = u
    · exact hact hu
    · rw [he.2.2.1 w hu]; exact hw
  | liquidate l v r =>
    by_cases hl : w = l
    · exact hact hl
    · by_cases hv : w = v
      · subst hv; exact absurd hw he.2.1
      · rw [he.2.2.2.2.2.1 w hl hv]; exact hw

theorem req_no_bad_debt : NoBadDebt step := by
  intro s hs
  induction hs with
  | genesis => intro u; exact healthy_zero
  | step op _ h ih => intro u; exact req_stays_healthy _ op _ u h (ih u)

end EulerLending
