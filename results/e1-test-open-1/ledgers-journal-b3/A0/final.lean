import Journal.Spec
import Journal.Lemmas

namespace Journal

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def step : Impl := fun s e =>
  if _h : ValidEntry s e then
    (.ok, ⟨s.accounts, fun a => s.balance a + netOf e.lines a, e.id :: s.posted⟩)
  else
    (.rejected, s)

private theorem step_ok_imp_valid {s : State} {e : Entry} (h : (step s e).1 = .ok) : ValidEntry s e := by
  have hem : ValidEntry s e ∨ ¬ ValidEntry s e := Classical.em _
  cases hem with
  | inl hv => exact hv
  | inr hnv =>
    have hs : step s e = (.rejected, s) := by
      unfold step
      simp [hnv]
    have h1 : (step s e).1 = .rejected := by rw [hs]
    rw [h1] at h
    simp at h

private theorem sumOver_zero {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem sumOver_swap {α β : Type} (l₁ : List α) (l₂ : List β) (f : α → β → Int) :
    sumOver l₁ (fun a => sumOver l₂ (fun b => f a b)) =
    sumOver l₂ (fun b => sumOver l₁ (fun a => f a b)) := by
  induction l₁ with
  | nil =>
    simp only [sumOver_nil]
    exact (sumOver_zero l₂).symm
  | cons a l₁ ih =>
    simp only [sumOver_cons]
    calc sumOver l₂ (fun b => f a b) + sumOver l₁ (fun a => sumOver l₂ (fun b => f a b))
        = sumOver l₂ (fun b => f a b) + sumOver l₂ (fun b => sumOver l₁ (fun a => f a b)) := by rw [ih]
      _ = sumOver l₂ (fun b => f a b + sumOver l₁ (fun a => f a b)) := by rw [← sumOver_add]
      _ = sumOver l₂ (fun b => sumOver (a :: l₁) (fun a => f a b)) := by simp [sumOver_cons]

private theorem sumOver_netOf_eq (acc : List AccountId) (ls : List Line) (hl : acc.Nodup) :
    sumOver acc (fun a => netOf ls a) = sumOver ls (fun l => if l.1 ∈ acc then l.2 else 0) := by
  unfold netOf
  have hswap := sumOver_swap acc ls (fun a l => if l.1 = a then l.2 else 0)
  rw [hswap]
  apply sumOver_congr
  intro l _
  have h : (fun a => if l.1 = a then l.2 else (0 : Int)) = (fun a => if a = l.1 then l.2 else 0) := by
    funext a
    by_cases ha : l.1 = a <;> by_cases hb : a = l.1 <;> simp_all
  rw [h]
  exact sumOver_ite_eq hl l.1 l.2

private theorem sumOver_netOf_eq_lineSum (acc : List AccountId) (ls : List Line)
    (hl : acc.Nodup) (hknown : ∀ l ∈ ls, l.1 ∈ acc) :
    sumOver acc (fun a => netOf ls a) = lineSum ls := by
  rw [sumOver_netOf_eq acc ls hl]
  unfold lineSum
  apply sumOver_congr
  intro l hlmem
  have hk := hknown l hlmem
  simp [hk]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hv
  show (step s e).1 = .ok
  unfold step
  simp [hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hv
  show step s e = (.rejected, s)
  unfold step
  simp [hv]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hOk l hl
  have hv := step_ok_imp_valid hOk
  exact hv.2.2.1 l hl

theorem req_balanced : Balanced step := by
  intro s e hOk
  have hv := step_ok_imp_valid hOk
  exact hv.2.2.2.2.1

theorem req_effects : Effects step := by
  intro s e hOk
  have hv := step_ok_imp_valid hOk
  have hstep : step s e = (.ok, ⟨s.accounts, fun a => s.balance a + netOf e.lines a, e.id :: s.posted⟩) := by
    unfold step
    simp [hv]
  constructor
  · have h : (step s e).2.accounts = s.accounts := by rw [hstep]
    exact h
  · intro a
    have h : (step s e).2.balance a = s.balance a + netOf e.lines a := by
      rw [hstep]
    exact h

theorem req_idempotency : Idempotent step := by
  intro s e hOk
  have hv := step_ok_imp_valid hOk
  have hstep : step s e = (.ok, ⟨s.accounts, fun a => s.balance a + netOf e.lines a, e.id :: s.posted⟩) := by
    unfold step
    simp [hv]
  have hposted : (step s e).2.posted = e.id :: s.posted := by rw [hstep]
  have hmem : e.id ∈ (step s e).2.posted := by rw [hposted]; simp
  have hNotValid : ¬ ValidEntry (step s e).2 e := by
    intro hContra
    exact hContra.2.2.2.2.2 hmem
  have hstep2 : step (step s e).2 e = (.rejected, (step s e).2) := by
    unfold step
    exact dif_neg hNotValid
  constructor
  · intro x
    rw [hposted]
    simp
  · exact hstep2

theorem req_trial_balance : TrialBalance step := by
  intro s e hOk
  have hv := step_ok_imp_valid hOk
  have hstep : step s e = (.ok, ⟨s.accounts, fun a => s.balance a + netOf e.lines a, e.id :: s.posted⟩) := by
    unfold step
    simp [hv]
  have hAcc : (step s e).2.accounts = s.accounts := by rw [hstep]
  show total (step s e).2 = total s
  unfold total
  rw [hAcc]
  have hBal : ∀ a, (step s e).2.balance a = s.balance a + netOf e.lines a := by
    intro a
    rw [hstep]
  have hCong : sumOver s.accounts (step s e).2.balance = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    apply sumOver_congr
    intro a _
    exact hBal a
  rw [hCong]
  rw [sumOver_add]
  have hNetZero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
    rw [sumOver_netOf_eq_lineSum s.accounts e.lines hv.1 hv.2.2.1]
    exact hv.2.2.2.2.1
  rw [hNetZero]
  simp

end Journal
