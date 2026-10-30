import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (.rejected, s)

def myTestDef : Nat := 5

theorem my_append_lemma {α : Type} (l1 l2 : List α) (f : α → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a t ih =>
    calc sumOver ((a :: t) ++ l2) f
        = sumOver (a :: (t ++ l2)) f := by rfl
      _ = f a + sumOver (t ++ l2) f := by rfl
      _ = f a + (sumOver t f + sumOver l2 f) := by rw [ih]
      _ = (f a + sumOver t f) + sumOver l2 f := by omega
      _ = sumOver (a :: t) f + sumOver l2 f := by rfl











theorem arch0_sum_range_fairShare (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by sorry

theorem arch0_indexOf_cons_ne (x a : AccountId) (xs : List AccountId) (h : a ≠ x) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  simp [indexOf?, Ne.symm h]


theorem arch0_sumOver_range_succ_head (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f
      = f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by
  have hmap : ∀ (l : List Nat) (g : Nat → Nat), sumOver (l.map g) f = sumOver l (fun i => f (g i)) := by
    intro l g
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  have h : List.range (n + 1) = 0 :: (List.range n).map (· + 1) := by
    simp [List.range_succ_eq_map]
  rw [h]
  simp [hmap]


theorem arch0_sumOver_indexOf_range (l : List AccountId) (f : Nat → Int) (hl : l.Nodup) :
    sumOver l (fun a => match indexOf? l a with
                         | some i => f i
                         | none => 0)
      = sumOver (List.range l.length) (fun i => f i) := by
  induction l generalizing f with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    have hhead : (match indexOf? (x :: xs) x with | some i => f i | none => 0) = f 0 := by
      simp [indexOf?]
    have hne_symm : ∀ a ∈ xs, a ≠ x := fun a ha heq => hl.1 (heq ▸ ha)
    have hcongr : ∀ a ∈ xs,
        (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0) a
        = (fun a => match indexOf? xs a with | some i => f (i + 1) | none => 0) a := by
      intro a ha
      have hne : a ≠ x := hne_symm a ha
      have hmap := arch0_indexOf_cons_ne x a xs hne
      simp only
      rw [hmap]
      cases h : indexOf? xs a with
      | none => rfl
      | some i => rfl
    have hsum_xs : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0)
        = sumOver xs (fun a => match indexOf? xs a with | some i => f (i + 1) | none => 0) :=
      sumOver_congr xs _ _ hcongr
    have ih' := ih (fun i => f (i + 1)) hl.2
    have hsucc := arch0_sumOver_range_succ_head xs.length f
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    simp only [sumOver_cons]
    rw [hhead, hsum_xs, ih', hlen, hsucc]


theorem arch0_shareOf_eq_zero_of_not_mem (r : Request) (a : AccountId) (h : a ∉ r.recipients) :
    shareOf r a = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none h]


theorem arch0_sum_recipients_share (r : Request) (hnd : r.recipients.Nodup)
    (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have hlen : 0 < r.recipients.length := by
    exact Nat.pos_of_ne_zero (fun h => hne (List.length_eq_zero_iff.mp h))
  have hrewrite : ∀ a ∈ r.recipients,
      (fun a => (shareOf r a : Int)) a
      = (fun a => match indexOf? r.recipients a with
                   | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int)
                   | none => 0) a := by
    intro a _
    simp only [shareOf]
    cases h : indexOf? r.recipients a <;> rfl
  rw [sumOver_congr r.recipients _ _ hrewrite]
  rw [arch0_sumOver_indexOf_range r.recipients (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int)) hnd]
  exact arch0_sum_range_fairShare r.amount r.recipients.length hlen


theorem arch0_sumOver_eq_of_subset (L l : List AccountId) (f : AccountId → Int)
    (hL : L.Nodup) (hl : l.Nodup) (hsub : ∀ x ∈ l, x ∈ L)
    (hzero : ∀ x, x ∉ l → f x = 0) :
    sumOver L f = sumOver l f := by sorry

theorem arch0_sum_accounts_share (s : State) (r : Request) (hs : s.accounts.Nodup)
    (hr : r.recipients.Nodup) (hne : r.recipients ≠ [])
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have hzero : ∀ x, x ∉ r.recipients → (fun a => (shareOf r a : Int)) x = 0 := by
    intro x hx
    simp only
    have h := arch0_shareOf_eq_zero_of_not_mem r x hx
    simp [h]
  have heq := arch0_sumOver_eq_of_subset s.accounts r.recipients (fun a => (shareOf r a : Int)) hs hr hsub hzero
  rw [heq]
  exact arch0_sum_recipients_share r hr hne




theorem arch0_valid_of_ok (s : State) (r : Request) :
    (step s r).1 = .ok → ValidPayout s r := by
  intro h
  unfold step at h
  by_cases hv : ValidPayout s r
  · exact hv
  · simp [hv] at h

theorem arch0_sum_expectedBalance (s : State) (r : Request) (h : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = total s := by
  obtain ⟨hs, _, hne, hr, _, hsrcMem, hsub, _, _, _⟩ := h
  have hShare : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
    arch0_sum_accounts_share s r hs hr hne hsub
  have hDed : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) = (r.amount : Int) := by
    have := sumOver_ite_eq hs r.source (r.amount : Int)
    simpa [hsrcMem] using this
  have hexp : (fun a => expectedBalance s r a) = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (shareOf r a : Int)) := rfl
  have hsum : sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) + sumOver s.accounts (fun a => (shareOf r a : Int)) := by
    rw [hexp]
    rw [sumOver_add]
    rw [sumOver_sub]
  rw [hsum, hDed, hShare]
  unfold total
  omega

theorem arch0_sum_accounts_share_aux_trivial : True := trivial

theorem tmp_fairShare_int_check2 (amount n i : Nat) :
    (fairShare amount n i : Int)
      = (amount / n : Int) + (if i < amount % n then (1 : Int) else 0) := by
  unfold fairShare
  by_cases h : i < amount % n <;> simp [h]

theorem arch0_sum_recipients_share_proof (r : Request) (hnd : r.recipients.Nodup)
    (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have hlen : 0 < r.recipients.length := by
    exact Nat.pos_of_ne_zero (fun h => hne (List.length_eq_zero_iff.mp h))
  have hrewrite : ∀ a ∈ r.recipients,
      (fun a => (shareOf r a : Int)) a
      = (fun a => match indexOf? r.recipients a with
                   | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int)
                   | none => 0) a := by
    intro a _
    simp only [shareOf]
    cases h : indexOf? r.recipients a <;> rfl
  rw [sumOver_congr r.recipients _ _ hrewrite]
  rw [arch0_sumOver_indexOf_range r.recipients (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int)) hnd]
  exact arch0_sum_range_fairShare r.amount r.recipients.length hlen

theorem arch0_fairShare_int_proof (amount n i : Nat) :
    (fairShare amount n i : Int)
      = (amount / n : Int) + (if i < amount % n then (1 : Int) else 0) := by
  unfold fairShare
  by_cases h : i < amount % n <;> simp [h]

theorem arch0_sumOver_indexOf_range_test2 (l : List AccountId) (f : Nat → Int) (hl : l.Nodup) :
    sumOver l (fun a => match indexOf? l a with
                         | some i => f i
                         | none => 0)
      = sumOver (List.range l.length) (fun i => f i) := by
  induction l generalizing f with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    have hhead : (match indexOf? (x :: xs) x with | some i => f i | none => 0) = f 0 := by
      simp [indexOf?]
    have hne_symm : ∀ a ∈ xs, a ≠ x := fun a ha heq => hl.1 (heq ▸ ha)
    have hcongr : ∀ a ∈ xs,
        (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0) a
        = (fun a => match indexOf? xs a with | some i => f (i + 1) | none => 0) a := by
      intro a ha
      have hne : a ≠ x := hne_symm a ha
      have hmap := arch0_indexOf_cons_ne x a xs hne
      simp only
      rw [hmap]
      cases h : indexOf? xs a with
      | none => rfl
      | some i => rfl
    have hsum_xs : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => f i | none => 0)
        = sumOver xs (fun a => match indexOf? xs a with | some i => f (i + 1) | none => 0) :=
      sumOver_congr xs _ _ hcongr
    have ih' := ih (fun i => f (i + 1)) hl.2
    have hsucc := arch0_sumOver_range_succ_head xs.length f
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    simp only [sumOver_cons]
    rw [hhead, hsum_xs, ih', hlen, hsucc]

theorem arch0_sumOver_range_succ_head_aux_map (l : List Nat) (g : Nat → Nat) (f : Nat → Int) :
    sumOver (l.map g) f = sumOver l (fun i => f (g i)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem arch0_sumOver_range_succ_head_proof (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f
      = f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by
  have h : List.range (n + 1) = 0 :: (List.range n).map (· + 1) := by
    simp [List.range_succ_eq_map]
  rw [h]
  simp [arch0_sumOver_range_succ_head_aux_map]

theorem arch0_sumOver_range_succ_head_inline_test (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f
      = f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by
  have hmap : ∀ (l : List Nat) (g : Nat → Nat), sumOver (l.map g) f = sumOver l (fun i => f (g i)) := by
    intro l g
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  have h : List.range (n + 1) = 0 :: (List.range n).map (· + 1) := by
    simp [List.range_succ_eq_map]
  rw [h]
  simp [hmap]

def arch0_erase_test (l : List AccountId) (a : AccountId) : List AccountId :=
  match l with
  | [] => []
  | x :: xs => if x = a then xs else x :: arch0_erase_test xs a
#check @List.nodup_cons

theorem arch0_erase_mem_test (l : List AccountId) (a z : AccountId) (h : z ∈ arch0_erase_test l a) : z ∈ l := by
  induction l with
  | nil => simp [arch0_erase_test] at h
  | cons y ys ih =>
    simp only [arch0_erase_test] at h ⊢
    by_cases hy : y = a
    · simp [hy] at h ⊢
      exact Or.inr h
    · simp [hy] at h ⊢
      cases h with
      | inl heq => exact Or.inl heq
      | inr hmem => exact Or.inr (ih hmem)

theorem tmp_sum_zero (l : List AccountId) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons y ys ih => simp [sumOver_cons, ih]
#check @sumOver_ite_eq

theorem arch0_subset_mem_erase2 {l : List AccountId} {a z : AccountId} (h : z ∈ l) (hne : z ≠ a) : z ∈ arch0_erase_test l a := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [arch0_erase_test]
    by_cases hy : y = a
    · simp [hy]
      simp at h
      cases h with
      | inl heq =>
        have : z = a := heq.trans hy
        exact absurd this hne
      | inr hmem => exact hmem
    · simp [hy]
      simp at h
      cases h with
      | inl heq => exact Or.inl heq
      | inr hmem => exact Or.inr (ih hmem)

theorem arch0_erase_eq_self (l : List AccountId) (a : AccountId) (h : a ∉ l) : arch0_erase_test l a = l := by
  induction l with
  | nil => simp [arch0_erase_test]
  | cons y ys ih =>
    simp only [arch0_erase_test]
    simp at h
    simp [Ne.symm h.1, ih h.2]

theorem req_valid_succeeds : ValidSucceeds step := fun s r h => by
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := fun s r h => by
  simp [step, h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hV : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hV
    exact hauth
  · simp [step, hV] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hV : ValidPayout s r
  · simp [step, hV]
  · simp [step, hV] at h

theorem req_idempotency : Idempotent step := by
  intro s r h
  have hv : ValidPayout s r := by
    by_cases hc : ValidPayout s r
    · exact hc
    · have hrej : (step s r).1 = .rejected := by simp [step, hc]
      rw [hrej] at h
      exact absurd h (by decide)
  have hstep : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
    simp [step, hv]
  have hfst : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
    rw [hstep]
  constructor
  · intro x
    rw [hfst]
    simp only [List.mem_cons]
  · have hnvalid : ¬ ValidPayout (step s r).2 r := by
      intro hv2
      obtain ⟨_, _, _, _, _, _, _, _, _, hnotin⟩ := hv2
      rw [hfst] at hnotin
      simp only at hnotin
      exact hnotin (List.mem_cons.mpr (Or.inl rfl))
    have h2 := req_invalid_noop _ _ hnvalid
    exact h2

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hV : ValidPayout s r
  · have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      simp [step, hV]
    have ha' : a ∈ s.accounts := by rw [h2] at ha; simpa using ha
    rw [h2]
    show 0 ≤ expectedBalance s r a
    obtain ⟨_, _, _, _, hsrcNot, _, _, _, hle, _⟩ := hV
    have hnn_a : 0 ≤ s.balance a := hnn a ha'
    by_cases heq : a = r.source
    · subst heq
      have hshare : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hsrcNot]
      unfold expectedBalance
      simp [hshare]
      omega
    · unfold expectedBalance
      simp [heq]
      omega
  · have h2 : (step s r).2 = s := by simp [step, hV]
    rw [h2] at ha ⊢
    exact hnn a ha

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  by_cases hV : ValidPayout s r
  · obtain ⟨hNodup, hpos, hne, hrecNodup, hsrcNot, hsrcMem, hrecMem, hauth, hle, htxNot⟩ := hV
    have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] :=
      (req_effects s r hok).2.2 _
    rw [hbal]
    have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hne_src : r.recipients[i] ≠ r.source := fun heq => hsrcNot (heq ▸ hmem)
    have hidx : indexOf? r.recipients r.recipients[i] = some i :=
      indexOf?_getElem hrecNodup i hi
    unfold expectedBalance shareOf
    rw [hidx, if_neg hne_src]
    simp only [Int.sub_zero]
    omega
  · have hrej : (step s r).1 = .rejected := by simp [step, hV]
    rw [hrej] at hok
    simp at hok

theorem req_conservation   : Conserves step := by
  intro s r hOk
  have hValid : ValidPayout s r := arch0_valid_of_ok s r hOk
  have hEff := req_effects s r hOk
  have hSum : total (step s r).2
      = sumOver s.accounts (fun a => expectedBalance s r a) := by
    show sumOver (step s r).2.accounts (step s r).2.balance = _
    rw [hEff.1]
    exact sumOver_congr s.accounts _ _ (fun a _ => hEff.2.2 a)
  rw [hSum, arch0_sum_expectedBalance s r hValid]

end Payout
