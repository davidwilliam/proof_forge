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

theorem req_authorization_aux : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · simp [hv] at h

def foo := 1

theorem myhelp1 (s : State) (r : Request) (hv : ValidPayout s r) : (step s r).1 = .ok := by simp [step, hv]

theorem req_idempotency_aux2 : Idempotent step := by
  intro s r hok
  have hv : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · exfalso
      have hstep : step s r = (.rejected, s) := by unfold step; simp [h]
      have heq : (step s r).1 = .rejected := by rw [hstep]
      rw [hok] at heq
      exact (Outcome.noConfusion heq)
  have hstep_eq : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
    unfold step; simp [hv]
  have h2 : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
    rw [hstep_eq]
  constructor
  · intro x
    rw [h2]
    simp
  · have hnv2 : ¬ ValidPayout { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } r := by
      intro hcon
      unfold ValidPayout at hcon
      obtain ⟨_, _, _, _, _, _, _, _, _, hnotin⟩ := hcon
      exact hnotin (by simp)
    have hstep2 : step { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } r = (.rejected, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step; simp [hnv2]
    calc step (step s r).2 r = step { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } r := by rw [h2]
      _ = (.rejected, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := hstep2
      _ = (.rejected, (step s r).2) := by rw [h2]

theorem tmp_nn_test (s : State) (r : Request) (hv : ValidPayout s r) :
    (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
  unfold step
  simp [hv]

theorem req_nonnegative_aux3 : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · obtain ⟨hnodup, hpos, hne, hrnodup, hsrcnotin, hsrcmem, hmem, hauth, hle, htx⟩ := hv
    have hstep2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) :=
      tmp_nn_test s r ⟨hnodup, hpos, hne, hrnodup, hsrcnotin, hsrcmem, hmem, hauth, hle, htx⟩
    rw [hstep2] at ha ⊢
    simp only at ha ⊢
    have h0 : 0 ≤ s.balance a := hnn a ha
    unfold expectedBalance
    by_cases heq : a = r.source
    · subst heq
      rw [if_pos rfl]
      have hshare0 : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hsrcnotin]
      rw [hshare0]
      omega
    · rw [if_neg heq]
      omega
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hv]
    have h2 : (step s r).2 = s := by rw [hstep]
    rw [h2] at ha ⊢
    exact hnn a ha

theorem sumOver_append_test {α : Type} (l1 l2 : List α) (f : α → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, sumOver_cons, ih]; omega

#check List.erase
#check List.range

theorem arch0_valid_of_ok (s : State) (r : Request)
    (h : (step s r).1 = .ok) : ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · have hstep : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [hstep] at h
    exact Outcome.noConfusion h


theorem arch0_step_eq_of_valid (s : State) (r : Request) (hv : ValidPayout s r) :
    step s r = (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied }) := by
  unfold step
  simp [hv]


theorem arch0_sum_fairShare_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by
  have hrange_eq : ∀ k : Nat, List.range (k + 1) = List.range k ++ [k] := by
    intro k; simp [List.range_succ]
  have hcast1 : ∀ k : Nat, ((k + 1 : Nat) : Int) = (k : Int) + 1 := by intro k; simp
  have haddmul : ∀ (k : Nat) (c : Int), ((k : Int) + 1) * c = (k : Int) * c + c := by
    intro k c; simp only [Int.add_mul, Int.one_mul]
  have hconst : ∀ (k : Nat) (c : Int),
      sumOver (List.range k) (fun _ => c) = (k : Int) * c := by
    intro k c
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hrange_eq k, sumOver_append_test, ih]
      simp only [sumOver_cons, sumOver_nil, Int.add_zero]
      rw [hcast1 k, haddmul k c]
  have hge : ∀ (k m : Nat), k ≤ m →
      sumOver (List.range k) (fun i => if i < m then (1 : Int) else 0) = (k : Int) := by
    intro k
    induction k with
    | zero => intro m _; simp
    | succ k ih =>
      intro m hle
      have hle' : k ≤ m := by omega
      have hlt : k < m := by omega
      rw [hrange_eq k, sumOver_append_test, ih m hle']
      simp only [sumOver_cons, sumOver_nil, hlt, ↓reduceIte]
      push_cast
      omega
  have hle2 : ∀ (m k : Nat), m ≤ k →
      sumOver (List.range k) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := by
    intro m k
    induction k generalizing m with
    | zero =>
      intro h
      have hm : m = 0 := by omega
      subst hm; simp
    | succ k ih =>
      intro h
      rw [hrange_eq k, sumOver_append_test]
      have hsingle : sumOver ([k] : List Nat) (fun i => if i < m then (1 : Int) else 0) = (if k < m then (1 : Int) else 0) := by
        simp [sumOver]
      rw [hsingle]
      by_cases hmn : m ≤ k
      · have h1 : sumOver (List.range k) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := ih m hmn
        have hnm : ¬ k < m := by omega
        have hif : (if k < m then (1 : Int) else 0) = 0 := by simp [hnm]
        rw [h1, hif]; simp
      · have hmeq : m = k + 1 := by omega
        subst hmeq
        have hg : sumOver (List.range k) (fun i => if i < k + 1 then (1 : Int) else 0) = (k : Int) :=
          hge k (k + 1) (by omega)
        have hlt : k < k + 1 := by omega
        have hif : (if k < k + 1 then (1 : Int) else 0) = 1 := by simp [hlt]
        rw [hg, hif]
        rw [hcast1 k]
  have hdecomp : ∀ i ∈ List.range n,
      (fun i => (fairShare amount n i : Int)) i
        = (fun i => ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0)) i := by
    intro i _
    simp only
    unfold fairShare
    by_cases h : i < amount % n <;> simp [h]
  have hcongr : sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = sumOver (List.range n) (fun i => ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0)) :=
    sumOver_congr _ _ _ (fun a ha => hdecomp a ha)
  rw [hcongr, sumOver_add]
  have h1 : sumOver (List.range n) (fun _ => ((amount / n : Nat) : Int)) = (n : Int) * ((amount / n : Nat) : Int) :=
    hconst n _
  have hmod_le : amount % n ≤ n := by
    have hlt : amount % n < n := Nat.mod_lt _ hn
    omega
  have h2 : sumOver (List.range n) (fun i => if i < amount % n then (1 : Int) else 0) = ((amount % n : Nat) : Int) :=
    hle2 _ _ hmod_le
  rw [h1, h2]
  have h := Nat.div_add_mod amount n
  omega


theorem arch0_sum_shareOf_recipients_range (r : Request) (hn : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by sorry

theorem arch0_sum_shareOf_recipients_amount (r : Request)
    (hn : r.recipients.Nodup) (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have h1 : sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) :=
    arch0_sum_shareOf_recipients_range r hn
  have hpos : 0 < r.recipients.length := by
    cases hlen : r.recipients with
    | nil => simp [hlen] at hne
    | cons _ _ => simp
  have h2 : sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) = (r.amount : Int) :=
    arch0_sum_fairShare_range r.amount r.recipients.length hpos
  rw [h1, h2]


theorem arch0_sum_shareOf_accounts (s : State) (r : Request) (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem arch0_sum_source_indicator (s : State) (r : Request)
    (hnd : s.accounts.Nodup) (hmem : r.source ∈ s.accounts) :
    sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by sorry



theorem arch0_valid_of_ok_test (s : State) (r : Request)
    (h : (step s r).1 = .ok) : ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · have hstep : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [hstep] at h
    exact Outcome.noConfusion h

theorem arch0_step_eq_of_valid_proof (s : State) (r : Request) (hv : ValidPayout s r) :
    step s r = (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied }) := by
  unfold step
  simp [hv]

theorem arch0_total_eq_of_valid (s : State) (r : Request) (hv : ValidPayout s r) :
    total (step s r).2 = total s := by
  have hstep : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
    have heq := arch0_step_eq_of_valid s r hv
    simp [heq]
  have hnd : s.accounts.Nodup := hv.1
  have hmem : r.source ∈ s.accounts := hv.2.2.2.2.2.1
  have hshare : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
    arch0_sum_shareOf_accounts s r hv
  have hsrc : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) :=
    arch0_sum_source_indicator s r hnd hmem
  have htot : total (step s r).2 = sumOver s.accounts (fun a => expectedBalance s r a) := by
    rw [hstep]
    rfl
  rw [htot]
  unfold total
  have hcongr : sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int))) := by
    apply sumOver_congr
    intro a _
    rfl
  rw [hcongr]
  have hsplit : sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int)))
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        + sumOver s.accounts (fun a => (shareOf r a : Int)) :=
    sumOver_add s.accounts
      (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      (fun a => (shareOf r a : Int))
  have hsplit2 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance
        - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) :=
    sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
  rw [hsplit, hsplit2, hshare, hsrc]
  omega

theorem tmp_shareOf_eq_zero (r : Request) (a : AccountId) (h : a ∉ r.recipients) : (shareOf r a : Int) = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none (l := r.recipients) (a := a) h]
  rfl

theorem tmp_sum_zero {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sumOver_cons, ih]

theorem tmp_erase_check (a b : AccountId) (bs : List AccountId) (hb : b ≠ a) :
    (b :: bs).erase a = b :: bs.erase a := by
  simp [hb]

theorem tmp_sum_erase4 (f : AccountId → Int) (l : List AccountId) (a : AccountId) (hl : l.Nodup) (hmem : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f := by
  induction l with
  | nil => simp at hmem
  | cons b bs ih =>
    rw [List.nodup_cons] at hl
    by_cases hb : b = a
    · subst hb
      simp [List.erase_cons_head, sumOver_cons]
    · have hmem' : a ∈ bs := by
        simp only [List.mem_cons] at hmem
        exact hmem.resolve_left (fun h => hb h.symm)
      have herase : (b :: bs).erase a = b :: bs.erase a := by simp [hb]
      rw [herase]
      simp only [sumOver_cons]
      rw [ih hl.2 hmem']
      omega

theorem tmp_mem_erase_of_mem (a b : AccountId) (l : List AccountId) (h : a ∈ l.erase b) : a ∈ l := by
  induction l with
  | nil => simp [List.erase_nil] at h
  | cons x xs ih =>
    by_cases hx : x = b
    · subst hx
      simp [List.erase_cons_head] at h
      simp [h]
    · have her : (x :: xs).erase b = x :: (xs.erase b) := by simp [hx]
      rw [her] at h
      simp only [List.mem_cons] at h ⊢
      cases h with
      | inl heq => exact Or.inl heq
      | inr hmem => exact Or.inr (ih hmem)

theorem tmp_erase_head (a : AccountId) (l : List AccountId) : (a :: l).erase a = l := by
  simp

theorem tmp_mem_erase_of_mem_ne (a b : AccountId) (l : List AccountId) (hmem : a ∈ l) (hne : a ≠ b) : a ∈ l.erase b := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    simp only [List.mem_cons] at hmem
    by_cases hx : x = b
    · subst hx
      have ha : a ∈ xs := by
        cases hmem with
        | inl h => exact absurd h hne
        | inr h => exact h
      simp [List.erase_cons_head, ha]
    · have her : (x :: xs).erase b = x :: (xs.erase b) := by simp [hx]
      rw [her]
      simp only [List.mem_cons]
      cases hmem with
      | inl h =>
        exact Or.inl h
      | inr h =>
        exact Or.inr (ih h)



theorem plan0_sumOver_eq_add_sumOver_erase (f : AccountId → Int)
    (l : List AccountId) (a : AccountId) (hl : l.Nodup) (hmem : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f :=
  tmp_sum_erase4 f l a hl hmem


theorem plan0_of_mem_erase (a b : AccountId) (l : List AccountId)
    (h : a ∈ l.erase b) : a ≠ b ∧ a ∈ l := by sorry





theorem plan0_sum_shareOf_accounts_eq_amount (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have erase_nodup : ∀ (l : List AccountId) (a : AccountId), l.Nodup → (l.erase a).Nodup := by
    intro l a hl
    induction l with
    | nil => simp
    | cons x xs ih =>
      have hnd : xs.Nodup := (List.nodup_cons.mp hl).2
      have hnin : x ∉ xs := (List.nodup_cons.mp hl).1
      by_cases hxa : x = a
      · subst hxa
        simpa [tmp_erase_head] using hnd
      · have her : (x :: xs).erase a = x :: xs.erase a := tmp_erase_check a x xs hxa
        rw [her]
        rw [List.nodup_cons]
        constructor
        · intro hmem
          have hmem2 : x ∈ xs := tmp_mem_erase_of_mem x a xs hmem
          exact hnin hmem2
        · exact ih hnd
  have mem_erase : ∀ (a b : AccountId) (l : List AccountId), l.Nodup → a ∈ l.erase b → a ≠ b ∧ a ∈ l := by
    intro a b l hl h
    induction l with
    | nil => simp [List.erase_nil] at h
    | cons x xs ih =>
      rw [List.nodup_cons] at hl
      obtain ⟨hnin, hnod⟩ := hl
      by_cases hx : x = b
      · subst hx
        simp only [List.erase_cons_head] at h
        constructor
        · intro heq
          subst heq
          exact hnin h
        · exact List.mem_cons_of_mem _ h
      · have her : (x :: xs).erase b = x :: (xs.erase b) := by simp [hx]
        rw [her] at h
        simp only [List.mem_cons] at h ⊢
        cases h with
        | inl heq => exact ⟨fun hab => hx (heq.symm.trans hab), Or.inl heq⟩
        | inr hmem =>
          have ihh := ih hnod hmem
          exact ⟨ihh.1, Or.inr ihh.2⟩
  have subset_eq : ∀ (f : AccountId → Int) (l1 l2 : List AccountId),
      l1.Nodup → l2.Nodup → (∀ x ∈ l2, x ∈ l1) → (∀ x ∈ l1, x ∉ l2 → f x = 0) →
      sumOver l1 f = sumOver l2 f := by
    intro f l1 l2 hl1 hl2 hsub hzero
    induction l1 generalizing l2 with
    | nil =>
      have hempty : l2 = [] := by
        cases l2 with
        | nil => rfl
        | cons y ys =>
          have hmem : y ∈ y :: ys := by simp
          have h := hsub y hmem
          simp at h
      subst hempty
      simp
    | cons a tl ih =>
      have hl1_tail : tl.Nodup := (List.nodup_cons.mp hl1).2
      have ha_notin_tail : a ∉ tl := (List.nodup_cons.mp hl1).1
      by_cases ha_mem : a ∈ l2
      · have h_l2_eq : sumOver l2 f = f a + sumOver (l2.erase a) f :=
          plan0_sumOver_eq_add_sumOver_erase f l2 a hl2 ha_mem
        have h_cons : sumOver (a :: tl) f = f a + sumOver tl f := rfl
        have h_erase_nodup : (l2.erase a).Nodup := erase_nodup l2 a hl2
        have hsub' : ∀ x ∈ l2.erase a, x ∈ tl := by
          intro x hx
          have hpair := mem_erase x a l2 hl2 hx
          have hx_ne : x ≠ a := hpair.1
          have hx_in : x ∈ a :: tl := hsub x hpair.2
          simp at hx_in
          cases hx_in with
          | inl h => exact absurd h hx_ne
          | inr h => exact h
        have hzero' : ∀ x ∈ tl, x ∉ l2.erase a → f x = 0 := by
          intro x hx_tl hx_noterase
          by_cases hx_l2 : x ∈ l2
          · have hx_ne : x ≠ a := by
              intro hx_eq
              subst hx_eq
              exact ha_notin_tail hx_tl
            have hx_in_erase : x ∈ l2.erase a :=
              tmp_mem_erase_of_mem_ne x a l2 hx_l2 hx_ne
            exact absurd hx_in_erase hx_noterase
          · exact hzero x (by simp [hx_tl]) hx_l2
        have ih_eq : sumOver tl f = sumOver (l2.erase a) f :=
          ih (l2.erase a) hl1_tail h_erase_nodup hsub' hzero'
        rw [h_cons, h_l2_eq, ih_eq]
      · have hfa : f a = 0 := hzero a (by simp) ha_mem
        have h_cons : sumOver (a :: tl) f = f a + sumOver tl f := rfl
        have hsub' : ∀ x ∈ l2, x ∈ tl := by
          intro x hx
          have hx_in : x ∈ a :: tl := hsub x hx
          simp at hx_in
          cases hx_in with
          | inl h =>
            subst h
            exact absurd hx ha_mem
          | inr h => exact h
        have hzero' : ∀ x ∈ tl, x ∉ l2 → f x = 0 := by
          intro x hx_tl hx_nmem
          exact hzero x (by simp [hx_tl]) hx_nmem
        have ih_eq : sumOver tl f = sumOver l2 f :=
          ih l2 hl1_tail hl2 hsub' hzero'
        rw [h_cons, hfa, Int.zero_add, ih_eq]
  unfold ValidPayout at hv
  obtain ⟨hnd_acc, hpos, hne, hnd_rec, hsrc_not, hsrc_mem, hsub, hauth, hbal, htx⟩ := hv
  have h_eq : sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => (shareOf r a : Int)) := by
    apply subset_eq _ _ _ hnd_acc hnd_rec hsub
    intro x hx hx_not
    exact tmp_shareOf_eq_zero r x hx_not
  rw [h_eq]
  exact arch0_sum_shareOf_recipients_amount r hnd_rec hne


theorem plan0_shareOf_int_eq_zero (r : Request) (a : AccountId)
    (h : a ∉ r.recipients) : (shareOf r a : Int) = 0 := by
  have hidx : indexOf? r.recipients a = none := indexOf?_eq_none h
  unfold shareOf
  rw [hidx]
  rfl

theorem plan0_sumOver_eq_add_sumOver_erase_proof (f : AccountId → Int)
    (l : List AccountId) (a : AccountId) (hl : l.Nodup) (hmem : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f :=
  tmp_sum_erase4 f l a hl hmem

theorem tmp_check_erase_head (a : AccountId) (l : List AccountId) : (a :: l).erase a = l := by simp

theorem tmp_check_erase_ne (a b : AccountId) (l : List AccountId) (h : a ≠ b) : (a :: l).erase b = a :: l.erase b := by simp [h]

theorem plan0_of_mem_erase_fixed (a b : AccountId) (l : List AccountId) (hl : l.Nodup) (h : a ∈ l.erase b) : a ≠ b ∧ a ∈ l := by
  induction l with
  | nil => simp [List.erase_nil] at h
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotin, hnod⟩ := hl
    by_cases hx : x = b
    · subst hx
      simp only [List.erase_cons_head] at h
      constructor
      · intro heq
        subst heq
        exact hnotin h
      · exact List.mem_cons_of_mem _ h
    · have her : (x :: xs).erase b = x :: (xs.erase b) := by simp [hx]
      rw [her] at h
      simp only [List.mem_cons] at h ⊢
      cases h with
      | inl heq =>
        exact ⟨fun hab => hx (heq.symm.trans hab), Or.inl heq⟩
      | inr hmem =>
        have ihh := ih hnod hmem
        exact ⟨ihh.1, Or.inr ihh.2⟩

theorem plan0_nodup_erase_test (l : List AccountId) (a : AccountId)
    (hl : l.Nodup) : (l.erase a).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hnd : xs.Nodup := (List.nodup_cons.mp hl).2
    have hnin : x ∉ xs := (List.nodup_cons.mp hl).1
    by_cases hxa : x = a
    · subst hxa
      simpa [tmp_erase_head] using hnd
    · have her : (x :: xs).erase a = x :: xs.erase a :=
        tmp_erase_check a x xs hxa
      rw [her]
      rw [List.nodup_cons]
      constructor
      · intro hmem
        have hmem2 : x ∈ xs := tmp_mem_erase_of_mem x a xs hmem
        exact hnin hmem2
      · exact ih hnd

theorem plan0_nodup_erase (l : List AccountId) (a : AccountId)
    (hl : l.Nodup) : (l.erase a).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hnd : xs.Nodup := (List.nodup_cons.mp hl).2
    have hnin : x ∉ xs := (List.nodup_cons.mp hl).1
    by_cases hxa : x = a
    · subst hxa
      simpa [tmp_erase_head] using hnd
    · have her : (x :: xs).erase a = x :: xs.erase a :=
        tmp_erase_check a x xs hxa
      rw [her]
      rw [List.nodup_cons]
      constructor
      · intro hmem
        have hmem2 : x ∈ xs := tmp_mem_erase_of_mem x a xs hmem
        exact hnin hmem2
      · exact ih hnd

theorem plan0_sumOver_eq_of_subset_of_eq_zero_aux2 (f : AccountId → Int)
    (l1 l2 : List AccountId) (hl1 : l1.Nodup) (hl2 : l2.Nodup)
    (hsub : ∀ x ∈ l2, x ∈ l1) (hzero : ∀ x ∈ l1, x ∉ l2 → f x = 0) :
    sumOver l1 f = sumOver l2 f := by
  induction l1 generalizing l2 with
  | nil =>
    have hempty : l2 = [] := by
      cases l2 with
      | nil => rfl
      | cons y ys =>
        have hmem : y ∈ y :: ys := by simp
        have h := hsub y hmem
        simp at h
    subst hempty
    simp
  | cons a tl ih =>
    have hl1_tail : tl.Nodup := (List.nodup_cons.mp hl1).2
    have ha_notin_tail : a ∉ tl := (List.nodup_cons.mp hl1).1
    by_cases ha_mem : a ∈ l2
    · have h_l2_eq : sumOver l2 f = f a + sumOver (l2.erase a) f :=
        plan0_sumOver_eq_add_sumOver_erase f l2 a hl2 ha_mem
      have h_cons : sumOver (a :: tl) f = f a + sumOver tl f := rfl
      have h_erase_nodup : (l2.erase a).Nodup := plan0_nodup_erase l2 a hl2
      have hsub' : ∀ x ∈ l2.erase a, x ∈ tl := by
        intro x hx
        have hpair := plan0_of_mem_erase_fixed x a l2 hl2 hx
        have hx_l2 : x ∈ l2 := hpair.2
        have hx_ne : x ≠ a := hpair.1
        have hx_in : x ∈ a :: tl := hsub x hx_l2
        simp at hx_in
        cases hx_in with
        | inl h => exact absurd h hx_ne
        | inr h => exact h
      have hzero' : ∀ x ∈ tl, x ∉ l2.erase a → f x = 0 := by
        intro x hx_tl hx_noterase
        by_cases hx_l2 : x ∈ l2
        · have hx_ne : x ≠ a := by
            intro hx_eq
            subst hx_eq
            exact ha_notin_tail hx_tl
          have hx_in_erase : x ∈ l2.erase a :=
            tmp_mem_erase_of_mem_ne x a l2 hx_l2 hx_ne
          exact absurd hx_in_erase hx_noterase
        · exact hzero x (by simp [hx_tl]) hx_l2
      have ih_eq : sumOver tl f = sumOver (l2.erase a) f :=
        ih (l2.erase a) hl1_tail h_erase_nodup hsub' hzero'
      rw [h_cons, h_l2_eq, ih_eq]
    · have hfa : f a = 0 := hzero a (by simp) ha_mem
      have h_cons : sumOver (a :: tl) f = f a + sumOver tl f := rfl
      have hsub' : ∀ x ∈ l2, x ∈ tl := by
        intro x hx
        have hx_in : x ∈ a :: tl := hsub x hx
        simp at hx_in
        cases hx_in with
        | inl h =>
          subst h
          exact absurd hx ha_mem
        | inr h => exact h
      have hzero' : ∀ x ∈ tl, x ∉ l2 → f x = 0 := by
        intro x hx_tl hx_nmem
        exact hzero x (by simp [hx_tl]) hx_nmem
      have ih_eq : sumOver tl f = sumOver l2 f :=
        ih l2 hl1_tail hl2 hsub' hzero'
      rw [h_cons, hfa, Int.zero_add, ih_eq]

theorem plan0_sumOver_eq_of_subset_of_eq_zero (f : AccountId → Int)
    (l1 l2 : List AccountId) (hl1 : l1.Nodup) (hl2 : l2.Nodup)
    (hsub : ∀ x ∈ l2, x ∈ l1) (hzero : ∀ x ∈ l1, x ∉ l2 → f x = 0) :
    sumOver l1 f = sumOver l2 f :=
  plan0_sumOver_eq_of_subset_of_eq_zero_aux2 f l1 l2 hl1 hl2 hsub hzero

theorem plan0_sum_shareOf_accounts_eq_amount_proof (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  unfold ValidPayout at hv
  obtain ⟨hnd_acc, hpos, hne, hnd_rec, hsrc_not, hsrc_mem, hsub, hauth, hbal, htx⟩ := hv
  have h_eq : sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => (shareOf r a : Int)) := by
    apply plan0_sumOver_eq_of_subset_of_eq_zero _ _ _ hnd_acc hnd_rec hsub
    intro x hx hx_not
    exact plan0_shareOf_int_eq_zero r x hx_not
  rw [h_eq]
  exact arch0_sum_shareOf_recipients_amount r hnd_rec hne

theorem plan0_early_selfcontained2_dummy : True := trivial

theorem arch0_sum_shareOf_recipients_amount_proof2 (r : Request)
    (hn : r.recipients.Nodup) (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have h1 : sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) :=
    arch0_sum_shareOf_recipients_range r hn
  have hpos : 0 < r.recipients.length := by
    cases hlen : r.recipients with
    | nil => simp [hlen] at hne
    | cons _ _ => simp
  have h2 : sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) = (r.amount : Int) :=
    arch0_sum_fairShare_range r.amount r.recipients.length hpos
  rw [h1, h2]

theorem tmp_range_check (n : Nat) : List.range (n+1) = List.range n ++ [n] := by simp [List.range_succ]

theorem tmp_probe1 (n : Nat) (c : Int) : ((n : Int) + 1) * c = (n : Int) * c + c := by
  simp only [Int.add_mul, Int.one_mul]

theorem tmp_probe_cast (n : Nat) : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp

theorem tmp_probe_cast2 (n m : Nat) : ((n + m : Nat) : Int) = (n : Int) + (m : Int) := by simp
#check Nat.add_mul
#check Int.add_mul

theorem tmp_probe_addmul2 : True := trivial
#check Nat.div_add_mod









theorem plan1_sum_fairShare_range_eq (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) := by
  have hconst : ∀ (k : Nat) (c : Int),
      sumOver (List.range k) (fun _ => c) = (k : Int) * c := by
    intro k c
    induction k with
    | zero => simp
    | succ k ih =>
      have hrange : List.range (k + 1) = List.range k ++ [k] := tmp_range_check k
      rw [hrange, sumOver_append_test, ih]
      simp only [sumOver_cons, sumOver_nil, Int.add_zero]
      rw [tmp_probe_cast (n := k), tmp_probe1]
  have hge : ∀ (k m : Nat), k ≤ m →
      sumOver (List.range k) (fun i => if i < m then (1 : Int) else 0) = (k : Int) := by
    intro k
    induction k with
    | zero => intro m _; simp
    | succ k ih =>
      intro m hle
      have hle' : k ≤ m := by omega
      have hlt : k < m := by omega
      have hrange : List.range (k + 1) = List.range k ++ [k] := by simp [List.range_succ]
      rw [hrange, sumOver_append_test, ih m hle']
      simp only [sumOver_cons, sumOver_nil, hlt, ↓reduceIte]
      push_cast
      omega
  have hle2 : ∀ (m k : Nat), m ≤ k →
      sumOver (List.range k) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := by
    intro m k
    induction k generalizing m with
    | zero =>
      intro h
      have hm : m = 0 := by omega
      subst hm; simp
    | succ k ih =>
      intro h
      have hrw : List.range (k + 1) = List.range k ++ [k] := tmp_range_check k
      rw [hrw, sumOver_append_test]
      have hsingle : sumOver ([k] : List Nat) (fun i => if i < m then (1 : Int) else 0) = (if k < m then (1 : Int) else 0) := by
        simp [sumOver]
      rw [hsingle]
      by_cases hmn : m ≤ k
      · have h1 : sumOver (List.range k) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := ih m hmn
        have hnm : ¬ k < m := by omega
        have hif : (if k < m then (1 : Int) else 0) = 0 := by simp [hnm]
        rw [h1, hif]; simp
      · have hmeq : m = k + 1 := by omega
        subst hmeq
        have hg : sumOver (List.range k) (fun i => if i < k + 1 then (1 : Int) else 0) = (k : Int) :=
          hge k (k + 1) (by omega)
        have hlt : k < k + 1 := by omega
        have hif : (if k < k + 1 then (1 : Int) else 0) = 1 := by simp [hlt]
        rw [hg, hif]
        have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := tmp_probe_cast k
        rw [hcast]
  have hdecomp : ∀ i ∈ List.range n,
      (fun i => (fairShare amount n i : Int)) i
        = (fun i => ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0)) i := by
    intro i _
    simp only
    unfold fairShare
    by_cases h : i < amount % n <;> simp [h]
  have hcongr : sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = sumOver (List.range n) (fun i => ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0)) :=
    sumOver_congr _ _ _ (fun a ha => hdecomp a ha)
  rw [hcongr, sumOver_add]
  have h1 : sumOver (List.range n) (fun _ => ((amount / n : Nat) : Int)) = (n : Int) * ((amount / n : Nat) : Int) :=
    hconst n _
  have hmod_le : amount % n ≤ n := by
    have hlt : amount % n < n := Nat.mod_lt _ hn
    omega
  have h2 : sumOver (List.range n) (fun i => if i < amount % n then (1 : Int) else 0) = ((amount % n : Nat) : Int) :=
    hle2 _ _ hmod_le
  rw [h1, h2]




theorem plan1_append_helper2 {α : Type} (l1 : List α) (f : α → Int) (b : Int) :
    List.foldr (fun a acc => f a + acc) b l1 = List.foldr (fun a acc => f a + acc) 0 l1 + b := by
  induction l1 generalizing b with
  | nil => simp
  | cons a t ih => simp only [List.foldr]; rw [ih]; omega

theorem plan1_sumOver_append {α : Type} (l1 l2 : List α) (f : α → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  unfold sumOver
  have h : ∀ (l1 : List α) (b : Int),
    List.foldr (fun a acc => f a + acc) b l1 = List.foldr (fun a acc => f a + acc) 0 l1 + b := by
    intro l1 b
    induction l1 generalizing b with
    | nil => simp
    | cons a t ih => simp only [List.foldr]; rw [ih]; omega
  have hfold : List.foldr (fun a acc => f a + acc) 0 (l1 ++ l2)
    = List.foldr (fun a acc => f a + acc) (List.foldr (fun a acc => f a + acc) 0 l2) l1 := by
    induction l1 with
    | nil => simp
    | cons a t ih => simp [ih]
  rw [hfold, h]

theorem tmp_probe_cast3 (n : Nat) : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by
  omega

theorem tmp_probe_cast3b : True := trivial

theorem plan1_sumOver_range_const (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrange : List.range (n + 1) = List.range n ++ [n] := tmp_range_check n
    rw [hrange, plan1_sumOver_append, ih]
    simp only [sumOver_cons, sumOver_nil, Int.add_zero]
    rw [tmp_probe_cast (n := n), tmp_probe1]

theorem plan1_sumOver_range_ite_ge (n m : Nat) (h : n ≤ m) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) = (n : Int) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    have hle : n ≤ m := by omega
    have hlt : n < m := by omega
    have hrange : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    rw [hrange, plan1_sumOver_append, ih m hle]
    simp only [sumOver_cons, sumOver_nil, hlt, ↓reduceIte]
    push_cast
    omega

theorem tmp_debug1 (m n : Nat) : sumOver ([n] : List Nat) (fun i => if i < m then (1 : Int) else 0) = (if n < m then 1 else 0) := by
  simp [sumOver]

theorem tmp_debug3 (m : Nat) : (if m < m + 1 then (1 : Int) else 0) = 1 := by
  have h : m < m + 1 := by omega
  simp [h]

theorem plan1_sumOver_range_ite_le (m n : Nat) (h : m ≤ n) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := by
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by omega
    subst hm
    simp
  | succ n ih =>
    have hrw : List.range (n + 1) = List.range n ++ [n] := tmp_range_check n
    rw [hrw, plan1_sumOver_append]
    have hsingle : sumOver ([n] : List Nat) (fun i => if i < m then (1 : Int) else 0) = (if n < m then (1 : Int) else 0) := by
      simp [sumOver]
    rw [hsingle]
    by_cases hmn : m ≤ n
    · have h1 : sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := ih m hmn
      have hnm : ¬ n < m := by omega
      have hif : (if n < m then (1 : Int) else 0) = 0 := by simp [hnm]
      rw [h1, hif]
      simp
    · have hmeq : m = n + 1 := by omega
      subst hmeq
      have hge : sumOver (List.range n) (fun i => if i < n + 1 then (1 : Int) else 0) = (n : Int) :=
        plan1_sumOver_range_ite_ge n (n + 1) (by omega)
      have hlt : n < n + 1 := by omega
      have hif : (if n < n + 1 then (1 : Int) else 0) = 1 := by simp [hlt]
      rw [hge, hif]
      have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := tmp_probe_cast n
      rw [hcast]

theorem plan1_sum_fairShare_range_eq_proof (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) := by
  have hdecomp : ∀ i ∈ List.range n,
      (fun i => (fairShare amount n i : Int)) i
        = (fun i => ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0)) i := by
    intro i _
    simp only
    unfold fairShare
    by_cases h : i < amount % n <;> simp [h]
  have hcongr : sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = sumOver (List.range n) (fun i => ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0)) :=
    sumOver_congr _ _ _ (fun a ha => hdecomp a ha)
  rw [hcongr, sumOver_add]
  have h1 : sumOver (List.range n) (fun _ => ((amount / n : Nat) : Int)) = (n : Int) * ((amount / n : Nat) : Int) :=
    plan1_sumOver_range_const n _
  have hmod_le : amount % n ≤ n := by
    have hlt : amount % n < n := Nat.mod_lt _ hn
    omega
  have h2 : sumOver (List.range n) (fun i => if i < amount % n then (1 : Int) else 0) = ((amount % n : Nat) : Int) :=
    plan1_sumOver_range_ite_le _ _ hmod_le
  rw [h1, h2]

theorem plan1_selfcontained_full_dummy : True := trivial

theorem plan1_probe_order : True := trivial
#check tmp_range_check
#check sumOver_append_test
#check tmp_probe_cast
#check tmp_probe1

theorem tmp_probe_castA (n m : Nat) : ((n + m : Nat) : Int) = (n : Int) + (m : Int) := by simp

theorem tmp_probe_castB (n m : Nat) : ((n * m : Nat) : Int) = (n : Int) * (m : Int) := by simp

theorem tmp_probe_omega (amount n : Nat) (h : n * (amount / n) + amount % n = amount) :
    (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) = (amount : Int) := by omega

theorem plan1_int_mul_div_add_mod (amount n : Nat) :
    (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) = (amount : Int) := by
  have h := Nat.div_add_mod amount n
  omega

theorem arch0_sum_fairShare_range_proof (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by
  have h1 := plan1_sum_fairShare_range_eq amount n hn
  have h2 := plan1_int_mul_div_add_mod amount n
  omega

theorem arch0_fairShare_selftest (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by
  have hrange_eq : ∀ k : Nat, List.range (k + 1) = List.range k ++ [k] := by
    intro k; simp [List.range_succ]
  have hcast1 : ∀ k : Nat, ((k + 1 : Nat) : Int) = (k : Int) + 1 := by intro k; simp
  have haddmul : ∀ (k : Nat) (c : Int), ((k : Int) + 1) * c = (k : Int) * c + c := by
    intro k c; simp only [Int.add_mul, Int.one_mul]
  have hconst : ∀ (k : Nat) (c : Int),
      sumOver (List.range k) (fun _ => c) = (k : Int) * c := by
    intro k c
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hrange_eq k, sumOver_append_test, ih]
      simp only [sumOver_cons, sumOver_nil, Int.add_zero]
      rw [hcast1 k, haddmul k c]
  have hge : ∀ (k m : Nat), k ≤ m →
      sumOver (List.range k) (fun i => if i < m then (1 : Int) else 0) = (k : Int) := by
    intro k
    induction k with
    | zero => intro m _; simp
    | succ k ih =>
      intro m hle
      have hle' : k ≤ m := by omega
      have hlt : k < m := by omega
      rw [hrange_eq k, sumOver_append_test, ih m hle']
      simp only [sumOver_cons, sumOver_nil, hlt, ↓reduceIte]
      push_cast
      omega
  have hle2 : ∀ (m k : Nat), m ≤ k →
      sumOver (List.range k) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := by
    intro m k
    induction k generalizing m with
    | zero =>
      intro h
      have hm : m = 0 := by omega
      subst hm; simp
    | succ k ih =>
      intro h
      rw [hrange_eq k, sumOver_append_test]
      have hsingle : sumOver ([k] : List Nat) (fun i => if i < m then (1 : Int) else 0) = (if k < m then (1 : Int) else 0) := by
        simp [sumOver]
      rw [hsingle]
      by_cases hmn : m ≤ k
      · have h1 : sumOver (List.range k) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := ih m hmn
        have hnm : ¬ k < m := by omega
        have hif : (if k < m then (1 : Int) else 0) = 0 := by simp [hnm]
        rw [h1, hif]; simp
      · have hmeq : m = k + 1 := by omega
        subst hmeq
        have hg : sumOver (List.range k) (fun i => if i < k + 1 then (1 : Int) else 0) = (k : Int) :=
          hge k (k + 1) (by omega)
        have hlt : k < k + 1 := by omega
        have hif : (if k < k + 1 then (1 : Int) else 0) = 1 := by simp [hlt]
        rw [hg, hif]
        rw [hcast1 k]
  have hdecomp : ∀ i ∈ List.range n,
      (fun i => (fairShare amount n i : Int)) i
        = (fun i => ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0)) i := by
    intro i _
    simp only
    unfold fairShare
    by_cases h : i < amount % n <;> simp [h]
  have hcongr : sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = sumOver (List.range n) (fun i => ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0)) :=
    sumOver_congr _ _ _ (fun a ha => hdecomp a ha)
  rw [hcongr, sumOver_add]
  have h1 : sumOver (List.range n) (fun _ => ((amount / n : Nat) : Int)) = (n : Int) * ((amount / n : Nat) : Int) :=
    hconst n _
  have hmod_le : amount % n ≤ n := by
    have hlt : amount % n < n := Nat.mod_lt _ hn
    omega
  have h2 : sumOver (List.range n) (fun i => if i < amount % n then (1 : Int) else 0) = ((amount % n : Nat) : Int) :=
    hle2 _ _ hmod_le
  rw [h1, h2]
  have h := Nat.div_add_mod amount n
  omega

theorem my_map_sum_aux {α β : Type} (l : List α) (g : α → β) (f : β → Int) :
    sumOver (l.map g) f = sumOver l (fun a => f (g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem my_index_cons_head (x : Nat) (xs : List Nat) :
    indexOf? (x :: xs) x = some 0 := by simp [indexOf?]

theorem my_index_cons_ne (x a : Nat) (xs : List Nat) (h : x ≠ a) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  simp [indexOf?, h]







theorem plan2_sumOver_indexOf_offset (l : List AccountId) (g : Nat → Int)
    (k : Nat) (hl : l.Nodup) :
    sumOver l (fun a => match indexOf? l a with
                          | some i => g (k + i)
                          | none => 0)
      = sumOver (List.range l.length) (fun i => g (k + i)) := by sorry

theorem plan2_shareOf_int_eq_match (r : Request) (a : AccountId) :
    (shareOf r a : Int)
      = (match indexOf? r.recipients a with
         | some i => (fairShare r.amount r.recipients.length i : Int)
         | none => 0) := by sorry

theorem plan2_indexOf_cons_head_apply (x : AccountId) (xs : List AccountId)
    (g : Nat → Int) (k : Nat) :
    (match indexOf? (x :: xs) x with
     | some i => g (k + i)
     | none => 0) = g k := by
  simp [indexOf?]

theorem plan2_indexOf_cons_tail_apply (x a : AccountId) (xs : List AccountId)
    (g : Nat → Int) (k : Nat) (h : x ≠ a) :
    (match indexOf? (x :: xs) a with
     | some i => g (k + i)
     | none => 0)
      = (match indexOf? xs a with
         | some i => g ((k + 1) + i)
         | none => 0) := by
  have hcond : (x = a) = False := by simp [h]
  have hunfold : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
    simp only [indexOf?, hcond, ↓reduceIte]
  rw [hunfold]
  have key : ∀ o : Option Nat,
    (match o.map (· + 1) with | some i => g (k + i) | none => (0 : Int))
      = (match o with | some i => g ((k + 1) + i) | none => 0) := by
    intro o
    cases o with
    | none => rfl
    | some i =>
      simp only [Option.map_some]
      have heq : k + (i + 1) = (k + 1) + i := by omega
      rw [heq]
  exact key _

theorem tmp_range_succ_head_test2 (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f
      = f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by
  induction n generalizing f with
  | zero => simp [sumOver]
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := tmp_range_check (n + 1)
    have h2 : List.range (n + 1) = List.range n ++ [n] := tmp_range_check n
    have ihf := ih f
    rw [h2] at ihf
    have h3 : sumOver (List.range n ++ [n]) f = sumOver (List.range n) f + f n := by
      rw [plan1_sumOver_append]; simp [sumOver]
    have h3s : sumOver (List.range n ++ [n]) (fun i => f (i+1))
      = sumOver (List.range n) (fun i => f (i+1)) + f (n+1) := by
      rw [plan1_sumOver_append]; simp [sumOver]
    rw [h3] at ihf
    rw [h1, plan1_sumOver_append, h2, plan1_sumOver_append]
    simp only [sumOver_cons, sumOver_nil]
    omega

theorem plan2_sumOver_range_succ_head (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f
      = f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by
  induction n generalizing f with
  | zero => simp [sumOver]
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := tmp_range_check (n + 1)
    have h2 : List.range (n + 1) = List.range n ++ [n] := tmp_range_check n
    have ihf := ih f
    rw [h2] at ihf
    have h3 : sumOver (List.range n ++ [n]) f = sumOver (List.range n) f + f n := by
      rw [plan1_sumOver_append]; simp [sumOver]
    have h3s : sumOver (List.range n ++ [n]) (fun i => f (i+1))
      = sumOver (List.range n) (fun i => f (i+1)) + f (n+1) := by
      rw [plan1_sumOver_append]; simp [sumOver]
    rw [h3] at ihf
    rw [h1, plan1_sumOver_append, h2, plan1_sumOver_append]
    simp only [sumOver_cons, sumOver_nil]
    omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization  : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · simp [hv] at h

theorem req_effects        : Effects step := by
  intro s r h
  have hv := arch0_valid_of_ok s r h
  have hstep := arch0_step_eq_of_valid s r hv
  have h2 : (step s r).2 = { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied } := by rw [hstep]
  refine ⟨?_, ?_, ?_⟩
  · simp [h2]
  · simp [h2]
  · intro a
    simp [h2]

theorem req_idempotency : Idempotent step := by
  exact req_idempotency_aux2

theorem req_nonnegative    : NonNegative step := by
  exact req_nonnegative_aux3

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  by_cases hv : ValidPayout s r
  · have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      unfold step; simp [hv]
    obtain ⟨hnodup, hpos, hne, hrnodup, hsrcnotin, hsrcmem, hmem, hauth, hle, htx⟩ := hv
    have hmem_i : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hne_src : r.recipients[i] ≠ r.source := fun h => hsrcnotin (h ▸ hmem_i)
    have hidx : indexOf? r.recipients r.recipients[i] = some i :=
      indexOf?_getElem hrnodup i hi
    have hshare : shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
      unfold shareOf; rw [hidx]
    have hbal_eq : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
      rw [h2]
    rw [hbal_eq]
    unfold expectedBalance
    have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := if_neg hne_src
    rw [hif, hshare]
    omega
  · have hstep : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [hstep] at hok
    exact (Outcome.noConfusion hok)

theorem req_conservation   : Conserves step := by
  intro s r h
  have hv := arch0_valid_of_ok s r h
  exact arch0_total_eq_of_valid s r hv

end Payout
