import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := expectedBalance s r,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_fair_shares_aux2 : FairShares step := by
  intro s r hok i hi
  by_cases h : ValidPayout s r
  · have hstep : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
      simp only [step, h, ↓reduceIte]
    obtain ⟨hnodup_acc, hpos, hne, hnodup_rec, hsrc_notin, hsrc_mem, hmem, hauth, hle, htx⟩ := h
    have hstep2 : (step s r).2 = (({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
      rw [hstep]
    have hmem_i : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hne_i : r.recipients[i] ≠ r.source := fun heq => hsrc_notin (heq ▸ hmem_i)
    have hidx : indexOf? r.recipients r.recipients[i] = some i :=
      indexOf?_getElem hnodup_rec i hi
    have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
      rw [hstep2]
    rw [hbal]
    unfold expectedBalance shareOf
    rw [hidx]
    simp only [hne_i, ↓reduceIte]
    simp
    omega
  · simp only [step, h, ↓reduceIte] at hok
    simp_all

theorem sumOver_zero_test (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem range_prop_test (n : Nat) : (List.range n).length = n := by simp
#check List.range
#check List.nodup_range

theorem probe_check1 : True := trivial
#check List.range_succ
#check Nat.div_add_mod
#check Nat.mod_add_div
#check Nat.mod_lt

theorem helper_sum_append (l1 l2 : List Nat) (f : Nat → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a t ih => simp [ih]; omega

theorem helper_mul_succ (k : Nat) (c : Int) :
    ((k + 1 : Nat) : Int) * c = (k : Int) * c + c := by
  have h1 : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by simp
  rw [h1, Int.add_mul, Int.one_mul]

theorem helper_cast_succ (k : Nat) : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by simp

theorem helper_range_const4 (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : List.range (k + 1) = List.range k ++ [k] := by
      simp [List.range_succ]
    rw [h1, helper_sum_append]
    simp only [sumOver_cons, sumOver_nil]
    rw [ih, helper_cast_succ, Int.add_mul, Int.one_mul]
    omega

theorem helper_all_lt_succ (k : Nat) (a : Nat) (ha : a ∈ List.range k) :
    a < k + 1 := by
  have hmem := List.mem_range.mp ha
  omega

theorem helper_sum_true (k : Nat) :
    sumOver (List.range k) (fun _ => (1 : Int)) = (k : Int) := by
  have h := helper_range_const4 k 1
  simp at h
  exact h



theorem plan0_sum_fairShare_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by
  have h_ind : ∀ (k m : Nat), k ≤ m →
      sumOver (List.range m) (fun i => if i < k then (1 : Int) else 0) = (k : Int) := by
    intro k m
    induction m generalizing k with
    | zero =>
      intro h
      have hk0 : k = 0 := by omega
      subst hk0; simp
    | succ m ih =>
      intro h
      have hrange : List.range (m + 1) = List.range m ++ [m] := by simp [List.range_succ]
      rw [hrange, helper_sum_append]
      simp only [sumOver_cons, sumOver_nil]
      by_cases hk : k = m + 1
      · subst hk
        have heq : ∀ i ∈ List.range m, (if i < m + 1 then (1 : Int) else 0) = 1 := by
          intro i hi
          have hm : i < m + 1 := by
            have := List.mem_range.mp hi; omega
          simp [hm]
        have hsum : sumOver (List.range m) (fun i => if i < m + 1 then (1 : Int) else 0) = sumOver (List.range m) (fun _ => (1 : Int)) := by
          apply sumOver_congr
          intro a ha; exact heq a ha
        rw [hsum, helper_sum_true]
        have hmem : m < m + 1 := by omega
        simp only [hmem, ↓reduceIte]
        have hc : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by simp
        omega
      · have hk_le : k ≤ m := by omega
        have ih' := ih k hk_le
        rw [ih']
        have hn_not : ¬ (m < k) := by omega
        simp only [hn_not, ↓reduceIte, Int.add_zero]
  have hmod_le : amount % n ≤ n := by
    have hlt : amount % n < n := Nat.mod_lt amount hn
    omega
  have h_indicator : sumOver (List.range n) (fun i => if i < amount % n then (1 : Int) else 0) = ((amount % n : Nat) : Int) := h_ind (amount % n) n hmod_le
  have h_const : sumOver (List.range n) (fun _ => ((amount / n : Nat) : Int)) = (n : Int) * ((amount / n : Nat) : Int) := helper_range_const4 n ((amount / n : Nat) : Int)
  have h_congr : sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = sumOver (List.range n) (fun i => ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0)) := by
    apply sumOver_congr
    intro a ha
    unfold fairShare
    by_cases h : a < amount % n <;> simp [h]
  rw [h_congr, sumOver_add, h_const, h_indicator]
  have hdiv : n * (amount / n) + amount % n = amount := Nat.div_add_mod amount n
  have hcast : ((n * (amount / n) + amount % n : Nat) : Int) = (amount : Int) := by rw [hdiv]
  have h1 : ((n * (amount / n) + amount % n : Nat) : Int) = (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) := by simp
  rw [← h1, hcast]




theorem plan0_sumOver_accounts_shareOf (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) =
      sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  have hzero : ∀ a : Nat, a ∉ r.recipients → (shareOf r a : Int) = 0 := by
    intro a ha
    unfold shareOf
    rw [indexOf?_eq_none ha]
    rfl
  have aux : ∀ (l : List Nat), l.Nodup →
      sumOver l (fun a => (shareOf r a : Int)) =
      sumOver r.recipients (fun a => if a ∈ l then (shareOf r a : Int) else 0) := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [sumOver_nil]
      have hcongr : (fun a => if a ∈ ([] : List Nat) then (shareOf r a : Int) else 0) = (fun _ => (0 : Int)) := by
        funext a; simp
      rw [hcongr]
      exact (sumOver_zero_test r.recipients).symm
    | cons z zs ih =>
      intro hl
      rw [List.nodup_cons] at hl
      obtain ⟨hz_not, hz_nodup⟩ := hl
      have ih' := ih hz_nodup
      simp only [sumOver_cons]
      rw [ih']
      have hsplit : ∀ a : Nat, (if a ∈ z :: zs then (shareOf r a : Int) else 0) =
          (if a = z then (shareOf r a : Int) else 0) + (if a ∈ zs then (shareOf r a : Int) else 0) := by
        intro a
        by_cases haz : a = z
        · subst haz; simp [hz_not]
        · simp [haz]
      have hcongr2 : (fun a => if a ∈ z :: zs then (shareOf r a : Int) else 0) =
          (fun a => (if a = z then (shareOf r a : Int) else 0) + (if a ∈ zs then (shareOf r a : Int) else 0)) := by
        funext a; exact hsplit a
      rw [hcongr2, sumOver_add]
      have hsingle_congr : (fun a => if a = z then (shareOf r a : Int) else (0 : Int)) =
          (fun a => if a = z then (shareOf r z : Int) else (0 : Int)) := by
        funext a
        by_cases h : a = z
        · subst h; rfl
        · simp [h]
      rw [hsingle_congr, sumOver_ite_eq hrec]
      by_cases hm : z ∈ r.recipients
      · simp only [hm, ↓reduceIte]
      · have hz0 : (shareOf r z : Int) = 0 := hzero z hm
        simp only [hm, ↓reduceIte, hz0]
  have hgen := aux s.accounts hacc
  rw [hgen]
  apply sumOver_congr
  intro a ha
  simp [hsub a ha]




theorem plan0_sumOver_expectedBalance (l : List AccountId) (hl : l.Nodup)
    (s : State) (r : Request) :
    sumOver l (fun a => expectedBalance s r a) =
      sumOver l s.balance
        - (if r.source ∈ l then (r.amount : Int) else 0)
        + sumOver l (fun a => (shareOf r a : Int)) := by
  have h1 : (fun a => expectedBalance s r a) = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int))) := by
    funext a
    unfold expectedBalance
    rfl
  rw [h1]
  have h2 : sumOver l (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int)))
    = sumOver l (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) + sumOver l (fun a => (shareOf r a : Int)) :=
    sumOver_add l (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) (fun a => (shareOf r a : Int))
  rw [h2]
  have h3 : sumOver l (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
    = sumOver l s.balance - sumOver l (fun a => (if a = r.source then (r.amount : Int) else 0)) :=
    sumOver_sub l s.balance (fun a => (if a = r.source then (r.amount : Int) else 0))
  rw [h3]
  have h4 : sumOver l (fun a => (if a = r.source then (r.amount : Int) else 0)) = (if r.source ∈ l then (r.amount : Int) else 0) :=
    sumOver_ite_eq hl r.source (r.amount : Int)
  rw [h4]


theorem plan0_sumOver_range_indicator_aux3 (k n : Nat) (h : k ≤ n) :
    sumOver (List.range n) (fun i => if i < k then (1 : Int) else 0) = (k : Int) := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0; simp
  | succ n ih =>
    have hrange : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    rw [hrange, helper_sum_append]
    simp only [sumOver_cons, sumOver_nil]
    by_cases hk : k = n + 1
    · subst hk
      have heq : ∀ i ∈ List.range n, (if i < n + 1 then (1 : Int) else 0) = 1 := by
        intro i hi
        have hm : i < n + 1 := by
          have := List.mem_range.mp hi; omega
        simp [hm]
      have hsum : sumOver (List.range n) (fun i => if i < n + 1 then (1 : Int) else 0) = sumOver (List.range n) (fun _ => (1 : Int)) := by
        apply sumOver_congr
        intro a ha; exact heq a ha
      rw [hsum, helper_sum_true]
      have hmem : n < n + 1 := by omega
      simp only [hmem, ↓reduceIte]
      have hc : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
      omega
    · have hk_le : k ≤ n := by omega
      have ih' := ih k hk_le
      rw [ih']
      have hn_not : ¬ (n < k) := by omega
      simp only [hn_not, ↓reduceIte, Int.add_zero]

theorem plan0_sumOver_range_indicator (k n : Nat) (h : k ≤ n) :
    sumOver (List.range n) (fun i => if i < k then (1 : Int) else 0) = (k : Int) := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0; simp
  | succ n ih =>
    have hrange : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    rw [hrange, helper_sum_append]
    simp only [sumOver_cons, sumOver_nil]
    by_cases hk : k = n + 1
    · subst hk
      have heq : ∀ i ∈ List.range n, (if i < n + 1 then (1 : Int) else 0) = 1 := by
        intro i hi
        have hm : i < n + 1 := by
          have := List.mem_range.mp hi; omega
        simp [hm]
      have hsum : sumOver (List.range n) (fun i => if i < n + 1 then (1 : Int) else 0) = sumOver (List.range n) (fun _ => (1 : Int)) := by
        apply sumOver_congr
        intro a ha; exact heq a ha
      rw [hsum, helper_sum_true]
      have hmem : n < n + 1 := by omega
      simp only [hmem, ↓reduceIte]
      have hc : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
      omega
    · have hk_le : k ≤ n := by omega
      have ih' := ih k hk_le
      rw [ih']
      have hn_not : ¬ (n < k) := by omega
      simp only [hn_not, ↓reduceIte, Int.add_zero]

theorem probe_cast_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp

theorem probe_cast_mul (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by simp

theorem plan0_sum_fairShare_range_proof2 : ∀ (amount n : Nat), 0 < n →
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by
  intro amount n hn
  have hmod_le : amount % n ≤ n := by
    have hlt : amount % n < n := Nat.mod_lt amount hn
    omega
  have h_indicator : sumOver (List.range n) (fun i => if i < amount % n then (1 : Int) else 0) = ((amount % n : Nat) : Int) := plan0_sumOver_range_indicator (amount % n) n hmod_le
  have h_const : sumOver (List.range n) (fun _ => ((amount / n : Nat) : Int)) = (n : Int) * ((amount / n : Nat) : Int) := helper_range_const4 n ((amount / n : Nat) : Int)
  have h_congr : sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = sumOver (List.range n) (fun i => ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0)) := by
    apply sumOver_congr
    intro a ha
    unfold fairShare
    by_cases h : a < amount % n <;> simp [h]
  rw [h_congr, sumOver_add, h_const, h_indicator]
  have hdiv : n * (amount / n) + amount % n = amount := Nat.div_add_mod amount n
  have hcast : ((n * (amount / n) + amount % n : Nat) : Int) = (amount : Int) := by rw [hdiv]
  have h1 : ((n * (amount / n) + amount % n : Nat) : Int) = (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) := by simp
  rw [← h1, hcast]

theorem plan0_selfcontained_test (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by
  have h_ind : ∀ (k m : Nat), k ≤ m →
      sumOver (List.range m) (fun i => if i < k then (1 : Int) else 0) = (k : Int) := by
    intro k m
    induction m generalizing k with
    | zero =>
      intro h
      have hk0 : k = 0 := by omega
      subst hk0; simp
    | succ m ih =>
      intro h
      have hrange : List.range (m + 1) = List.range m ++ [m] := by simp [List.range_succ]
      rw [hrange, helper_sum_append]
      simp only [sumOver_cons, sumOver_nil]
      by_cases hk : k = m + 1
      · subst hk
        have heq : ∀ i ∈ List.range m, (if i < m + 1 then (1 : Int) else 0) = 1 := by
          intro i hi
          have hm : i < m + 1 := by
            have := List.mem_range.mp hi; omega
          simp [hm]
        have hsum : sumOver (List.range m) (fun i => if i < m + 1 then (1 : Int) else 0) = sumOver (List.range m) (fun _ => (1 : Int)) := by
          apply sumOver_congr
          intro a ha; exact heq a ha
        rw [hsum, helper_sum_true]
        have hmem : m < m + 1 := by omega
        simp only [hmem, ↓reduceIte]
        have hc : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by simp
        omega
      · have hk_le : k ≤ m := by omega
        have ih' := ih k hk_le
        rw [ih']
        have hn_not : ¬ (m < k) := by omega
        simp only [hn_not, ↓reduceIte, Int.add_zero]
  have hmod_le : amount % n ≤ n := by
    have hlt : amount % n < n := Nat.mod_lt amount hn
    omega
  have h_indicator : sumOver (List.range n) (fun i => if i < amount % n then (1 : Int) else 0) = ((amount % n : Nat) : Int) := h_ind (amount % n) n hmod_le
  have h_const : sumOver (List.range n) (fun _ => ((amount / n : Nat) : Int)) = (n : Int) * ((amount / n : Nat) : Int) := helper_range_const4 n ((amount / n : Nat) : Int)
  have h_congr : sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = sumOver (List.range n) (fun i => ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0)) := by
    apply sumOver_congr
    intro a ha
    unfold fairShare
    by_cases h : a < amount % n <;> simp [h]
  rw [h_congr, sumOver_add, h_const, h_indicator]
  have hdiv : n * (amount / n) + amount % n = amount := Nat.div_add_mod amount n
  have hcast : ((n * (amount / n) + amount % n : Nat) : Int) = (amount : Int) := by rw [hdiv]
  have h1 : ((n * (amount / n) + amount % n : Nat) : Int) = (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) := by simp
  rw [← h1, hcast]

theorem helper_indexOf_cons_ne (x a : Nat) (xs : List Nat) (h : x ≠ a) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  simp [indexOf?, h]

theorem helper_sumOver_map (l : List Nat) (f : Nat → Nat) (g : Nat → Int) :
    sumOver (l.map f) g = sumOver l (fun a => g (f a)) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem helper_map_succ_eq2 (l : List Nat) (g : Nat → Int) :
    sumOver (List.map Nat.succ l) g = sumOver l (fun i => g (i + 1)) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem helper_share_general3 (l : List Nat) (hl : l.Nodup) (g : Nat → Int) :
    sumOver l (fun a => match indexOf? l a with | some i => g i | none => 0) =
      sumOver (List.range l.length) (fun i => g i) := by
  induction l generalizing g with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hx_not, hx_nodup⟩ := hl
    have hx_eq : indexOf? (x :: xs) x = some 0 := by simp [indexOf?]
    have hhead : (match indexOf? (x :: xs) x with | some i => g i | none => 0) = g 0 := by
      rw [hx_eq]
    have htail_congr : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0)
        = sumOver xs (fun a => match indexOf? xs a with | some i => g (i + 1) | none => 0) := by
      apply sumOver_congr
      intro a ha
      have hne : x ≠ a := fun heq => hx_not (heq ▸ ha)
      have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
        simp [indexOf?, hne]
      rw [hidx]
      cases h : indexOf? xs a <;> simp
    have ih' := ih hx_nodup (fun i => g (i + 1))
    have h1 : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0)
        = g 0 + sumOver (List.range xs.length) (fun i => g (i + 1)) := by
      have : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0)
        = (match indexOf? (x :: xs) x with | some i => g i | none => 0)
          + sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0) := rfl
      rw [this, hhead, htail_congr, ih']
    rw [h1]
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    rw [hlen, List.range_succ_eq_map, sumOver_cons, helper_map_succ_eq2]

theorem plan0_sumOver_recipients_shareOf (r : Request) (h : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) =
      sumOver (List.range r.recipients.length)
        (fun i => (fairShare r.amount r.recipients.length i : Int)) := by
  have hgen := helper_share_general3 r.recipients h (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int))
  have hcongr : sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => match indexOf? r.recipients a with | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int) | none => 0) := by
    apply sumOver_congr
    intro a ha
    unfold shareOf
    cases hidx : indexOf? r.recipients a <;> rfl
  rw [hcongr, hgen]

theorem aux_share_zero_of_notmem (r : Request) (a : Nat) (h : a ∉ r.recipients) :
    (shareOf r a : Int) = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none h]
  rfl

theorem aux_indicator_split (z : Nat) (zs : List Nat) (hzne : z ∉ zs) (a : Nat) (g : Nat → Int) :
    (if a ∈ z :: zs then g a else 0) = (if a = z then g a else 0) + (if a ∈ zs then g a else 0) := by
  by_cases haz : a = z
  · subst haz
    simp [hzne]
  · simp [haz]

theorem aux_zero_list2 (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp only [sumOver_cons] at ih ⊢; omega

theorem aux_gen_full2 (r : Request) (hrec : r.recipients.Nodup) (l : List Nat) (hl : l.Nodup) :
    sumOver l (fun a => (shareOf r a : Int)) =
    sumOver r.recipients (fun a => if a ∈ l then (shareOf r a : Int) else 0) := by
  induction l with
  | nil =>
    simp only [sumOver_nil]
    have hcongr : sumOver r.recipients (fun a => if a ∈ ([] : List Nat) then (shareOf r a : Int) else 0)
        = sumOver r.recipients (fun _ => (0 : Int)) := by
      apply sumOver_congr
      intro a ha
      simp
    rw [hcongr, aux_zero_list2]
  | cons z zs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hz_not, hz_nodup⟩ := hl
    have ih' := ih hz_nodup
    simp only [sumOver_cons]
    rw [ih']
    have hsplit_congr : sumOver r.recipients (fun a => if a ∈ z :: zs then (shareOf r a : Int) else 0)
        = sumOver r.recipients (fun a => (if a = z then (shareOf r a : Int) else 0) + (if a ∈ zs then (shareOf r a : Int) else 0)) := by
      apply sumOver_congr
      intro a ha
      exact aux_indicator_split z zs hz_not a (fun b => (shareOf r b : Int))
    rw [hsplit_congr, sumOver_add]
    have hsingle_congr : sumOver r.recipients (fun a => if a = z then (shareOf r a : Int) else 0)
        = sumOver r.recipients (fun a => if a = z then (shareOf r z : Int) else 0) := by
      apply sumOver_congr
      intro a ha
      by_cases h : a = z
      · subst h; rfl
      · simp [h]
    rw [hsingle_congr, sumOver_ite_eq hrec]
    by_cases hm : z ∈ r.recipients
    · simp only [hm, ↓reduceIte]
    · have hz0 : (shareOf r z : Int) = 0 := aux_share_zero_of_notmem r z hm
      simp only [hm, ↓reduceIte, hz0]

theorem plan0_sumOver_accounts_shareOf_try (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) =
      sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  have hgen := aux_gen_full2 r hrec s.accounts hacc
  rw [hgen]
  apply sumOver_congr
  intro a ha
  simp [hsub a ha]

theorem plan0_sumOver_accounts_shareOf2 (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) =
      sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  have hgen := aux_gen_full2 r hrec s.accounts hacc
  rw [hgen]
  apply sumOver_congr
  intro a ha
  simp [hsub a ha]





theorem plan1_sumOver_shareOf_eq_recipients_ite (r : Request) (hrec : r.recipients.Nodup) (l : List AccountId) (hl : l.Nodup) : sumOver l (fun a => (shareOf r a : Int)) = sumOver r.recipients (fun a => if a ∈ l then (shareOf r a : Int) else 0) := aux_gen_full2 r hrec l hl




theorem plan1_accounts_shareOf_eq_recipients (s : State) (r : Request) (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup) (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) : sumOver s.accounts (fun a => (shareOf r a : Int)) = sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  have hgen := aux_gen_full2 r hrec s.accounts hacc
  rw [hgen]
  apply sumOver_congr
  intro a ha
  simp [hsub a ha]


theorem plan1_shareOf_eq_zero_of_not_mem (r : Request) (a : AccountId) (h : a ∉ r.recipients) : (shareOf r a : Int) = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none h]
  simp

theorem plan1_ite_mem_cons_split (z : AccountId) (zs : List AccountId) (hz : z ∉ zs) (a : AccountId) (g : AccountId → Int) : (if a ∈ (z :: zs) then g a else 0) = (if a = z then g a else 0) + (if a ∈ zs then g a else 0) := by
  by_cases haz : a = z
  · subst haz
    simp [hz]
  · simp [haz]

theorem plan1_sumOver_shareOf_eq_recipients_ite_proof (r : Request) (hrec : r.recipients.Nodup) (l : List AccountId) (hl : l.Nodup) : sumOver l (fun a => (shareOf r a : Int)) = sumOver r.recipients (fun a => if a ∈ l then (shareOf r a : Int) else 0) := aux_gen_full2 r hrec l hl

theorem plan1_sumOver_recipients_ite_eq_of_subset (r : Request) (l : List AccountId) (hsub : ∀ x ∈ r.recipients, x ∈ l) : sumOver r.recipients (fun a => if a ∈ l then (shareOf r a : Int) else 0) = sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  apply sumOver_congr
  intro a ha
  simp [hsub a ha]

theorem plan1_accounts_shareOf_eq_recipients_proof (s : State) (r : Request) (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup) (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) : sumOver s.accounts (fun a => (shareOf r a : Int)) = sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  have hgen := aux_gen_full2 r hrec s.accounts hacc
  have hsub2 := plan1_sumOver_recipients_ite_eq_of_subset r s.accounts hsub
  rw [hgen, hsub2]

theorem plan1_accounts_shareOf_eq_recipients2 (s : State) (r : Request) (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup) (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) : sumOver s.accounts (fun a => (shareOf r a : Int)) = sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  have hgen := aux_gen_full2 r hrec s.accounts hacc
  rw [hgen]
  apply sumOver_congr
  intro a ha
  simp [hsub a ha]

theorem plan0_sumOver_accounts_shareOf_check (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) =
      sumOver r.recipients (fun a => (shareOf r a : Int)) :=
  plan1_accounts_shareOf_eq_recipients s r hacc hrec hsub

theorem plan0_sumOver_accounts_shareOf_UNUSED : True := trivial

theorem plan0_sumOver_accounts_shareOf_amount_proof : ∀ (s : State) (r : Request),
    ValidPayout s r →
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  intro s r h
  obtain ⟨hacc, hpos, hne, hrec, hsrc_notin, hsrc_mem, hsub, hauth, hle, htx⟩ := h
  have h1 : sumOver s.accounts (fun a => (shareOf r a : Int)) =
      sumOver r.recipients (fun a => (shareOf r a : Int)) :=
    plan1_accounts_shareOf_eq_recipients s r hacc hrec hsub
  have h2 : sumOver r.recipients (fun a => (shareOf r a : Int)) =
      sumOver (List.range r.recipients.length)
        (fun i => (fairShare r.amount r.recipients.length i : Int)) :=
    plan0_sumOver_recipients_shareOf r hrec
  have hne_len : 0 < r.recipients.length := by
    cases hr : r.recipients with
    | nil => simp [hr] at hne
    | cons _ _ => simp
  have h3 : sumOver (List.range r.recipients.length)
        (fun i => (fairShare r.amount r.recipients.length i : Int)) = (r.amount : Int) :=
    plan0_selfcontained_test r.amount r.recipients.length hne_len
  rw [h1, h2, h3]

theorem check_use_amount_proof : ∀ (s : State) (r : Request), ValidPayout s r →
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := plan0_sumOver_accounts_shareOf_amount_proof
#check @plan0_sumOver_accounts_shareOf_amount_proof
#check @plan0_sumOver_expectedBalance
#check @plan0_sumOver_recipients_shareOf

theorem plan0_sumOver_accounts_shareOf_amount2 (s : State) (r : Request)
    (h : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
  plan0_sumOver_accounts_shareOf_amount_proof s r h

theorem plan0_sumOver_accounts_shareOf_amount_dup (s : State) (r : Request)
    (h : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
  plan0_sumOver_accounts_shareOf_amount_proof s r h

theorem plan0_sumOver_accounts_shareOf_amount (s : State) (r : Request)
    (h : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
  plan0_sumOver_accounts_shareOf_amount_proof s r h

theorem plan0_sumOver_expectedBalance_test2 (l : List AccountId) (hl : l.Nodup)
    (s : State) (r : Request) :
    sumOver l (fun a => expectedBalance s r a) =
      sumOver l s.balance
        - (if r.source ∈ l then (r.amount : Int) else 0)
        + sumOver l (fun a => (shareOf r a : Int)) := by
  have h1 : (fun a => expectedBalance s r a) = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int))) := by
    funext a
    unfold expectedBalance
    rfl
  rw [h1]
  have h2 : sumOver l (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int)))
    = sumOver l (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) + sumOver l (fun a => (shareOf r a : Int)) :=
    sumOver_add l (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) (fun a => (shareOf r a : Int))
  rw [h2]
  have h3 : sumOver l (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
    = sumOver l s.balance - sumOver l (fun a => (if a = r.source then (r.amount : Int) else 0)) :=
    sumOver_sub l s.balance (fun a => (if a = r.source then (r.amount : Int) else 0))
  rw [h3]
  have h4 : sumOver l (fun a => (if a = r.source then (r.amount : Int) else 0)) = (if r.source ∈ l then (r.amount : Int) else 0) :=
    sumOver_ite_eq hl r.source (r.amount : Int)
  rw [h4]

theorem req_conservation_proof2 : Conserves step := by
  intro s r hok
  by_cases hvalid : ValidPayout s r
  · have hcopy : ValidPayout s r := hvalid
    have hstep : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
      simp only [step, hvalid, ↓reduceIte]
    have h2 : (step s r).2 = (({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
      rw [hstep]
    obtain ⟨hacc, hpos, hne, hrec, hsrc_notin, hsrc_mem, hsub, hauth, hle, htx⟩ := hcopy
    have htot : total (step s r).2 = sumOver s.accounts (fun a => expectedBalance s r a) := by
      rw [h2]
      rfl
    rw [htot]
    have hexp := plan0_sumOver_expectedBalance s.accounts hacc s r
    rw [hexp]
    have hsrc : (if r.source ∈ s.accounts then (r.amount : Int) else 0) = (r.amount : Int) := by
      simp [hsrc_mem]
    rw [hsrc]
    have hshares : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
      plan0_sumOver_accounts_shareOf_amount s r hvalid
    rw [hshares]
    unfold total
    omega
  · have hstep : step s r = (.rejected, s) := by simp only [step, hvalid, ↓reduceIte]
    rw [hstep] at hok
    simp at hok

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp only [step, h, ↓reduceIte]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp only [step, h, ↓reduceIte]

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  by_cases h : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := h
    exact hauth
  · simp [step, h] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases h : ValidPayout s r
  · have hstep : step s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
      simp only [step, h, ↓reduceIte]
    rw [hstep]
    exact ⟨rfl, rfl, fun a => rfl⟩
  · have hstep : step s r = (.rejected, s) := by simp only [step, h, ↓reduceIte]
    rw [hstep] at hok
    simp at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases h : ValidPayout s r
  · have hstep : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
      simp only [step, h, ↓reduceIte]
    have h2eq : (step s r).2 = (({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
      rw [hstep]
    have hmem_iff : ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
      intro x
      rw [h2eq]
      simp
    have hnotvalid2' : ¬ ValidPayout (({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) r := by
      intro hcontra
      obtain ⟨_, _, _, _, _, _, _, _, _, htx2⟩ := hcontra
      simp at htx2
    have hstep2 : step (step s r).2 r = (.rejected, (step s r).2) := by
      rw [h2eq]
      simp only [step, hnotvalid2', ↓reduceIte]
    exact ⟨hmem_iff, hstep2⟩
  · simp only [step, h, ↓reduceIte] at hok
    simp at hok

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases h : ValidPayout s r
  · have hstep : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
      simp only [step, h, ↓reduceIte]
    have h2acc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have h2bal : ∀ b, (step s r).2.balance b = expectedBalance s r b := by
      intro b; rw [hstep]
    have ha' : a ∈ s.accounts := h2acc ▸ ha
    rw [h2bal]
    obtain ⟨hnodup_acc, hpos, hne, hnodup_rec, hsrc_notin, hsrc_mem, hmem, hauth, hle, htx⟩ := h
    have hbal_a : 0 ≤ s.balance a := hnn a ha'
    unfold expectedBalance
    by_cases heq : a = r.source
    · subst heq
      have hshare0 : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hsrc_notin]
      simp only [↓reduceIte] at hshare0 ⊢
      simp [hshare0]
      omega
    · simp only [heq, ↓reduceIte]
      have hshare_nonneg : (0 : Int) ≤ (shareOf r a : Int) := Int.ofNat_nonneg _
      omega
  · have hstep : step s r = (.rejected, s) := by simp only [step, h, ↓reduceIte]
    have h2 : (step s r).2 = s := by rw [hstep]
    have ha' : a ∈ s.accounts := by
      have hmem : a ∈ (step s r).2.accounts := ha
      rw [h2] at hmem
      exact hmem
    have hgoal : (step s r).2.balance a = s.balance a := by rw [h2]
    rw [hgoal]
    exact hnn a ha'

theorem req_fair_shares : FairShares step := req_fair_shares_aux2

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases hvalid : ValidPayout s r
  · have hcopy : ValidPayout s r := hvalid
    have hstep : step s r = (.ok, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
      simp only [step, hvalid, ↓reduceIte]
    have h2 : (step s r).2 = (({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
      rw [hstep]
    obtain ⟨hacc, hpos, hne, hrec, hsrc_notin, hsrc_mem, hsub, hauth, hle, htx⟩ := hcopy
    have htot : total (step s r).2 = sumOver s.accounts (fun a => expectedBalance s r a) := by
      rw [h2]
      rfl
    rw [htot]
    have hexp := plan0_sumOver_expectedBalance s.accounts hacc s r
    rw [hexp]
    have hsrc : (if r.source ∈ s.accounts then (r.amount : Int) else 0) = (r.amount : Int) := by
      simp [hsrc_mem]
    rw [hsrc]
    have hshares : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
      plan0_sumOver_accounts_shareOf_amount s r hvalid
    rw [hshares]
    unfold total
    omega
  · have hstep : step s r = (.rejected, s) := by simp only [step, hvalid, ↓reduceIte]
    rw [hstep] at hok
    simp at hok

end Payout
