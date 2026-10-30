import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    let n := r.recipients.length
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (match indexOf? r.recipients a with
                             | some i => (fairShare r.amount n i : Int)
                             | none => 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_effects_aux3 (s : State) (r : Request) (hV : ValidPayout s r) (a : AccountId) :
    (step s r).2.balance a = expectedBalance s r a := by
  unfold step expectedBalance shareOf
  simp only [hV, ↓reduceIte]
  cases h : indexOf? r.recipients a <;> rfl

theorem req_effects_aux1 (s : State) (r : Request) (hV : ValidPayout s r) :
    (step s r).2.accounts = s.accounts := by
  simp [step, hV]

theorem req_effects_aux2 (s : State) (r : Request) (hV : ValidPayout s r) :
    (step s r).2.auth = s.auth := by
  simp [step, hV]

theorem valid_of_ok_aux : ∀ s r, (step s r).1 = .ok → ValidPayout s r := by
  intro s r hOk
  by_cases hV : ValidPayout s r
  · exact hV
  · exfalso
    have h1 : (step s r).1 = Outcome.rejected := by simp [step, hV]
    rw [h1] at hOk
    exact Outcome.noConfusion hOk

theorem req_idempotency_aux_applied (s : State) (r : Request) (hV : ValidPayout s r) : (step s r).2.applied = r.txId :: s.applied := by
  simp [step, hV]

theorem idem_mem_test (s : State) (r : Request) (hV : ValidPayout s r) : r.txId ∈ (step s r).2.applied := by
  rw [req_idempotency_aux_applied s r hV]
  simp

theorem idem_notvalid_test (s : State) (r : Request) (hV : ValidPayout s r) : ¬ ValidPayout (step s r).2 r := by
  intro hC
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hC
  have hmem : r.txId ∈ (step s r).2.applied := by rw [req_idempotency_aux_applied s r hV]; simp
  exact h10 hmem

theorem sumOver_append_test {α : Type} (l1 l2 : List α) (f : α → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a l1 ih => simp [ih]; omega
#check @List.range_succ
#check @List.nodup_range



theorem arch0_idem_replay (s : State) (r : Request) (hok : (step s r).1 = .ok) :
    step (step s r).2 r = (.rejected, (step s r).2) := by
  have hV : ValidPayout s r := valid_of_ok_aux s r hok
  have hNV : ¬ ValidPayout (step s r).2 r := idem_notvalid_test s r hV
  generalize (step s r).2 = s2 at hNV ⊢
  unfold step
  simp [hNV]


theorem arch0_shareOf_getElem (r : Request) (hnd : r.recipients.Nodup)
    (i : Nat) (hi : i < r.recipients.length) :
    shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
  unfold shareOf
  rw [indexOf?_getElem hnd i hi]


theorem arch0_shareOf_eq_zero_of_not_mem (r : Request) (a : AccountId)
    (h : a ∉ r.recipients) :
    shareOf r a = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none h]






theorem arch0_sumOver_recipients_share (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem arch0_sumOver_subset_eq (big small : List AccountId) (f : AccountId → Int)
    (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hzero : ∀ x, x ∈ big → x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by sorry

theorem arch0_sumOver_accounts_share (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry



theorem arch0_idem_applied_mem (s : State) (r : Request) (hok : (step s r).1 = .ok)
    (x : TxId) :
    x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
  have hV := valid_of_ok_aux s r hok
  have happ := req_idempotency_aux_applied s r hV
  rw [happ]
  simp

theorem arch0_idem_replay_d (s : State) (r : Request) (hok : (step s r).1 = .ok) :
    step (step s r).2 r = (.rejected, (step s r).2) := by
  have hV : ValidPayout s r := valid_of_ok_aux s r hok
  have hNV : ¬ ValidPayout (step s r).2 r := idem_notvalid_test s r hV
  generalize (step s r).2 = s2 at hNV ⊢
  simp [step, hNV]

theorem arch0_idem_replay_e (s : State) (r : Request) (hok : (step s r).1 = .ok) :
    step (step s r).2 r = (.rejected, (step s r).2) := by
  have hV : ValidPayout s r := valid_of_ok_aux s r hok
  have hNV : ¬ ValidPayout (step s r).2 r := idem_notvalid_test s r hV
  have hrep : ∀ s2 : State, ¬ ValidPayout s2 r → step s2 r = (.rejected, s2) := by
    intro s2 hs2
    unfold step
    simp [hs2]
  exact hrep _ hNV



theorem plan0_valid_of_ok (s : State) (r : Request)
    (hok : (step s r).1 = .ok) : ValidPayout s r := valid_of_ok_aux s r hok




theorem plan0_not_valid_after_ok_aux_tmp2 (s : State) (r : Request)
    (hok : (step s r).1 = .ok) : ¬ ValidPayout (step s r).2 r := by
  exact idem_notvalid_test s r (valid_of_ok_aux s r hok)


theorem plan0_step_eq_rejected_of_not_valid (t : State) (r : Request)
    (h : ¬ ValidPayout t r) : step t r = (.rejected, t) := by
  unfold step
  simp [h]


theorem plan0_validPayout_txId_not_mem {s : State} {r : Request}
    (h : ValidPayout s r) : r.txId ∉ s.applied := by
  unfold ValidPayout at h
  obtain ⟨_, _, _, _, _, _, _, _, _, hj⟩ := h
  exact hj

theorem tmp_plan0_valid_of_ok_test (s : State) (r : Request) (hok : (step s r).1 = .ok) : ValidPayout s r := valid_of_ok_aux s r hok

theorem plan0_txId_mem_applied_of_ok (s : State) (r : Request)
    (hok : (step s r).1 = .ok) : r.txId ∈ (step s r).2.applied := by
  have hV : ValidPayout s r := valid_of_ok_aux s r hok
  have h : (step s r).2.applied = r.txId :: s.applied :=
    req_idempotency_aux_applied s r hV
  rw [h]
  simp

theorem plan0_not_valid_after_ok2 (s : State) (r : Request)
    (hok : (step s r).1 = .ok) : ¬ ValidPayout (step s r).2 r := by
  intro hV2
  have hmem : r.txId ∈ (step s r).2.applied := plan0_txId_mem_applied_of_ok s r hok
  have hnot : r.txId ∉ (step s r).2.applied := plan0_validPayout_txId_not_mem (s := (step s r).2) (r := r) hV2
  exact hnot hmem

theorem plan0_not_valid_after_ok_aux_tmp (s : State) (r : Request)
    (hok : (step s r).1 = .ok) : ¬ ValidPayout (step s r).2 r := by
  have hV : ValidPayout s r := valid_of_ok_aux s r hok
  exact idem_notvalid_test s r hV


theorem plan0_step_eq_rejected_of_not_valid_aux_tmp (t : State) (r : Request)
    (h : ¬ ValidPayout t r) : step t r = (.rejected, t) := by
  unfold step
  simp [h]

theorem arch0_idem_replay_check2 (s : State) (r : Request) (hok : (step s r).1 = .ok) :
    step (step s r).2 r = (.rejected, (step s r).2) := by
  have hV : ValidPayout s r := valid_of_ok_aux s r hok
  have hNV : ¬ ValidPayout (step s r).2 r := idem_notvalid_test s r hV
  generalize (step s r).2 = s2 at hNV ⊢
  unfold step
  simp [hNV]

theorem plan0_helper_test_unique123 : ∀ (t : State) (r : Request), ¬ ValidPayout t r → step t r = (.rejected, t) := by
  intro t r h
  unfold step
  simp [h]

theorem tmp_check_hV2 (s : State) (r : Request) (hW : ValidPayout s r) :
    sumOver s.accounts (expectedBalance s r) = total s := by
  have hAccNodup : s.accounts.Nodup := hW.1
  have hSrcMem : r.source ∈ s.accounts := hW.2.2.2.2.2.1
  have hshare : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
    arch0_sumOver_accounts_share s r hW
  have hdebit : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq (l := s.accounts) hAccNodup r.source (r.amount : Int)
    simpa [hSrcMem] using h
  have hsplit : sumOver s.accounts (expectedBalance s r)
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
        + sumOver s.accounts (fun a => (shareOf r a : Int)) := by
    have hadd : sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int)))
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
          + sumOver s.accounts (fun a => (shareOf r a : Int)) :=
      sumOver_add _ _ _
    have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) :=
      sumOver_sub _ _ _
    have hcongr : sumOver s.accounts (expectedBalance s r)
        = sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int))) := by
      apply sumOver_congr
      intro a _
      rfl
    rw [hcongr, hadd, hsub]
  rw [hsplit, hdebit, hshare]
  unfold total
  omega

theorem arch0_sumOver_accounts_expected (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver s.accounts (expectedBalance s r) = total s := by
  have hAccNodup : s.accounts.Nodup := hV.1
  have hSrcMem : r.source ∈ s.accounts := hV.2.2.2.2.2.1
  have hshare : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) :=
    arch0_sumOver_accounts_share s r hV
  have hdebit : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq (l := s.accounts) hAccNodup r.source (r.amount : Int)
    simpa [hSrcMem] using h
  have hsplit : sumOver s.accounts (expectedBalance s r)
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
        + sumOver s.accounts (fun a => (shareOf r a : Int)) := by
    have hadd : sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int)))
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
          + sumOver s.accounts (fun a => (shareOf r a : Int)) :=
      sumOver_add _ _ _
    have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) :=
      sumOver_sub _ _ _
    have hcongr : sumOver s.accounts (expectedBalance s r)
        = sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int))) := by
      apply sumOver_congr
      intro a _
      rfl
    rw [hcongr, hadd, hsub]
  rw [hsplit, hdebit, hshare]
  unfold total
  omega

theorem arch0_sumOver_accounts_share_proof (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  have hVcopy := hV
  obtain ⟨hNodupAcc, hpos, hne, hNodupRec, hsrcNot, hsrcMem, hsub, hauth, hbal, htx⟩ := hV
  have hzero : ∀ x, x ∈ s.accounts → x ∉ r.recipients → (fun a => (shareOf r a : Int)) x = 0 := by
    intro x _ hx
    simp only
    rw [arch0_shareOf_eq_zero_of_not_mem r x hx]
    simp
  have h1 := arch0_sumOver_subset_eq s.accounts r.recipients (fun a => (shareOf r a : Int)) hNodupAcc hNodupRec hsub hzero
  have h2 := arch0_sumOver_recipients_share s r hVcopy
  rw [h1]
  exact h2

theorem arch0_shareOf_getElem_proof (r : Request) (hnd : r.recipients.Nodup)
    (i : Nat) (hi : i < r.recipients.length) :
    shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
  unfold shareOf
  rw [indexOf?_getElem hnd i hi]

theorem tmp_zero_test (r : Request) (a : AccountId) (h : a ∉ r.recipients) : shareOf r a = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none h]













theorem plan1_range_succ_cons_aux6 (n : Nat) :
    List.range (n + 1) = 0 :: List.map (fun i => i + 1) (List.range n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hrange : List.range (n + 2) = List.range (n + 1) ++ [n + 1] := List.range_succ
    have hrange' : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    have hmap : List.map (fun i => i + 1) (List.range (n + 1))
        = List.map (fun i => i + 1) (List.range n) ++ [n + 1] := by
      rw [hrange', List.map_append]
      simp
    have h1 : (n + 1 + 1) = (n + 2) := by omega
    have eL : List.range (n + 1 + 1) = (0 :: List.map (fun i => i + 1) (List.range n)) ++ [n + 1] := by
      rw [h1, hrange, ih]
    have eR : (0 : Nat) :: List.map (fun i => i + 1) (List.range (n + 1))
        = (0 :: List.map (fun i => i + 1) (List.range n)) ++ [n + 1] := by
      rw [hmap]
      rfl
    rw [eL, eR]

theorem plan1_range_succ_cons (n : Nat) :
    List.range (n + 1) = 0 :: List.map (fun i => i + 1) (List.range n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hrange : List.range (n + 2) = List.range (n + 1) ++ [n + 1] := List.range_succ
    have hrange' : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    have hmap : List.map (fun i => i + 1) (List.range (n + 1))
        = List.map (fun i => i + 1) (List.range n) ++ [n + 1] := by
      rw [hrange', List.map_append]
      simp
    have h1 : (n + 1 + 1) = (n + 2) := by omega
    have eL : List.range (n + 1 + 1) = (0 :: List.map (fun i => i + 1) (List.range n)) ++ [n + 1] := by
      rw [h1, hrange, ih]
    have eR : (0 : Nat) :: List.map (fun i => i + 1) (List.range (n + 1))
        = (0 :: List.map (fun i => i + 1) (List.range n)) ++ [n + 1] := by
      rw [hmap]
      rfl
    rw [eL, eR]

theorem plan1_sumOver_map {α β : Type} (l : List α) (h : α → β) (f : β → Int) :
    sumOver (List.map h l) f = sumOver l (fun a => f (h a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem tmp_probe1 (n : Nat) (c : Int) : ((n + 1 : Nat) : Int) * c = (n : Int) * c + c := by
  have h1 : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
  rw [h1]
  rw [Int.add_mul, Int.one_mul]

theorem plan1_sumOver_range_const (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrange : List.range (n + 1) = List.range n ++ [n] := by rw [List.range_succ]
    rw [hrange, sumOver_append_test, ih]
    simp only [sumOver_cons, sumOver_nil, Int.add_zero]
    have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
    rw [hcast, Int.add_mul, Int.one_mul]

theorem plan1_sumOver_range_indicator (n k : Nat) (hk : k ≤ n) :
    sumOver (List.range n) (fun i => if i < k then (1 : Int) else 0) = (k : Int) := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    rfl
  | succ n ih =>
    by_cases hk0 : k = 0
    · subst hk0
      have heq : ∀ a ∈ List.range (n + 1), (if a < 0 then (1 : Int) else 0) = 0 := by
        intro a _
        rw [if_neg (by omega)]
      rw [sumOver_congr _ _ _ heq]
      induction (List.range (n + 1)) with
      | nil => rfl
      | cons a l ihl => simp [ihl]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hjle : j ≤ n := by omega
      have ihj := ih j hjle
      have hrange : List.range (n + 1) = 0 :: List.map (fun i => i + 1) (List.range n) :=
        plan1_range_succ_cons n
      rw [hrange]
      simp only [sumOver_cons]
      have hhead : (if (0 : Nat) < j + 1 then (1 : Int) else 0) = 1 := by
        rw [if_pos (by omega)]
      rw [hhead]
      have hmap : sumOver (List.map (fun i => i + 1) (List.range n))
          (fun i => if i < j + 1 then (1 : Int) else 0)
          = sumOver (List.range n) (fun i => if i < j then (1 : Int) else 0) := by
        rw [plan1_sumOver_map]
        apply sumOver_congr
        intro a _
        by_cases h1 : a < j <;> by_cases h2 : a + 1 < j + 1 <;> simp [h1, h2] <;> omega
      rw [hmap, ihj]
      push_cast
      omega

theorem probe_final (amount n : Nat) (h : amount / n * n + amount % n = amount) :
    (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) = (amount : Int) := by
  have hInt : ((amount / n * n + amount % n : Nat) : Int) = (amount : Int) := by rw [h]
  simp at hInt
  have hcomm : (n : Int) * ((amount / n : Nat) : Int) = ((amount / n : Nat) : Int) * (n : Int) :=
    Int.mul_comm _ _
  rw [hcomm]
  omega

theorem plan1_fairShare_range_sum (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by
  have hmod_le : amount % n ≤ n := Nat.le_of_lt (Nat.mod_lt amount hn)
  have hcongr : ∀ i ∈ List.range n,
      (fairShare amount n i : Int) = ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) := by
    intro i _
    unfold fairShare
    by_cases h : i < amount % n <;> simp [h]
  have h1 : sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = sumOver (List.range n) (fun _ => ((amount / n : Nat) : Int))
        + sumOver (List.range n) (fun i => (if i < amount % n then (1 : Int) else 0)) := by
    rw [← sumOver_add]
    apply sumOver_congr
    intro a ha
    exact hcongr a ha
  rw [h1, plan1_sumOver_range_const, plan1_sumOver_range_indicator _ _ hmod_le]
  have h := Nat.div_add_mod amount n
  have hInt : ((n * (amount / n) + amount % n : Nat) : Int) = (amount : Int) := by rw [h]
  simp at hInt
  omega

theorem plan1_sumOver_erase_mem (l : List AccountId) (hl : l.Nodup)
    (a : AccountId) (ha : a ∈ l) (f : AccountId → Int) :
    sumOver l f = f a + sumOver (l.erase a) f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    have hl2 : xs.Nodup := (List.nodup_cons.mp hl).2
    simp only [sumOver_cons]
    by_cases hxa : x = a
    · subst hxa
      simp
    · have ha' : a ∈ xs := by
        simp at ha
        cases ha with
        | inl h => exact absurd h.symm hxa
        | inr h => exact h
      have herase : (x :: xs).erase a = x :: xs.erase a := by simp [hxa]
      rw [herase]
      simp only [sumOver_cons]
      rw [ih hl2 ha']
      omega

theorem tmp_eq_range_proof {α : Type} (l : List α) (f : α → Int) (g : Nat → Int)
    (h : ∀ (i : Nat) (hi : i < l.length), f l[i] = g i) :
    sumOver l f = sumOver (List.range l.length) g := by
  induction l generalizing g with
  | nil => simp
  | cons x xs ih =>
    have h0 : f x = g 0 := by
      have hh := h 0 (by simp)
      simpa using hh
    have hrest : ∀ (i : Nat) (hi : i < xs.length), f xs[i] = (fun j => g (j + 1)) i := by
      intro i hi
      have hi' : i + 1 < (x :: xs).length := by simp; omega
      have hh := h (i + 1) hi'
      simp at hh
      exact hh
    have ih' := ih (fun j => g (j + 1)) hrest
    have hrange : List.range (xs.length + 1) = 0 :: List.map (fun i => i + 1) (List.range xs.length) :=
      plan1_range_succ_cons xs.length
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    rw [hlen, hrange]
    simp only [sumOver_cons]
    have hmap : sumOver (List.map (fun i => i + 1) (List.range xs.length)) g
        = sumOver (List.range xs.length) (fun j => g (j + 1)) := plan1_sumOver_map _ _ _
    rw [hmap, ← ih', h0]

theorem tmp_recipients_share_proof2 (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  obtain ⟨hAccNd, hpos, hne, hNd, hsrcNot, hsrcMem, hsub, hauth, hbal, htx⟩ := hV
  have hne' : 0 < r.recipients.length := by
    cases e : r.recipients with
    | nil => simp [e] at hne
    | cons x xs => simp
  have hpoint : ∀ (i : Nat) (hi : i < r.recipients.length),
      (fun a => (shareOf r a : Int)) r.recipients[i]
        = (fun i => (fairShare r.amount r.recipients.length i : Int)) i := by
    intro i hi
    simp only
    rw [arch0_shareOf_getElem_proof r hNd i hi]
  have hstep := tmp_eq_range_proof r.recipients (fun a => (shareOf r a : Int))
    (fun i => (fairShare r.amount r.recipients.length i : Int)) hpoint
  rw [hstep]
  exact plan1_fairShare_range_sum r.amount r.recipients.length hne'

theorem tmp_subset_probe1 (l : List AccountId) (a : AccountId) : l.erase a ⊆ l := by
  intro x hx
  have := List.mem_of_mem_erase hx
  exact this
#check @List.mem_of_mem_erase
#check @List.Nodup
#check @List.erase

theorem tmp_zero_lemma (l : List AccountId) (f : AccountId → Int)
    (h : ∀ x, x ∈ l → f x = 0) : sumOver l f = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumOver_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    simp
#check @List.erase_sublist
#check @List.mem_of_mem_erase

theorem arch1_total_step_eq_sum_expected (s : State) (r : Request)
    (hV : ValidPayout s r) :
    total (step s r).2 = sumOver s.accounts (expectedBalance s r) := by
  unfold total
  rw [req_effects_aux1 s r hV]
  exact sumOver_congr s.accounts _ _ (fun a _ => req_effects_aux3 s r hV a)




theorem plan2_sumOver_subset_eq (big small : List AccountId) (f : AccountId → Int)
    (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hzero : ∀ x, x ∈ big → x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by sorry

theorem plan2_shareOf_int_eq_zero_of_not_mem (r : Request) (a : AccountId)
    (h : a ∉ r.recipients) :
    (shareOf r a : Int) = 0 := by
  have h0 : shareOf r a = 0 := tmp_zero_test r a h
  simp [h0]


theorem plan2_sumOver_recipients_eq_range (r : Request)
    (hnd : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by
  apply tmp_eq_range_proof r.recipients _ _
  intro i hi
  have h : shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i :=
    arch0_shareOf_getElem r hnd i hi
  simp [h]




theorem plan2_sumOver_accounts_eq_recipients (s : State) (r : Request)
    (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  apply plan2_sumOver_subset_eq
  · exact hV.1
  · exact hV.2.2.2.1
  · exact hV.2.2.2.2.2.2.1
  · intro x _ hx
    exact plan2_shareOf_int_eq_zero_of_not_mem r x hx


theorem plan2_sumOver_erase_add (l : List AccountId) (f : AccountId → Int)
    (hl : l.Nodup) (a : AccountId) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f :=
  plan1_sumOver_erase_mem l hl a ha f

theorem probe_print_erase : True := trivial
#check @List.erase
#check @List.erase_subset

theorem probeEraseCheckA2 {a : AccountId} {l : List AccountId} : List.erase l a ⊆ l :=
  List.erase_subset

theorem probeEraseCheckB2 (a : AccountId) (l : List AccountId) (h : l.Nodup) : (List.erase l a).Nodup :=
  List.Nodup.erase a h

theorem probeSubUse (big : List AccountId) (y x : AccountId) (h : x ∈ List.erase big y) : x ∈ big :=
  List.erase_subset h

theorem probeNodupEraseUse (big : List AccountId) (y : AccountId) (h : big.Nodup) : (List.erase big y).Nodup :=
  List.Nodup.erase y h

theorem plan2_shareOf_int_eq_zero_of_not_mem_proof (r : Request) (a : AccountId)
    (h : a ∉ r.recipients) :
    (shareOf r a : Int) = 0 := by
  have h0 : shareOf r a = 0 := tmp_zero_test r a h
  simp [h0]

theorem plan2_sumOver_recipients_eq_range_proof (r : Request)
    (hnd : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by
  apply tmp_eq_range_proof r.recipients _ _
  intro i hi
  have h : shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i :=
    arch0_shareOf_getElem r hnd i hi
  simp [h]

theorem plan2_fairShare_range_sum_helper (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = (amount : Int) :=
  plan1_fairShare_range_sum amount n hn

theorem plan2_fairShare_range_sum (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = (amount : Int) :=
  plan1_fairShare_range_sum amount n hn

theorem plan2_sumOver_accounts_eq_recipients_aux_tmp2 (s : State) (r : Request)
    (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  apply plan2_sumOver_subset_eq
  · exact hV.1
  · exact hV.2.2.2.1
  · exact hV.2.2.2.2.2.2.1
  · intro x _ hx
    exact plan2_shareOf_int_eq_zero_of_not_mem_proof r x hx

theorem plan2_sumOver_accounts_eq_recipients_aux_tmp3 (s : State) (r : Request)
    (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  apply plan2_sumOver_subset_eq
  · exact hV.1
  · exact hV.2.2.2.1
  · exact hV.2.2.2.2.2.2.1
  · intro x _ hx
    exact plan2_shareOf_int_eq_zero_of_not_mem r x hx
#check @plan2_shareOf_int_eq_zero_of_not_mem
#check @plan2_sumOver_subset_eq

theorem plan2_sumOver_accounts_eq_recipients_check_tmp (s : State) (r : Request)
    (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => (shareOf r a : Int)) :=
  plan2_sumOver_accounts_eq_recipients_aux_tmp3 s r hV
#check @plan2_sumOver_subset_eq
#check @plan2_shareOf_int_eq_zero_of_not_mem

theorem plan2_sumOver_accounts_eq_recipients_final_check (s : State) (r : Request)
    (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  exact plan2_sumOver_accounts_eq_recipients_aux_tmp3 s r hV

theorem arch1_total_step_eq_sum_expected_proof (s : State) (r : Request)
    (hV : ValidPayout s r) :
    total (step s r).2 = sumOver s.accounts (expectedBalance s r) := by
  unfold total
  rw [req_effects_aux1 s r hV]
  exact sumOver_congr s.accounts _ _ (fun a _ => req_effects_aux3 s r hV a)

theorem arch2_total_step_eq_sum_expected (s : State) (r : Request)
    (hV : ValidPayout s r) :
    total (step s r).2 = sumOver s.accounts (expectedBalance s r) := by sorry

theorem arch2_sumOver_accounts_expected_eq_total (s : State) (r : Request)
    (hV : ValidPayout s r) :
    sumOver s.accounts (expectedBalance s r) = total s := by sorry



theorem arch2_total_step_of_valid_proof (s : State) (r : Request)
    (hV : ValidPayout s r) :
    total (step s r).2 = total s :=
  calc total (step s r).2
      = sumOver s.accounts (expectedBalance s r) := arch1_total_step_eq_sum_expected_proof s r hV
    _ = total s := arch0_sumOver_accounts_expected s r hV

theorem arch2_total_step_of_valid (s : State) (r : Request)
    (hV : ValidPayout s r) :
    total (step s r).2 = total s :=
  calc total (step s r).2
      = sumOver s.accounts (expectedBalance s r) := arch1_total_step_eq_sum_expected_proof s r hV
    _ = total s := arch0_sumOver_accounts_expected s r hV



theorem plan3_sumOver_subset_eq (big small : List AccountId) (f : AccountId → Int)
    (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hzero : ∀ x, x ∈ big → x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by sorry

theorem plan3_sumOver_list_eq_range {α : Type} (l : List α) (f : α → Int)
    (g : Nat → Int)
    (h : ∀ (i : Nat) (hi : i < l.length), f l[i] = g i) :
    sumOver l f = sumOver (List.range l.length) g := by sorry

theorem plan3_fairShare_range_sum (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = (amount : Int) := by sorry

theorem plan3_sumOver_recipients_share (r : Request)
    (hnd : r.recipients.Nodup) (hpos : 0 < r.recipients.length) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem plan3_sumOver_accounts_eq_recipients (s : State) (r : Request)
    (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver r.recipients (fun a => (shareOf r a : Int)) := by sorry

theorem plan3_sumOver_erase_add (l : List AccountId) (f : AccountId → Int)
    (hl : l.Nodup) (a : AccountId) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f :=
  plan1_sumOver_erase_mem l hl a ha f

theorem probe_print_erase2 : True := trivial
#check @List.erase
#check @List.Nodup
#print List.erase

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization  : AuthorizedOnly step := by
  unfold AuthorizedOnly
  intro s r h
  unfold step at h
  by_cases hv : ValidPayout s r
  · exact hv.2.2.2.2.2.2.2.1
  · simp [hv] at h

theorem req_effects : Effects step := by
  intro s r hOk
  by_cases hV : ValidPayout s r
  · exact ⟨req_effects_aux1 s r hV, req_effects_aux2 s r hV, fun a => req_effects_aux3 s r hV a⟩
  · exfalso
    have h1 : (step s r).1 = Outcome.rejected := by simp [step, hV]
    rw [h1] at hOk
    exact Outcome.noConfusion hOk

theorem req_idempotency    : Idempotent step := by
  unfold Idempotent
  intro s r hok
  exact ⟨arch0_idem_applied_mem s r hok, arch0_idem_replay s r hok⟩

theorem req_nonnegative : NonNegative step := by
  unfold NonNegative
  intro s r hnn a ha
  by_cases hV : ValidPayout s r
  · have hacc : (step s r).2.accounts = s.accounts := req_effects_aux1 s r hV
    have hbal : (step s r).2.balance a = expectedBalance s r a := req_effects_aux3 s r hV a
    rw [hacc] at ha
    have ha0 : 0 ≤ s.balance a := hnn a ha
    rw [hbal]
    unfold ValidPayout at hV
    obtain ⟨_, _, _, _, hsrcNot, _, _, _, hle, _⟩ := hV
    unfold expectedBalance shareOf
    by_cases heq : a = r.source
    · subst heq
      have hidx : indexOf? r.recipients r.source = none := indexOf?_eq_none hsrcNot
      rw [hidx]
      simp
      omega
    · simp only [heq, ↓reduceIte]
      cases h : indexOf? r.recipients a
      · simp; exact ha0
      · simp; omega
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hV]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have hbal : (step s r).2.balance a = s.balance a := by rw [hstep]
    rw [hacc] at ha
    rw [hbal]
    exact hnn a ha

theorem req_fair_shares    : FairShares step := by
  unfold FairShares
  intro s r hOk i hi
  have hV : ValidPayout s r := valid_of_ok_aux s r hOk
  unfold ValidPayout at hV
  obtain ⟨_, _, _, hRnodup, hSrcNot, _, _, _, _, _⟩ := hV
  have hBal := req_effects_aux3 s r (valid_of_ok_aux s r hOk) (r.recipients[i])
  have hIdx : indexOf? r.recipients r.recipients[i] = some i :=
    indexOf?_getElem hRnodup i hi
  have hMem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hNe : r.recipients[i] ≠ r.source := by
    intro hEq
    exact hSrcNot (hEq ▸ hMem)
  have hEq : (step s r).2.balance r.recipients[i] - s.balance r.recipients[i]
      = (shareOf r r.recipients[i] : Int) := by
    rw [hBal]
    unfold expectedBalance
    simp [hNe]
    omega
  calc (step s r).2.balance r.recipients[i] - s.balance r.recipients[i]
      = (shareOf r r.recipients[i] : Int) := hEq
    _ = (fairShare r.amount r.recipients.length i : Int) := by
        unfold shareOf
        rw [hIdx]

theorem req_conservation   : Conserves step := by
  intro s r hok
  exact arch2_total_step_of_valid s r (valid_of_ok_aux s r hok)

end Payout
