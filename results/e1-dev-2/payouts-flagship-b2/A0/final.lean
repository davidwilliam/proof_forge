import Payout.Spec
import Payout.Lemmas
import Init.Data.Int.Lemmas
import Init.Data.Nat.Lemmas
namespace Payout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout
  infer_instance

def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied })
  else
    (.rejected, s)

theorem step_eq_of_valid (s : State) (r : Request) (h : ValidPayout s r) :
    step s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
  unfold step
  simp [h]

theorem step_eq_of_invalid (s : State) (r : Request) (h : ¬ ValidPayout s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [h]

theorem valid_of_ok (s : State) (r : Request) (h : (step s r).1 = .ok) : ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · have h2 : (step s r).1 = .rejected := by
      unfold step
      simp [hv]
    rw [h2] at h
    exact absurd h (by decide)

theorem getElem_mem (l : List Nat) (i : Nat) (h : i < l.length) : l[i] ∈ l := by
  revert i
  induction l with
  | nil =>
    intro i h
    simp at h
  | cons x xs ih =>
    intro i h
    cases i with
    | zero =>
      simp
    | succ n =>
      have hi : n < xs.length := by simp at h; omega
      have hm := ih n hi
      simp [hm]

theorem shareOf_zero_of_not_mem (r : Request) (a : AccountId) (h : a ∉ r.recipients) :
    shareOf r a = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none h]

theorem shareOf_eq_fair_of_getElem (r : Request) (i : Nat) (h : i < r.recipients.length)
    (hnodup : r.recipients.Nodup) :
    shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
  unfold shareOf
  rw [indexOf?_getElem hnodup i h]

theorem indexOf?_ne_none_of_mem {l : List Nat} {a : Nat} (hm : a ∈ l) : indexOf? l a ≠ none := by
  induction l with
  | nil => simp at hm
  | cons x xs ih =>
    simp only [indexOf?]
    by_cases hxa : x = a
    · simp [hxa]
    · simp [hxa]
      intro hnone
      apply ih _ hnone
      simp at hm
      cases hm with
      | inl he =>
        have he2 : x = a := he.symm
        exact absurd he2 hxa
      | inr hm2 => exact hm2

theorem sumOver_zero {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [sumOver_cons, ih]

theorem sumOver_interchange {α β : Type} (l1 : List α) (l2 : List β) (F : α → β → Int) :
    sumOver l1 (fun a => sumOver l2 (fun b => F a b)) =
    sumOver l2 (fun b => sumOver l1 (fun a => F a b)) := by
  induction l1 with
  | nil =>
    simp only [sumOver_nil]
    exact (sumOver_zero l2).symm
  | cons x xs ih =>
    have h1 : sumOver (x :: xs) (fun a => sumOver l2 (fun b => F a b))
        = sumOver l2 (fun b => F x b) + sumOver xs (fun a => sumOver l2 (fun b => F a b)) := rfl
    rw [h1, ih]
    have h2 : (fun b : β => sumOver (x :: xs) (fun a => F a b))
        = (fun b => F x b + sumOver xs (fun a => F a b)) := rfl
    rw [h2]
    rw [← sumOver_add]

def sumFrom (n k : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | Nat.succ n => f k + sumFrom n (k + 1) f

theorem sumFrom_add_aux (n : Nat) : ∀ (k : Nat) (f g : Nat → Int),
    sumFrom n k (fun i => f i + g i) = sumFrom n k f + sumFrom n k g := by
  induction n with
  | zero =>
    intro k f g
    simp [sumFrom]
  | succ n ih =>
    intro k f g
    have h0 : sumFrom (n + 1) k (fun i => f i + g i) = (f k + g k) + sumFrom n (k + 1) (fun i => f i + g i) := rfl
    have h1 : sumFrom (n + 1) k f = f k + sumFrom n (k + 1) f := rfl
    have h2 : sumFrom (n + 1) k g = g k + sumFrom n (k + 1) g := rfl
    rw [h0, h1, h2, ih]
    omega

theorem sumFrom_add (n k : Nat) (f g : Nat → Int) :
    sumFrom n k (fun i => f i + g i) = sumFrom n k f + sumFrom n k g :=
  sumFrom_add_aux n k f g

theorem sumFrom_const_aux (n : Nat) : ∀ (k d : Nat),
    sumFrom n k (fun _ => (d : Int)) = ((d * n : Nat) : Int) := by
  induction n with
  | zero =>
    intro k d
    simp [sumFrom]
  | succ n ih =>
    intro k d
    have h0 : sumFrom (n + 1) k (fun _ => (d : Int))
      = (d : Int) + sumFrom n (k + 1) (fun _ => (d : Int)) := rfl
    rw [h0, ih]
    have heq : d * (n + 1) = d * n + d := rfl
    rw [heq]
    omega

theorem sumFrom_const_cast (n k d : Nat) :
    sumFrom n k (fun _ => (d : Int)) = ((d * n : Nat) : Int) :=
  sumFrom_const_aux n k d

theorem sumFrom_ite_zero_aux (n : Nat) : ∀ (k r : Nat), r ≤ k →
    sumFrom n k (fun i => if i < r then (1 : Int) else 0) = 0 := by
  induction n with
  | zero =>
    intro k r hkr
    rfl
  | succ n ih =>
    intro k r hkr
    have h0 : sumFrom (n + 1) k (fun i => if i < r then (1 : Int) else 0)
      = (if k < r then (1 : Int) else 0) + sumFrom n (k + 1) (fun i => if i < r then (1 : Int) else 0) := rfl
    rw [h0]
    have hk : ¬ k < r := by omega
    simp [hk, ih (k + 1) r (by omega)]

theorem sumFrom_ite_zero (n k r : Nat) (hkr : r ≤ k) :
    sumFrom n k (fun i => if i < r then (1 : Int) else 0) = 0 :=
  sumFrom_ite_zero_aux n k r hkr

theorem sumFrom_ite_eq_aux (n : Nat) : ∀ (k r : Nat), k ≤ r → r ≤ k + n →
    sumFrom n k (fun i => if i < r then (1 : Int) else 0) = ((r - k : Nat) : Int) := by
  induction n with
  | zero =>
    intro k r h1 h2
    have hrk : r = k := by omega
    simp [sumFrom, hrk]
  | succ n ih =>
    intro k r h1 h2
    have h0 : sumFrom (n + 1) k (fun i => if i < r then (1 : Int) else 0)
      = (if k < r then (1 : Int) else 0) + sumFrom n (k + 1) (fun i => if i < r then (1 : Int) else 0) := rfl
    rw [h0]
    by_cases hkr : k < r
    · simp [hkr]
      have ihv := ih (k + 1) r (by omega) (by omega)
      rw [ihv]
      have hcast : ((r - k : Nat) : Int) = (((r - (k + 1) : Nat)) : Int) + 1 := by
        have heq : (r - k : Nat) = (r - (k + 1) : Nat) + 1 := by omega
        have h1x : ((r - k : Nat) : Int) = ((((r - (k + 1) : Nat) + 1 : Nat)) : Int) := by
          rw [← heq]
        rw [h1x]
        simp
      rw [hcast]
      omega
    · have hrk : r = k := by omega
      have hkr2 : (if k < r then (1 : Int) else 0) = 0 := by simp [hkr]
      rw [hkr2]
      have hzero : sumFrom n (k + 1) (fun i => if i < r then (1 : Int) else 0) = 0 := by
        rw [hrk]
        exact sumFrom_ite_zero_aux n (k + 1) k (by omega)
      rw [hzero]
      simp [hrk]

theorem sumFrom_ite_eq (n k r : Nat) (h1 : k ≤ r) (h2 : r ≤ k + n) :
    sumFrom n k (fun i => if i < r then (1 : Int) else 0) = ((r - k : Nat) : Int) :=
  sumFrom_ite_eq_aux n k r h1 h2

theorem sumFrom_ite_le (n r : Nat) (h : r ≤ n) :
    sumFrom n 0 (fun i => if i < r then (1 : Int) else 0) = (r : Int) := by
  have h0 := sumFrom_ite_eq n 0 r (by omega) (by omega)
  simpa using h0

theorem fairShare_cast (A N i : Nat) :
    ((fairShare A N i : Nat) : Int) = ((A / N : Nat) : Int) + (if i < A % N then (1 : Int) else 0) := by
  unfold fairShare
  by_cases h : i < A % N
  · simp [h]
  · simp [h]

theorem sumFrom_fair (N A : Nat) (hN : 0 < N) :
    sumFrom N 0 (fun i => ((fairShare A N i : Nat) : Int)) = (A : Int) := by
  have hstep : (fun i => ((fairShare A N i : Nat) : Int))
    = (fun i => ((A / N : Nat) : Int) + (if i < A % N then (1 : Int) else 0)) := by
    funext i
    exact fairShare_cast A N i
  rw [hstep]
  have hcongr : sumFrom N 0 (fun i => ((A / N : Nat) : Int) + (if i < A % N then (1 : Int) else 0))
    = sumFrom N 0 (fun _ => ((A / N : Nat) : Int)) + sumFrom N 0 (fun i => if i < A % N then (1 : Int) else 0) :=
    sumFrom_add N 0 _ _
  rw [hcongr, sumFrom_const_cast]
  have hmod : A % N ≤ N := by
    have hlt : A % N < N := Nat.mod_lt A hN
    omega
  rw [sumFrom_ite_le N (A % N) hmod]
  have hNat : (A / N) * N + A % N = A := by
    have h1 := Nat.div_add_mod A N
    have h2 : N * (A / N) = (A / N) * N := Nat.mul_comm _ _
    rw [h2] at h1
    exact h1
  have hcast : ((((A / N) * N + A % N : Nat)) : Int) = (A : Int) := by
    rw [hNat]
  have hsplit : ((((A / N) * N : Nat)) : Int) + (((A % N : Nat)) : Int) = ((((A / N) * N + A % N : Nat)) : Int) := by
    simp
  rw [hsplit, hcast]

def shareAt (A N k : Nat) (l : List Nat) (a : Nat) : Int :=
  match indexOf? l a with
  | some i => ((fairShare A N (k + i) : Nat) : Int)
  | none => 0

def sumFair (A N : Nat) (l : List Nat) (k : Nat) : Int :=
  sumOver l (shareAt A N k l)

theorem shareAt_head_eq (A N k x : Nat) (xs : List Nat) :
    shareAt A N k (x :: xs) x = ((fairShare A N k : Nat) : Int) := by
  unfold shareAt
  simp [indexOf?]

theorem shareAt_shift_of_mem (A N k x a : Nat) (xs : List Nat) (hm : a ∈ xs) (hxx : x ∉ xs) :
    shareAt A N k (x :: xs) a = shareAt A N (k + 1) xs a := by
  have hxa : x ≠ a := fun h => hxx (h.symm ▸ hm)
  unfold shareAt
  have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
    simp [indexOf?, hxa]
  rw [hidx]
  cases h : indexOf? xs a with
  | none => rfl
  | some i =>
    simp only [Option.map_some]
    have heq : k + (i + 1) = (k + 1) + i := by omega
    rw [heq]

theorem sumFair_cons (A N k x : Nat) (xs : List Nat) (hxx : x ∉ xs) :
    sumFair A N (x :: xs) k = ((fairShare A N k : Nat) : Int) + sumFair A N xs (k + 1) := by
  unfold sumFair
  have hhead : shareAt A N k (x :: xs) x = ((fairShare A N k : Nat) : Int) :=
    shareAt_head_eq A N k x xs
  have hcons : sumOver (x :: xs) (shareAt A N k (x :: xs))
    = shareAt A N k (x :: xs) x + sumOver xs (shareAt A N k (x :: xs)) := rfl
  rw [hcons, hhead]
  congr 1
  apply sumOver_congr
  intro a ha
  exact shareAt_shift_of_mem A N k x a xs ha hxx

theorem sumFair_eq_sumFrom_aux (l : List Nat) : ∀ (A N k : Nat), l.Nodup →
    sumFair A N l k = sumFrom l.length k (fun i => ((fairShare A N i : Nat) : Int)) := by
  induction l with
  | nil =>
    intro A N k hl
    simp [sumFair, sumFrom, sumOver]
  | cons x xs ih =>
    intro A N k hl
    rw [List.nodup_cons] at hl
    rw [sumFair_cons A N k x xs hl.1]
    have ihv := ih A N (k + 1) hl.2
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    have hsum : sumFrom (xs.length + 1) k (fun i => ((fairShare A N i : Nat) : Int))
      = ((fairShare A N k : Nat) : Int) + sumFrom xs.length (k + 1) (fun i => ((fairShare A N i : Nat) : Int)) := rfl
    rw [hlen, hsum, ihv]

theorem sumFair_eq_sumFrom (l : List Nat) (A N k : Nat) (hl : l.Nodup) :
    sumFair A N l k = sumFrom l.length k (fun i => ((fairShare A N i : Nat) : Int)) :=
  sumFair_eq_sumFrom_aux l A N k hl

theorem sumOver_recipients_eq (r : Request) (hpos : 0 < r.recipients.length) (hnodup : r.recipients.Nodup) :
    sumOver r.recipients (fun b => ((shareOf r b : Nat) : Int)) = (r.amount : Int) := by
  have hN : 0 < r.recipients.length := hpos
  have hfair : sumFair r.amount r.recipients.length r.recipients 0
    = sumFrom r.recipients.length 0 (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int)) :=
    sumFair_eq_sumFrom r.recipients r.amount r.recipients.length 0 hnodup
  have hsum := sumFrom_fair r.recipients.length r.amount hN
  rw [hsum] at hfair
  have hcongr : sumOver r.recipients (fun b => ((shareOf r b : Nat) : Int))
    = sumFair r.amount r.recipients.length r.recipients 0 := by
    unfold sumFair
    apply sumOver_congr
    intro a ha
    unfold shareAt
    cases heq : indexOf? r.recipients a with
    | none =>
      have hne : indexOf? r.recipients a ≠ none := indexOf?_ne_none_of_mem ha
      exact absurd heq hne
    | some i =>
      simp only [heq, Nat.zero_add]
      have hsh : shareOf r a = fairShare r.amount r.recipients.length i := by
        unfold shareOf
        rw [heq]
      rw [hsh]
  rw [hcongr, hfair]

theorem sumShares_accounts_eq (s : State) (r : Request)
    (hNodupAcc : s.accounts.Nodup) (hNodupRec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) =
    sumOver r.recipients (fun b => ((shareOf r b : Nat) : Int)) := by
  have hz : ∀ a, ((shareOf r a : Nat) : Int)
      = sumOver r.recipients (fun b => if b = a then ((shareOf r a : Nat) : Int) else 0) := by
    intro a
    have h := sumOver_ite_eq hNodupRec a (((shareOf r a : Nat)) : Int)
    rw [h]
    by_cases hm : a ∈ r.recipients
    · simp [hm]
    · have hs : shareOf r a = 0 := shareOf_zero_of_not_mem r a hm
      simp [hm, hs]
  have heq1 : sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int))
      = sumOver s.accounts (fun a => sumOver r.recipients (fun b => if b = a then ((shareOf r a : Nat) : Int) else (0 : Int))) := by
    apply sumOver_congr
    intro a _
    exact hz a
  rw [heq1]
  have hinter := sumOver_interchange s.accounts r.recipients (fun a b => if b = a then ((shareOf r a : Nat) : Int) else (0 : Int))
  rw [hinter]
  apply sumOver_congr
  intro b hb
  have heq : (fun a => (if b = a then ((shareOf r a : Nat) : Int) else (0 : Int)))
    = (fun a => if a = b then ((shareOf r b : Nat) : Int) else 0) := by
    funext a
    by_cases he : a = b
    · subst he
      simp
    · have h1 : b ≠ a := fun h => he h.symm
      simp [he, h1]
  rw [heq, sumOver_ite_eq hNodupAcc b (((shareOf r b : Nat)) : Int)]
  simp [hsub b hb]

theorem sumShares_total (s : State) (r : Request) (h : ValidPayout s r) :
    sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) = (r.amount : Int) := by
  obtain ⟨hNodupAcc, hpos, hne, hNodupRec, hnsrc, hsrcmem, hsub, hauth, hle, hfresh⟩ := h
  have hposlen : 0 < r.recipients.length := by
    cases hr : r.recipients with
    | nil => exact absurd hr hne
    | cons _ _ => simp
  rw [sumShares_accounts_eq s r hNodupAcc hNodupRec hsub]
  exact sumOver_recipients_eq r hposlen hNodupRec

theorem total_after (s : State) (r : Request) (h : ValidPayout s r) :
    sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance := by
  obtain ⟨hNodupAcc, hpos, hne, hNodupRec, hnsrc, hsrcmem, hsub, hauth, hle, hfresh⟩ := h
  have hvalid : ValidPayout s r := ⟨hNodupAcc, hpos, hne, hNodupRec, hnsrc, hsrcmem, hsub, hauth, hle, hfresh⟩
  have hsum := sumShares_total s r hvalid
  have hsrcsum : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
    = (r.amount : Int) := by
    have hh := sumOver_ite_eq hNodupAcc r.source (r.amount : Int)
    rw [hh]
    simp [hsrcmem]
  have h1 : sumOver s.accounts (expectedBalance s r)
    = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int)) := by
    apply sumOver_congr
    intro a ha
    rfl
  rw [h1]
  have h2 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int))
    = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      + sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by
    have e1 : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int))
      = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + ((shareOf r a : Nat) : Int)) := by
      funext a
      omega
    rw [e1, sumOver_add]
    have e3 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) :=
      sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
    rw [e3]
  rw [h2, hsrcsum, hsum]
  omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have heq := step_eq_of_valid s r h
  simp [heq]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  exact step_eq_of_invalid s r h

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  have hvalid := valid_of_ok s r hok
  obtain ⟨hNodupAcc, hpos, hne, hNodupRec, hnsrc, hsrcmem, hsub, hauth, hle, hfresh⟩ := hvalid
  have hvalid2 : ValidPayout s r := ⟨hNodupAcc, hpos, hne, hNodupRec, hnsrc, hsrcmem, hsub, hauth, hle, hfresh⟩
  have heq := step_eq_of_valid s r hvalid2
  have hstate : (step s r).2 = { s with balance := expectedBalance s r, applied := r.txId :: s.applied } := by
    rw [heq]
  have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
    rw [hstate]
  rw [hbal]
  unfold expectedBalance
  have hmem : r.recipients[i] ∈ r.recipients := getElem_mem r.recipients i hi
  have hne2 : ¬ (r.recipients[i] = r.source) := fun heq2 => hnsrc (heq2 ▸ hmem)
  simp [hne2]
  have hsh := shareOf_eq_fair_of_getElem r i hi hNodupRec
  have hcast : ((shareOf r r.recipients[i] : Nat) : Int) = ((fairShare r.amount r.recipients.length i : Nat) : Int) := by
    rw [hsh]
  omega

theorem req_effects : Effects step := by
  intro s r hok
  have hvalid := valid_of_ok s r hok
  have heq := step_eq_of_valid s r hvalid
  have hstate : (step s r).2 = { s with balance := expectedBalance s r, applied := r.txId :: s.applied } := by
    rw [heq]
  have hacc : (step s r).2.accounts = s.accounts := by rw [hstate]
  have hauth2 : (step s r).2.auth = s.auth := by rw [hstate]
  have hbal : ∀ a, (step s r).2.balance a = expectedBalance s r a := by intro a; rw [hstate]
  exact ⟨hacc, hauth2, hbal⟩

theorem req_conservation : Conserves step := by
  intro s r hok
  have hvalid := valid_of_ok s r hok
  have heq := step_eq_of_valid s r hvalid
  have hstate : (step s r).2 = { s with balance := expectedBalance s r, applied := r.txId :: s.applied } := by
    rw [heq]
  unfold total
  have hacc : (step s r).2.accounts = s.accounts := by rw [hstate]
  rw [hacc]
  have hbal : ∀ a ∈ s.accounts, (step s r).2.balance a = expectedBalance s r a := by
    intro a _
    rw [hstate]
  have hcongr := sumOver_congr s.accounts (fun a => (step s r).2.balance a) (expectedBalance s r) (fun a ha => hbal a ha)
  rw [hcongr]
  exact total_after s r hvalid

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hvalid : ValidPayout s r
  · obtain ⟨hNodupAcc, hpos, hne, hNodupRec, hnsrc, hsrcmem, hsub, hauth, hle, hfresh⟩ := hvalid
    have hvalid2 : ValidPayout s r := ⟨hNodupAcc, hpos, hne, hNodupRec, hnsrc, hsrcmem, hsub, hauth, hle, hfresh⟩
    have heq := step_eq_of_valid s r hvalid2
    have hstate : (step s r).2 = { s with balance := expectedBalance s r, applied := r.txId :: s.applied } := by
      rw [heq]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstate]
    rw [hacc] at ha
    have hbal : (step s r).2.balance a = expectedBalance s r a := by rw [hstate]
    rw [hbal]
    unfold expectedBalance
    have hold : 0 ≤ s.balance a := hnn a ha
    by_cases hsrc : a = r.source
    · subst hsrc
      have hshare : shareOf r r.source = 0 := shareOf_zero_of_not_mem r r.source hnsrc
      simp [hshare]
      omega
    · simp [hsrc]
      have hge : (0 : Int) ≤ ((shareOf r a : Nat) : Int) := by omega
      omega
  · have heq := step_eq_of_invalid s r hvalid
    have hstate : (step s r).2 = s := by
      have h2 : (step s r).2 = s := by rw [heq]
      exact h2
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstate]
    rw [hacc] at ha
    have hbal : (step s r).2.balance a = s.balance a := by rw [hstate]
    rw [hbal]
    exact hnn a ha

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  have hvalid := valid_of_ok s r hok
  obtain ⟨hNodupAcc, hpos, hne, hNodupRec, hnsrc, hsrcmem, hsub, hauth, hle, hfresh⟩ := hvalid
  exact hauth

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hvalid := valid_of_ok s r hok
  have heq := step_eq_of_valid s r hvalid
  have hstate : (step s r).2 = { s with balance := expectedBalance s r, applied := r.txId :: s.applied } := by
    rw [heq]
  constructor
  · intro x
    have happ : (step s r).2.applied = r.txId :: s.applied := by rw [hstate]
    rw [happ]
    simp
  · have happ : (step s r).2.applied = r.txId :: s.applied := by rw [hstate]
    have hnvalid : ¬ ValidPayout (step s r).2 r := by
      intro hv
      obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10⟩ := hv
      have hmem : r.txId ∈ (step s r).2.applied := by
        rw [happ]
        simp
      exact u10 hmem
    have heq2 := step_eq_of_invalid (step s r).2 r hnvalid
    exact heq2

end Payout
