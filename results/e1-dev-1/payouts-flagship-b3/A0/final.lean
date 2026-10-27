import Payout.Spec
import Payout.Lemmas

namespace Payout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout
  infer_instance

def nextState (s : State) (r : Request) : State :=
  ⟨s.accounts, fun a => expectedBalance s r a, s.auth, r.txId :: s.applied⟩

def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, nextState s r)
  else
    (.rejected, s)

theorem step_eq_ok_of_valid {s : State} {r : Request} (h : ValidPayout s r) :
    step s r = (.ok, nextState s r) := by
  unfold step
  simp [h]

theorem step_eq_reject_of_invalid {s : State} {r : Request} (h : ¬ ValidPayout s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [h]

theorem ok_imp_valid {s : State} {r : Request} (h : (step s r).1 = .ok) :
    ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · have heq := step_eq_reject_of_invalid hv
    rw [heq] at h
    simp at h

theorem second_eq_next_of_ok {s : State} {r : Request} (h : (step s r).1 = .ok) :
    (step s r).2 = nextState s r := by
  have hv := ok_imp_valid h
  have heq := step_eq_ok_of_valid hv
  rw [heq]

theorem valid_nodup_acc {s : State} {r : Request} (h : ValidPayout s r) : s.accounts.Nodup := h.1
theorem valid_rec_nodup {s : State} {r : Request} (h : ValidPayout s r) : r.recipients.Nodup := h.2.2.2.1
theorem valid_src_notin {s : State} {r : Request} (h : ValidPayout s r) : r.source ∉ r.recipients := h.2.2.2.2.1
theorem valid_src_mem {s : State} {r : Request} (h : ValidPayout s r) : r.source ∈ s.accounts := h.2.2.2.2.2.1
theorem valid_rec_mem {s : State} {r : Request} (h : ValidPayout s r) : ∀ x ∈ r.recipients, x ∈ s.accounts := h.2.2.2.2.2.2.1
theorem valid_auth {s : State} {r : Request} (h : ValidPayout s r) : s.auth r.requester r.source = true := h.2.2.2.2.2.2.2.1
theorem valid_bal {s : State} {r : Request} (h : ValidPayout s r) : (r.amount : Int) ≤ s.balance r.source := h.2.2.2.2.2.2.2.2.1
theorem valid_txid {s : State} {r : Request} (h : ValidPayout s r) : r.txId ∉ s.applied := h.2.2.2.2.2.2.2.2.2
theorem valid_ne_nil {s : State} {r : Request} (h : ValidPayout s r) : r.recipients ≠ [] := h.2.2.1

theorem shareOf_eq_zero_of_not_mem {r : Request} {a : AccountId} (h : a ∉ r.recipients) :
    shareOf r a = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none h]

theorem shareOf_mem_eq {r : Request} (hn : r.recipients.Nodup)
    (i : Nat) (hi : i < r.recipients.length) :
    shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
  unfold shareOf
  rw [indexOf?_getElem hn i hi]

theorem getElem_ne_source {r : Request} (hs : r.source ∉ r.recipients)
    (i : Nat) (hi : i < r.recipients.length) : r.recipients[i] ≠ r.source := by
  intro heq
  apply hs
  rw [← heq]
  exact List.getElem_mem hi

def myErase : List Nat → Nat → List Nat
  | [], _ => []
  | y :: ys, a => if y = a then ys else y :: myErase ys a

theorem myErase_cons_eq (y : Nat) (ys : List Nat) (a : Nat) :
    myErase (y :: ys) a = (if y = a then ys else y :: myErase ys a) := rfl

theorem mem_myErase_of_ne_mem (x a : Nat) (hne : x ≠ a) :
    ∀ (l : List Nat), x ∈ l → x ∈ myErase l a := by
  intro l
  induction l with
  | nil => intro hm; simp at hm
  | cons y ys ih =>
    intro hm
    have hm' := (List.mem_cons.mp hm)
    have heq : myErase (y :: ys) a = (if y = a then ys else y :: myErase ys a) := rfl
    rw [heq]
    by_cases hy : y = a
    · rw [if_pos hy]
      cases hm' with
      | inl heq2 => exact absurd (heq2 ▸ hy) hne
      | inr h2 => exact h2
    · rw [if_neg hy]
      cases hm' with
      | inl heq2 => exact List.mem_cons.mpr (Or.inl heq2)
      | inr h2 => exact List.mem_cons.mpr (Or.inr (ih h2))

theorem mem_of_mem_myErase (x a : Nat) :
    ∀ (l : List Nat), x ∈ myErase l a → x ∈ l := by
  intro l
  induction l with
  | nil =>
    intro hm
    have he : myErase ([] : List Nat) a = [] := rfl
    rw [he] at hm
    simp at hm
  | cons y ys ih =>
    intro hm
    have heq : myErase (y :: ys) a = (if y = a then ys else y :: myErase ys a) := rfl
    rw [heq] at hm
    by_cases hy : y = a
    · rw [if_pos hy] at hm
      exact List.mem_cons.mpr (Or.inr (ih hm))
    · rw [if_neg hy] at hm
      have hm' := (List.mem_cons.mp hm)
      cases hm' with
      | inl heq2 => exact List.mem_cons.mpr (Or.inl heq2)
      | inr h2 => exact List.mem_cons.mpr (Or.inr (ih h2))

theorem not_mem_myErase_self (a : Nat) :
    ∀ (l : List Nat), l.Nodup → a ∈ l → a ∉ myErase l a := by
  intro l
  induction l with
  | nil => intro hn hm hcon; simp at hm
  | cons y ys ih =>
    intro hn hm hcon
    have hn1 : y ∉ ys := (List.nodup_cons.mp hn).1
    have hn2 : ys.Nodup := (List.nodup_cons.mp hn).2
    have heq : myErase (y :: ys) a = (if y = a then ys else y :: myErase ys a) := rfl
    rw [heq] at hcon
    have hm' := (List.mem_cons.mp hm)
    by_cases hy : y = a
    · rw [if_pos hy] at hcon
      cases hm' with
      | inl heq2 =>
        have hy2 : y ∈ ys := by rw [hy]; exact hcon
        exact hn1 hy2
      | inr h2 => exact hn1 hcon
    · rw [if_neg hy] at hcon
      have hcon' := (List.mem_cons.mp hcon)
      cases hcon' with
      | inl heq2 => exact hy heq2.symm
      | inr h3 =>
        cases hm' with
        | inl heq2 => exact hy heq2.symm
        | inr h2 => exact ih hn2 h2 h3

theorem nodup_myErase (a : Nat) :
    ∀ (l : List Nat), l.Nodup → (myErase l a).Nodup := by
  intro l
  induction l with
  | nil =>
    intro hn
    have he : myErase ([] : List Nat) a = [] := rfl
    rw [he]
    exact List.nodup_nil
  | cons y ys ih =>
    intro hn
    have hn1 : y ∉ ys := (List.nodup_cons.mp hn).1
    have hn2 : ys.Nodup := (List.nodup_cons.mp hn).2
    have heq : myErase (y :: ys) a = (if y = a then ys else y :: myErase ys a) := rfl
    rw [heq]
    by_cases hy : y = a
    · rw [if_pos hy]
      exact hn2
    · rw [if_neg hy]
      have ih' := ih hn2
      have hmem : y ∉ myErase ys a := by
        intro hcon
        exact hn1 (mem_of_mem_myErase y a ys hcon)
      exact (List.nodup_cons.mpr ⟨hmem, ih'⟩)

theorem sum_myErase_nodup (f : Nat → Int) (a : Nat) :
    ∀ (l : List Nat), l.Nodup → a ∈ l → sumOver l f = f a + sumOver (myErase l a) f := by
  intro l
  induction l with
  | nil => intro hn hm; simp at hm
  | cons y ys ih =>
    intro hn hm
    have hn1 : y ∉ ys := (List.nodup_cons.mp hn).1
    have hn2 : ys.Nodup := (List.nodup_cons.mp hn).2
    have hm' := (List.mem_cons.mp hm)
    by_cases hy : y = a
    · have hmy : myErase (y :: ys) a = ys := by
        have e : myErase (y :: ys) a = (if y = a then ys else y :: myErase ys a) := rfl
        rw [e, if_pos hy]
      rw [hmy]
      cases hm' with
      | inl heq2 =>
        rw [← heq2]
        rfl
      | inr h2 =>
        have hy2 : y ∈ ys := by rw [hy]; exact h2
        exact absurd hy2 hn1
    · have hmem : a ∈ ys := by
        cases hm' with
        | inl heq => exact absurd heq.symm hy
        | inr h2 => exact h2
      have heq2 : myErase (y :: ys) a = y :: myErase ys a := by
        have e : myErase (y :: ys) a = (if y = a then ys else y :: myErase ys a) := rfl
        rw [e, if_neg hy]
      have ih' := ih hn2 hmem
      calc sumOver (y :: ys) f = f y + sumOver ys f := rfl
        _ = f y + (f a + sumOver (myErase ys a) f) := by rw [ih']
        _ = f a + (f y + sumOver (myErase ys a) f) := by omega
        _ = f a + sumOver (y :: myErase ys a) f := rfl
        _ = f a + sumOver (myErase (y :: ys) a) f := by rw [heq2]

theorem superset_sum_aux :
    ∀ (S : List Nat) (R : List Nat) (f : Nat → Int),
    S.Nodup → R.Nodup → (∀ x ∈ R, x ∈ S) → (∀ x ∈ S, x ∉ R → f x = 0) →
    sumOver S f = sumOver R f := by
  intro S
  induction S with
  | nil =>
    intro R f _ _ hsub _
    cases R with
    | nil => rfl
    | cons y ys =>
      have hmem : y ∈ y :: ys := List.mem_cons.mpr (Or.inl rfl)
      have hs := hsub y hmem
      simp at hs
  | cons a t ih =>
    intro R f hS hR hsub hzero
    have hS1 : a ∉ t := (List.nodup_cons.mp hS).1
    have hS2 : t.Nodup := (List.nodup_cons.mp hS).2
    simp only [sumOver_cons]
    by_cases haR : a ∈ R
    · have hRerase_nodup : (myErase R a).Nodup := nodup_myErase a R hR
      have ha_not_erase : a ∉ myErase R a := not_mem_myErase_self a R hR haR
      have hsub' : ∀ x ∈ myErase R a, x ∈ t := by
        intro x hx
        have hxR := mem_of_mem_myErase x a R hx
        have hxS := hsub x hxR
        have hxS' := (List.mem_cons.mp hxS)
        cases hxS' with
        | inl heq2 =>
          subst heq2
          exact absurd hx ha_not_erase
        | inr h2 => exact h2
      have hzero' : ∀ x ∈ t, x ∉ myErase R a → f x = 0 := by
        intro x hxt hxnerase
        apply hzero x (List.mem_cons.mpr (Or.inr hxt))
        intro hxR
        have hne : x ≠ a := by
          intro heq2
          subst heq2
          exact hS1 hxt
        exact hxnerase (mem_myErase_of_ne_mem x a hne R hxR)
      have hsumR := sum_myErase_nodup f a R hR haR
      have ih' := ih (myErase R a) f hS2 hRerase_nodup hsub' hzero'
      rw [hsumR, ih']
      omega
    · have hfa : f a = 0 := hzero a (List.mem_cons.mpr (Or.inl rfl)) haR
      have hsub' : ∀ x ∈ R, x ∈ t := by
        intro x hx
        have hxS := hsub x hx
        have hxS' := (List.mem_cons.mp hxS)
        cases hxS' with
        | inl heq =>
          subst heq
          exact absurd hx haR
        | inr h2 => exact h2
      have hzero' : ∀ x ∈ t, x ∉ R → f x = 0 := by
        intro x hxt hxR
        exact hzero x (List.mem_cons.mpr (Or.inr hxt)) hxR
      have ih' := ih R f hS2 hR hsub' hzero'
      rw [hfa, ih']
      omega

def recSum (amt N m k : Nat) : Int :=
  match m with
  | 0 => 0
  | Nat.succ m' => (fairShare amt N k : Int) + recSum amt N m' (k + 1)

def natRec (amt N m k : Nat) : Nat :=
  match m with
  | 0 => 0
  | Nat.succ m' => fairShare amt N k + natRec amt N m' (k + 1)

def cnt (q m k : Nat) : Nat :=
  match m with
  | 0 => 0
  | Nat.succ m' => (if k < q then 1 else 0) + cnt q m' (k + 1)

theorem cnt_eq_zero_of_ge (q : Nat) :
    ∀ (m k : Nat), q ≤ k → cnt q m k = 0 := by
  intro m
  induction m with
  | zero => intro k hle; rfl
  | succ m ih =>
    intro k hle
    have he : cnt q (Nat.succ m) k = (if k < q then 1 else 0) + cnt q m (k + 1) := rfl
    rw [he]
    have h : ¬ k < q := by omega
    simp [h, ih (k + 1) (by omega)]

theorem cnt_eq_min_of_le (q : Nat) :
    ∀ (m k : Nat), k ≤ q → cnt q m k = min m (q - k) := by
  intro m
  induction m with
  | zero => intro k hle; simp [cnt]
  | succ m ih =>
    intro k hle
    have he : cnt q (Nat.succ m) k = (if k < q then 1 else 0) + cnt q m (k + 1) := rfl
    rw [he]
    by_cases h : k < q
    · rw [if_pos h, ih (k + 1) (by omega)]
      omega
    · have heqk : k = q := by omega
      subst heqk
      rw [if_neg (by omega : ¬ q < q)]
      simp only [Nat.zero_add]
      have h0 : cnt q m (q + 1) = 0 := cnt_eq_zero_of_ge q m (q + 1) (by omega)
      rw [h0]
      simp
      omega

theorem cnt_full (amt N : Nat) (hN : 0 < N) : cnt (amt % N) N 0 = amt % N := by
  have heq := cnt_eq_min_of_le (amt % N) N 0 (Nat.zero_le _)
  simp only [Nat.sub_zero] at heq
  rw [heq]
  have hlt : amt % N < N := Nat.mod_lt _ hN
  omega

theorem natRec_eq (amt N : Nat) :
    ∀ (m k : Nat), natRec amt N m k = m * (amt / N) + cnt (amt % N) m k := by
  intro m
  induction m with
  | zero => intro k; simp [natRec, cnt]
  | succ m ih =>
    intro k
    have e1 : natRec amt N (Nat.succ m) k = fairShare amt N k + natRec amt N m (k + 1) := rfl
    have e2 : cnt (amt % N) (Nat.succ m) k = (if k < amt % N then 1 else 0) + cnt (amt % N) m (k + 1) := rfl
    rw [e1, e2, ih (k + 1)]
    have hfs : fairShare amt N k = amt / N + (if k < amt % N then 1 else 0) := rfl
    rw [hfs]
    have hmul : (Nat.succ m) * (amt / N) = m * (amt / N) + amt / N := by
      rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul]
    rw [hmul]
    omega

theorem natRec_full (amt N : Nat) (hN : 0 < N) : natRec amt N N 0 = amt := by
  rw [natRec_eq, cnt_full amt N hN, Nat.add_comm]
  have h := Nat.div_add_mod amt N
  omega

theorem recSum_eq_natRec (amt N : Nat) :
    ∀ (m k : Nat), recSum amt N m k = ((natRec amt N m k : Nat) : Int) := by
  intro m
  induction m with
  | zero => intro k; simp [recSum, natRec]
  | succ m ih =>
    intro k
    have e1 : recSum amt N (Nat.succ m) k = (fairShare amt N k : Int) + recSum amt N m (k + 1) := rfl
    have e2 : natRec amt N (Nat.succ m) k = fairShare amt N k + natRec amt N m (k + 1) := rfl
    rw [e1, e2, ih (k + 1)]
    simp

theorem recSum_full (amt N : Nat) (hN : 0 < N) : recSum amt N N 0 = (amt : Int) := by
  rw [recSum_eq_natRec, natRec_full amt N hN]

theorem sum_rec_eq :
    ∀ (R : List Nat) (l : List Nat) (k amt N : Nat),
    (∀ j (hj : j < l.length), indexOf? R l[j] = some (k + j)) →
    sumOver l (fun a => match indexOf? R a with | some i => (fairShare amt N i : Int) | none => 0)
      = recSum amt N l.length k := by
  intro R l
  induction l with
  | nil =>
    intro k amt N _
    simp [recSum]
  | cons x xs ih =>
    intro k amt N hidx
    have h0lt : 0 < (x :: xs).length := by simp
    have h0 := hidx 0 h0lt
    have hhead : indexOf? R x = some k := by
      have hget : (x :: xs)[0]'h0lt = x := by simp
      have hk0 : k + 0 = k := by omega
      rw [hget, hk0] at h0
      exact h0
    have htail : ∀ j (hj : j < xs.length), indexOf? R xs[j] = some ((k + 1) + j) := by
      intro j hj
      have hj' : j + 1 < (x :: xs).length := by simp; omega
      have h := hidx (j + 1) hj'
      have hget : (x :: xs)[j + 1]'hj' = xs[j]'hj := by simp
      rw [hget] at h
      have heq : k + (j + 1) = (k + 1) + j := by omega
      rw [heq] at h
      exact h
    have ih' := ih (k + 1) amt N htail
    have hlen : (x :: xs).length = Nat.succ xs.length := rfl
    have hrec : recSum amt N (Nat.succ xs.length) k = (fairShare amt N k : Int) + recSum amt N xs.length (k + 1) := rfl
    have hsum : sumOver (x :: xs) (fun a => match indexOf? R a with | some i => (fairShare amt N i : Int) | none => 0)
        = (fairShare amt N k : Int) + sumOver xs (fun a => match indexOf? R a with | some i => (fairShare amt N i : Int) | none => 0) := by
      simp only [sumOver_cons, hhead]
    rw [hsum, ih', hlen, hrec]

theorem sumOver_recips_eq (R : List Nat) (hn : R.Nodup) (amt N : Nat) (hN : R.length = N) :
    sumOver R (fun a => match indexOf? R a with | some i => (fairShare amt N i : Int) | none => 0)
      = recSum amt N N 0 := by
  subst hN
  have hidx : ∀ j (hj : j < R.length), indexOf? R R[j] = some (0 + j) := by
    intro j hj
    simp only [Nat.zero_add]
    exact indexOf?_getElem hn j hj
  exact sum_rec_eq R R 0 amt R.length hidx

theorem sum_shares_eq (s : State) (req : Request) (hv : ValidPayout s req) :
    sumOver s.accounts (fun a => (shareOf req a : Int)) = (req.amount : Int) := by
  have hnR := valid_rec_nodup hv
  have hnS := valid_nodup_acc hv
  have hsub := valid_rec_mem hv
  have hne : req.recipients ≠ [] := valid_ne_nil hv
  have hzero : ∀ x ∈ s.accounts, x ∉ req.recipients → (shareOf req x : Int) = 0 := by
    intro x _ hx
    rw [shareOf_eq_zero_of_not_mem hx]
    rfl
  have hsup := superset_sum_aux s.accounts req.recipients (fun a => (shareOf req a : Int)) hnS hnR hsub hzero
  rw [hsup]
  have hcongr : sumOver req.recipients (fun a => (shareOf req a : Int)) =
      sumOver req.recipients (fun a => match indexOf? req.recipients a with | some i => (fairShare req.amount req.recipients.length i : Int) | none => 0) := by
    apply sumOver_congr
    intro a _
    unfold shareOf
    cases indexOf? req.recipients a with
    | none => rfl
    | some i => rfl
  rw [hcongr]
  have hrec := sumOver_recips_eq req.recipients hnR req.amount req.recipients.length rfl
  rw [hrec]
  have hpos : 0 < req.recipients.length := by
    cases h : req.recipients with
    | nil => exact absurd h hne
    | cons _ _ => simp
  exact recSum_full req.amount req.recipients.length (by omega)

theorem total_next_eq (s : State) (req : Request) (hv : ValidPayout s req) :
    total (nextState s req) = total s := by
  have hnS := valid_nodup_acc hv
  have hsrc := valid_src_mem hv
  have hcongr : sumOver (nextState s req).accounts (fun a => (nextState s req).balance a) =
      sumOver s.accounts (fun a => s.balance a - (if a = req.source then (req.amount : Int) else 0) + (shareOf req a : Int)) := by
    have hacc : (nextState s req).accounts = s.accounts := rfl
    rw [hacc]
    apply sumOver_congr
    intro a _
    have hbal : (nextState s req).balance a = expectedBalance s req a := rfl
    rw [hbal]
    unfold expectedBalance
    rfl
  have htotal1 : total (nextState s req) = sumOver (nextState s req).accounts (fun a => (nextState s req).balance a) := rfl
  have htotal2 : total s = sumOver s.accounts s.balance := rfl
  rw [htotal1, htotal2, hcongr]
  have hsplit1 : sumOver s.accounts (fun a => s.balance a - (if a = req.source then (req.amount : Int) else 0) + (shareOf req a : Int))
      = sumOver s.accounts (fun a => s.balance a - (if a = req.source then (req.amount : Int) else 0)) + sumOver s.accounts (fun a => (shareOf req a : Int)) := by
    rw [← sumOver_add]
    apply sumOver_congr
    intro a _
    rfl
  rw [hsplit1]
  have hsplit2 : sumOver s.accounts (fun a => s.balance a - (if a = req.source then (req.amount : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = req.source then (req.amount : Int) else 0) := by
    rw [← sumOver_sub]
    apply sumOver_congr
    intro a _
    rfl
  rw [hsplit2]
  have hsrc_sum : sumOver s.accounts (fun a => if a = req.source then (req.amount : Int) else 0) = (req.amount : Int) := by
    have h := sumOver_ite_eq hnS req.source (req.amount : Int)
    rw [h]
    simp [hsrc]
  have hshare := sum_shares_eq s req hv
  rw [hshare, hsrc_sum]
  omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have heq := step_eq_ok_of_valid h
  rw [heq]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  exact step_eq_reject_of_invalid h

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  have hv := ok_imp_valid hok
  have h2 := second_eq_next_of_ok hok
  have hnR := valid_rec_nodup hv
  have hsrc_notin := valid_src_notin hv
  have hshare := shareOf_mem_eq hnR i hi
  have hne : r.recipients[i] ≠ r.source := getElem_ne_source hsrc_notin i hi
  have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
    rw [h2]
    rfl
  rw [hbal]
  unfold expectedBalance
  have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by
    simp [hne]
  rw [hif]
  have hshareI : ((shareOf r r.recipients[i] : Nat) : Int) = ((fairShare r.amount r.recipients.length i : Nat) : Int) := by
    rw [hshare]
  omega

theorem req_effects : Effects step := by
  intro s r hok
  have h2 := second_eq_next_of_ok hok
  exact ⟨by rw [h2], by rw [h2], by intro a; rw [h2]⟩

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv := ok_imp_valid hok
  have h2 := second_eq_next_of_ok hok
  show total (step s r).2 = total s
  rw [h2]
  exact total_next_eq s r hv

theorem req_nonnegative : NonNegative step := by
  intro s r hnonneg a ha
  by_cases hv : ValidPayout s r
  · have hfst : (step s r).1 = Outcome.ok := by
      have heq := step_eq_ok_of_valid hv
      rw [heq]
    have h2nd : (step s r).2 = nextState s r := second_eq_next_of_ok hfst
    have ha' : a ∈ (nextState s r).accounts := by rw [← h2nd]; exact ha
    have hmem : a ∈ s.accounts := ha'
    have hbal1 : (step s r).2.balance a = expectedBalance s r a := by
      rw [h2nd]
      rfl
    rw [hbal1]
    unfold expectedBalance
    by_cases heq : a = r.source
    · subst heq
      have hsrc_notin := valid_src_notin hv
      have hshare0 : shareOf r r.source = 0 := shareOf_eq_zero_of_not_mem hsrc_notin
      simp only [if_true, hshare0]
      have hle := valid_bal hv
      have h0 := hnonneg r.source hmem
      simp
      omega
    · simp only [heq, if_false]
      have h0 := hnonneg a hmem
      have hpos : (0 : Int) ≤ ((shareOf r a : Nat) : Int) := by omega
      omega
  · have h2 := step_eq_reject_of_invalid hv
    have ha_s : a ∈ s.accounts := by
      have h2' : (step s r).2 = s := by rw [h2]
      rw [h2'] at ha
      simpa using ha
    have hbal_eq : (step s r).2.balance a = s.balance a := by rw [h2]
    rw [hbal_eq]
    exact hnonneg a ha_s

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  exact valid_auth (ok_imp_valid hok)

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have h2 : (step s r).2 = nextState s r := second_eq_next_of_ok hok
  constructor
  · intro x
    have happ : (step s r).2.applied = r.txId :: s.applied := by
      rw [h2]
      rfl
    rw [happ]
    simp
  · have hmem : r.txId ∈ (nextState s r).applied := by simp [nextState]
    have hnvalid : ¬ ValidPayout (nextState s r) r := by
      intro hcon
      exact (valid_txid hcon) hmem
    have hstep : step (nextState s r) r = (.rejected, nextState s r) :=
      step_eq_reject_of_invalid hnvalid
    rw [h2]
    exact hstep

end Payout
