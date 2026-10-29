import WeightedPayout.Spec
import WeightedPayout.Lemmas
namespace WeightedPayout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout
  infer_instance

theorem floor_mul_le {amount W w : Nat} : floorShare amount W w * W ≤ amount * w := by
  unfold floorShare
  have h := Nat.div_add_mod (amount * w) W
  omega

theorem lt_floor_succ_mul {amount W w : Nat} (hW : 0 < W) :
    amount * w < (floorShare amount W w + 1) * W := by
  unfold floorShare
  have hdm := Nat.div_add_mod (amount * w) W
  have hmod : amount * w % W < W := Nat.mod_lt (amount * w) hW
  have hdist : (amount * w / W + 1) * W = amount * w / W * W + W := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

theorem sum_floor_rem_eq (amount W0 : Nat) (ws' : List Nat) :
    natSum (ws'.map (fun w => amount * w / W0)) * W0
      + natSum (ws'.map (fun w => (amount * w) % W0))
      = amount * natSum ws' := by
  induction ws' with
  | nil => simp [natSum]
  | cons w ws ih =>
    simp only [List.map_cons, natSum]
    have hdm := Nat.div_add_mod (amount * w) W0
    have h1 : (amount * w / W0 + natSum (List.map (fun w => amount * w / W0) ws)) * W0
        = amount * w / W0 * W0 + natSum (List.map (fun w => amount * w / W0) ws) * W0 := by
      rw [Nat.add_mul]
    have h2 : amount * (w + natSum ws) = amount * w + amount * natSum ws := by
      rw [Nat.mul_add]
    omega

theorem rem_sum_le (amount W0 : Nat) (hW : 0 < W0) (ws' : List Nat) :
    natSum (ws'.map (fun w => (amount * w) % W0)) ≤ ws'.length * W0 := by
  induction ws' with
  | nil => simp [natSum]
  | cons w ws ih =>
    simp only [List.map_cons, natSum, List.length_cons]
    have hlt : amount * w % W0 < W0 := Nat.mod_lt (amount * w) hW
    have hdist : (ws.length + 1) * W0 = ws.length * W0 + W0 := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

theorem cancel_le : ∀ (a b W : Nat), a * W ≤ b * W → 0 < W → a ≤ b := by
  intro a
  induction a with
  | zero => intro b W _ _; exact Nat.zero_le b
  | succ a ih =>
    intro b W h hW
    cases b with
    | zero =>
      have h1 : Nat.succ a * W = a * W + W := Nat.succ_mul a W
      have h0 : (0 : Nat) * W = 0 := Nat.zero_mul W
      omega
    | succ b =>
      have h1 : Nat.succ a * W = a * W + W := Nat.succ_mul a W
      have h2 : Nat.succ b * W = b * W + W := Nat.succ_mul b W
      omega

def cntAux : Nat → List Nat → Nat → Nat
  | _, [], _ => 0
  | k, _ :: ws, L => (if k < L then 1 else 0) + cntAux (k + 1) ws L

theorem cntAux_zero_of_ge : ∀ (k : Nat) (ws : List Nat) (L : Nat), L ≤ k →
    cntAux k ws L = 0 := by
  intro k ws L h
  induction ws generalizing k with
  | nil => simp [cntAux]
  | cons _ ws ih =>
    simp only [cntAux]
    have h1 : ¬ (k < L) := by omega
    simp [h1, ih (k + 1) (by omega)]

theorem cntAux_eq_sub : ∀ (k : Nat) (ws : List Nat) (L : Nat), k ≤ L → L ≤ k + ws.length →
    cntAux k ws L = L - k := by
  intro k ws
  induction ws generalizing k with
  | nil =>
    intro L h1 h2
    simp [cntAux]
    omega
  | cons _ ws ih =>
    intro L h1 h2
    simp only [cntAux, List.length_cons] at h2 ⊢
    by_cases hk : k < L
    · simp only [hk, if_true]
      have h1' : k + 1 ≤ L := by omega
      have h2' : L ≤ (k + 1) + ws.length := by omega
      have ihr := ih (k + 1) L h1' h2'
      omega
    · simp only [hk, if_false]
      have hke : k = L := by omega
      subst hke
      have hz := cntAux_zero_of_ge k ws k (by omega)
      omega

theorem cntAux_zero_len (ws : List Nat) (L : Nat) (h : L ≤ ws.length) :
    cntAux 0 ws L = L := by
  have h1 : (0 : Nat) ≤ L := Nat.zero_le L
  have h2 : L ≤ 0 + ws.length := by simpa using h
  have hr := cntAux_eq_sub 0 ws L h1 h2
  simpa using hr

def shareAux (amount W L k : Nat) (ws : List Nat) (rs : List AccountId)
    (a : AccountId) : Nat :=
  match indexOf? rs a with
  | some i => floorShare amount W (ws.getD i 0) + (if k + i < L then 1 else 0)
  | none => 0

theorem shareAux_zero_eq_shareOf (r : Request) (a : AccountId)
    (W L : Nat) (hW : W = natSum r.weights) (hL : L = leftover r.amount r.weights) :
    shareAux r.amount W L 0 r.weights r.recipients a = shareOf r a := by
  unfold shareAux shareOf weightedShare
  rw [hW, hL]
  cases h : indexOf? r.recipients a with
  | none => rfl
  | some i =>
    simp only
    have hz : (0 : Nat) + i = i := Nat.zero_add i
    rw [hz]

theorem indexOf_cons_ne {x a : Nat} {xs : List Nat} (hne : x ≠ a) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  simp [indexOf?, hne]

theorem sum_acc_aux_n (acc : List Nat) (amount W L : Nat) (hacc : acc.Nodup) :
    ∀ (n : Nat) (k : Nat) (ws : List Nat) (rs : List Nat),
      ws.length = n → rs.length = n → rs.Nodup → (∀ x ∈ rs, x ∈ acc) →
      sumOver acc (fun a => ((shareAux amount W L k ws rs a : Nat) : Int))
        = (natSum (ws.map (fun w => amount * w / W)) : Int) + (cntAux k ws L : Int) := by
  intro n
  induction n with
  | zero =>
    intro k ws rs hws hrs hrsnodup hsub
    have hwsnil : ws = [] := List.length_eq_zero_iff.mp hws
    have hrsnil : rs = [] := List.length_eq_zero_iff.mp hrs
    subst hwsnil
    subst hrsnil
    have hzero : ∀ a ∈ acc, ((shareAux amount W L k [] [] a : Nat) : Int) = 0 := by
      intro a _
      unfold shareAux
      simp [indexOf?]
    have h1 : sumOver acc (fun a => ((shareAux amount W L k [] [] a : Nat) : Int))
        = sumOver acc (fun _ => (0 : Int)) := by
      apply sumOver_congr
      intro a ha
      simp [hzero a ha]
    have h2 : sumOver acc (fun _ => (0 : Int)) = 0 := by
      induction acc with
      | nil => rfl
      | cons x xs ih2 => simp [sumOver_cons, ih2]
    rw [h1, h2]
    simp [natSum, cntAux]
  | succ n ih =>
    intro k ws rs hws hrs hrsnodup hsub
    cases ws with
    | nil => simp at hws
    | cons w ws' =>
      cases rs with
      | nil => simp at hrs
      | cons r rs' =>
        simp only [List.length_cons] at hws hrs
        have hws' : ws'.length = n := by omega
        have hrs' : rs'.length = n := by omega
        rw [List.nodup_cons] at hrsnodup
        obtain ⟨hrnot, hrsnodup'⟩ := hrsnodup
        have hsub' : ∀ x ∈ rs', x ∈ acc := fun x hx => hsub x (by simp [hx])
        have hmemr : r ∈ acc := hsub r (by simp)
        have hnot : r ∉ rs' := hrnot
        have htail_zero : shareAux amount W L (k + 1) ws' rs' r = 0 := by
          unfold shareAux
          rw [indexOf?_eq_none hnot]
          rfl
        have hhead : shareAux amount W L k (w :: ws') (r :: rs') r
            = amount * w / W + (if k < L then 1 else 0) := by
          unfold shareAux floorShare
          simp [indexOf?]
        have htail_eq : ∀ a, a ≠ r → shareAux amount W L k (w :: ws') (r :: rs') a
            = shareAux amount W L (k + 1) ws' rs' a := by
          intro a hne
          have hner : r ≠ a := fun h => hne h.symm
          have hidx : indexOf? (r :: rs') a = (indexOf? rs' a).map (· + 1) :=
            indexOf_cons_ne hner
          cases h : indexOf? rs' a with
          | none =>
            have hidxnone : indexOf? (r :: rs') a = none := by
              rw [hidx, h]; rfl
            have e1 : shareAux amount W L k (w :: ws') (r :: rs') a = 0 := by
              unfold shareAux; rw [hidxnone]; rfl
            have e2 : shareAux amount W L (k + 1) ws' rs' a = 0 := by
              unfold shareAux; rw [h]; rfl
            rw [e1, e2]
          | some i =>
            have hidxsome : indexOf? (r :: rs') a = some (i + 1) := by
              rw [hidx, h]; rfl
            have e1 : shareAux amount W L k (w :: ws') (r :: rs') a
                = floorShare amount W ((w :: ws').getD (i + 1) 0) + (if k + (i + 1) < L then 1 else 0) := by
              unfold shareAux; rw [hidxsome]
            have e2 : shareAux amount W L (k + 1) ws' rs' a
                = floorShare amount W (ws'.getD i 0) + (if (k + 1) + i < L then 1 else 0) := by
              unfold shareAux; rw [h]
            rw [e1, e2]
            have hget : (w :: ws').getD (i + 1) 0 = ws'.getD i 0 := by simp
            rw [hget]
            have heq : k + (i + 1) = (k + 1) + i := by omega
            rw [heq]
        have hfun : ∀ a, ((shareAux amount W L k (w :: ws') (r :: rs') a : Nat) : Int)
            = ((shareAux amount W L (k + 1) ws' rs' a : Nat) : Int)
              + (if a = r then (((amount * w / W + (if k < L then 1 else 0) : Nat)) : Int) else 0) := by
          intro a
          by_cases heq : a = r
          · subst heq
            rw [hhead, htail_zero]
            simp
          · have he := htail_eq a heq
            rw [he]
            simp [heq]
        have hsum1 : sumOver acc (fun a => ((shareAux amount W L k (w :: ws') (r :: rs') a : Nat) : Int))
            = sumOver acc (fun a => ((shareAux amount W L (k + 1) ws' rs' a : Nat) : Int)
              + (if a = r then (((amount * w / W + (if k < L then 1 else 0) : Nat)) : Int) else 0)) := by
          apply sumOver_congr
          intro a ha
          exact hfun a
        rw [hsum1, sumOver_add]
        have hIH := ih (k + 1) ws' rs' hws' hrs' hrsnodup' hsub'
        rw [hIH]
        have hite : sumOver acc (fun a => (if a = r then (((amount * w / W + (if k < L then 1 else 0) : Nat)) : Int) else 0))
            = (((amount * w / W + (if k < L then 1 else 0) : Nat)) : Int) := by
          have h := sumOver_ite_eq hacc r ((((amount * w / W + (if k < L then 1 else 0) : Nat)) : Int))
          rw [h]
          simp [hmemr]
        rw [hite]
        have hS : natSum ((w :: ws').map (fun w => amount * w / W))
            = amount * w / W + natSum (ws'.map (fun w => amount * w / W)) := by
          simp [natSum]
        have hc : cntAux k (w :: ws') L = (if k < L then 1 else 0) + cntAux (k + 1) ws' L := rfl
        omega

theorem sum_acc_aux (acc : List Nat) (rs : List Nat) (ws : List Nat)
    (amount W L k : Nat)
    (hacc : acc.Nodup) (hrs : rs.Nodup) (hlen : ws.length = rs.length)
    (hsub : ∀ x ∈ rs, x ∈ acc) :
    sumOver acc (fun a => ((shareAux amount W L k ws rs a : Nat) : Int))
      = (natSum (ws.map (fun w => amount * w / W)) : Int) + (cntAux k ws L : Int) := by
  have h := sum_acc_aux_n acc amount W L hacc ws.length k ws rs rfl (by omega) hrs hsub
  exact h

theorem natSum_pos_of_mem2 {ws : List Nat} (hpos : ∀ w ∈ ws, 0 < w) (hne : ws ≠ []) :
    0 < natSum ws := by
  cases ws with
  | nil => simp at hne
  | cons w ws =>
    simp only [natSum]
    have hw : 0 < w := hpos w (by simp)
    omega

-- linear cast helper proved in isolation so omega never sees nonlinear hyps
theorem cast_add_eq_of_nat_eq (a b c : Nat) (h : a + b = c) :
    (a : Int) + (b : Int) = (c : Int) := by omega

theorem sumShares_eq_amount {s : State} {r : Request} (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) = (r.amount : Int) := by
  obtain ⟨hnd_acc, hpos, hne, hlen, hposW, hnd_rec, hnsrc, hsrcAcc, hrecAcc, hauth, hle, htx⟩ := hv
  have hwsne : r.weights ≠ [] := by
    intro hc
    have hlen0 : r.weights.length = 0 := by rw [hc]; simp
    rw [hlen] at hlen0
    have hrecnil : r.recipients = [] := List.length_eq_zero_iff.mp hlen0
    exact hne hrecnil
  have hWpos : 0 < natSum r.weights := natSum_pos_of_mem2 hposW hwsne
  let W := natSum r.weights
  let F := natSum (r.weights.map (fun w => r.amount * w / W))
  let R := natSum (r.weights.map (fun w => (r.amount * w) % W))
  let Ln := r.amount - F
  have hsum : F * W + R = r.amount * W := sum_floor_rem_eq r.amount W r.weights
  have hRW : R ≤ r.weights.length * W := rem_sum_le r.amount W hWpos r.weights
  have hSle : F ≤ r.amount := by
    apply cancel_le _ _ W _ hWpos
    omega
  have hSL : F + Ln = r.amount := by omega
  have hLdef : Ln = leftover r.amount r.weights := by
    unfold leftover Ln F W
    rfl
  have hmul : (Ln + F) * W = r.amount * W := by
    have hAdd : Ln + F = r.amount := by omega
    rw [hAdd]
  have hmul2 : Ln * W + F * W = r.amount * W := by
    have h1 : (Ln + F) * W = Ln * W + F * W := Nat.add_mul Ln F W
    omega
  have hLW : Ln * W = R := by omega
  have hLleW : Ln * W ≤ r.weights.length * W := by omega
  have hLle : Ln ≤ r.weights.length := cancel_le _ _ _ hLleW hWpos
  have hllen : Ln ≤ r.recipients.length := by omega
  have hcnt : cntAux 0 r.weights Ln = Ln := cntAux_zero_len r.weights _ (by omega)
  have hsumacc := sum_acc_aux s.accounts r.recipients r.weights r.amount
    W Ln 0 hnd_acc hnd_rec hlen hrecAcc
  have hconn : ∀ a ∈ s.accounts,
      ((shareAux r.amount W Ln 0 r.weights r.recipients a : Nat) : Int)
      = ((shareOf r a : Nat) : Int) := by
    intro a _
    have he := shareAux_zero_eq_shareOf r a W Ln rfl hLdef.symm
    rw [he]
  have hcongr2 : sumOver s.accounts (fun a => ((shareAux r.amount W Ln 0 r.weights r.recipients a : Nat) : Int))
      = sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by
    apply sumOver_congr
    intro a ha
    exact hconn a ha
  rw [hcongr2] at hsumacc
  rw [hcnt] at hsumacc
  have hcast := cast_add_eq_of_nat_eq F Ln r.amount hSL
  omega

def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, ⟨s.accounts, fun a => expectedBalance s r a, s.auth, r.txId :: s.applied⟩)
  else (.rejected, s)

theorem step_ok_of_valid {s : State} {r : Request} (h : ValidPayout s r) :
    step s r = (.ok, ⟨s.accounts, fun a => expectedBalance s r a, s.auth, r.txId :: s.applied⟩) := by
  unfold step
  simp [h]

theorem step_rejected_of_invalid {s : State} {r : Request} (h : ¬ ValidPayout s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [h]

theorem ok_imp_valid {s : State} {r : Request} (h : (step s r).1 = .ok) :
    ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · have h2 := step_rejected_of_invalid hv
    rw [h2] at h
    contradiction

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  rw [step_ok_of_valid h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  exact step_rejected_of_invalid h

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  have hv := ok_imp_valid h
  obtain ⟨_, _, _, _, _, _, _, _, _, hauth, _, _⟩ := hv
  exact hauth

theorem req_effects : Effects step := by
  intro s r h
  have hv := ok_imp_valid h
  have hst := step_ok_of_valid hv
  have hacc : (step s r).2.accounts = s.accounts := by rw [hst]
  have hauth : (step s r).2.auth = s.auth := by rw [hst]
  have hbal : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
    intro a
    rw [hst]
  exact ⟨hacc, hauth, hbal⟩

theorem req_idempotency : Idempotent step := by
  intro s r h
  have hv := ok_imp_valid h
  have hst := step_ok_of_valid hv
  have hmem : r.txId ∈ (r.txId :: s.applied) := by simp
  have hnvalid : ¬ ValidPayout ⟨s.accounts, fun a => expectedBalance s r a, s.auth, r.txId :: s.applied⟩ r := by
    intro hc
    exact hc.2.2.2.2.2.2.2.2.2.2.2 hmem
  have h2 : step ⟨s.accounts, fun a => expectedBalance s r a, s.auth, r.txId :: s.applied⟩ r
      = (.rejected, ⟨s.accounts, fun a => expectedBalance s r a, s.auth, r.txId :: s.applied⟩) :=
    step_rejected_of_invalid hnvalid
  have e2 : (step s r).2 = ⟨s.accounts, fun a => expectedBalance s r a, s.auth, r.txId :: s.applied⟩ := by
    rw [hst]
  have g1 : ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
    rw [e2]
    intro x
    simp
  have g2 : step (step s r).2 r = (.rejected, (step s r).2) := by
    rw [e2]
    rw [h2]
  exact ⟨g1, g2⟩

theorem shareOf_source_eq_zero {r : Request} (hs : r.source ∉ r.recipients) :
    shareOf r r.source = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none hs]

theorem shareOf_recip {r : Request} (hnd : r.recipients.Nodup)
    {i : Nat} (hi : i < r.recipients.length) :
    shareOf r r.recipients[i] = weightedShare r.amount r.weights i := by
  unfold shareOf
  rw [indexOf?_getElem hnd i hi]

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · obtain ⟨hnd_acc, hpos, hne, hlen, hposW, hnd_rec, hnsrc, hsrcAcc, hrecAcc, hauth, hle, htx⟩ := hv
    have hv2 : ValidPayout s r :=
      ⟨hnd_acc, hpos, hne, hlen, hposW, hnd_rec, hnsrc, hsrcAcc, hrecAcc, hauth, hle, htx⟩
    have hst := step_ok_of_valid hv2
    have ha2 : a ∈ (step s r).2.accounts := ha
    rw [hst] at ha2
    simp at ha2
    have hbal : (step s r).2.balance a = expectedBalance s r a := by rw [hst]
    rw [hbal]
    have h0 : 0 ≤ s.balance a := hnn a ha2
    unfold expectedBalance
    by_cases heq : a = r.source
    · subst heq
      simp only [if_true]
      have hsh0 : shareOf r r.source = 0 := shareOf_source_eq_zero hnsrc
      rw [hsh0]
      simp
      omega
    · simp only [heq, if_false]
      omega
  · have hst := step_rejected_of_invalid hv
    have ha2 : a ∈ (step s r).2.accounts := ha
    rw [hst] at ha2 ⊢
    simp at ha2 ⊢
    exact hnn a ha2

theorem diff_eq_share {s : State} {r : Request} (hv : ValidPayout s r) (i : Nat)
    (hi : i < r.recipients.length) :
    expectedBalance s r r.recipients[i] - s.balance r.recipients[i]
      = (weightedShare r.amount r.weights i : Int) := by
  obtain ⟨_, _, _, _, _, hnd_rec, hnsrc, _, _, _, _, _⟩ := hv
  have hne : r.recipients[i] ≠ r.source := by
    intro hc
    exact hnsrc (hc ▸ List.getElem_mem hi)
  have hrw := shareOf_recip hnd_rec hi
  unfold expectedBalance
  simp only [hne, if_false]
  omega

-- helpers to move Nat mul/add through Int cast using only simp (simp set contains OfNat lemmas)
theorem cast_mul_helper (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by simp
theorem cast_add_helper (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp
theorem cast_nat_mul_eq (a b : Nat) : (a : Int) * (b : Int) = ((a * b : Nat) : Int) := by simp

theorem nat_le_to_int_le {a b : Nat} (h : a ≤ b) : (a : Int) ≤ (b : Int) := by omega
theorem nat_lt_to_int_lt {a b : Nat} (h : a < b) : (a : Int) < (b : Int) := by omega

theorem req_rounding_bound : RoundingBound step := by
  intro s r h i hi
  have hv := ok_imp_valid h
  have hst := step_ok_of_valid hv
  have heff : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
    rw [hst]
  have hdiff : (step s r).2.balance r.recipients[i] - s.balance r.recipients[i]
      = (weightedShare r.amount r.weights i : Int) := by
    rw [heff]
    exact diff_eq_share hv i hi
  rw [hdiff]
  have hlenW : r.weights.length = r.recipients.length := hv.2.2.2.1
  have hposW : ∀ w ∈ r.weights, 0 < w := hv.2.2.2.2.1
  have hne2 : r.recipients ≠ [] := hv.2.2.1
  have hwsne : r.weights ≠ [] := by
    intro hc
    have hlen0 : r.weights.length = 0 := by rw [hc]; simp
    rw [hlenW] at hlen0
    have hrecnil : r.recipients = [] := List.length_eq_zero_iff.mp hlen0
    exact hne2 hrecnil
  have hWpos : 0 < natSum r.weights := natSum_pos_of_mem2 hposW hwsne
  have h1 : floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights
      ≤ r.amount * r.weights.getD i 0 := floor_mul_le
  have h2 : r.amount * r.weights.getD i 0
      < (floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights :=
    lt_floor_succ_mul hWpos
  have hdist : (floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights
      = floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights + natSum r.weights := by
    rw [Nat.add_mul, Nat.one_mul]
  have hsplit : weightedShare r.amount r.weights i
      = floorShare r.amount (natSum r.weights) (r.weights.getD i 0)
        + (if i < leftover r.amount r.weights then 1 else 0) := rfl
  by_cases hb : i < leftover r.amount r.weights
  · have hws : weightedShare r.amount r.weights i
        = floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1 := by
      rw [hsplit, if_pos hb]
    rw [hws]
    have nle : (floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights
        ≤ r.amount * r.weights.getD i 0 + natSum r.weights := by
      rw [hdist]
      exact Nat.add_le_add_right h1 (natSum r.weights)
    have nlt : r.amount * r.weights.getD i 0
        < (floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights
          + natSum r.weights := by omega
    have hleI : ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights : Nat)) : Int)
        ≤ ((((r.amount * r.weights.getD i 0 + natSum r.weights : Nat))) : Int) :=
      nat_le_to_int_le nle
    have hltI : ((((r.amount * r.weights.getD i 0 : Nat))) : Int)
        < ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights : Nat))) : Int)
          + ((((natSum r.weights : Nat))) : Int) := by
      have h1' : ((((r.amount * r.weights.getD i 0 : Nat))) : Int)
          < ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights
            + natSum r.weights : Nat))) : Int) := nat_lt_to_int_lt nlt
      have heq : ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights
            + natSum r.weights : Nat))) : Int)
          = ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights : Nat))) : Int)
          + ((((natSum r.weights : Nat))) : Int) := cast_add_helper _ _
      rw [heq] at h1'
      exact h1'
    have eL : ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights : Nat)) : Int)
        = ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1 : Nat))) : Int)
          * ((((natSum r.weights : Nat))) : Int) := cast_mul_helper _ _
    have eR : ((((r.amount * r.weights.getD i 0 + natSum r.weights : Nat))) : Int)
        = ((((r.amount * r.weights.getD i 0 : Nat))) : Int) + ((((natSum r.weights : Nat))) : Int) :=
      cast_add_helper _ _
    have eQ : ((((r.amount * r.weights.getD i 0 : Nat))) : Int)
        = (r.amount : Int) * ((r.weights.getD i 0 : Nat) : Int) := cast_mul_helper _ _
    have eF : ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1 : Nat))) : Int)
        = ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) : Nat))) : Int) + 1 := by simp
    rw [eL, eR] at hleI
    rw [eQ] at hleI ⊢
    rw [eL] at hltI
    have hgoal1 : ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1 : Nat))) : Int)
          * ((((natSum r.weights : Nat))) : Int))
        ≤ (r.amount : Int) * ((r.weights.getD i 0 : Nat) : Int) + ((((natSum r.weights : Nat))) : Int) := hleI
    have hgoal2 : (r.amount : Int) * ((r.weights.getD i 0 : Nat) : Int)
        < ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1 : Nat))) : Int)
          * ((((natSum r.weights : Nat))) : Int) + ((((natSum r.weights : Nat))) : Int) := hltI
    exact ⟨hgoal1, hgoal2⟩
  · have hws : weightedShare r.amount r.weights i
        = floorShare r.amount (natSum r.weights) (r.weights.getD i 0) := by
      rw [hsplit, if_neg hb, Nat.add_zero]
    rw [hws]
    have nle : floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights
        ≤ r.amount * r.weights.getD i 0 + natSum r.weights :=
      Nat.le_trans h1 (Nat.le_add_right _ _)
    have nlt : r.amount * r.weights.getD i 0
        < floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights
          + natSum r.weights := by
      rw [← hdist]
      exact h2
    have hleI : ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights : Nat))) : Int)
        ≤ ((((r.amount * r.weights.getD i 0 + natSum r.weights : Nat))) : Int) :=
      nat_le_to_int_le nle
    have hltI : ((((r.amount * r.weights.getD i 0 : Nat))) : Int)
        < ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights : Nat))) : Int)
          + ((((natSum r.weights : Nat))) : Int) := by
      have h1' : ((((r.amount * r.weights.getD i 0 : Nat))) : Int)
          < ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights
            + natSum r.weights : Nat))) : Int) := nat_lt_to_int_lt nlt
      have heq : ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights
            + natSum r.weights : Nat))) : Int)
          = ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights : Nat))) : Int)
          + ((((natSum r.weights : Nat))) : Int) := cast_add_helper _ _
      rw [heq] at h1'
      exact h1'
    have eL : ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights : Nat)) : Int)
        = ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) : Nat))) : Int)
          * ((((natSum r.weights : Nat))) : Int) := cast_mul_helper _ _
    have eR : ((((r.amount * r.weights.getD i 0 + natSum r.weights : Nat))) : Int)
        = ((((r.amount * r.weights.getD i 0 : Nat))) : Int) + ((((natSum r.weights : Nat))) : Int) :=
      cast_add_helper _ _
    have eQ : ((((r.amount * r.weights.getD i 0 : Nat))) : Int)
        = (r.amount : Int) * ((r.weights.getD i 0 : Nat) : Int) := cast_mul_helper _ _
    rw [eL, eR] at hleI
    rw [eQ] at hleI ⊢
    rw [eL] at hltI
    exact ⟨hleI, hltI⟩

theorem req_conservation : Conserves step := by
  intro s r h
  have hv : ValidPayout s r := ok_imp_valid h
  have hst := step_ok_of_valid hv
  have hnd_acc : s.accounts.Nodup := hv.1
  have hsrcAcc : r.source ∈ s.accounts := hv.2.2.2.2.2.2.2.1
  have htot : total ⟨s.accounts, fun a => expectedBalance s r a, s.auth, r.txId :: s.applied⟩ = total s := by
    unfold total
    have heq : ∀ a ∈ s.accounts, expectedBalance s r a
        = s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + ((shareOf r a : Nat) : Int) := by
      intro a _
      rfl
    have c1 : sumOver s.accounts (fun a => expectedBalance s r a)
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + ((shareOf r a : Nat) : Int)) := by
      apply sumOver_congr
      intro a ha
      exact congrArg id (heq a ha)
    rw [c1]
    have e1 : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + ((shareOf r a : Nat) : Int))
        = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0))
          + ((shareOf r a : Nat) : Int)) := rfl
    rw [e1, sumOver_add]
    have e2 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance
          - sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) := by
      exact sumOver_sub s.accounts s.balance _
    rw [e2]
    have hsrc : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0))
        = (r.amount : Int) := by
      have hh := sumOver_ite_eq hnd_acc r.source (r.amount : Int)
      rw [hh]
      simp [hsrcAcc]
    have hshares := sumShares_eq_amount hv
    omega
  have e2 : (step s r).2 = ⟨s.accounts, fun a => expectedBalance s r a, s.auth, r.txId :: s.applied⟩ := by
    rw [hst]
  rw [e2]
  exact htot

end WeightedPayout
