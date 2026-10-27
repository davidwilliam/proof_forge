import WeightedPayout.Spec
import WeightedPayout.Lemmas
/-!
# Reference solution A (build team; hidden from agents)

Loop implementation: debit the source, then walk recipients and weights together, paying\nthe floor share plus one extra cent while extra cents remain.
-/

namespace WeightedPayout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance

/-- Add `amt` (possibly negative) to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

/-- Sum of the floor shares `A * w / W` over a list of weights. -/
def floorTotal (A W : Nat) : List Nat → Nat
  | [] => 0
  | w :: ws => A * w / W + floorTotal A W ws

/-- Walk recipients and weights together, paying each its floor share plus one cent while
`extra` cents remain. -/
def payAll (A W : Nat) : Nat → List AccountId → List Nat → (AccountId → Int) → (AccountId → Int)
  | _, [], _, bal => bal
  | extra, x :: xs, ws, bal =>
      payAll A W (extra - 1) xs ws.tail
        (adjust bal x ((A * ws.headD 0 / W + if 0 < extra then 1 else 0 : Nat) : Int))

def newBalance (s : State) (r : Request) : AccountId → Int :=
  let W := natSum r.weights
  let extra := r.amount - floorTotal r.amount W r.weights
  payAll r.amount W extra r.recipients r.weights (adjust s.balance r.source (-(r.amount : Int)))

def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with balance := newBalance s r, applied := r.txId :: s.applied })
  else
    (.rejected, s)

theorem step_of_valid {s : State} {r : Request} (h : ValidPayout s r) :
    step s r = (.ok, { s with balance := newBalance s r, applied := r.txId :: s.applied }) := by
  simp [step, h]

theorem step_of_invalid {s : State} {r : Request} (h : ¬ ValidPayout s r) :
    step s r = (.rejected, s) := by
  simp [step, h]

theorem floorTotal_eq (A W : Nat) : ∀ ws : List Nat,
    floorTotal A W ws = natSum (ws.map (floorShare A W)) := by
  intro ws
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [floorTotal, natSum, floorShare, ih]

theorem headD_eq (ws : List Nat) : ws.headD 0 = ws.getD 0 0 := by
  cases ws <;> rfl

theorem tail_getD (ws : List Nat) (i : Nat) : ws.tail.getD i 0 = ws.getD (i + 1) 0 := by
  cases ws <;> simp

/-- What `payAll` adds to each account. -/
theorem payAll_eq (A W : Nat) : ∀ (xs : List AccountId) (extra : Nat) (ws : List Nat)
    (bal : AccountId → Int) (b : AccountId), xs.Nodup →
    payAll A W extra xs ws bal b
      = bal b + (match indexOf? xs b with
                 | some i => ((A * ws.getD i 0 / W + if i < extra then 1 else 0 : Nat) : Int)
                 | none => 0) := by
  intro xs
  induction xs with
  | nil => intro extra ws bal b _; simp [payAll, indexOf?]
  | cons x xs ih =>
    intro extra ws bal b hnd
    rw [List.nodup_cons] at hnd
    simp only [payAll]
    rw [ih (extra - 1) ws.tail _ b hnd.2]
    by_cases hxb : x = b
    · subst hxb
      rw [headD_eq]
      simp [adjust, indexOf?, indexOf?_eq_none hnd.1]
    · have hbx : b ≠ x := fun h => hxb h.symm
      simp only [adjust, hbx, ite_false, indexOf?, hxb]
      cases indexOf? xs b with
      | none => simp
      | some i =>
        simp only [Option.map_some, tail_getD]
        by_cases hi : i + 1 < extra
        · have : i < extra - 1 := by omega
          simp [hi, this]
        · have : ¬ i < extra - 1 := by omega
          simp [hi, this]

theorem balance_eq {s : State} {r : Request} (hv : ValidPayout s r) (a : AccountId) :
    (step s r).2.balance a = expectedBalance s r a := by
  have hnd := hv.2.2.2.2.2.1
  rw [step_of_valid hv]
  show newBalance s r a = _
  unfold newBalance
  rw [payAll_eq _ _ _ _ _ _ _ hnd, floorTotal_eq]
  unfold expectedBalance shareOf weightedShare leftover floorShare adjust
  by_cases has : a = r.source
  · subst has
    rw [indexOf?_eq_none hv.2.2.2.2.2.2.1]
    simp; omega
  · generalize indexOf? r.recipients a = o
    cases o <;> simp [has]

/-! ## Arithmetic of weighted shares -/

/-- Sum of `F 0 + ... + F (n-1)`, recursing on the first index. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, F => F 0 + sumRange n (fun i => F (i + 1))

theorem sumRange_add : ∀ (n : Nat) (F G : Nat → Int),
    sumRange n (fun i => F i + G i) = sumRange n F + sumRange n G := by
  intro n
  induction n with
  | zero => intro F G; simp [sumRange]
  | succ n ih =>
    intro F G
    simp only [sumRange]
    rw [ih (fun i => F (i + 1)) (fun i => G (i + 1))]
    omega

theorem sumRange_ind : ∀ (n k : Nat),
    sumRange n (fun i => if i < k then (1 : Int) else 0) = ((min k n : Nat) : Int) := by
  intro n
  induction n with
  | zero => intro k; simp [sumRange]
  | succ n ih =>
    intro k
    simp only [sumRange]
    have hshift : (fun i => if i + 1 < k then (1 : Int) else 0)
        = (fun i => if i < k - 1 then (1 : Int) else 0) := by
      funext i
      by_cases hk : i + 1 < k
      · have : i < k - 1 := by omega
        simp [hk, this]
      · have : ¬ i < k - 1 := by omega
        simp [hk, this]
    rw [hshift, ih (k - 1)]
    by_cases hk : 0 < k
    · simp only [hk, ite_true]; omega
    · simp only [hk, ite_false]; omega

theorem sumRange_getD (f : Nat → Nat) : ∀ l : List Nat,
    sumRange l.length (fun i => (f (l.getD i 0) : Int)) = (natSum (l.map f) : Int) := by
  intro l
  induction l with
  | nil => simp [sumRange, natSum]
  | cons x xs ih =>
    simp only [List.length_cons, sumRange, List.map_cons, natSum, List.getD_cons_zero,
      List.getD_cons_succ]
    rw [ih]; push_cast; rfl

theorem natSum_pos : ∀ ws : List Nat, 0 < ws.length → (∀ w ∈ ws, 0 < w) → 0 < natSum ws := by
  intro ws hl hp
  cases ws with
  | nil => simp at hl
  | cons x xs =>
    have := hp x (by simp)
    simp only [natSum]; omega

theorem floor_sum_mul_le (A W : Nat) : ∀ ws : List Nat,
    natSum (ws.map (floorShare A W)) * W ≤ A * natSum ws := by
  intro ws
  induction ws with
  | nil => simp [natSum]
  | cons x xs ih =>
    simp only [List.map_cons, natSum]
    have h1 : floorShare A W x * W ≤ A * x := Nat.div_mul_le_self _ _
    rw [Nat.add_mul, Nat.mul_add]
    omega

theorem floor_sum_lower (A W : Nat) (hW : 0 < W) : ∀ ws : List Nat,
    A * natSum ws + ws.length ≤ (natSum (ws.map (floorShare A W)) + ws.length) * W := by
  intro ws
  induction ws with
  | nil => simp [natSum]
  | cons x xs ih =>
    simp only [List.map_cons, natSum, List.length_cons]
    have h1 : floorShare A W x * W + A * x % W = A * x := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have h2 := Nat.mod_lt (A * x) hW
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul] at ih ⊢
    omega

theorem leftover_lt (A : Nat) (ws : List Nat) (hl : 0 < ws.length) (hp : ∀ w ∈ ws, 0 < w) :
    natSum (ws.map (floorShare A (natSum ws))) ≤ A ∧ leftover A ws < ws.length := by
  have hW := natSum_pos ws hl hp
  have h1 := floor_sum_mul_le A (natSum ws) ws
  have h2 := floor_sum_lower A (natSum ws) hW ws
  have hle : natSum (ws.map (floorShare A (natSum ws))) ≤ A := by
    exact Nat.le_of_mul_le_mul_right h1 hW
  have hlt : A < natSum (ws.map (floorShare A (natSum ws))) + ws.length := by
    have : A * natSum ws < (natSum (ws.map (floorShare A (natSum ws))) + ws.length) * natSum ws := by
      omega
    exact Nat.lt_of_mul_lt_mul_right this
  unfold leftover
  omega

theorem sum_weighted (A : Nat) (ws : List Nat) (hl : 0 < ws.length) (hp : ∀ w ∈ ws, 0 < w) :
    sumRange ws.length (fun i => (weightedShare A ws i : Int)) = A := by
  have hsplit : (fun i => (weightedShare A ws i : Int))
      = (fun i => (floorShare A (natSum ws) (ws.getD i 0) : Int)
          + (if i < leftover A ws then (1 : Int) else 0)) := by
    funext i
    unfold weightedShare
    split <;> simp
  rw [hsplit, sumRange_add, sumRange_getD (floorShare A (natSum ws)), sumRange_ind]
  obtain ⟨hle, hlt⟩ := leftover_lt A ws hl hp
  rw [Nat.min_eq_left (Nat.le_of_lt hlt)]
  unfold leftover
  omega

/-- Summing an index-keyed share over a superset of a duplicate-free list. -/
theorem sumOver_indexed (L : List Nat) (hL : L.Nodup) : ∀ (R : List Nat) (F : Nat → Int),
    R.Nodup → (∀ x ∈ R, x ∈ L) →
    sumOver L (fun a => match indexOf? R a with | some i => F i | none => 0)
      = sumRange R.length F := by
  intro R
  induction R with
  | nil =>
    intro F _ _
    have : ∀ l : List Nat, sumOver l (fun a => match indexOf? ([] : List Nat) a with
        | some i => F i | none => 0) = 0 := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih => rw [sumOver_cons, ih]; simp [indexOf?]
    rw [this]; rfl
  | cons x xs ih =>
    intro F hR hsub
    rw [List.nodup_cons] at hR
    have hsplit : (fun a => match indexOf? (x :: xs) a with | some i => F i | none => 0)
        = (fun a => (if a = x then F 0 else 0)
            + (match indexOf? xs a with | some i => F (i + 1) | none => 0)) := by
      funext a
      by_cases hxa : x = a
      · subst hxa
        simp [indexOf?, indexOf?_eq_none hR.1]
      · have : a ≠ x := fun h => hxa h.symm
        simp only [indexOf?, hxa, this, ite_false]
        cases indexOf? xs a <;> simp
    rw [hsplit, sumOver_add, sumOver_ite_eq hL, ih (fun i => F (i + 1)) hR.2
      (fun y hy => hsub y (by simp [hy]))]
    have hxL : x ∈ L := hsub x (by simp)
    simp [hxL, sumRange]

/-- The shares of a valid request add up to the amount, summed over the whole universe. -/
theorem sum_shares (s : State) (r : Request) (h : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = r.amount := by
  obtain ⟨hacc, _, hne, hlen, hpos, hnd, _, _, hsub, _⟩ := h
  have hl : 0 < r.weights.length := by rw [hlen]; exact List.length_pos_iff.mpr hne
  have := sumOver_indexed s.accounts hacc r.recipients
    (fun i => (weightedShare r.amount r.weights i : Int)) hnd hsub
  rw [← hlen, sum_weighted r.amount r.weights hl hpos] at this
  rw [← this]
  apply sumOver_congr
  intro a _
  unfold shareOf
  cases indexOf? r.recipients a <;> simp

/-- Conservation follows from the specified balances on any valid request. -/
theorem total_expected (s : State) (r : Request) (h : ValidPayout s r) :
    sumOver s.accounts (expectedBalance s r) = total s := by
  have hacc := h.1
  have hsrc := h.2.2.2.2.2.2.2.1
  unfold expectedBalance total
  rw [sumOver_add (f := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)),
    sumOver_sub, sumOver_ite_eq hacc, sum_shares s r h]
  simp [hsrc]

/-- Nonnegativity of the specified balances. -/
theorem expected_nonneg (s : State) (r : Request) (h : ValidPayout s r) (a : AccountId)
    (h0 : 0 ≤ s.balance a) : 0 ≤ expectedBalance s r a := by
  have hbal := h.2.2.2.2.2.2.2.2.2.2.1
  unfold expectedBalance
  by_cases has : a = r.source
  · subst has; simp; omega
  · simp [has]; omega

/-- The specified balance change of the `i`-th recipient. -/
theorem expected_recipient (s : State) (r : Request) (h : ValidPayout s r) (i : Nat)
    (hi : i < r.recipients.length) :
    expectedBalance s r r.recipients[i] - s.balance r.recipients[i]
      = (weightedShare r.amount r.weights i : Int) := by
  have hnd := h.2.2.2.2.2.1
  have hsrc := h.2.2.2.2.2.2.1
  have hne : r.recipients[i] ≠ r.source := fun e => hsrc (e ▸ List.getElem_mem hi)
  simp [expectedBalance, hne, shareOf, indexOf?_getElem hnd i hi] <;> omega

theorem bound_nat (A W w e : Nat) (hW : 0 < W) (he : e ≤ 1) :
    (A * w / W + e) * W ≤ A * w + W ∧ A * w < (A * w / W + e) * W + W := by
  have h1 : A * w / W * W + A * w % W = A * w := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have h2 := Nat.mod_lt (A * w) hW
  have h3 : e * W ≤ W := by
    have := Nat.mul_le_mul_right W he
    rw [Nat.one_mul] at this; exact this
  rw [Nat.add_mul]
  constructor <;> omega

theorem weighted_bound (A : Nat) (ws : List Nat) (i : Nat) (hW : 0 < natSum ws) :
    (weightedShare A ws i : Int) * (natSum ws : Int) ≤ ((A * ws.getD i 0 : Nat) : Int) + (natSum ws : Int) ∧
    ((A * ws.getD i 0 : Nat) : Int) < (weightedShare A ws i : Int) * (natSum ws : Int) + (natSum ws : Int) := by
  have he : (if i < leftover A ws then 1 else 0) ≤ 1 := by split <;> omega
  have := bound_nat A (natSum ws) (ws.getD i 0) _ hW he
  unfold weightedShare floorShare
  exact_mod_cast this

/-! ## Requirements -/

theorem ok_valid {s : State} {r : Request} (h : (step s r).1 = .ok) : ValidPayout s r := by
  by_cases hv : ValidPayout s r
  · exact hv
  · rw [step_of_invalid hv] at h; cases h

theorem accounts_eq {s : State} {r : Request} (hv : ValidPayout s r) :
    (step s r).2.accounts = s.accounts := by
  rw [step_of_valid hv]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h; rw [step_of_valid h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h; exact step_of_invalid h

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  exact (ok_valid hok).2.2.2.2.2.2.2.2.2.1

theorem req_effects : Effects step := by
  intro s r hok
  have hv := ok_valid hok
  refine ⟨accounts_eq hv, ?_, balance_eq hv⟩
  rw [step_of_valid hv]

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv := ok_valid hok
  rw [step_of_valid hv]
  refine ⟨fun x => by simp, ?_⟩
  apply step_of_invalid
  intro h'
  exact h'.2.2.2.2.2.2.2.2.2.2.2 (by simp)

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · rw [accounts_eq hv] at ha
    rw [balance_eq hv]
    exact expected_nonneg s r hv a (hnn a ha)
  · rw [step_of_invalid hv] at ha ⊢
    exact hnn a ha

theorem req_pro_rata : ProRataShares step := by
  intro s r hok i hi
  have hv := ok_valid hok
  rw [balance_eq hv]
  exact expected_recipient s r hv i hi

theorem req_rounding_bound : RoundingBound step := by
  intro s r hok i hi
  have hv := ok_valid hok
  have ⟨_, _, hne, hlen, hpos, _⟩ := hv
  have hl : 0 < r.weights.length := by rw [hlen]; exact List.length_pos_iff.mpr hne
  rw [balance_eq hv, expected_recipient s r hv i hi]
  exact weighted_bound r.amount r.weights i (natSum_pos r.weights hl hpos)

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv := ok_valid hok
  unfold total
  rw [accounts_eq hv, sumOver_congr _ _ _ (fun a _ => balance_eq hv a)]
  exact total_expected s r hv

end WeightedPayout
