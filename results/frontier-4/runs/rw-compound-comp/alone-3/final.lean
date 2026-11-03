import CompRewards.Spec
namespace CompRewards

def supplyUpd (s : St) (a : Acct) : Acct :=
  { a with
    supplierIndex :=
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
    accrued := a.accrued + creditFor a.supply
      (accrualStart a.supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }

def borrowUpd (s : St) (a : Acct) : Acct :=
  { a with
    borrowerIndex :=
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
    accrued := a.accrued + creditFor a.borrow
      (accrualStart a.borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }

def doSupply (s : St) (who : Account) : Option St :=
  if s.supplyState.block ≤ s.blockNumber ∧
      accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index then
    some { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who (supplyUpd s) }
  else none

def doBorrow (s : St) (who : Account) : Option St :=
  if s.borrowState.block ≤ s.blockNumber ∧
      accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index then
    some { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who (borrowUpd s) }
  else none

def speedsResult (s : St) (sup bor : Nat) : St :=
  { s with
    supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
    borrowState := if s.borrowState.speed = bor then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } }

def speedsCond (s : St) (sup bor : Nat) : Prop :=
  (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber)

def doSpeeds (s : St) (sup bor : Nat) : Option St :=
  if (s.supplyState.speed = sup ∨ s.supplyState.block ≤ s.blockNumber) ∧
     (s.borrowState.speed = bor ∨ s.borrowState.block ≤ s.blockNumber) then
    some (speedsResult s sup bor)
  else none

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => doSupply s who
  | .borrowHook who => doBorrow s who
  | .claim who =>
    match doBorrow s who with
    | none => none
    | some m1 =>
      match doSupply m1 who with
      | none => none
      | some m2 => some (grant m2 who)
  | .setSpeeds a b => doSpeeds s a b

theorem accrue_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem accrue_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem accrualStart_le_of_le {r old idx : Nat} (h1 : r ≤ old) (h2 : old ≤ idx) :
    accrualStart r idx ≤ idx := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp [hr]
    by_cases hi : compInitialIndex ≤ idx
    · simp [hi]
    · simp [hi]
  · simp [hr]
    omega

theorem acct_eq_getElem (s : St) (who : Nat) (hm : who < s.accts.length) :
    s.acct who = s.accts[who]'hm := by
  unfold St.acct
  simp [hm]

theorem acct_eq_default (s : St) (who : Nat) (hm : ¬ who < s.accts.length) :
    s.acct who = noAcct := by
  unfold St.acct
  simp [hm]

theorem acct_supply_le_of_consistent (s : St) (hc : Consistent s) (who : Nat) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hmem⟩ := hc
  by_cases hm : who < s.accts.length
  · rw [acct_eq_getElem s who hm]
    exact (hmem _ (List.getElem_mem hm)).1
  · rw [acct_eq_default s who hm]
    unfold noAcct
    simp

theorem acct_borrow_le_of_consistent (s : St) (hc : Consistent s) (who : Nat) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hmem⟩ := hc
  by_cases hm : who < s.accts.length
  · rw [acct_eq_getElem s who hm]
    exact (hmem _ (List.getElem_mem hm)).2
  · rw [acct_eq_default s who hm]
    unfold noAcct
    simp

theorem supply_cond_of_consistent (s : St) (hc : Consistent s) (who : Nat) :
    s.supplyState.block ≤ s.blockNumber ∧
      accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  constructor
  · exact hc.1
  · apply accrualStart_le_of_le
    · exact acct_supply_le_of_consistent s hc who
    · exact accrue_ge _ _ _

theorem borrow_cond_of_consistent (s : St) (hc : Consistent s) (who : Nat) :
    s.borrowState.block ≤ s.blockNumber ∧
      accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  constructor
  · exact hc.2.1
  · apply accrualStart_le_of_le
    · exact acct_borrow_le_of_consistent s hc who
    · exact accrue_ge _ _ _

theorem speeds_or_of_consistent (s : St) (hc : Consistent s) (sup bor : Nat) :
    (s.supplyState.speed = sup ∨ s.supplyState.block ≤ s.blockNumber) ∧
    (s.borrowState.speed = bor ∨ s.borrowState.block ≤ s.blockNumber) := by
  unfold Consistent at hc
  obtain ⟨h1, h2, _⟩ := hc
  constructor
  · by_cases heq : s.supplyState.speed = sup
    · exact Or.inl heq
    · exact Or.inr h1
  · by_cases heq : s.borrowState.speed = bor
    · exact Or.inl heq
    · exact Or.inr h2

theorem speedsCond_of_or
    (h : (s.supplyState.speed = sup ∨ s.supplyState.block ≤ s.blockNumber) ∧
      (s.borrowState.speed = bor ∨ s.borrowState.block ≤ s.blockNumber)) :
    speedsCond s sup bor := by
  unfold speedsCond
  obtain ⟨hs, hb⟩ := h
  constructor
  · intro hne
    cases hs with
    | inl heq => exact absurd heq hne
    | inr hle => exact hle
  · intro hne
    cases hb with
    | inl heq => exact absurd heq hne
    | inr hle => exact hle

theorem or_of_speedsCond (h : speedsCond s sup bor) :
    (s.supplyState.speed = sup ∨ s.supplyState.block ≤ s.blockNumber) ∧
    (s.borrowState.speed = bor ∨ s.borrowState.block ≤ s.blockNumber) := by
  unfold speedsCond at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · by_cases heq : s.supplyState.speed = sup
    · exact Or.inl heq
    · exact Or.inr (h1 heq)
  · by_cases heq : s.borrowState.speed = bor
    · exact Or.inl heq
    · exact Or.inr (h2 heq)

-- Every element of a modified list satisfies P when old elements do and mapped ones do.
theorem all_modify (l : List Acct) (i : Nat) (f : Acct → Acct) (P : Acct → Prop)
    (h1 : ∀ b ∈ l, P b) (h2 : ∀ b ∈ l, P (f b)) :
    ∀ a ∈ l.modify i f, P a := by
  induction l generalizing i with
  | nil =>
    intro a ha
    simp at ha
  | cons x xs ih =>
    intro a ha
    cases i with
    | zero =>
      have heq : (x :: xs).modify 0 f = f x :: xs := rfl
      rw [heq] at ha
      simp at ha
      cases ha with
      | inl heq2 =>
        rw [heq2]
        exact h2 x (by simp)
      | inr hmem =>
        exact h1 a (List.mem_cons_of_mem x hmem)
    | succ n =>
      have heq : (x :: xs).modify (n + 1) f = x :: xs.modify n f := rfl
      rw [heq] at ha
      simp at ha
      cases ha with
      | inl heq2 =>
        rw [heq2]
        exact h1 x (by simp)
      | inr hmem =>
        have h1t : ∀ b ∈ xs, P b := fun b hb => h1 b (List.mem_cons_of_mem x hb)
        have h2t : ∀ b ∈ xs, P (f b) := fun b hb => h2 b (List.mem_cons_of_mem x hb)
        exact ih n h1t h2t a hmem

theorem consistent_doSupply_of_consistent (s : St) (who : Nat) (hc : Consistent s)
    (m : St) (hm : doSupply s who = some m) : Consistent m := by
  unfold doSupply at hm
  split at hm
  · obtain ⟨rfl⟩ := hm
    unfold Consistent at hc ⊢
    obtain ⟨h1, h2, h3⟩ := hc
    have hge : s.supplyState.index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrue_ge _ _ _
    have hbeq : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block =
        s.blockNumber := accrue_block _ _ _
    refine ⟨?_, ?_, ?_⟩
    · show (accrueSide s.supplyState s.blockNumber (totalSupply s)).block ≤ s.blockNumber
      rw [hbeq]
      exact Nat.le_refl _
    · exact h2
    · intro a ha
      constructor
      · have hS1 : ∀ b ∈ s.accts,
            b.supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
          intro b hb
          obtain ⟨hs, _⟩ := h3 b hb
          calc b.supplierIndex ≤ s.supplyState.index := hs
            _ ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := hge
        have hS2 : ∀ b ∈ s.accts, (supplyUpd s b).supplierIndex ≤
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
          intro b hb
          simp [supplyUpd]
        exact all_modify s.accts who (supplyUpd s)
          (fun a => a.supplierIndex ≤
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) hS1 hS2 a ha
      · have hB1 : ∀ b ∈ s.accts, b.borrowerIndex ≤ s.borrowState.index := by
          intro b hb
          exact (h3 b hb).2
        have hB2 : ∀ b ∈ s.accts, (supplyUpd s b).borrowerIndex ≤
            s.borrowState.index := by
          intro b hb
          simp [supplyUpd]
          exact (h3 b hb).2
        exact all_modify s.accts who (supplyUpd s)
          (fun a => a.borrowerIndex ≤ s.borrowState.index) hB1 hB2 a ha
  · exact absurd hm (by simp)

theorem consistent_doBorrow_of_consistent (s : St) (who : Nat) (hc : Consistent s)
    (m : St) (hm : doBorrow s who = some m) : Consistent m := by
  unfold doBorrow at hm
  split at hm
  · obtain ⟨rfl⟩ := hm
    unfold Consistent at hc ⊢
    obtain ⟨h1, h2, h3⟩ := hc
    have hge : s.borrowState.index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrue_ge _ _ _
    have hbeq : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block =
        s.blockNumber := accrue_block _ _ _
    refine ⟨?_, ?_, ?_⟩
    · exact h1
    · show (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block ≤ s.blockNumber
      rw [hbeq]
      exact Nat.le_refl _
    · intro a ha
      constructor
      · have hS1 : ∀ b ∈ s.accts, b.supplierIndex ≤ s.supplyState.index := by
          intro b hb
          exact (h3 b hb).1
        have hS2 : ∀ b ∈ s.accts, (borrowUpd s b).supplierIndex ≤
            s.supplyState.index := by
          intro b hb
          simp [borrowUpd]
          exact (h3 b hb).1
        exact all_modify s.accts who (borrowUpd s)
          (fun a => a.supplierIndex ≤ s.supplyState.index) hS1 hS2 a ha
      · have hB1 : ∀ b ∈ s.accts,
            b.borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
          intro b hb
          obtain ⟨_, hb2⟩ := h3 b hb
          calc b.borrowerIndex ≤ s.borrowState.index := hb2
            _ ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := hge
        have hB2 : ∀ b ∈ s.accts, (borrowUpd s b).borrowerIndex ≤
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
          intro b hb
          simp [borrowUpd]
        exact all_modify s.accts who (borrowUpd s)
          (fun a => a.borrowerIndex ≤
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) hB1 hB2 a ha
  · exact absurd hm (by simp)

theorem consistent_speeds_of_consistent (s : St) (sup bor : Nat) (hc : Consistent s)
    (m : St) (hm : doSpeeds s sup bor = some m) : Consistent m := by
  unfold doSpeeds at hm
  split at hm
  · obtain ⟨rfl⟩ := hm
    unfold Consistent at hc ⊢
    obtain ⟨h1, h2, h3⟩ := hc
    have hgeS : s.supplyState.index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrue_ge _ _ _
    have hgeB : s.borrowState.index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrue_ge _ _ _
    by_cases hs : s.supplyState.speed = sup <;> by_cases hb : s.borrowState.speed = bor
    · simp [speedsResult, hs, hb]
      exact ⟨h1, h2, h3⟩
    · simp [speedsResult, hs, hb]
      refine ⟨?_, ?_, ?_⟩
      · exact h1
      · show (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block ≤ s.blockNumber
        rw [accrue_block]
        exact Nat.le_refl _
      · intro a ha
        have hh := h3 a ha
        obtain ⟨hs1, hb1⟩ := hh
        constructor
        · exact hs1
        · calc a.borrowerIndex ≤ s.borrowState.index := hb1
            _ ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := hgeB
    · simp [speedsResult, hs, hb]
      refine ⟨?_, ?_, ?_⟩
      · show (accrueSide s.supplyState s.blockNumber (totalSupply s)).block ≤ s.blockNumber
        rw [accrue_block]
        exact Nat.le_refl _
      · exact h2
      · intro a ha
        have hh := h3 a ha
        obtain ⟨hs1, hb1⟩ := hh
        constructor
        · calc a.supplierIndex ≤ s.supplyState.index := hs1
            _ ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := hgeS
        · exact hb1
    · simp [speedsResult, hs, hb]
      refine ⟨?_, ?_, ?_⟩
      · show (accrueSide s.supplyState s.blockNumber (totalSupply s)).block ≤ s.blockNumber
        rw [accrue_block]
        exact Nat.le_refl _
      · show (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block ≤ s.blockNumber
        rw [accrue_block]
        exact Nat.le_refl _
      · intro a ha
        have hh := h3 a ha
        obtain ⟨hs1, hb1⟩ := hh
        constructor
        · calc a.supplierIndex ≤ s.supplyState.index := hs1
            _ ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := hgeS
        · calc a.borrowerIndex ≤ s.borrowState.index := hb1
            _ ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := hgeB
  · exact absurd hm (by simp)

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hs
  cases c with
  | supplyHook who =>
    unfold comptroller doSupply
    have hcnd := supply_cond_of_consistent s hs who
    simp [hcnd]
  | borrowHook who =>
    unfold comptroller doBorrow
    have hcnd := borrow_cond_of_consistent s hs who
    simp [hcnd]
  | claim who =>
    unfold comptroller
    have hb := borrow_cond_of_consistent s hs who
    have hBi : (doBorrow s who).isSome := by
      unfold doBorrow
      simp [hb]
    cases hBm : doBorrow s who with
    | none =>
      simp [hBm] at hBi
    | some m1 =>
      simp [hBm]
      have hc1 := consistent_doBorrow_of_consistent s who hs m1 hBm
      have hs2 := supply_cond_of_consistent m1 hc1 who
      have hSi : (doSupply m1 who).isSome := by
        unfold doSupply
        simp [hs2]
      cases hSm : doSupply m1 who with
      | none =>
        simp [hSm] at hSi
      | some m2 =>
        simp [hSm]
  | setSpeeds a b =>
    unfold comptroller doSpeeds
    have hcnd := speeds_or_of_consistent s hs a b
    simp [hcnd]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller doSupply at h
  by_cases hcnd : (s.supplyState.block ≤ s.blockNumber ∧
      accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
  · simp [hcnd] at h
    obtain ⟨rfl⟩ := h
    exact ⟨hcnd.1, hcnd.2, rfl⟩
  · simp [hcnd] at h

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller doBorrow at h
  by_cases hcnd : (s.borrowState.block ≤ s.blockNumber ∧
      accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
  · simp [hcnd] at h
    obtain ⟨rfl⟩ := h
    exact ⟨hcnd.1, hcnd.2, rfl⟩
  · simp [hcnd] at h

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hB : doBorrow s who with
  | none =>
    simp [hB] at h
  | some m1 =>
    simp [hB] at h
    cases hS : doSupply m1 who with
    | none =>
      simp [hS] at h
    | some m2 =>
      simp [hS] at h
      obtain ⟨rfl⟩ := h
      have hBc : comptroller s (.borrowHook who) = some m1 := hB
      have hSc : comptroller m1 (.supplyHook who) = some m2 := hS
      have hbD := req_borrow_hook s who m1 hBc
      have hsD := req_supply_hook m1 who m2 hSc
      exact ⟨m1, m2, hbD, hsD, rfl⟩

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller doSpeeds speedsResult at h
  by_cases hcnd : ((s.supplyState.speed = a ∨ s.supplyState.block ≤ s.blockNumber) ∧
    (s.borrowState.speed = b ∨ s.borrowState.block ≤ s.blockNumber))
  · simp [hcnd] at h
    obtain ⟨rfl⟩ := h
    have hc := speedsCond_of_or hcnd
    unfold speedsCond at hc
    obtain ⟨h1, h2⟩ := hc
    refine ⟨?_, ?_, ?_⟩
    · intro hne
      exact h1 hne
    · intro hne
      exact h2 hne
    · rfl
  · simp [hcnd] at h
def supPending (s : St) : Nat :=
  (s.accts.map fun a => a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)).sum

def borPending (s : St) : Nat :=
  (s.accts.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum

def supUnindexed (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed

def borUnindexed (s : St) : Nat :=
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def J (s : St) : Nat :=
  s.credited + (supPending s + borPending s) / doubleScale + supUnindexed s + borUnindexed s

def pendWho (s : St) (who : Account) : Nat :=
  (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) +
  (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)

def unidxWho (s : St) (who : Account) : Nat :=
  (if 0 < (s.acct who).supply then supUnindexed s else 0) +
  (if 0 < (s.acct who).borrow then borUnindexed s else 0)

def Jwho (s : St) (who : Account) : Nat :=
  s.creditedTo who + pendWho s who / doubleScale + unidxWho s who

theorem doubleScale_pos : 0 < doubleScale := by decide
theorem compInitial_pos : 0 < compInitialIndex := by decide
theorem scale_eq_initial : doubleScale = compInitialIndex := rfl

theorem accrualStart_self (idx : Nat) : accrualStart idx idx = idx := by
  unfold accrualStart
  by_cases h : idx = 0
  · simp [h]
  · simp [h]

theorem accrualStart_mono {r i1 i2 : Nat} (hle : i1 ≤ i2) :
    accrualStart r i1 ≤ accrualStart r i2 := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp [hr]
    by_cases h1 : compInitialIndex ≤ i1 <;> by_cases h2 : compInitialIndex ≤ i2
    · simp [h1, h2]
    · simp [h1, h2]
      omega
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [hr]

theorem map_modify_sum_preserve (l : List Acct) (i : Nat) (f : Acct → Acct) (g : Acct → Nat)
    (h : ∀ a, g (f a) = g a) :
    ((l.modify i f).map g).sum = (l.map g).sum := by
  induction l generalizing i with
  | nil =>
    simp
  | cons x xs ih =>
    cases i with
    | zero =>
      simp [h x]
    | succ n =>
      simp
      exact ih n

theorem totalSupply_doSupply (s : St) (who : Nat) (m : St)
    (hm : doSupply s who = some m) : totalSupply m = totalSupply s := by
  unfold doSupply at hm
  split at hm
  · obtain ⟨rfl⟩ := hm
    unfold totalSupply
    apply map_modify_sum_preserve
    intro a
    rfl
  · contradiction

theorem totalBorrows_doSupply (s : St) (who : Nat) (m : St)
    (hm : doSupply s who = some m) : totalBorrows m = totalBorrows s := by
  unfold doSupply at hm
  split at hm
  · obtain ⟨rfl⟩ := hm
    unfold totalBorrows
    apply map_modify_sum_preserve
    intro a
    rfl
  · exact absurd hm (by simp)

theorem totalSupply_doBorrow (s : St) (who : Nat) (m : St)
    (hm : doBorrow s who = some m) : totalSupply m = totalSupply s := by
  unfold doBorrow at hm
  split at hm
  · obtain ⟨rfl⟩ := hm
    unfold totalSupply
    apply map_modify_sum_preserve
    intro a
    rfl
  · exact absurd hm (by simp)

theorem totalBorrows_doBorrow (s : St) (who : Nat) (m : St)
    (hm : doBorrow s who = some m) : totalBorrows m = totalBorrows s := by
  unfold doBorrow at hm
  split at hm
  · obtain ⟨rfl⟩ := hm
    unfold totalBorrows
    apply map_modify_sum_preserve
    intro a
    rfl
  · exact absurd hm (by simp)

theorem credited_advance (s : St) (k : Nat) :
    ({ s with blockNumber := s.blockNumber + k } : St).credited = s.credited := rfl

theorem supPending_advance (s : St) (k : Nat) :
    supPending { s with blockNumber := s.blockNumber + k } = supPending s := rfl

theorem borPending_advance (s : St) (k : Nat) :
    borPending { s with blockNumber := s.blockNumber + k } = borPending s := rfl

theorem supUnindexed_advance (s : St) (k : Nat)
    (h1 : s.supplyState.block ≤ s.blockNumber) :
    supUnindexed { s with blockNumber := s.blockNumber + k } =
      supUnindexed s + k * s.supplyState.speed := by
  unfold supUnindexed
  simp
  have hle : s.supplyState.block ≤ s.blockNumber + k := Nat.le_trans h1 (Nat.le_add_right _ _)
  have h1' : s.blockNumber + k - s.supplyState.block =
      (s.blockNumber - s.supplyState.block) + k := by omega
  rw [h1']
  exact Nat.add_mul _ _ _

theorem borUnindexed_advance (s : St) (k : Nat)
    (h2 : s.borrowState.block ≤ s.blockNumber) :
    borUnindexed { s with blockNumber := s.blockNumber + k } =
      borUnindexed s + k * s.borrowState.speed := by
  unfold borUnindexed
  simp
  have hle : s.borrowState.block ≤ s.blockNumber + k := Nat.le_trans h2 (Nat.le_add_right _ _)
  have h1' : s.blockNumber + k - s.borrowState.block =
      (s.blockNumber - s.borrowState.block) + k := by omega
  rw [h1']
  exact Nat.add_mul _ _ _

theorem J_advance (s : St) (k : Nat)
    (h1 : s.supplyState.block ≤ s.blockNumber)
    (h2 : s.borrowState.block ≤ s.blockNumber) :
    J { s with blockNumber := s.blockNumber + k } =
      J s + k * (s.supplyState.speed + s.borrowState.speed) := by
  have hE : k * (s.supplyState.speed + s.borrowState.speed) =
      k * s.supplyState.speed + k * s.borrowState.speed := Nat.mul_add _ _ _
  unfold J
  rw [credited_advance, supPending_advance, borPending_advance,
    supUnindexed_advance s k h1, borUnindexed_advance s k h2, hE]
  ac_rfl

theorem pendWho_advance (s : St) (who : Nat) (k : Nat) :
    pendWho { s with blockNumber := s.blockNumber + k } who = pendWho s who := rfl

theorem creditedTo_advance (s : St) (who : Nat) (k : Nat) :
    ({ s with blockNumber := s.blockNumber + k } : St).creditedTo who =
      s.creditedTo who := rfl

theorem supUnindexed_le_advance (s : St) (k : Nat) :
    supUnindexed { s with blockNumber := s.blockNumber + k } ≤
      supUnindexed s + k * s.supplyState.speed := by
  unfold supUnindexed
  simp only
  have hle : s.blockNumber + k - s.supplyState.block ≤
      (s.blockNumber - s.supplyState.block) + k := by omega
  have hmul := Nat.mul_le_mul hle (Nat.le_refl (s.supplyState.speed))
  calc (s.blockNumber + k - s.supplyState.block) * s.supplyState.speed
      ≤ ((s.blockNumber - s.supplyState.block) + k) * s.supplyState.speed := hmul
    _ = (s.blockNumber - s.supplyState.block) * s.supplyState.speed +
        k * s.supplyState.speed := Nat.add_mul _ _ _

theorem borUnindexed_le_advance (s : St) (k : Nat) :
    borUnindexed { s with blockNumber := s.blockNumber + k } ≤
      borUnindexed s + k * s.borrowState.speed := by
  unfold borUnindexed
  simp only
  have hle : s.blockNumber + k - s.borrowState.block ≤
      (s.blockNumber - s.borrowState.block) + k := by omega
  have hmul := Nat.mul_le_mul hle (Nat.le_refl (s.borrowState.speed))
  calc (s.blockNumber + k - s.borrowState.block) * s.borrowState.speed
      ≤ ((s.blockNumber - s.borrowState.block) + k) * s.borrowState.speed := hmul
    _ = (s.blockNumber - s.borrowState.block) * s.borrowState.speed +
        k * s.borrowState.speed := Nat.add_mul _ _ _

theorem Jwho_advance_le (s : St) (who : Nat) (k : Nat)
    (h1 : s.supplyState.block ≤ s.blockNumber)
    (h2 : s.borrowState.block ≤ s.blockNumber) :
    Jwho { s with blockNumber := s.blockNumber + k } who ≤
      Jwho s who + k * (s.supplyState.speed + s.borrowState.speed) := by
  have hU1 := supUnindexed_advance s k h1
  have hU2 := borUnindexed_advance s k h2
  have hP : pendWho { s with blockNumber := s.blockNumber + k } who = pendWho s who := rfl
  have hC : ({ s with blockNumber := s.blockNumber + k } : St).creditedTo who =
      s.creditedTo who := rfl
  have hA1 : (({ s with blockNumber := s.blockNumber + k } : St).acct who).supply =
      (s.acct who).supply := rfl
  have hA2 : (({ s with blockNumber := s.blockNumber + k } : St).acct who).borrow =
      (s.acct who).borrow := rfl
  have hE : k * (s.supplyState.speed + s.borrowState.speed) =
      k * s.supplyState.speed + k * s.borrowState.speed := Nat.mul_add _ _ _
  unfold Jwho unidxWho
  rw [hP, hC, hA1, hA2, hU1, hU2, hE]
  by_cases hs : 0 < (s.acct who).supply <;> by_cases hb : 0 < (s.acct who).borrow
  · simp [hs, hb]
    apply Nat.le_of_eq
    ac_rfl
  · simp [hs, hb]
    have hle : k * s.supplyState.speed ≤
        k * s.supplyState.speed + k * s.borrowState.speed :=
      Nat.le_add_right _ _
    have hle2 : supUnindexed s + k * s.supplyState.speed ≤
        supUnindexed s + (k * s.supplyState.speed + k * s.borrowState.speed) := by
      apply Nat.add_le_add_left
      exact hle
    calc s.creditedTo who + pendWho s who / doubleScale +
          (supUnindexed s + k * s.supplyState.speed)
        ≤ s.creditedTo who + pendWho s who / doubleScale +
          (supUnindexed s + (k * s.supplyState.speed + k * s.borrowState.speed)) := by
          apply Nat.add_le_add_left
          exact hle2
      _ = s.creditedTo who + pendWho s who / doubleScale + supUnindexed s +
          (k * s.supplyState.speed + k * s.borrowState.speed) := by ac_rfl
  · simp [hs, hb]
    have hle : k * s.borrowState.speed ≤
        k * s.supplyState.speed + k * s.borrowState.speed :=
      Nat.le_add_left _ _
    have hle2 : borUnindexed s + k * s.borrowState.speed ≤
        borUnindexed s + (k * s.supplyState.speed + k * s.borrowState.speed) := by
      apply Nat.add_le_add_left
      exact hle
    calc s.creditedTo who + pendWho s who / doubleScale +
          (borUnindexed s + k * s.borrowState.speed)
        ≤ s.creditedTo who + pendWho s who / doubleScale +
          (borUnindexed s + (k * s.supplyState.speed + k * s.borrowState.speed)) := by
          apply Nat.add_le_add_left
          exact hle2
      _ = s.creditedTo who + pendWho s who / doubleScale + borUnindexed s +
          (k * s.supplyState.speed + k * s.borrowState.speed) := by ac_rfl
  · simp [hs, hb]

theorem accrue_mul_le (sd : Side) (now total : Nat) :
    ((accrueSide sd now total).index - sd.index) * total ≤
      (now - sd.block) * sd.speed * doubleScale := by
  unfold accrueSide
  split
  · have h1 : (now - sd.block) * sd.speed * doubleScale / total * total ≤
        (now - sd.block) * sd.speed * doubleScale :=
      Nat.div_mul_le_self _ _
    have heq : sd.index + (now - sd.block) * sd.speed * doubleScale / total - sd.index =
        (now - sd.block) * sd.speed * doubleScale / total := by
      calc sd.index + (now - sd.block) * sd.speed * doubleScale / total - sd.index
          = (now - sd.block) * sd.speed * doubleScale / total + sd.index - sd.index := by
            rw [Nat.add_comm]
        _ = (now - sd.block) * sd.speed * doubleScale / total := Nat.add_sub_cancel _ _
    calc ((sd.index + (now - sd.block) * sd.speed * doubleScale / total) - sd.index) * total
        = ((now - sd.block) * sd.speed * doubleScale / total) * total := by
          rw [heq]
      _ ≤ (now - sd.block) * sd.speed * doubleScale := h1
  · simp

theorem J_doSupply_le (s : St) (who : Nat) (m : St)
    (hm : doSupply s who = some m) : J m ≤ J s := by
  sorry
theorem J_doBorrow_le (s : St) (who : Nat) (m : St)
    (hm : doBorrow s who = some m) : J m ≤ J s := by
  sorry
theorem sum_add_distrib (l : List Acct) (f g : Acct → Nat) :
    ((l.map fun a => f a + g a).sum) = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sum_mul_supply (l : List Acct) (C : Nat) :
    ((l.map fun a => a.supply * C).sum) = (l.map Acct.supply).sum * C := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [ih, Nat.add_mul]

theorem sum_mul_borrow (l : List Acct) (C : Nat) :
    ((l.map fun a => a.borrow * C).sum) = (l.map Acct.borrow).sum * C := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [ih, Nat.add_mul]

theorem div_add_le (a b D : Nat) : a / D + b / D ≤ (a + b) / D := by
  by_cases hD : D = 0
  · simp [hD]
  · have hDpos : 0 < D := Nat.pos_of_ne_zero hD
    have ha := Nat.div_add_mod a D
    have hb := Nat.div_add_mod b D
    -- a = (a/D)*D + a%D, b = (b/D)*D + b%D
    have hab : a + b = (a / D + b / D) * D + (a % D + b % D) := by
      calc a + b
          = (a / D * D + a % D) + (b / D * D + b % D) := by
            rw [← ha, ← hb]
        _ = (a / D + b / D) * D + (a % D + b % D) := by
            rw [Nat.add_mul]
            ac_rfl
    have hle : a / D + b / D ≤ a / D + b / D + (a % D + b % D) / D := by
      apply Nat.le_add_right
    calc a / D + b / D
        ≤ a / D + b / D + (a % D + b % D) / D := hle
      _ = ((a / D + b / D) * D + (a % D + b % D)) / D := by
          rw [Nat.add_mul_div_right _ _ hDpos]
          ac_rfl
      _ = (a + b) / D := by
          rw [← hab]
          ac_rfl

theorem pend_le_of_mono {u r i1 i2 : Nat}
    (h1 : accrualStart r i1 ≤ i1) (h2 : accrualStart r i2 ≤ i2)
    (h3 : accrualStart r i1 ≤ accrualStart r i2) (h4 : i1 ≤ i2) :
    i2 - accrualStart r i2 ≤ (i1 - accrualStart r i1) + (i2 - i1) := by
  omega
theorem Jwho_doSupply_le (s : St) (who q : Nat) (m : St)
    (hm : doSupply s who = some m) : Jwho m q ≤ Jwho s q + 0 := by
  sorry
theorem Jwho_doBorrow_le (s : St) (who q : Nat) (m : St)
    (hm : doBorrow s who = some m) : Jwho m q ≤ Jwho s q + 0 := by
  sorry

theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
