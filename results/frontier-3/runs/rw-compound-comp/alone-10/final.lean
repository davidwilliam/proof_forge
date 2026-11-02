import CompRewards.Spec
namespace CompRewards

def fraction (a b : Nat) : Nat := a * doubleScale / b
def mulDouble (a mantissa : Nat) : Nat := a * mantissa / doubleScale
def subChecked (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

def updateCompSupplyIndex (s : St) : Option St :=
  match subChecked s.blockNumber s.supplyState.block with
  | none => none
  | some deltaBlocks =>
    if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
      let supplyTokens := totalSupply s
      let compAccrued := deltaBlocks * s.supplyState.speed
      let ratio := if supplyTokens > 0 then fraction compAccrued supplyTokens else 0
      some { s with supplyState :=
        { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } }
    else if deltaBlocks > 0 then
      some { s with supplyState := { s.supplyState with block := s.blockNumber } }
    else some s

def updateCompBorrowIndex (s : St) : Option St :=
  match subChecked s.blockNumber s.borrowState.block with
  | none => none
  | some deltaBlocks =>
    if deltaBlocks > 0 ∧ s.borrowState.speed > 0 then
      let borrowAmount := totalBorrows s
      let compAccrued := deltaBlocks * s.borrowState.speed
      let ratio := if borrowAmount > 0 then fraction compAccrued borrowAmount else 0
      some { s with borrowState :=
        { s.borrowState with index := s.borrowState.index + ratio, block := s.blockNumber } }
    else if deltaBlocks > 0 then
      some { s with borrowState := { s.borrowState with block := s.blockNumber } }
    else some s

def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  let supplyIndex := s.supplyState.index
  let supplierIndex :=
    if (s.acct supplier).supplierIndex = 0 ∧ compInitialIndex ≤ supplyIndex then compInitialIndex
    else (s.acct supplier).supplierIndex
  match subChecked supplyIndex supplierIndex with
  | none => none
  | some deltaIndex =>
    let supplierDelta := mulDouble (s.acct supplier).supply deltaIndex
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := supplyIndex, accrued := a.accrued + supplierDelta })

def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  let borrowIndex := s.borrowState.index
  let borrowerIndex :=
    if (s.acct borrower).borrowerIndex = 0 ∧ compInitialIndex ≤ borrowIndex then compInitialIndex
    else (s.acct borrower).borrowerIndex
  match subChecked borrowIndex borrowerIndex with
  | none => none
  | some deltaIndex =>
    let borrowerDelta := mulDouble (s.acct borrower).borrow deltaIndex
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := borrowIndex, accrued := a.accrued + borrowerDelta })

def grantCompInternal (s : St) (user : Account) : St :=
  let amount := (s.acct user).accrued
  if amount > 0 ∧ amount ≤ s.reserve then
    { s with reserve := s.reserve - amount,
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + amount } }
  else s

def claimComp (s : St) (holder : Account) : Option St := do
  let s ← updateCompBorrowIndex s
  let s ← distributeBorrowerComp s holder
  let s ← updateCompSupplyIndex s
  let s ← distributeSupplierComp s holder
  return grantCompInternal s holder

def setSupplySpeed (s : St) (supplySpeed : Nat) : Option St :=
  if s.supplyState.speed ≠ supplySpeed then
    (updateCompSupplyIndex s).map fun s =>
      { s with supplyState := { s.supplyState with speed := supplySpeed } }
  else some s

def setBorrowSpeed (s : St) (borrowSpeed : Nat) : Option St :=
  if s.borrowState.speed ≠ borrowSpeed then
    (updateCompBorrowIndex s).map fun s =>
      { s with borrowState := { s.borrowState with speed := borrowSpeed } }
  else some s

def setCompSpeedInternal (s : St) (supplySpeed borrowSpeed : Nat) : Option St :=
  (setSupplySpeed s supplySpeed).bind fun s => setBorrowSpeed s borrowSpeed

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => do
    let s ← updateCompSupplyIndex s
    distributeSupplierComp s who
  | .borrowHook who => do
    let s ← updateCompBorrowIndex s
    distributeBorrowerComp s who
  | .claim who => claimComp s who
  | .setSpeeds a b => setCompSpeedInternal s a b

theorem bind_some {a : Option St} {f : St → Option St} {s' : St} :
    a.bind f = some s' → ∃ s1, a = some s1 ∧ f s1 = some s' := by
  intro h
  cases ha : a with
  | none => simp [ha] at h
  | some s1 => exact ⟨s1, rfl, by simp [ha] at h; exact h⟩

theorem sub_some {a b d : Nat} : subChecked a b = some d ↔ b ≤ a ∧ d = a - b := by
  unfold subChecked
  constructor
  · intro hh
    by_cases h : b ≤ a
    · rw [if_pos h] at hh
      have e : a - b = d := Option.some_inj.mp hh
      exact ⟨h, e.symm⟩
    · rw [if_neg h] at hh
      contradiction
  · intro hh
    rw [if_pos hh.left, hh.right]

theorem sub_none {a b : Nat} : subChecked a b = none ↔ ¬ b ≤ a := by
  unfold subChecked
  constructor
  · intro hh h
    rw [if_pos h] at hh
    contradiction
  · intro hh
    rw [if_neg hh]

theorem accrue_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · rw [if_pos h]
  · rw [if_neg h]

theorem accrue_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · rw [if_pos h]
    apply Nat.le_add_right
  · simp [if_neg h]

theorem start_le (rec idx : Nat) (h : rec ≤ idx) : accrualStart rec idx ≤ idx := by
  unfold accrualStart
  by_cases hr : rec = 0
  · simp only [hr, ↓reduceIte]
    by_cases hi : compInitialIndex ≤ idx
    · simp [hi]
    · simp [hi]
  · simp [hr, h]

theorem start_eq_zero_ge (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).supplierIndex = 0
  · by_cases hi : compInitialIndex ≤ s.supplyState.index <;> simp [h0, hi]
  · simp [h0]

theorem bstart_eq_zero_ge (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).borrowerIndex = 0
  · by_cases hi : compInitialIndex ≤ s.borrowState.index <;> simp [h0, hi]
  · simp [h0]

theorem updateSupply_of_le (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) := by
  unfold updateCompSupplyIndex
  have hs : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
    rw [sub_some]; exact ⟨h, rfl⟩
  rw [hs]
  simp only
  by_cases h1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · rw [if_pos h1]
    by_cases ht : totalSupply s > 0
    · rw [if_pos ht]
      have e2 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s :=
        ⟨h1.left, h1.right, ht⟩
      unfold accrueSide fraction
      rw [if_pos e2]
    · rw [if_neg ht]
      have e2 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        intro hc
        exact ht hc.right.right
      unfold accrueSide
      rw [if_neg e2]
      simp
  · rw [if_neg h1]
    by_cases h2 : s.blockNumber - s.supplyState.block > 0
    · rw [if_pos h2]
      have e2 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        intro hc
        exact h1 ⟨hc.left, hc.right.left⟩
      unfold accrueSide
      rw [if_neg e2]
    · rw [if_neg h2]
      have e2 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        omega
      unfold accrueSide
      rw [if_neg e2]
      have hb : s.supplyState.block = s.blockNumber := by omega
      cases s with
      | mk bn sup bor res ac =>
        simp only at hb ⊢
        cases sup with
        | mk i b sp =>
          simp only at hb ⊢
          rw [hb]

theorem updateSupply_of_gt (s : St) (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex
  have hs : subChecked s.blockNumber s.supplyState.block = none := by
    rw [sub_none]; exact h
  rw [hs]

theorem updateBorrow_of_le (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) := by
  unfold updateCompBorrowIndex
  have hs : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    rw [sub_some]; exact ⟨h, rfl⟩
  rw [hs]
  simp only
  by_cases h1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · rw [if_pos h1]
    by_cases ht : totalBorrows s > 0
    · rw [if_pos ht]
      have e2 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s :=
        ⟨h1.left, h1.right, ht⟩
      unfold accrueSide fraction
      rw [if_pos e2]
    · rw [if_neg ht]
      have e2 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        intro hc
        exact ht hc.right.right
      unfold accrueSide
      rw [if_neg e2]
      simp
  · rw [if_neg h1]
    by_cases h2 : s.blockNumber - s.borrowState.block > 0
    · rw [if_pos h2]
      have e2 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        intro hc
        exact h1 ⟨hc.left, hc.right.left⟩
      unfold accrueSide
      rw [if_neg e2]
    · rw [if_neg h2]
      have e2 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        omega
      unfold accrueSide
      rw [if_neg e2]
      have hb : s.borrowState.block = s.blockNumber := by omega
      cases s with
      | mk bn sup bor res ac =>
        simp only at hb ⊢
        cases bor with
        | mk i b sp =>
          simp only at hb ⊢
          rw [hb]

theorem updateBorrow_of_gt (s : St) (h : ¬ s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = none := by
  unfold updateCompBorrowIndex
  have hs : subChecked s.blockNumber s.borrowState.block = none := by
    rw [sub_none]; exact h
  rw [hs]

theorem mod_congr {l : List Acct} {i : Nat} {f g : Acct → Acct}
    (h : f (l.getD i noAcct) = g (l.getD i noAcct)) :
    l.modify i f = l.modify i g := by
  apply List.ext_getElem
  · rw [List.length_modify, List.length_modify]
  · intro j h1 h2
    have e1 := List.getElem_modify f i l j h1
    have e2 := List.getElem_modify g i l j h2
    rw [e1, e2]
    by_cases he : i = j
    · simp only [he, ↓reduceIte]
      have hg1 : ∀ (hj : j < l.length), l[j] = l.getD j noAcct :=
        fun hj => List.getElem_eq_getD noAcct
      have hj : j < l.length := by
        have e : (l.modify i f).length = l.length := List.length_modify f l i
        omega
      rw [hg1 hj]
      have hjj : l.getD j noAcct = l.getD i noAcct := by rw [he]
      rw [hjj, h]
    · simp [he]

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant St.acct
  by_cases h : 0 < (s.accts.getD who noAcct).accrued ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve
  · rw [if_pos h, if_pos h]
    congr 1
    apply mod_congr
    simp only
  · rw [if_neg h, if_neg h]

theorem getD_modify_inbounds {l : List Acct} {who : Nat} {f : Acct → Acct} (h : who < l.length) :
    (l.modify who f).getD who noAcct = f (l.getD who noAcct) := by
  have h1 : who < (l.modify who f).length := by rw [List.length_modify]; exact h
  have e1 := List.getElem_modify f who l who h1
  have g1 : (l.modify who f).getD who noAcct = (l.modify who f)[who] := (List.getElem_eq_getD noAcct).symm
  have g2 : l.getD who noAcct = l[who] := (List.getElem_eq_getD noAcct).symm
  simp only [ite_true] at e1
  rw [g1, g2, e1]

theorem getD_modify_oob {l : List Acct} {who : Nat} {f : Acct → Acct} (h : l.length ≤ who) :
    (l.modify who f).getD who noAcct = noAcct := by
  have h1 : (l.modify who f).length ≤ who := by rw [List.length_modify]; exact h
  have heq2 : (l.modify who f)[who]? = none := List.getElem?_eq_none h1
  simp [heq2]

theorem getD_oob {l : List Acct} {who : Nat} (h : l.length ≤ who) :
    l.getD who noAcct = noAcct := by
  have heq : l[who]? = none := List.getElem?_eq_none h
  simp [heq]

theorem preserves_supplierIndex {s : St} {who : Account} {f : Acct → Acct}
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
  unfold St.acct St.withAcct
  by_cases hlen : who < s.accts.length
  · have h1 := getD_modify_inbounds (l := s.accts) (who := who) (f := f) hlen
    rw [h1, hf]
  · have hge : s.accts.length ≤ who := Nat.le_of_not_lt hlen
    have h1 := getD_modify_oob (l := s.accts) (who := who) (f := f) hge
    have h2 := getD_oob (l := s.accts) (who := who) hge
    rw [h1, h2]

theorem preserves_borrowerIndex {s : St} {who : Account} {f : Acct → Acct}
    (hf : ∀ a, (f a).borrowerIndex = a.borrowerIndex) :
    ((s.withAcct who f).acct who).borrowerIndex = (s.acct who).borrowerIndex := by
  unfold St.acct St.withAcct
  by_cases hlen : who < s.accts.length
  · have h1 := getD_modify_inbounds (l := s.accts) (who := who) (f := f) hlen
    rw [h1, hf]
  · have hge : s.accts.length ≤ who := Nat.le_of_not_lt hlen
    have h1 := getD_modify_oob (l := s.accts) (who := who) (f := f) hge
    have h2 := getD_oob (l := s.accts) (who := who) hge
    rw [h1, h2]

theorem acct_sup_le (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  unfold St.acct
  obtain ⟨h1, h2, h3⟩ := hc
  by_cases hlen : who < s.accts.length
  · have heq : s.accts.getD who noAcct = s.accts[who] := (List.getElem_eq_getD noAcct).symm
    rw [heq]
    have hmem : s.accts[who] ∈ s.accts := List.getElem_mem hlen
    exact (h3 _ hmem).left
  · have hge : s.accts.length ≤ who := Nat.le_of_not_lt hlen
    have heq : s.accts[who]? = none := List.getElem?_eq_none hge
    have hget : s.accts.getD who noAcct = noAcct := by
      unfold List.getD
      rw [heq]
      rfl
    rw [hget]
    exact Nat.zero_le _

theorem acct_bor_le (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  unfold St.acct
  obtain ⟨h1, h2, h3⟩ := hc
  by_cases hlen : who < s.accts.length
  · have heq : s.accts.getD who noAcct = s.accts[who] := (List.getElem_eq_getD noAcct).symm
    rw [heq]
    have hmem : s.accts[who] ∈ s.accts := List.getElem_mem hlen
    exact (h3 _ hmem).right
  · have hge : s.accts.length ≤ who := Nat.le_of_not_lt hlen
    have heq : s.accts[who]? = none := List.getElem?_eq_none hge
    have hget : s.accts.getD who noAcct = noAcct := by
      unfold List.getD
      rw [heq]
      rfl
    rw [hget]
    exact Nat.zero_le _

theorem distSup_ok (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by
  unfold distributeSupplierComp mulDouble creditFor
  simp only
  rw [start_eq_zero_ge]
  have hs : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) =
      some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := by
    rw [sub_some]; exact ⟨h, rfl⟩
  rw [hs]
  simp only
  congr 1
  unfold St.withAcct
  congr 1
  apply mod_congr
  simp only [St.acct]

theorem distSup_fail (s : St) (who : Account)
    (h : ¬ accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = none := by
  unfold distributeSupplierComp
  simp only
  rw [start_eq_zero_ge]
  have hs : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) = none := by
    rw [sub_none]; omega
  rw [hs]

theorem distBor_ok (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who =
      some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by
  unfold distributeBorrowerComp mulDouble creditFor
  simp only
  rw [bstart_eq_zero_ge]
  have hs : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) =
      some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) := by
    rw [sub_some]; exact ⟨h, rfl⟩
  rw [hs]
  simp only
  congr 1
  unfold St.withAcct
  congr 1
  apply mod_congr
  simp only [St.acct]

theorem distBor_fail (s : St) (who : Account)
    (h : ¬ accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = none := by
  unfold distributeBorrowerComp
  simp only
  rw [bstart_eq_zero_ge]
  have hs : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = none := by
    rw [sub_none]; omega
  rw [hs]

def supU (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed
def borU (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed
def supE (s : St) : Nat :=
  (s.accts.map fun a => a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)).sum
def borE (s : St) : Nat :=
  (s.accts.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum
def supEwho (s : St) (who : Account) : Nat :=
  (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index)
def borEwho (s : St) (who : Account) : Nat :=
  (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)
def supUcond (s : St) (who : Account) : Nat :=
  if 0 < (s.acct who).supply then supU s else 0
def borUcond (s : St) (who : Account) : Nat :=
  if 0 < (s.acct who).borrow then borU s else 0
def liability (s : St) : Nat :=
  doubleScale * s.credited + supE s + borE s + doubleScale * (supU s + borU s)
def liabilityWho (s : St) (who : Account) : Nat :=
  doubleScale * s.creditedTo who + supEwho s who + borEwho s who +
    doubleScale * (supUcond s who + borUcond s who)

theorem elem_sup_le (l : List Acct) (who : Nat) :
    (l.getD who noAcct).supply ≤ (l.map Acct.supply).sum := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => simp [noAcct]
    | succ n => simp [noAcct]
  | cons x xs ih =>
    cases who with
    | zero => simp
    | succ n =>
      simp only [List.getD, List.map, List.sum_cons]
      have h1 : (xs.getD n noAcct).supply ≤ (xs.map Acct.supply).sum := ih n
      have h2 : (xs.map Acct.supply).sum ≤ x.supply + (xs.map Acct.supply).sum := Nat.le_add_left _ _
      exact Nat.le_trans h1 h2

theorem elem_bor_le (l : List Acct) (who : Nat) :
    (l.getD who noAcct).borrow ≤ (l.map Acct.borrow).sum := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => simp [noAcct]
    | succ n => simp [noAcct]
  | cons x xs ih =>
    cases who with
    | zero => simp
    | succ n =>
      simp only [List.getD, List.map, List.sum_cons]
      have h1 : (xs.getD n noAcct).borrow ≤ (xs.map Acct.borrow).sum := ih n
      have h2 : (xs.map Acct.borrow).sum ≤ x.borrow + (xs.map Acct.borrow).sum := Nat.le_add_left _ _
      exact Nat.le_trans h1 h2

theorem sum_map_add (l : List Acct) (f g : Acct → Nat) :
    ((l.map fun a => f a + g a).sum) = ((l.map f).sum) + ((l.map g).sum) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.sum_cons, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sum_single_mul (l : List Acct) (C : Nat) :
    ((l.map fun a => a.supply * C).sum) = ((l.map Acct.supply).sum) * C := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.map, List.sum_cons, ih, Nat.add_mul]

theorem map_modify_eq {l : List Acct} {who : Nat} {f : Acct → Acct} {g : Acct → Nat}
    (h : g (f (l.getD who noAcct)) = g (l.getD who noAcct)) :
    ((l.modify who f).map g).sum = (l.map g).sum := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => simp
    | succ n => simp
  | cons x xs ih =>
    cases who with
    | zero =>
      simp only [List.getD] at h
      simp only [List.modify]
      rw [h]
    | succ n =>
      simp only [List.getD] at h
      simp only [List.modify]
      have ih' := ih n h
      simp [ih']

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsup, hbor, hmem⟩ := hc
  unfold comptroller
  cases c with
  | supplyHook who =>
    have hacct := acct_sup_le s ⟨hsup, hbor, hmem⟩ who
    have hnew := accrue_index_ge s.supplyState s.blockNumber (totalSupply s)
    have hle : (s.acct who).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      Nat.le_trans hacct hnew
    have hstart : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := start_le _ _ hle
    have hu := updateSupply_of_le s hsup
    have hd := distSup_ok ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) who hstart
    simp [hu, hd]
  | borrowHook who =>
    have hacct := acct_bor_le s ⟨hsup, hbor, hmem⟩ who
    have hnew := accrue_index_ge s.borrowState s.blockNumber (totalBorrows s)
    have hle : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      Nat.le_trans hacct hnew
    have hstart : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := start_le _ _ hle
    have hu := updateBorrow_of_le s hbor
    have hd := distBor_ok ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) who hstart
    simp [hu, hd]
  | claim who => sorry
  | setSpeeds a b => sorry

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  obtain ⟨s1, hu, hd⟩ := bind_some h
  have hblock : s.supplyState.block ≤ s.blockNumber := by
    by_cases hc : s.supplyState.block ≤ s.blockNumber
    · exact hc
    · have hnone := updateSupply_of_gt s hc
      rw [hnone] at hu
      contradiction
  have hs1 : s1 = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) := by
    have := updateSupply_of_le s hblock
    rw [this] at hu
    exact (Option.some_inj.mp hu).symm
  have hstart1 : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index := by
    by_cases hc : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index
    · exact hc
    · have hnone := distSup_fail s1 who hc
      rw [hnone] at hd
      contradiction
  have hdok := distSup_ok s1 who hstart1
  rw [hdok] at hd
  have hstart : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    have e1 : (s1.acct who).supplierIndex = (s.acct who).supplierIndex := by rw [hs1]; rfl
    have e2 : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [hs1]
    rw [e1, e2] at hstart1
    exact hstart1
  refine ⟨hblock, hstart, ?_⟩
  have heq : s1.withAcct who (fun a =>
      { a with supplierIndex := s1.supplyState.index,
               accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s1.supplyState.index) s1.supplyState.index }) =
      { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
               accts := s.accts.modify who fun a =>
      { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
               accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
                 (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by
    rw [hs1]; rfl
  rw [heq] at hd
  exact (Option.some_inj.mp hd).symm

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  obtain ⟨s1, hu, hd⟩ := bind_some h
  have hblock : s.borrowState.block ≤ s.blockNumber := by
    by_cases hc : s.borrowState.block ≤ s.blockNumber
    · exact hc
    · have hnone := updateBorrow_of_gt s hc
      rw [hnone] at hu
      contradiction
  have hs1 : s1 = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) := by
    have := updateBorrow_of_le s hblock
    rw [this] at hu
    exact (Option.some_inj.mp hu).symm
  have hstart1 : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index := by
    by_cases hc : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index
    · exact hc
    · have hnone := distBor_fail s1 who hc
      rw [hnone] at hd
      contradiction
  have hdok := distBor_ok s1 who hstart1
  rw [hdok] at hd
  have hstart : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    have e1 : (s1.acct who).borrowerIndex = (s.acct who).borrowerIndex := by rw [hs1]; rfl
    have e2 : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hs1]
    rw [e1, e2] at hstart1
    exact hstart1
  refine ⟨hblock, hstart, ?_⟩
  have heq : s1.withAcct who (fun a =>
      { a with borrowerIndex := s1.borrowState.index,
               accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index }) =
      { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
               accts := s.accts.modify who fun a =>
      { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
               accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
                 (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
    rw [hs1]; rfl
  rw [heq] at hd
  exact (Option.some_inj.mp hd).symm

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  simp only at h
  obtain ⟨sb1, hu1, hr1⟩ := bind_some h
  obtain ⟨m1, hd1, hr2⟩ := bind_some hr1
  obtain ⟨ss1, hu2, hr3⟩ := bind_some hr2
  obtain ⟨m2, hd2, hr4⟩ := bind_some hr3
  have hblockb : s.borrowState.block ≤ s.blockNumber := by
    by_cases hc : s.borrowState.block ≤ s.blockNumber
    · exact hc
    · have hnone := updateBorrow_of_gt s hc
      rw [hnone] at hu1
      contradiction
  have hsb1 : sb1 = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) := by
    have := updateBorrow_of_le s hblockb
    rw [this] at hu1
    exact (Option.some_inj.mp hu1).symm
  have hstartb1 : accrualStart (sb1.acct who).borrowerIndex sb1.borrowState.index ≤ sb1.borrowState.index := by
    by_cases hc : accrualStart (sb1.acct who).borrowerIndex sb1.borrowState.index ≤ sb1.borrowState.index
    · exact hc
    · have hnone := distBor_fail sb1 who hc
      rw [hnone] at hd1
      contradiction
  have hdok1 := distBor_ok sb1 who hstartb1
  rw [hdok1] at hd1
  have hm1 : m1 = sb1.withAcct who (fun a =>
      { a with borrowerIndex := sb1.borrowState.index,
               accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex sb1.borrowState.index) sb1.borrowState.index }) :=
    (Option.some_inj.mp hd1).symm
  have hblocks : m1.supplyState.block ≤ m1.blockNumber := by
    by_cases hc : m1.supplyState.block ≤ m1.blockNumber
    · exact hc
    · have hnone := updateSupply_of_gt m1 hc
      rw [hnone] at hu2
      contradiction
  have hss1 : ss1 = ({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) }) := by
    have := updateSupply_of_le m1 hblocks
    rw [this] at hu2
    exact (Option.some_inj.mp hu2).symm
  have hstarts1 : accrualStart (ss1.acct who).supplierIndex ss1.supplyState.index ≤ ss1.supplyState.index := by
    by_cases hc : accrualStart (ss1.acct who).supplierIndex ss1.supplyState.index ≤ ss1.supplyState.index
    · exact hc
    · have hnone := distSup_fail ss1 who hc
      rw [hnone] at hd2
      contradiction
  have hdok2 := distSup_ok ss1 who hstarts1
  rw [hdok2] at hd2
  have hm2 : m2 = ss1.withAcct who (fun a =>
      { a with supplierIndex := ss1.supplyState.index,
               accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex ss1.supplyState.index) ss1.supplyState.index }) :=
    (Option.some_inj.mp hd2).symm
  have hs' : s' = grant m2 who := by
    have h1 : grantCompInternal m2 who = s' := Option.some_inj.mp hr4
    have hgr : grantCompInternal m2 who = grant m2 who := grant_eq m2 who
    exact h1.symm.trans hgr
  refine ⟨m1, m2, ?_, ?_, hs'⟩
  · refine ⟨hblockb, ?_, ?_⟩
    · have e1 : (sb1.acct who).borrowerIndex = (s.acct who).borrowerIndex := by rw [hsb1]; rfl
      have e2 : sb1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hsb1]
      rw [e1, e2] at hstartb1
      exact hstartb1
    · rw [hsb1] at hm1
      rw [hm1]
      rfl
  · refine ⟨hblocks, ?_, ?_⟩
    · have e1 : (ss1.acct who).supplierIndex = (m1.acct who).supplierIndex := by rw [hss1]; rfl
      have e2 : ss1.supplyState.index = (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by rw [hss1]
      rw [e1, e2] at hstarts1
      exact hstarts1
    · rw [hss1] at hm2
      rw [hm2]
      rfl

theorem req_set_speeds : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
