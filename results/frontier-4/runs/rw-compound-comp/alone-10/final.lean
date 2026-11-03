import CompRewards.Spec
namespace CompRewards

def supplyDist (s : St) (who : Account) : Option St :=
  if s.supplyState.block ≤ s.blockNumber then
    if accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index then
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), accts := s.accts.modify who fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } }
    else none
  else none

def borrowDist (s : St) (who : Account) : Option St :=
  if s.borrowState.block ≤ s.blockNumber then
    if accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index then
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } }
    else none
  else none

def claimDist (s : St) (who : Account) : Option St :=
  match borrowDist s who with
  | none => none
  | some m1 =>
    match supplyDist m1 who with
    | none => none
    | some m2 => some (grant m2 who)

def speedsDist (s : St) (sup bor : Nat) : Option St :=
  if s.supplyState.speed = sup then
    if s.borrowState.speed = bor then some s
    else if s.borrowState.block ≤ s.blockNumber then
      some { s with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } }
    else none
  else if s.supplyState.block ≤ s.blockNumber then
    if s.borrowState.speed = bor then some { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } }
    else if s.borrowState.block ≤ s.blockNumber then
      some { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup }, borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } }
    else none
  else none

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => supplyDist s who
  | .borrowHook who => borrowDist s who
  | .claim who => claimDist s who
  | .setSpeeds a b => speedsDist s a b

theorem accrue_block (sd : Side) (now total : Nat) : (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem accrue_index_ge (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem accrualStart_le_of_rec_le (recorded index : Nat) (h : recorded ≤ index) : accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · simp [hr]
    by_cases hle : compInitialIndex ≤ index
    · simp [hle]
    · simp [hle]
  · simpa [hr] using h

theorem acct_sup_le (l : List Acct) (idx : Nat) (who : Nat) (h : ∀ a ∈ l, a.supplierIndex ≤ idx) : (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp [noAcct]
  | cons a rest ih =>
    cases who with
    | zero =>
      simp
      exact h a (List.Mem.head _)
    | succ n =>
      simp
      apply ih
      intro x hx
      exact h x (List.Mem.tail _ hx)

theorem acct_bor_le (l : List Acct) (idx : Nat) (who : Nat) (h : ∀ a ∈ l, a.borrowerIndex ≤ idx) : (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp [noAcct]
  | cons a rest ih =>
    cases who with
    | zero =>
      simp
      exact h a (List.Mem.head _)
    | succ n =>
      simp
      apply ih
      intro x hx
      exact h x (List.Mem.tail _ hx)

theorem consistent_sup_rec (s : St) (who : Account) (hc : Consistent s) : (s.acct who).supplierIndex ≤ s.supplyState.index := by
  exact acct_sup_le s.accts s.supplyState.index who (fun a ha => (hc.2.2 a ha).1)

theorem consistent_bor_rec (s : St) (who : Account) (hc : Consistent s) : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  exact acct_bor_le s.accts s.borrowState.index who (fun a ha => (hc.2.2 a ha).2)

theorem supplyDist_spec (s : St) (who : Account) (t : St) (h : supplyDist s who = some t) : SupplyDistributed s who t := by
  unfold supplyDist at h
  by_cases h1 : s.supplyState.block ≤ s.blockNumber
  · simp [h1] at h
    by_cases h2 : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
    · simp [h2] at h
      exact ⟨h1, h2, h.symm⟩
    · simp [h2] at h
  · simp [h1] at h

theorem borrowDist_spec (s : St) (who : Account) (t : St) (h : borrowDist s who = some t) : BorrowDistributed s who t := by
  unfold borrowDist at h
  by_cases h1 : s.borrowState.block ≤ s.blockNumber
  · simp [h1] at h
    by_cases h2 : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
    · simp [h2] at h
      exact ⟨h1, h2, h.symm⟩
    · simp [h2] at h
  · simp [h1] at h

theorem req_supply_hook : SupplyHookEffects comptroller := fun s who t h => supplyDist_spec s who t h

theorem req_borrow_hook : BorrowHookEffects comptroller := fun s who t h => borrowDist_spec s who t h

theorem claimDist_spec (s : St) (who : Account) (t : St) (h : claimDist s who = some t) : Claimed s who t := by
  unfold claimDist at h
  cases hb : borrowDist s who
  · simp only [hb] at h
    nomatch h
  · rename_i m1
    simp only [hb] at h
    cases hb2 : supplyDist m1 who
    · simp only [hb2] at h
      nomatch h
    · rename_i m2
      simp only [hb2] at h
      have hx1 := borrowDist_spec s who m1 hb
      have hx2 := supplyDist_spec m1 who m2 hb2
      have hg : t = grant m2 who := (Option.some_inj.mp h).symm
      exact ⟨m1, m2, hx1, hx2, hg⟩

theorem req_claim : ClaimEffects comptroller := fun s who t h => claimDist_spec s who t h

theorem speedsDist_spec (s : St) (sup bor : Nat) (t : St) (h : speedsDist s sup bor = some t) : SpeedsSet s sup bor t := by
  unfold speedsDist at h
  by_cases hs : s.supplyState.speed = sup
  · simp [hs] at h
    by_cases hb : s.borrowState.speed = bor
    · simp [hb] at h
      have he : s = t := h
      subst he
      refine ⟨?_, ?_, ?_⟩
      · intro hc; exact absurd hs hc
      · intro hc; exact absurd hb hc
      · simp [hs, hb]
    · simp [hb] at h
      by_cases hbb : s.borrowState.block ≤ s.blockNumber
      · simp [hbb] at h
        refine ⟨?_, ?_, ?_⟩
        · intro hc; exact absurd hs hc
        · intro _; exact hbb
        · rw [← h]; simp [hs, hb]
      · simp [hbb] at h
  · simp [hs] at h
    by_cases hsb : s.supplyState.block ≤ s.blockNumber
    · simp [hsb] at h
      by_cases hb : s.borrowState.speed = bor
      · simp [hb] at h
        refine ⟨?_, ?_, ?_⟩
        · intro _; exact hsb
        · intro hc; exact absurd hb hc
        · rw [← h]; simp [hs, hb]
      · simp [hb] at h
        by_cases hbb : s.borrowState.block ≤ s.blockNumber
        · simp [hbb] at h
          refine ⟨?_, ?_, ?_⟩
          · intro _; exact hsb
          · intro _; exact hbb
          · rw [← h]; simp [hs, hb]
        · simp [hbb] at h
    · simp [hsb] at h

theorem req_set_speeds : SetSpeedsEffects comptroller := fun s a b t h => speedsDist_spec s a b t h

theorem supply_isSome (s : St) (who : Account) (hc : Consistent s) : (supplyDist s who).isSome := by
  unfold supplyDist
  have hblk := hc.1
  simp [hblk]
  have hrec := consistent_sup_rec s who hc
  have hge := accrue_index_ge s.supplyState s.blockNumber (totalSupply s)
  have hle : (s.acct who).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    Nat.le_trans hrec hge
  have hst := accrualStart_le_of_rec_le (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index hle
  simp [hst]

theorem borrow_isSome (s : St) (who : Account) (hc : Consistent s) : (borrowDist s who).isSome := by
  unfold borrowDist
  have hblk := hc.2.1
  simp [hblk]
  have hrec := consistent_bor_rec s who hc
  have hge := accrue_index_ge s.borrowState s.blockNumber (totalBorrows s)
  have hle : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    Nat.le_trans hrec hge
  have hst := accrualStart_le_of_rec_le (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index hle
  simp [hst]

theorem speeds_isSome (s : St) (sup bor : Nat) (hc : Consistent s) : (speedsDist s sup bor).isSome := by
  unfold speedsDist
  have hsb := hc.1
  have hbb := hc.2.1
  by_cases hs : s.supplyState.speed = sup
  · simp [hs]
    by_cases hb : s.borrowState.speed = bor
    · simp [hb]
    · simp [hb, hbb]
  · simp [hs, hsb]
    by_cases hb : s.borrowState.speed = bor
    · simp [hb]
    · simp [hb, hbb]

theorem supply_modify_all (l : List Acct) (who : Nat) (oldIdx newIdx borIdx : Nat)
    (hle : oldIdx ≤ newIdx) (hall : ∀ b ∈ l, b.supplierIndex ≤ oldIdx ∧ b.borrowerIndex ≤ borIdx) :
    ∀ a ∈ l.modify who (fun a => ({ a with supplierIndex := newIdx, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex newIdx) newIdx } : Acct)),
      a.supplierIndex ≤ newIdx ∧ a.borrowerIndex ≤ borIdx := by
  induction l generalizing who with
  | nil =>
    simp [List.modify_nil]
  | cons b rest ih =>
    intro a ha
    cases who with
    | zero =>
      have hmod : (b :: rest).modify 0 (fun a => ({ a with supplierIndex := newIdx, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex newIdx) newIdx } : Acct)) = ({ b with supplierIndex := newIdx, accrued := b.accrued + creditFor b.supply (accrualStart b.supplierIndex newIdx) newIdx } : Acct) :: rest := by simp [List.modify]
      rw [hmod] at ha
      simp [List.mem_cons] at ha
      cases ha with
      | inl heq =>
        rw [heq]
        constructor
        · simp
        · exact (hall b (List.Mem.head _)).2
      | inr hmem =>
        have hold := hall a (List.Mem.tail _ hmem)
        exact ⟨Nat.le_trans hold.1 hle, hold.2⟩
    | succ n =>
      have hmod : (b :: rest).modify (n + 1) (fun a => ({ a with supplierIndex := newIdx, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex newIdx) newIdx } : Acct)) = b :: rest.modify n (fun a => ({ a with supplierIndex := newIdx, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex newIdx) newIdx } : Acct)) := by simp [List.modify]
      rw [hmod] at ha
      simp [List.mem_cons] at ha
      cases ha with
      | inl heq =>
        rw [heq]
        have hold := hall b (List.Mem.head _)
        exact ⟨Nat.le_trans hold.1 hle, hold.2⟩
      | inr hmem =>
        exact ih n (fun x hx => hall x (List.Mem.tail _ hx)) a hmem

theorem borrow_modify_all (l : List Acct) (who : Nat) (supIdx oldIdx newIdx : Nat)
    (hle : oldIdx ≤ newIdx) (hall : ∀ b ∈ l, b.supplierIndex ≤ supIdx ∧ b.borrowerIndex ≤ oldIdx) :
    ∀ a ∈ l.modify who (fun a => ({ a with borrowerIndex := newIdx, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex newIdx) newIdx } : Acct)),
      a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ newIdx := by
  induction l generalizing who with
  | nil =>
    simp [List.modify_nil]
  | cons b rest ih =>
    intro a ha
    cases who with
    | zero =>
      have hmod : (b :: rest).modify 0 (fun a => ({ a with borrowerIndex := newIdx, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex newIdx) newIdx } : Acct)) = ({ b with borrowerIndex := newIdx, accrued := b.accrued + creditFor b.borrow (accrualStart b.borrowerIndex newIdx) newIdx } : Acct) :: rest := by simp [List.modify]
      rw [hmod] at ha
      simp [List.mem_cons] at ha
      cases ha with
      | inl heq =>
        rw [heq]
        simp
        exact (hall b (List.Mem.head _)).1
      | inr hmem =>
        have hold := hall a (List.Mem.tail _ hmem)
        exact ⟨hold.1, Nat.le_trans hold.2 hle⟩
    | succ n =>
      have hmod : (b :: rest).modify (n + 1) (fun a => ({ a with borrowerIndex := newIdx, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex newIdx) newIdx } : Acct)) = b :: rest.modify n (fun a => ({ a with borrowerIndex := newIdx, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex newIdx) newIdx } : Acct)) := by simp [List.modify]
      rw [hmod] at ha
      simp [List.mem_cons] at ha
      cases ha with
      | inl heq =>
        rw [heq]
        have hold := hall b (List.Mem.head _)
        exact ⟨hold.1, Nat.le_trans hold.2 hle⟩
      | inr hmem =>
        exact ih n (fun x hx => hall x (List.Mem.tail _ hx)) a hmem

theorem supply_preserves (s t : St) (who : Account) (hc : Consistent s) (h : supplyDist s who = some t) : Consistent t := by
  unfold supplyDist at h
  by_cases h1 : s.supplyState.block ≤ s.blockNumber
  · simp [h1] at h
    by_cases h2 : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
    · simp [h2] at h
      subst h
      have hge : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
        accrue_index_ge s.supplyState s.blockNumber (totalSupply s)
      have hblk : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block ≤ s.blockNumber := by
        have hb := accrue_block s.supplyState s.blockNumber (totalSupply s)
        rw [hb]
        exact Nat.le_refl _
      refine ⟨?_, ?_, ?_⟩
      · exact hblk
      · exact hc.2.1
      · exact supply_modify_all s.accts who s.supplyState.index (accrueSide s.supplyState s.blockNumber (totalSupply s)).index s.borrowState.index hge hc.2.2
    · simp [h2] at h
  · simp [h1] at h

theorem borrow_preserves (s t : St) (who : Account) (hc : Consistent s) (h : borrowDist s who = some t) : Consistent t := by
  unfold borrowDist at h
  by_cases h1 : s.borrowState.block ≤ s.blockNumber
  · simp [h1] at h
    by_cases h2 : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
    · simp [h2] at h
      subst h
      have hge : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
        accrue_index_ge s.borrowState s.blockNumber (totalBorrows s)
      have hblk : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block ≤ s.blockNumber := by
        have hb := accrue_block s.borrowState s.blockNumber (totalBorrows s)
        rw [hb]
        exact Nat.le_refl _
      refine ⟨?_, ?_, ?_⟩
      · exact hc.1
      · exact hblk
      · exact borrow_modify_all s.accts who s.supplyState.index s.borrowState.index (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index hge hc.2.2
    · simp [h2] at h
  · simp [h1] at h

theorem claim_isSome (s : St) (who : Account) (hc : Consistent s) : (claimDist s who).isSome := by
  unfold claimDist
  have hb := borrow_isSome s who hc
  cases hm : borrowDist s who with
  | none =>
    simp [hm] at hb
  | some m1 =>
    simp
    have hc1 := borrow_preserves s m1 who hc hm
    have hs := supply_isSome m1 who hc1
    cases hm2 : supplyDist m1 who with
    | none =>
      simp [hm2] at hs
    | some m2 =>
      simp

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold comptroller
  cases c with
  | supplyHook who =>
    simp
    exact supply_isSome s who hc
  | borrowHook who =>
    simp
    exact borrow_isSome s who hc
  | claim who =>
    simp
    exact claim_isSome s who hc
  | setSpeeds a b =>
    simp
    exact speeds_isSome s a b hc

theorem doubleScale_pos : 0 < doubleScale := by decide

theorem add_div_le (a b D : Nat) (hD : 0 < D) : a / D + b / D ≤ (a + b) / D := by
  have h1 : a / D * D ≤ a := Nat.div_mul_le_self a D
  have h2 : b / D * D ≤ b := Nat.div_mul_le_self b D
  have h3 : (a / D + b / D) * D ≤ a + b := by
    have heq : (a / D + b / D) * D = a / D * D + b / D * D := Nat.add_mul _ _ _
    rw [heq]
    exact Nat.add_le_add h1 h2
  exact (Nat.le_div_iff_mul_le hD).mpr h3

theorem mul_Q_le (u E T D : Nat) (hle : u ≤ T) : u * ((E * D) / T) ≤ E * D := by
  have hQ : (E * D) / T * T ≤ E * D := Nat.div_mul_le_self _ _
  have h1 : u * ((E * D) / T) ≤ T * ((E * D) / T) := Nat.mul_le_mul hle (Nat.le_refl _)
  have h2 : T * ((E * D) / T) = (E * D) / T * T := Nat.mul_comm _ _
  rw [h2] at h1
  exact Nat.le_trans h1 hQ

theorem accrualStart_mono (recorded I I' : Nat) (hle : I ≤ I') : accrualStart recorded I ≤ accrualStart recorded I' := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · simp [hr]
    by_cases h1 : compInitialIndex ≤ I
    · have h2 : compInitialIndex ≤ I' := Nat.le_trans h1 hle
      simp [h1, h2]
    · simp [h1]
  · simp [hr]

theorem accrue_speed (sd : Side) (now total : Nat) : (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem acct_sup_le_total (l : List Acct) (who : Nat) : (l.getD who noAcct).supply ≤ (l.map Acct.supply).sum := by
  induction l generalizing who with
  | nil =>
    simp [noAcct]
  | cons a rest ih =>
    cases who with
    | zero =>
      simp
    | succ n =>
      simp
      have h1 := ih n
      have h2 : (rest.map Acct.supply).sum ≤ a.supply + (rest.map Acct.supply).sum := Nat.le_add_left _ _
      exact Nat.le_trans h1 h2

theorem acct_bor_le_total (l : List Acct) (who : Nat) : (l.getD who noAcct).borrow ≤ (l.map Acct.borrow).sum := by
  induction l generalizing who with
  | nil =>
    simp [noAcct]
  | cons a rest ih =>
    cases who with
    | zero =>
      simp
    | succ n =>
      simp
      have h1 := ih n
      have h2 : (rest.map Acct.borrow).sum ≤ a.borrow + (rest.map Acct.borrow).sum := Nat.le_add_left _ _
      exact Nat.le_trans h1 h2

def supOne (s : St) (who : Account) : Nat :=
  (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index)

def borOne (s : St) (who : Account) : Nat :=
  (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)

def unSup (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed

def unBor (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def Pacc (s : St) (who : Account) : Nat :=
  s.creditedTo who + (supOne s who + borOne s who) / doubleScale +
    (if 0 < (s.acct who).supply then unSup s else 0) +
    (if 0 < (s.acct who).borrow then unBor s else 0)

def Pscaled (s : St) (who : Account) : Nat :=
  s.creditedTo who * doubleScale + (supOne s who + borOne s who) +
    (if 0 < (s.acct who).supply then unSup s * doubleScale else 0) +
    (if 0 < (s.acct who).borrow then unBor s * doubleScale else 0)

theorem Pacc_eq_Pscaled (s : St) (who : Account) : Pacc s who = Pscaled s who / doubleScale := by
  unfold Pacc Pscaled St.creditedTo supOne borOne unSup unBor
  split
  · split
    · simp
      have hD := doubleScale_pos
      have h_factor : ((s.acct who).accrued + (s.acct who).wallet) * doubleScale + ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale = ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) + (((s.acct who).accrued + (s.acct who).wallet) + (s.blockNumber - s.supplyState.block) * s.supplyState.speed + (s.blockNumber - s.borrowState.block) * s.borrowState.speed) * doubleScale := by
        simp [Nat.add_mul]
        ac_rfl
      have h_div : (((s.acct who).accrued + (s.acct who).wallet) * doubleScale + ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale) / doubleScale = ((s.acct who).accrued + (s.acct who).wallet) + (s.blockNumber - s.supplyState.block) * s.supplyState.speed + (s.blockNumber - s.borrowState.block) * s.borrowState.speed + ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) / doubleScale := by
        rw [h_factor]
        rw [Nat.add_mul_div_right _ _ hD]
        ac_rfl
      rw [h_div]
      ac_rfl
    · simp
      have hD := doubleScale_pos
      have h_factor : ((s.acct who).accrued + (s.acct who).wallet) * doubleScale + ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale = ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) + (((s.acct who).accrued + (s.acct who).wallet) + (s.blockNumber - s.supplyState.block) * s.supplyState.speed) * doubleScale := by
        simp [Nat.add_mul]
        ac_rfl
      have h_div : (((s.acct who).accrued + (s.acct who).wallet) * doubleScale + ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale) / doubleScale = ((s.acct who).accrued + (s.acct who).wallet) + (s.blockNumber - s.supplyState.block) * s.supplyState.speed + ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) / doubleScale := by
        rw [h_factor]
        rw [Nat.add_mul_div_right _ _ hD]
        ac_rfl
      rw [h_div]
      ac_rfl
  · split
    · simp
      have hD := doubleScale_pos
      have h_factor : ((s.acct who).accrued + (s.acct who).wallet) * doubleScale + ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale = ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) + (((s.acct who).accrued + (s.acct who).wallet) + (s.blockNumber - s.borrowState.block) * s.borrowState.speed) * doubleScale := by
        simp [Nat.add_mul]
        ac_rfl
      have h_div : (((s.acct who).accrued + (s.acct who).wallet) * doubleScale + ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale) / doubleScale = ((s.acct who).accrued + (s.acct who).wallet) + (s.blockNumber - s.borrowState.block) * s.borrowState.speed + ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) / doubleScale := by
        rw [h_factor]
        rw [Nat.add_mul_div_right _ _ hD]
        ac_rfl
      rw [h_div]
      ac_rfl
    · simp
      have hD := doubleScale_pos
      have h_factor : ((s.acct who).accrued + (s.acct who).wallet) * doubleScale + ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) = ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) + ((s.acct who).accrued + (s.acct who).wallet) * doubleScale := by ac_rfl
      have h_div : (((s.acct who).accrued + (s.acct who).wallet) * doubleScale + ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index))) / doubleScale = ((s.acct who).accrued + (s.acct who).wallet) + ((s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)) / doubleScale := by
        rw [h_factor]
        rw [Nat.add_mul_div_right _ _ hD]
      rw [h_div]

theorem modify_getD_ne (l : List Acct) (who who' : Nat) (f : Acct → Acct) (d : Acct) (hne : who' ≠ who) :
    (l.modify who f).getD who' d = l.getD who' d := by
  induction l generalizing who who' with
  | nil =>
    simp [List.modify_nil]
  | cons b rest ih =>
    cases who with
    | zero =>
      cases who' with
      | zero =>
        exact absurd rfl hne
      | succ n =>
        have h1 : (b :: rest).modify 0 f = f b :: rest := by simp [List.modify]
        rw [h1]
        simp
    | succ n =>
      cases who' with
      | zero =>
        have h1 : (b :: rest).modify (n + 1) f = b :: rest.modify n f := by simp [List.modify]
        rw [h1]
        simp
      | succ m =>
        have h1 : (b :: rest).modify (n + 1) f = b :: rest.modify n f := by simp [List.modify]
        rw [h1]
        simp
        have hne2 : m ≠ n := fun h => hne (congrArg Nat.succ h)
        exact ih n m hne2

theorem modify_getD_eq (l : List Acct) (who : Nat) (f : Acct → Acct) (d : Acct) (hlt : who < l.length) :
    (l.modify who f).getD who d = f (l.getD who d) := by
  induction l generalizing who with
  | nil =>
    simp at hlt
  | cons b rest ih =>
    cases who with
    | zero =>
      simp [List.modify]
    | succ n =>
      simp [List.modify]
      have hlt2 : n < rest.length := Nat.lt_of_succ_lt_succ hlt
      exact ih n hlt2

theorem supply_P_le (s : St) (who who' : Account) (t : St) (hc : Consistent s) (h : supplyDist s who = some t) :
    Pacc t who' ≤ Pacc s who' := by
  unfold supplyDist at h
  by_cases h1 : s.supplyState.block ≤ s.blockNumber
  · simp [h1] at h
    by_cases h2 : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
    · simp [h2] at h
      subst h
      by_cases heq : who' = who
      · rw [heq]
        by_cases hlt : who < s.accts.length
        · sorry
        · sorry
      · have hne : who' ≠ who := heq
        have hacct : (s.accts.modify who (fun a => ({ a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } : Acct))).getD who' noAcct = s.accts.getD who' noAcct := modify_getD_ne _ _ _ _ _ hne
        sorry
    · simp [h2] at h
  · simp [h1] at h

theorem borrow_P_le (s : St) (who who' : Account) (t : St) (hc : Consistent s) (h : borrowDist s who = some t) :
    Pacc t who' ≤ Pacc s who' := sorry

theorem speeds_P_le (s : St) (sup bor : Nat) (who' : Account) (t : St) (hc : Consistent s) (h : speedsDist s sup bor = some t) :
    Pacc t who' ≤ Pacc s who' := sorry

theorem grant_P_eq (s : St) (who who' : Account) : Pacc (grant s who) who' ≤ Pacc s who' := sorry

theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
