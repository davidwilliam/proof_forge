import Allocation.Spec
namespace Allocation

def findMaxAux : List Nat → List Bool → Nat → Option (Nat × Nat) → Option (Nat × Nat)
  | [], [], _, best => best
  | r :: rs, c :: cs, i, best =>
    let best' :=
      if c then best
      else if r == 0 then best
      else match best with
        | none => some (i, r)
        | some (bi, br) => if br < r then some (i, r) else some (bi, br)
    findMaxAux rs cs (i + 1) best'
  | _ :: _, [], _, best => best
  | [], _ :: _, _, best => best

def findMaxIdx (rems : List Nat) (mask : List Bool) : Option Nat :=
  (findMaxAux rems mask 0 none).map Prod.fst

def chooseIter (rems : List Nat) : List Bool → Nat → List Bool
  | mask, 0 => mask
  | mask, (k + 1) =>
    match (findMaxAux rems mask 0 none) with
    | none => mask
    | some (idx, _) => chooseIter rems (mask.set idx true) k

def choose (rems : List Nat) (k : Nat) : List Bool :=
  chooseIter rems (List.replicate rems.length false) k

def allocateNonneg (A : Nat) (ratios : List Nat) (S : Nat) : List Int :=
  let floors : List Nat := ratios.map (fun r => (A * r) / S)
  let rems : List Nat := ratios.map (fun r => (A * r) % S)
  let k : Nat := A - floors.sum
  let mask := choose rems k
  List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0) floors mask

def allocate : Impl := fun amount ratios =>
  let S := ratios.sum
  if ratios = [] ∨ S = 0 then none
  else
    let A := amount.natAbs
    let shares := allocateNonneg A ratios S
    if 0 ≤ amount then some shares
    else some (shares.map (fun x => -x))

theorem req_invalid_fails_test2 : InvalidFails allocate := by
  unfold InvalidFails Valid allocate
  intro amount ratios h
  by_cases he : ratios = []
  · simp [he]
  · have h2 : ¬ (0 < ratios.sum) := fun hp => h ⟨he, hp⟩
    have h3 : ratios.sum = 0 := Nat.eq_zero_of_not_pos h2
    simp [he, h3]

theorem foo_test : True := trivial

theorem foo_test2 : True := trivial

theorem chooseIter_len_aux2 : (List.replicate 3 false).length = 3 := by simp

theorem probe1 (l : List Nat) (f : Nat → Nat) : (l.map f).length = l.length := by simp

theorem probe2 (a b : List Nat) : (List.zipWith (· + ·) a b).length = min a.length b.length := by simp
-- check names
#check List.length_map
#check List.length_zipWith

theorem probe_sum1 (l : List Int) : l.sum = l.sum := by rfl
#check List.sum
#check List.length_set

theorem probe_env : True := trivial
#check Allocation.Valid
#check Lean.versionString

theorem tprint : True := trivial
#print chooseIter
#check chooseIter.eq_1
#check chooseIter.eq_2

theorem findMaxAux_none_case : findMaxAux [] ([] : List Bool) 5 none = none := by simp [findMaxAux]

theorem findMax_step : findMaxAux (r :: rs) (c :: cs) i best =
    findMaxAux rs cs (i+1) (if c then best else if r == 0 then best else match best with | none => some (i, r) | some (bi, br) => if br < r then some (i, r) else some (bi, br)) := by
  simp [findMaxAux]

theorem indprobe2 (rems : List Nat) (mask : List Bool) (i : Nat) : True := by
  induction rems generalizing mask i with
  | nil => trivial
  | cons r rs ih => trivial

theorem foo_sign_probe : True := trivial

theorem mytest_induct (fl : List Nat) : fl.length = fl.length := by cases fl with | nil => simp | cons hd tl => simp

theorem probe_mem_nil (x : Int) (h : x ∈ ([] : List Int)) : 0 ≤ x := by simp at h

theorem probe_mem_nil2 (x : Int) (h : x ∈ ([] : List Int)) : 0 ≤ x := by simp at h

theorem mytest_induct4 (fl : List Nat) (mk : List Bool) : True := by induction fl generalizing mk with | nil => trivial | cons hd tl ih => trivial

theorem lem_probe : True := trivial
#check List.sum
#check List.get
#check List.set

theorem probe_ver : Lean.versionString = Lean.versionString := rfl
#check Lean.versionString
#print axioms probe_ver

theorem tmp1 : chooseIter [1] [false] 0 = [false] := by rfl
#check @List.length_set
#check List.getElem_set
#check chooseIter
#print chooseIter

theorem tmp2 : chooseIter [1] [false] 1 = [true] := by rfl

theorem tmp4 : True := trivial
#check chooseIter.eq_2

theorem tmpEqT : True := trivial
#check (chooseIter.eq_1)
#check (chooseIter.eq_2)
#check (chooseIter.eq_unfold)

theorem tmpLen2 (rems : List Nat) (mask : List Bool) : (chooseIter rems mask 0).length = mask.length := rfl

theorem tmpLenA (rems : List Nat) (mask : List Bool) (k : Nat)
    (heq : findMaxAux rems mask 0 none = none) :
    chooseIter rems mask (k+1) = mask := by simp [chooseIter, heq]

theorem plan0_chooseIter_length (rems : List Nat) (mask : List Bool) (k : Nat) :
    (chooseIter rems mask k).length = mask.length := by
  induction k generalizing mask with
  | zero => simp [chooseIter]
  | succ k ih =>
    unfold chooseIter
    cases h : findMaxAux rems mask 0 none with
    | none => rfl
    | some p =>
      cases p with
      | mk idx val =>
        simp only
        rw [ih]
        simp




theorem plan0_allocateNonneg_length (A : Nat) (ratios : List Nat) (S : Nat) :
    (allocateNonneg A ratios S).length = ratios.length := by
  unfold allocateNonneg choose
  simp only
  have h1 : (List.map (fun r => A * r / S) ratios).length = ratios.length := by simp
  have h2 : (chooseIter (List.map (fun r => A * r % S) ratios) (List.replicate (List.map (fun r => A * r % S) ratios).length false) (A - (List.map (fun r => A * r / S) ratios).sum)).length = ratios.length := by
    rw [plan0_chooseIter_length]
    simp
  rw [List.length_zipWith, h1, h2, Nat.min_self]


theorem plan0_length_of_allocate_some (amount : Int) (ratios : List Nat) (shares : List Int)
    (h : allocate amount ratios = some shares) :
    shares.length = ratios.length := by
  unfold allocate at h
  by_cases hcond : ratios = [] ∨ ratios.sum = 0
  · simp [hcond] at h
  · simp [hcond] at h
    split at h
    · next hle =>
      have heq := Option.some_inj.mp h
      rw [← heq]
      exact plan0_allocateNonneg_length amount.natAbs ratios ratios.sum
    · next hle =>
      have heq := Option.some_inj.mp h
      rw [← heq]
      simp [plan0_allocateNonneg_length amount.natAbs ratios ratios.sum]


theorem plan0_one_share_each : OneShareEach allocate := by
  intro amount ratios shares h
  unfold OneShareEachOn
  exact plan0_length_of_allocate_some amount ratios shares h


theorem helper_len_set_probe (l : List Bool) (n : Nat) (a : Bool) : (l.set n a).length = l.length := by simp
#check @List.length_set
#check List.length_set

theorem tmp_proof4 (rems : List Nat) (mask : List Bool) (k : Nat) :
    (chooseIter rems mask k).length = mask.length := by
  induction k generalizing mask with
  | zero => simp [chooseIter]
  | succ k ih =>
    unfold chooseIter
    cases h : findMaxAux rems mask 0 none with
    | none => rfl
    | some p =>
      cases p with
      | mk idx val =>
        simp only
        rw [ih]
        simp

theorem plan0_choose_length (rems : List Nat) (k : Nat) :
    (choose rems k).length = rems.length := by
  unfold choose
  rw [plan0_chooseIter_length]
  simp

theorem tmp_check_zip : True := trivial
#check @List.length_zipWith
#check @List.length_map

theorem tmp_len_rw (a b : List Nat) (f : Nat → Nat → Int) :
    (List.zipWith f a b).length = min a.length b.length := by
  exact List.length_zipWith

theorem plan0_allocateNonneg_length_aux (A : Nat) (ratios : List Nat) (S : Nat) :
    (allocateNonneg A ratios S).length = ratios.length := by
  unfold allocateNonneg
  simp only
  have h1 : (List.map (fun r => A * r / S) ratios).length = ratios.length := by simp
  have h2 : (choose (List.map (fun r => A * r % S) ratios) (A - (List.map (fun r => A * r / S) ratios).sum)).length = ratios.length := by
    rw [plan0_choose_length]
    simp
  rw [List.length_zipWith, h1, h2, Nat.min_self]

theorem plan0_allocateNonneg_length_check (A : Nat) (ratios : List Nat) (S : Nat) :
    (allocateNonneg A ratios S).length = ratios.length := by
  unfold allocateNonneg choose
  simp only
  have h1 : (List.map (fun r => A * r / S) ratios).length = ratios.length := by simp
  have h2 : (chooseIter (List.map (fun r => A * r % S) ratios) (List.replicate (List.map (fun r => A * r % S) ratios).length false) (A - (List.map (fun r => A * r / S) ratios).sum)).length = ratios.length := by
    rw [plan0_chooseIter_length]
    simp
  rw [List.length_zipWith, h1, h2, Nat.min_self]

theorem plan0_length_of_allocate_some_test (amount : Int) (ratios : List Nat) (shares : List Int)
    (h : allocate amount ratios = some shares) :
    shares.length = ratios.length := by
  unfold allocate at h
  by_cases hcond : ratios = [] ∨ ratios.sum = 0
  · simp [hcond] at h
  · simp [hcond] at h
    split at h
    · next hle =>
      have heq := Option.some_inj.mp h
      rw [← heq]
      exact plan0_allocateNonneg_length amount.natAbs ratios ratios.sum
    · next hle =>
      have heq := Option.some_inj.mp h
      rw [← heq]
      simp [plan0_allocateNonneg_length amount.natAbs ratios ratios.sum]

theorem plan0_one_share_each_helper : OneShareEach allocate := by
  intro amount ratios shares h
  unfold OneShareEachOn
  exact plan0_length_of_allocate_some amount ratios shares h

theorem my_one_share_each_final : OneShareEach allocate := plan0_one_share_each

theorem req_one_share_each_helper2 : OneShareEach allocate := plan0_one_share_each_helper

theorem divmod_sum_lemma2 (A S : Nat) (ratios : List Nat) :
    (ratios.map (fun r => (A * r) / S)).sum * S + (ratios.map (fun r => (A * r) % S)).sum = A * ratios.sum := by
  induction ratios with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h := Nat.div_add_mod (A * r) S
    -- h : S * ((A*r)/S) + (A*r)%S = A*r
    have h1 : ((A * r) / S + (List.map (fun r => A * r / S) rs).sum) * S =
      (A * r) / S * S + (List.map (fun r => A * r / S) rs).sum * S := Nat.add_mul _ _ _
    have h2 : A * (r + rs.sum) = A * r + A * rs.sum := Nat.mul_add _ _ _
    have hc : (A * r) / S * S = S * ((A * r) / S) := Nat.mul_comm _ _
    rw [h1, h2, hc]
    omega

theorem probe_le_cancel (a b k : Nat) (h : a * k ≤ b * k) (hk : 0 < k) : a ≤ b :=
  Nat.le_of_mul_le_mul_right h hk

theorem floors_sum_le_of_sum_eq2 (A : Nat) (ratios : List Nat) (hS : 0 < ratios.sum) :
    (ratios.map (fun r => (A * r) / ratios.sum)).sum ≤ A := by
  have h := divmod_sum_lemma2 A ratios.sum ratios
  have hle : (ratios.map (fun r => (A * r) / ratios.sum)).sum * ratios.sum ≤ A * ratios.sum := by
    omega
  exact Nat.le_of_mul_le_mul_right hle hS

theorem zip_sum_true_probe (b : Bool) : ((if b then (1 : Int) else 0)) = 1 ∨ ((if b then (1 : Int) else 0)) = 0 := by
  cases b <;> simp











theorem probe_set_map3 (hd : Bool) (tl : List Bool) (n : Nat) :
    List.map (fun (b : Bool) => (if b then (1:Nat) else 0)) ((hd :: tl).set (n+1) true) =
    (if hd then 1 else 0) :: List.map (fun (b : Bool) => (if b then (1:Nat) else 0)) (tl.set n true) := by simp

theorem probe_set_succ2 (hd : Bool) (tl : List Bool) (n : Nat) (b : Bool) :
    (hd :: tl).set (n+1) b = hd :: tl.set n b := by cases n with | zero => simp | succ m => simp

theorem probe_getop1 (hd : Bool) (tl : List Bool) (n : Nat) :
    ((hd :: tl)[n+1]? = tl[n]?) := by simp

theorem aux_mask_count_final2 (mask : List Bool) (idx : Nat)
    (h : mask[idx]? = some false) :
    ((mask.set idx true).map (fun (b : Bool) => (if b then (1:Nat) else 0))).sum =
      (mask.map (fun (b : Bool) => (if b then (1:Nat) else 0))).sum + 1 := by
  induction mask generalizing idx with
  | nil => simp at h
  | cons hd tl ih =>
    cases idx with
    | zero =>
      simp at h
      subst h
      simp
      omega
    | succ n =>
      have htl : tl[n]? = some false := by simpa using h
      have ihh := ih n htl
      have hset : (hd :: tl).set (n + 1) true = hd :: tl.set n true := probe_set_succ2 hd tl n true
      rw [hset]
      simp only [List.map_cons, List.sum_cons] at ihh ⊢
      omega

theorem plan2_findMaxAux_general (rems : List Nat) (mask : List Bool)
    (start : Nat) (best : Option (Nat × Nat))
    (hlen : mask.length = rems.length)
    (h : 0 < (List.zipWith
      (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems mask).sum) :
    ∃ idx val, findMaxAux rems mask start best = some (idx, val) ∧
      0 < val ∧
      ((∃ bi br, best = some (bi, br) ∧ idx = bi ∧ val = br) ∨
       (∃ rel, idx = start + rel ∧ rel < mask.length ∧
         mask[rel]? = some false ∧ rems[rel]? = some val)) := by sorry

theorem plan2_findMaxAux_zero (rems : List Nat) (mask : List Bool)
    (hlen : mask.length = rems.length)
    (h : 0 < (List.zipWith
      (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems mask).sum) :
    ∃ idx val, findMaxAux rems mask 0 none = some (idx, val) ∧
      mask[idx]? = some false ∧ rems[idx]? = some val ∧ 0 < val := by
  obtain ⟨idx, val, hfind, hpos, hcase⟩ := plan2_findMaxAux_general rems mask 0 none hlen h
  refine ⟨idx, val, hfind, ?_, ?_, hpos⟩
  · rcases hcase with ⟨bi, br, hcontra, _, _⟩ | ⟨rel, hidx, _, hmask, hrems⟩
    · simp at hcontra
    · have : idx = rel := by omega
      rw [this]
      exact hmask
  · rcases hcase with ⟨bi, br, hcontra, _, _⟩ | ⟨rel, hidx, _, hmask, hrems⟩
    · simp at hcontra
    · have : idx = rel := by omega
      rw [this]
      exact hrems






theorem snippet_ifbool (c : Bool) (a b : Nat) (hc : c = true) : (if c then a else b) = a := by simp [hc]

theorem snippet_ifbool2 (c : Bool) (a b : Nat) (hc : c = false) : (if c then a else b) = b := by simp [hc]
#check findMaxAux.eq_1
#check findMaxAux.eq_2

theorem snippet_beq_simp (r : Nat) (h : r = 0) : (r == 0) = true := by simp [h]

theorem snippet_beq_simp2 (r : Nat) (h : r ≠ 0) : (r == 0) = false := by simp [h]

theorem snippet_cases_c (c : Bool) (best : Option (Nat × Nat)) (r : Nat) :
    (if c then best else if r == 0 then best else best) = best := by
  cases c with
  | true => simp
  | false => simp

theorem snippet_avail_cons (r : Nat) (rs : List Nat) (c : Bool) (cs : List Bool) :
    (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (r :: rs) (c :: cs)).sum =
    (if c then (0:Nat) else if 0 < r then 1 else 0) + (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum := by
  simp
#check beq_iff_eq

theorem snippet_beq_true_iff (r : Nat) : (r == 0) = true ↔ r = 0 := beq_iff_eq

theorem snippet_ne_false (r : Nat) (h : r ≠ 0) : (r == 0) = false := by simp [h]

theorem plan2_findMaxAux_zero_from_general (rems : List Nat) (mask : List Bool)
    (hlen : mask.length = rems.length)
    (h : 0 < (List.zipWith
      (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems mask).sum) :
    ∃ idx val, findMaxAux rems mask 0 none = some (idx, val) ∧
      mask[idx]? = some false ∧ rems[idx]? = some val ∧ 0 < val := by
  obtain ⟨idx, val, hfind, hpos, hcase⟩ := plan2_findMaxAux_general rems mask 0 none hlen h
  refine ⟨idx, val, hfind, ?_, ?_, hpos⟩
  · rcases hcase with ⟨bi, br, hcontra, _, _⟩ | ⟨rel, hidx, _, hmask, hrems⟩
    · simp at hcontra
    · have : idx = rel := by omega
      rw [this]
      exact hmask
  · rcases hcase with ⟨bi, br, hcontra, _, _⟩ | ⟨rel, hidx, _, hmask, hrems⟩
    · simp at hcontra
    · have : idx = rel := by omega
      rw [this]
      exact hrems

theorem aux_avail_cons (r : Nat) (rs : List Nat) (c : Bool) (cs : List Bool) :
    (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (r :: rs) (c :: cs)).sum =
    (if c then (0:Nat) else if 0 < r then 1 else 0) + (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum := by
  simp

theorem aux_step_true (r : Nat) (rs : List Nat) (cs : List Bool) (start : Nat) (best : Option (Nat × Nat)) :
    findMaxAux (r :: rs) (true :: cs) start best = findMaxAux rs cs (start+1) best := by
  simp [findMaxAux]

theorem aux_step_false_zero (rs : List Nat) (cs : List Bool) (start : Nat) (best : Option (Nat × Nat)) :
    findMaxAux (0 :: rs) (false :: cs) start best = findMaxAux rs cs (start+1) best := by
  simp [findMaxAux]

theorem aux_base (start : Nat) (best : Option (Nat × Nat)) :
    findMaxAux [] ([] : List Bool) start best = best := by
  simp [findMaxAux]

theorem aux_findMaxAux_eq_best_of_avail_zero3 (rems : List Nat) (mask : List Bool)
    (start : Nat) (best : Option (Nat × Nat))
    (hlen : mask.length = rems.length)
    (h0 : (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rems mask).sum = 0) :
    findMaxAux rems mask start best = best := by
  induction rems generalizing mask start best with
  | nil =>
    match mask with
    | [] => exact aux_base start best
    | hd :: tl => simp at hlen
  | cons r rs ih =>
    match mask with
    | [] => simp at hlen
    | c :: cs =>
      have hlen1 : cs.length = rs.length := by simpa using hlen
      have hcons := aux_avail_cons r rs c cs
      rw [hcons] at h0
      have hhead : (if c then (0:Nat) else if 0 < r then 1 else 0) = 0 := by omega
      have htail : (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum = 0 := by omega
      cases c with
      | true =>
        have hstep := aux_step_true r rs cs start best
        rw [hstep]
        exact ih cs (start+1) best hlen1 htail
      | false =>
        have hr0 : r = 0 := by simp at hhead; omega
        subst hr0
        have hstep := aux_step_false_zero rs cs start best
        rw [hstep]
        exact ih cs (start+1) best hlen1 htail

theorem aux_nil_avail (mask : List Bool) :
    (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) ([] : List Nat) mask).sum = 0 := by
  cases mask with
  | nil => simp
  | cons hd tl => simp

theorem aux_get_succ (c : Bool) (cs : List Bool) (k : Nat) :
    ((c :: cs)[k+1]? = cs[k]?) := by simp

theorem aux_get_succ_nat (r : Nat) (rs : List Nat) (k : Nat) :
    ((r :: rs)[k+1]? = rs[k]?) := by simp

theorem aux_beq_true (r : Nat) (h : (r == 0) = true) : r = 0 := (beq_iff_eq.mp h)

theorem aux_beq_false (r : Nat) (h : (r == 0) = false) : r ≠ 0 := ne_of_beq_false h

theorem aux_step_false_pos (r : Nat) (rs : List Nat) (cs : List Bool) (start : Nat) (best : Option (Nat × Nat))
    (hbeq : (r == 0) = false) :
    findMaxAux (r :: rs) (false :: cs) start best =
    findMaxAux rs cs (start+1)
      (match best with | none => some (start, r) | some (bi, br) => if br < r then some (start, r) else some (bi, br)) := by
  simp [findMaxAux, hbeq]

theorem aux_head_true (r : Nat) : ((if (true:Bool) then (0:Nat) else if 0 < r then 1 else 0) = 0) := by simp

theorem aux_head_false_zero : ((if (false:Bool) then (0:Nat) else if 0 < (0:Nat) then 1 else 0) = 0) := by simp

theorem aux_avail_true_tail2 (r : Nat) (rs : List Nat) (cs : List Bool)
    (h : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (r :: rs) (true :: cs)).sum) :
    0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum := by
  have hcons := aux_avail_cons r rs true cs
  have hhead : (if (true:Bool) then (0:Nat) else if 0 < r then 1 else 0) = 0 := by simp
  -- need to connect hhead to the if inside hcons; the head term in hcons is same
  rw [hcons] at h
  simp at h
  exact h

theorem aux_avail_false_zero_tail2 (rs : List Nat) (cs : List Bool)
    (h : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (0 :: rs) (false :: cs)).sum) :
    0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum := by
  have hcons := aux_avail_cons 0 rs false cs
  rw [hcons] at h
  simp at h
  exact h

theorem aux_avail_true_tail3 (r : Nat) (rs : List Nat) (cs : List Bool)
    (h : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (r :: rs) (true :: cs)).sum) :
    0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum := by
  have hcons := aux_avail_cons r rs true cs
  rw [hcons] at h
  simp at h
  exact h

theorem aux_step_false_pos_none (r : Nat) (rs : List Nat) (cs : List Bool) (start : Nat)
    (hbeq : (r == 0) = false) :
    findMaxAux (r :: rs) (false :: cs) start none =
    findMaxAux rs cs (start+1) (some (start, r)) := by
  simp [findMaxAux, hbeq]

theorem aux_step_false_pos_some (r : Nat) (rs : List Nat) (cs : List Bool) (start : Nat)
    (bi br : Nat)
    (hbeq : (r == 0) = false) :
    findMaxAux (r :: rs) (false :: cs) start (some (bi, br)) =
    findMaxAux rs cs (start+1) (if br < r then some (start, r) else some (bi, br)) := by
  simp [findMaxAux, hbeq]

theorem plan2_mask_count_add_of_false (mask : List Bool) (idx : Nat)
    (h : mask[idx]? = some false) :
    ((mask.set idx true).map (fun b => if b then (1 : Nat) else 0)).sum =
      (mask.map (fun b => if b then (1 : Nat) else 0)).sum + 1 :=
  aux_mask_count_final2 mask idx h

theorem plan2_available_sum_set_true (rems : List Nat) (mask : List Bool)
    (idx : Nat) (val : Nat)
    (hlen : mask.length = rems.length)
    (hmask : mask[idx]? = some false)
    (hrem : rems[idx]? = some val)
    (hval : 0 < val) :
    (List.zipWith
      (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems (mask.set idx true)).sum + 1 =
      (List.zipWith
        (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
        rems mask).sum := by
  induction rems generalizing mask idx val with
  | nil =>
    simp at hrem
  | cons r rs ih =>
    match mask with
    | [] => simp at hlen
    | m :: ms =>
      have hlen' : ms.length = rs.length := by simpa using hlen
      cases idx with
      | zero =>
        have hm : m = false := by simpa using hmask
        have hr : r = val := by simpa using hrem
        subst hm
        rw [hr]
        have hif : (if 0 < val then (1:Nat) else 0) = 1 := if_pos hval
        have hset0 : (false :: ms).set 0 true = true :: ms := by simp
        rw [hset0]
        have hz1 : List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (val :: rs) (true :: ms) =
          (0:Nat) :: List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs ms := rfl
        have hz2 : List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (val :: rs) (false :: ms) =
          (if 0 < val then (1:Nat) else 0) :: List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs ms := rfl
        rw [hz1, hz2, hif]
        simp only [List.sum_cons]
        omega
      | succ n =>
        have hmask' : ms[n]? = some false := by simpa using hmask
        have hrem' : rs[n]? = some val := by simpa using hrem
        have ihh := ih (mask := ms) (idx := n) (val := val) hlen' hmask' hrem' hval
        have hset : (m :: ms).set (n + 1) true = m :: ms.set n true := by
          cases n with | zero => simp | succ k => simp
        rw [hset]
        have hz1 : List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (r :: rs) (m :: ms.set n true) =
          (if m then (0:Nat) else if 0 < r then 1 else 0) :: List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs (ms.set n true) := rfl
        have hz2 : List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (r :: rs) (m :: ms) =
          (if m then (0:Nat) else if 0 < r then 1 else 0) :: List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs ms := rfl
        rw [hz1, hz2]
        simp only [List.sum_cons] at ihh ⊢
        omega

theorem plan1_chooseIter_step_properties (rems : List Nat) (mask : List Bool)
    (hlen : mask.length = rems.length)
    (h : 0 < (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0) rems mask).sum) :
    ∃ idx val, findMaxAux rems mask 0 none = some (idx, val) ∧
      mask[idx]? = some false ∧ 0 < val ∧
      ((mask.set idx true).map (fun b => if b then (1 : Nat) else 0)).sum =
        (mask.map (fun b => if b then (1 : Nat) else 0)).sum + 1 ∧
      (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
        rems (mask.set idx true)).sum + 1 =
        (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0) rems mask).sum := by
  obtain ⟨idx, val, hfind, hmask, hrem, hpos⟩ := plan2_findMaxAux_zero rems mask hlen h
  refine ⟨idx, val, hfind, hmask, hpos, ?_, ?_⟩
  · exact plan2_mask_count_add_of_false mask idx hmask
  · exact plan2_available_sum_set_true rems mask idx val hlen hmask hrem hpos

theorem plan1_chooseIter_mask_sum_add (rems : List Nat) (mask : List Bool) (k : Nat)
    (hlen : mask.length = rems.length)
    (hk : k ≤ (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0) rems mask).sum) :
    ((chooseIter rems mask k).map (fun b => if b then (1 : Nat) else 0)).sum =
      (mask.map (fun b => if b then (1 : Nat) else 0)).sum + k := by
  induction k generalizing mask with
  | zero =>
    simp [chooseIter]
  | succ k ih =>
    have hpos : 0 < (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0) rems mask).sum := by omega
    obtain ⟨idx, val, hfind, _hmask, _hpos, hcount, havail⟩ :=
      plan1_chooseIter_step_properties rems mask hlen hpos
    have hstep : chooseIter rems mask (k + 1) = chooseIter rems (mask.set idx true) k := by
      simp only [chooseIter, hfind]
    rw [hstep]
    have hlen' : (mask.set idx true).length = rems.length := by
      simp [hlen]
    have hk' : k ≤ (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0) rems (mask.set idx true)).sum := by omega
    have hih := ih (mask.set idx true) hlen' hk'
    omega

theorem plan1_zipWith_share_sum_aux2 (floors : List Nat) (mask : List Bool)
    (hlen : mask.length = floors.length) :
    (List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0) floors mask).sum =
      (floors.sum : Int) + ((mask.map (fun b => if b then (1 : Nat) else 0)).sum : Int) := by
  induction floors generalizing mask with
  | nil =>
    cases mask with
    | nil => simp
    | cons hd tl => simp at hlen
  | cons f fs ih =>
    cases mask with
    | nil => simp at hlen
    | cons m ms =>
      have hlen' : ms.length = fs.length := by simpa using hlen
      have ihh := ih ms hlen'
      simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons, List.sum_cons, List.sum_cons]
      rw [ihh]
      cases m <;> simp <;> push_cast <;> omega

theorem plan1_zipWith_share_sum (floors : List Nat) (mask : List Bool)
    (hlen : mask.length = floors.length) :
    (List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0) floors mask).sum =
      (floors.sum : Int) + ((mask.map (fun b => if b then (1 : Nat) else 0)).sum : Int) :=
  plan1_zipWith_share_sum_aux2 floors mask hlen

theorem avail_eq_map_sum_aux2 (rems : List Nat) :
    (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems (List.replicate rems.length false)).sum =
    ((rems.map (fun r => if 0 < r then (1 : Nat) else 0))).sum := by
  induction rems with
  | nil => simp
  | cons r rs ih =>
    simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.map_cons, List.sum_cons]
    rw [ih]
    simp only [Bool.false_eq_true, ↓reduceIte]

theorem sum_le_avail_mul_aux2 (rems : List Nat) (S : Nat)
    (h : ∀ r ∈ rems, r < S) :
    rems.sum ≤ ((rems.map (fun r => if 0 < r then (1 : Nat) else 0))).sum * S := by
  induction rems with
  | nil => simp
  | cons r rs ih =>
    have hr : r < S := h r (by simp)
    have htail : ∀ x ∈ rs, x < S := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ihh := ih htail
    simp only [List.sum_cons, List.map_cons, List.sum_cons]
    by_cases hr0 : 0 < r
    · simp only [hr0, ↓reduceIte]
      have h1 : r ≤ S := Nat.le_of_lt hr
      have h2 : r + rs.sum ≤ S + ((rs.map (fun r => if 0 < r then 1 else 0)).sum * S) := Nat.add_le_add h1 ihh
      have h3 : S + ((rs.map (fun r => if 0 < r then 1 else 0)).sum * S) = (1 + (rs.map (fun r => if 0 < r then 1 else 0)).sum) * S := by rw [Nat.add_mul, Nat.one_mul]
      omega
    · have hr00 : r = 0 := Nat.eq_zero_of_not_pos hr0
      subst hr00
      simp only [hr0, ↓reduceIte, Nat.zero_add]
      exact ihh

theorem k_mul_eq_rem_sum_aux2 (A : Nat) (ratios : List Nat) (hS : 0 < ratios.sum) :
    (A - (ratios.map (fun r => (A * r) / ratios.sum)).sum) * ratios.sum =
      (ratios.map (fun r => (A * r) % ratios.sum)).sum := by
  have hdiv := divmod_sum_lemma2 A ratios.sum ratios
  have hFle := floors_sum_le_of_sum_eq2 A ratios hS
  have hA : A = (ratios.map (fun r => (A * r) / ratios.sum)).sum + (A - (ratios.map (fun r => (A * r) / ratios.sum)).sum) := by
    omega
  have hAS : A * ratios.sum =
      ((ratios.map (fun r => (A * r) / ratios.sum)).sum + (A - (ratios.map (fun r => (A * r) / ratios.sum)).sum)) * ratios.sum := by
    rw [← hA]
  have hadd : ((ratios.map (fun r => (A * r) / ratios.sum)).sum + (A - (ratios.map (fun r => (A * r) / ratios.sum)).sum)) * ratios.sum =
      (ratios.map (fun r => (A * r) / ratios.sum)).sum * ratios.sum +
      (A - (ratios.map (fun r => (A * r) / ratios.sum)).sum) * ratios.sum := Nat.add_mul _ _ _
  rw [hadd] at hAS
  omega

theorem plan1_k_le_available_initial (A : Nat) (ratios : List Nat) (hS : 0 < ratios.sum) :
    A - (ratios.map (fun r => (A * r) / ratios.sum)).sum ≤
      (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
        (ratios.map (fun r => (A * r) % ratios.sum))
        (List.replicate (ratios.map (fun r => (A * r) % ratios.sum)).length false)).sum := by
  have hrewrite := avail_eq_map_sum_aux2 (ratios.map (fun r => (A * r) % ratios.sum))
  rw [hrewrite]
  have hbound : (ratios.map (fun r => (A * r) % ratios.sum)).sum ≤
      ((ratios.map (fun r => (A * r) % ratios.sum)).map (fun r => if 0 < r then (1 : Nat) else 0)).sum * ratios.sum := by
    apply sum_le_avail_mul_aux2 _ ratios.sum
    intro r hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
    exact Nat.mod_lt _ hS
  have hkS := k_mul_eq_rem_sum_aux2 A ratios hS
  rw [← hkS] at hbound
  exact Nat.le_of_mul_le_mul_right hbound hS

theorem plan1_proof_aux_init_sum (A : Nat) (ratios : List Nat) :
    (((List.replicate (List.map (fun r => A * r % ratios.sum) ratios).length false).map (fun b => if b then (1:Nat) else 0)).sum = 0) := by simp

theorem my_cast_test (x y : Nat) : ((x + y : Nat) : Int) = (x : Int) + (y : Int) := by push_cast; rfl

theorem cast_probe (x y : Nat) : (((x + y : Nat) : Int) = (x : Int) + (y : Int)) := by simp

theorem mask_sum_cast3 (mask : List Bool) :
    (((mask.map (fun b => if b then (1:Nat) else 0)).sum : Nat) : Int) =
    (mask.map (fun b => if b then (1:Int) else 0)).sum := by
  induction mask with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    cases hd <;> simp_all

theorem plan3_findMaxAux_general (rems : List Nat) (mask : List Bool)
    (start : Nat) (best : Option (Nat × Nat))
    (hlen : mask.length = rems.length)
    (h : 0 < (List.zipWith
      (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems mask).sum) :
    ∃ idx val, findMaxAux rems mask start best = some (idx, val) ∧
      0 < val ∧
      ((∃ bi br, best = some (bi, br) ∧ idx = bi ∧ val = br) ∨
       (∃ rel, idx = start + rel ∧ rel < mask.length ∧
         mask[rel]? = some false ∧ rems[rel]? = some val)) := by
  induction rems generalizing mask start best with
  | nil =>
    cases mask with
    | nil => simp at h
    | cons hd tl => simp at hlen
  | cons r rs ih =>
    cases mask with
    | nil => simp at hlen
    | cons c cs =>
      have hlen1 : cs.length = rs.length := by simpa using hlen
      have hcons := aux_avail_cons r rs c cs
      cases c with
      | true =>
        have htail : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum := by
          rw [hcons] at h; simp at h; exact h
        have hstep : findMaxAux (r :: rs) (true :: cs) start best = findMaxAux rs cs (start + 1) best :=
          aux_step_true r rs cs start best
        obtain ⟨idx, val, hfind, hpos, hcase⟩ := ih cs (start+1) best hlen1 htail
        refine ⟨idx, val, by rw [hstep]; exact hfind, hpos, ?_⟩
        rcases hcase with ⟨bb1, bb2, hb, hidx, hval⟩ | ⟨rel, hidx, hlt, hmask, hrem⟩
        · exact Or.inl ⟨bb1, bb2, hb, hidx, hval⟩
        · apply Or.inr
          refine ⟨rel + 1, by omega, by simp; omega, ?_, ?_⟩
          · have h2 : ((true :: cs)[rel + 1]? = cs[rel]?) := by simp
            rw [h2]; exact hmask
          · have h2 : ((r :: rs)[rel + 1]? = rs[rel]?) := by simp
            rw [h2]; exact hrem
      | false =>
        by_cases hr0 : r = 0
        · subst hr0
          have htail : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum := by
            have hcons0 := aux_avail_cons 0 rs false cs
            rw [hcons0] at h; simp at h; exact h
          have hstep : findMaxAux (0 :: rs) (false :: cs) start best = findMaxAux rs cs (start + 1) best :=
            aux_step_false_zero rs cs start best
          obtain ⟨idx, val, hfind, hpos, hcase⟩ := ih cs (start+1) best hlen1 htail
          refine ⟨idx, val, by rw [hstep]; exact hfind, hpos, ?_⟩
          rcases hcase with ⟨bb1, bb2, hb, hidx, hval⟩ | ⟨rel, hidx, hlt, hmask, hrem⟩
          · exact Or.inl ⟨bb1, bb2, hb, hidx, hval⟩
          · apply Or.inr
            refine ⟨rel + 1, by omega, by simp; omega, ?_, ?_⟩
            · have h2 : ((false :: cs)[rel + 1]? = cs[rel]?) := by simp
              rw [h2]; exact hmask
            · have h2 : ((0 :: rs)[rel + 1]? = rs[rel]?) := by simp
              rw [h2]; exact hrem
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
          have hbeq : (r == 0) = false := by simp [hr0]
          cases best with
          | none =>
            have hstep : findMaxAux (r :: rs) (false :: cs) start none =
                findMaxAux rs cs (start + 1) (some (start, r)) := by
              simp [findMaxAux, hbeq]
            by_cases htail0 : (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum = 0
            · have hfin : findMaxAux rs cs (start+1) (some (start, r)) = some (start, r) :=
                aux_findMaxAux_eq_best_of_avail_zero3 rs cs (start+1) (some (start, r)) hlen1 htail0
              refine ⟨start, r, by rw [hstep, hfin], hrpos, ?_⟩
              apply Or.inr
              exact ⟨0, by omega, by simp, by simp, by simp⟩
            · have htail : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum :=
                Nat.pos_of_ne_zero htail0
              obtain ⟨idx, val, hfind, hpos, hcase⟩ := ih cs (start+1) (some (start, r)) hlen1 htail
              have hfound : findMaxAux (r :: rs) (false :: cs) start none = some (idx, val) := by
                rw [hstep]; exact hfind
              refine ⟨idx, val, hfound, hpos, ?_⟩
              rcases hcase with ⟨bb1, bb2, hb, hidx, hval⟩ | ⟨rel, hidx, hlt, hmask, hrem⟩
              · simp at hb
                obtain ⟨rfl, rfl⟩ := hb
                rw [hidx, hval]
                apply Or.inr
                exact ⟨0, by omega, by simp, by simp, by simp⟩
              · apply Or.inr
                refine ⟨rel + 1, by omega, by simp; omega, ?_, ?_⟩
                · have h2 : ((false :: cs)[rel + 1]? = cs[rel]?) := by simp
                  rw [h2]; exact hmask
                · have h2 : ((r :: rs)[rel + 1]? = rs[rel]?) := by simp
                  rw [h2]; exact hrem
          | some pr =>
            obtain ⟨bi, br⟩ := pr
            have hstep : findMaxAux (r :: rs) (false :: cs) start (some (bi, br)) =
                findMaxAux rs cs (start + 1) (if br < r then some (start, r) else some (bi, br)) := by
              simp [findMaxAux, hbeq]
            by_cases hbr : br < r
            · have hif : (if br < r then some (start, r) else some (bi, br)) = some (start, r) := by simp [hbr]
              rw [hif] at hstep
              by_cases htail0 : (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum = 0
              · have hfin : findMaxAux rs cs (start+1) (some (start, r)) = some (start, r) :=
                  aux_findMaxAux_eq_best_of_avail_zero3 rs cs (start+1) (some (start, r)) hlen1 htail0
                refine ⟨start, r, by rw [hstep, hfin], hrpos, ?_⟩
                apply Or.inr
                exact ⟨0, by omega, by simp, by simp, by simp⟩
              · have htail : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum :=
                  Nat.pos_of_ne_zero htail0
                obtain ⟨idx, val, hfind, hpos, hcase⟩ := ih cs (start+1) (some (start, r)) hlen1 htail
                have hfound : findMaxAux (r :: rs) (false :: cs) start (some (bi, br)) = some (idx, val) := by
                  rw [hstep]; exact hfind
                refine ⟨idx, val, hfound, hpos, ?_⟩
                rcases hcase with ⟨bb1, bb2, hb, hidx, hval⟩ | ⟨rel, hidx, hlt, hmask, hrem⟩
                · simp at hb
                  obtain ⟨rfl, rfl⟩ := hb
                  rw [hidx, hval]
                  apply Or.inr
                  exact ⟨0, by omega, by simp, by simp, by simp⟩
                · apply Or.inr
                  refine ⟨rel + 1, by omega, by simp; omega, ?_, ?_⟩
                  · have h2 : ((false :: cs)[rel + 1]? = cs[rel]?) := by simp
                    rw [h2]; exact hmask
                  · have h2 : ((r :: rs)[rel + 1]? = rs[rel]?) := by simp
                    rw [h2]; exact hrem
            · have hif : (if br < r then some (start, r) else some (bi, br)) = some (bi, br) := by simp [hbr]
              rw [hif] at hstep
              by_cases htail0 : (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum = 0
              · have hfin : findMaxAux rs cs (start+1) (some (bi, br)) = some (bi, br) :=
                  aux_findMaxAux_eq_best_of_avail_zero3 rs cs (start+1) (some (bi, br)) hlen1 htail0
                have hbrpos : 0 < br := by omega
                refine ⟨bi, br, by rw [hstep, hfin], hbrpos, ?_⟩
                exact Or.inl ⟨bi, br, rfl, rfl, rfl⟩
              · have htail : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum :=
                  Nat.pos_of_ne_zero htail0
                obtain ⟨idx, val, hfind, hpos, hcase⟩ := ih cs (start+1) (some (bi, br)) hlen1 htail
                have hfound : findMaxAux (r :: rs) (false :: cs) start (some (bi, br)) = some (idx, val) := by
                  rw [hstep]; exact hfind
                refine ⟨idx, val, hfound, hpos, ?_⟩
                rcases hcase with ⟨bb1, bb2, hb, hidx, hval⟩ | ⟨rel, hidx, hlt, hmask, hrem⟩
                · exact Or.inl ⟨bb1, bb2, hb, hidx, hval⟩
                · apply Or.inr
                  refine ⟨rel + 1, by omega, by simp; omega, ?_, ?_⟩
                  · have h2 : ((false :: cs)[rel + 1]? = cs[rel]?) := by simp
                    rw [h2]; exact hmask
                  · have h2 : ((r :: rs)[rel + 1]? = rs[rel]?) := by simp
                    rw [h2]; exact hrem


theorem plan3_mask_count_set_true (mask : List Bool) (idx : Nat)
    (h : mask[idx]? = some false) :
    ((mask.set idx true).map (fun b => if b then (1 : Nat) else 0)).sum =
      (mask.map (fun b => if b then (1 : Nat) else 0)).sum + 1 :=
  aux_mask_count_final2 mask idx h










theorem plan3_findMaxAux_general_proof4 (rems : List Nat) (mask : List Bool)
    (start : Nat) (best : Option (Nat × Nat))
    (hlen : mask.length = rems.length)
    (h : 0 < (List.zipWith
      (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems mask).sum) :
    ∃ idx val, findMaxAux rems mask start best = some (idx, val) ∧
      0 < val ∧
      ((∃ bi br, best = some (bi, br) ∧ idx = bi ∧ val = br) ∨
       (∃ rel, idx = start + rel ∧ rel < mask.length ∧
         mask[rel]? = some false ∧ rems[rel]? = some val)) := by
  induction rems generalizing mask start best with
  | nil =>
    cases mask with
    | nil => simp at h
    | cons hd tl => simp at hlen
  | cons r rs ih =>
    cases mask with
    | nil => simp at hlen
    | cons c cs =>
      have hlen1 : cs.length = rs.length := by simpa using hlen
      have hcons := aux_avail_cons r rs c cs
      cases c with
      | true =>
        have htail : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum := by
          rw [hcons] at h; simp at h; exact h
        have hstep : findMaxAux (r :: rs) (true :: cs) start best = findMaxAux rs cs (start + 1) best :=
          aux_step_true r rs cs start best
        obtain ⟨idx, val, hfind, hpos, hcase⟩ := ih cs (start+1) best hlen1 htail
        refine ⟨idx, val, by rw [hstep]; exact hfind, hpos, ?_⟩
        rcases hcase with ⟨bb1, bb2, hb, hidx, hval⟩ | ⟨rel, hidx, hlt, hmask, hrem⟩
        · exact Or.inl ⟨bb1, bb2, hb, hidx, hval⟩
        · apply Or.inr
          refine ⟨rel + 1, by omega, by simp; omega, ?_, ?_⟩
          · have h2 : ((true :: cs)[rel + 1]? = cs[rel]?) := by simp
            rw [h2]; exact hmask
          · have h2 : ((r :: rs)[rel + 1]? = rs[rel]?) := by simp
            rw [h2]; exact hrem
      | false =>
        by_cases hr0 : r = 0
        · subst hr0
          have htail : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum := by
            have hcons0 := aux_avail_cons 0 rs false cs
            rw [hcons0] at h; simp at h; exact h
          have hstep : findMaxAux (0 :: rs) (false :: cs) start best = findMaxAux rs cs (start + 1) best :=
            aux_step_false_zero rs cs start best
          obtain ⟨idx, val, hfind, hpos, hcase⟩ := ih cs (start+1) best hlen1 htail
          refine ⟨idx, val, by rw [hstep]; exact hfind, hpos, ?_⟩
          rcases hcase with ⟨bb1, bb2, hb, hidx, hval⟩ | ⟨rel, hidx, hlt, hmask, hrem⟩
          · exact Or.inl ⟨bb1, bb2, hb, hidx, hval⟩
          · apply Or.inr
            refine ⟨rel + 1, by omega, by simp; omega, ?_, ?_⟩
            · have h2 : ((false :: cs)[rel + 1]? = cs[rel]?) := by simp
              rw [h2]; exact hmask
            · have h2 : ((0 :: rs)[rel + 1]? = rs[rel]?) := by simp
              rw [h2]; exact hrem
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
          have hbeq : (r == 0) = false := by simp [hr0]
          cases best with
          | none =>
            have hstep : findMaxAux (r :: rs) (false :: cs) start none =
                findMaxAux rs cs (start + 1) (some (start, r)) := by
              simp [findMaxAux, hbeq]
            by_cases htail0 : (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum = 0
            · have hfin : findMaxAux rs cs (start+1) (some (start, r)) = some (start, r) :=
                aux_findMaxAux_eq_best_of_avail_zero3 rs cs (start+1) (some (start, r)) hlen1 htail0
              refine ⟨start, r, by rw [hstep, hfin], hrpos, ?_⟩
              apply Or.inr
              exact ⟨0, by omega, by simp, by simp, by simp⟩
            · have htail : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum :=
                Nat.pos_of_ne_zero htail0
              obtain ⟨idx, val, hfind, hpos, hcase⟩ := ih cs (start+1) (some (start, r)) hlen1 htail
              have hfound : findMaxAux (r :: rs) (false :: cs) start none = some (idx, val) := by
                rw [hstep]; exact hfind
              refine ⟨idx, val, hfound, hpos, ?_⟩
              rcases hcase with ⟨bb1, bb2, hb, hidx, hval⟩ | ⟨rel, hidx, hlt, hmask, hrem⟩
              · simp at hb
                obtain ⟨rfl, rfl⟩ := hb
                rw [hidx, hval]
                apply Or.inr
                exact ⟨0, by omega, by simp, by simp, by simp⟩
              · apply Or.inr
                refine ⟨rel + 1, by omega, by simp; omega, ?_, ?_⟩
                · have h2 : ((false :: cs)[rel + 1]? = cs[rel]?) := by simp
                  rw [h2]; exact hmask
                · have h2 : ((r :: rs)[rel + 1]? = rs[rel]?) := by simp
                  rw [h2]; exact hrem
          | some pr =>
            obtain ⟨bi, br⟩ := pr
            have hstep : findMaxAux (r :: rs) (false :: cs) start (some (bi, br)) =
                findMaxAux rs cs (start + 1) (if br < r then some (start, r) else some (bi, br)) := by
              simp [findMaxAux, hbeq]
            by_cases hbr : br < r
            · have hif : (if br < r then some (start, r) else some (bi, br)) = some (start, r) := by simp [hbr]
              rw [hif] at hstep
              by_cases htail0 : (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum = 0
              · have hfin : findMaxAux rs cs (start+1) (some (start, r)) = some (start, r) :=
                  aux_findMaxAux_eq_best_of_avail_zero3 rs cs (start+1) (some (start, r)) hlen1 htail0
                refine ⟨start, r, by rw [hstep, hfin], hrpos, ?_⟩
                apply Or.inr
                exact ⟨0, by omega, by simp, by simp, by simp⟩
              · have htail : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum :=
                  Nat.pos_of_ne_zero htail0
                obtain ⟨idx, val, hfind, hpos, hcase⟩ := ih cs (start+1) (some (start, r)) hlen1 htail
                have hfound : findMaxAux (r :: rs) (false :: cs) start (some (bi, br)) = some (idx, val) := by
                  rw [hstep]; exact hfind
                refine ⟨idx, val, hfound, hpos, ?_⟩
                rcases hcase with ⟨bb1, bb2, hb, hidx, hval⟩ | ⟨rel, hidx, hlt, hmask, hrem⟩
                · simp at hb
                  obtain ⟨rfl, rfl⟩ := hb
                  rw [hidx, hval]
                  apply Or.inr
                  exact ⟨0, by omega, by simp, by simp, by simp⟩
                · apply Or.inr
                  refine ⟨rel + 1, by omega, by simp; omega, ?_, ?_⟩
                  · have h2 : ((false :: cs)[rel + 1]? = cs[rel]?) := by simp
                    rw [h2]; exact hmask
                  · have h2 : ((r :: rs)[rel + 1]? = rs[rel]?) := by simp
                    rw [h2]; exact hrem
            · have hif : (if br < r then some (start, r) else some (bi, br)) = some (bi, br) := by simp [hbr]
              rw [hif] at hstep
              by_cases htail0 : (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum = 0
              · have hfin : findMaxAux rs cs (start+1) (some (bi, br)) = some (bi, br) :=
                  aux_findMaxAux_eq_best_of_avail_zero3 rs cs (start+1) (some (bi, br)) hlen1 htail0
                have hbrpos : 0 < br := by omega
                refine ⟨bi, br, by rw [hstep, hfin], hbrpos, ?_⟩
                exact Or.inl ⟨bi, br, rfl, rfl, rfl⟩
              · have htail : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum :=
                  Nat.pos_of_ne_zero htail0
                obtain ⟨idx, val, hfind, hpos, hcase⟩ := ih cs (start+1) (some (bi, br)) hlen1 htail
                have hfound : findMaxAux (r :: rs) (false :: cs) start (some (bi, br)) = some (idx, val) := by
                  rw [hstep]; exact hfind
                refine ⟨idx, val, hfound, hpos, ?_⟩
                rcases hcase with ⟨bb1, bb2, hb, hidx, hval⟩ | ⟨rel, hidx, hlt, hmask, hrem⟩
                · exact Or.inl ⟨bb1, bb2, hb, hidx, hval⟩
                · apply Or.inr
                  refine ⟨rel + 1, by omega, by simp; omega, ?_, ?_⟩
                  · have h2 : ((false :: cs)[rel + 1]? = cs[rel]?) := by simp
                    rw [h2]; exact hmask
                  · have h2 : ((r :: rs)[rel + 1]? = rs[rel]?) := by simp
                    rw [h2]; exact hrem

theorem tmp_plan3_mask_pf (mask : List Bool) (idx : Nat)
    (h : mask[idx]? = some false) :
    ((mask.set idx true).map (fun b => if b then (1 : Nat) else 0)).sum =
      (mask.map (fun b => if b then (1 : Nat) else 0)).sum + 1 :=
  aux_mask_count_final2 mask idx h

theorem plan3_avail_set_true (rems : List Nat) (mask : List Bool)
    (idx : Nat) (val : Nat)
    (hlen : mask.length = rems.length)
    (hmask : mask[idx]? = some false)
    (hrem : rems[idx]? = some val)
    (hval : 0 < val) :
    (List.zipWith
      (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems (mask.set idx true)).sum + 1 =
      (List.zipWith
        (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
        rems mask).sum := by
  induction rems generalizing mask idx val with
  | nil =>
    simp at hrem
  | cons r rs ih =>
    match mask with
    | [] => simp at hlen
    | m :: ms =>
      have hlen' : ms.length = rs.length := by simpa using hlen
      cases idx with
      | zero =>
        have hm : m = false := by simpa using hmask
        have hr : r = val := by simpa using hrem
        subst hm
        rw [hr]
        have hif : (if 0 < val then (1:Nat) else 0) = 1 := if_pos hval
        have hset0 : (false :: ms).set 0 true = true :: ms := by simp
        rw [hset0]
        have hz1 : List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (val :: rs) (true :: ms) =
          (0:Nat) :: List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs ms := rfl
        have hz2 : List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (val :: rs) (false :: ms) =
          (if 0 < val then (1:Nat) else 0) :: List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs ms := rfl
        rw [hz1, hz2, hif]
        simp only [List.sum_cons]
        omega
      | succ n =>
        have hmask' : ms[n]? = some false := by simpa using hmask
        have hrem' : rs[n]? = some val := by simpa using hrem
        have ihh := ih (mask := ms) (idx := n) (val := val) hlen' hmask' hrem' hval
        have hset : (m :: ms).set (n + 1) true = m :: ms.set n true := by
          cases n with | zero => simp | succ k => simp
        rw [hset]
        have hz1 : List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (r :: rs) (m :: ms.set n true) =
          (if m then (0:Nat) else if 0 < r then 1 else 0) :: List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs (ms.set n true) := rfl
        have hz2 : List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (r :: rs) (m :: ms) =
          (if m then (0:Nat) else if 0 < r then 1 else 0) :: List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs ms := rfl
        rw [hz1, hz2]
        simp only [List.sum_cons] at ihh ⊢
        omega

theorem plan3_chooseIter_count_add_aux_unique : True := trivial

theorem my_zero_aux (rems : List Nat) (mask : List Bool)
    (hlen : mask.length = rems.length)
    (h : 0 < (List.zipWith
      (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems mask).sum) :
    ∃ idx val, findMaxAux rems mask 0 none = some (idx, val) ∧
      mask[idx]? = some false ∧ rems[idx]? = some val ∧ 0 < val := by
  obtain ⟨idx, val, hfind, hpos, hcase⟩ := plan3_findMaxAux_general_proof4 rems mask 0 none hlen h
  refine ⟨idx, val, hfind, ?_, ?_, hpos⟩
  · rcases hcase with ⟨bi, br, hcontra, _, _⟩ | ⟨rel, hidx, _, hmask, hrems⟩
    · simp at hcontra
    · have : idx = rel := by omega
      rw [this]
      exact hmask
  · rcases hcase with ⟨bi, br, hcontra, _, _⟩ | ⟨rel, hidx, _, hmask, hrems⟩
    · simp at hcontra
    · have : idx = rel := by omega
      rw [this]
      exact hrems

theorem my_step_aux (rems : List Nat) (mask : List Bool)
    (hlen : mask.length = rems.length)
    (h : 0 < (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0) rems mask).sum) :
    ∃ idx val, findMaxAux rems mask 0 none = some (idx, val) ∧
      mask[idx]? = some false ∧ 0 < val ∧
      ((mask.set idx true).map (fun b => if b then (1 : Nat) else 0)).sum =
        (mask.map (fun b => if b then (1 : Nat) else 0)).sum + 1 ∧
      (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
        rems (mask.set idx true)).sum + 1 =
        (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0) rems mask).sum := by
  obtain ⟨idx, val, hfind, hmask, hrem, hpos⟩ := my_zero_aux rems mask hlen h
  refine ⟨idx, val, hfind, hmask, hpos, ?_, ?_⟩
  · exact aux_mask_count_final2 mask idx hmask
  · exact plan3_avail_set_true rems mask idx val hlen hmask hrem hpos

theorem plan3_chooseIter_count_add (rems : List Nat) (mask : List Bool) (k : Nat)
    (hlen : mask.length = rems.length)
    (hk : k ≤ (List.zipWith
      (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0)
      rems mask).sum) :
    ((chooseIter rems mask k).map (fun b => if b then (1 : Nat) else 0)).sum =
      (mask.map (fun b => if b then (1 : Nat) else 0)).sum + k := by
  induction k generalizing mask with
  | zero => simp [chooseIter]
  | succ k ih =>
    have hpos : 0 < (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0) rems mask).sum := by omega
    obtain ⟨idx, val, hfind, hmask, _hpos, hcount, havail⟩ := my_step_aux rems mask hlen hpos
    have hstep : chooseIter rems mask (k + 1) = chooseIter rems (mask.set idx true) k := by
      simp only [chooseIter, hfind]
    rw [hstep]
    have hlen' : (mask.set idx true).length = rems.length := by simp [hlen]
    have hk' : k ≤ (List.zipWith (fun r c => if c then (0 : Nat) else if 0 < r then 1 else 0) rems (mask.set idx true)).sum := by omega
    have hih := ih (mask.set idx true) hlen' hk'
    omega

theorem plan3_choose_count_initial (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    ((choose (ratios.map (fun r => (A * r) % ratios.sum))
      (A - (ratios.map (fun r => (A * r) / ratios.sum)).sum)).map
        (fun b => if b then (1 : Nat) else 0)).sum =
      A - (ratios.map (fun r => (A * r) / ratios.sum)).sum := by
  unfold choose
  have hlen : (List.replicate (List.map (fun r => A * r % ratios.sum) ratios).length false).length =
      (List.map (fun r => A * r % ratios.sum) ratios).length := by simp
  have hk := plan1_k_le_available_initial A ratios hS
  have h := plan3_chooseIter_count_add
    (ratios.map (fun r => (A * r) % ratios.sum))
    (List.replicate (List.map (fun r => A * r % ratios.sum) ratios).length false)
    (A - (ratios.map (fun r => (A * r) / ratios.sum)).sum)
    hlen hk
  have h0 := plan1_proof_aux_init_sum A ratios
  omega

theorem plan3_zipWith_share_sum_helper (floors : List Nat) (mask : List Bool)
    (hlen : mask.length = floors.length) :
    (List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0)
      floors mask).sum =
      (floors.sum : Int) +
        ((mask.map (fun b => if b then (1 : Nat) else 0)).sum : Int) :=
  plan1_zipWith_share_sum floors mask hlen

theorem plan3_zipWith_share_sum (floors : List Nat) (mask : List Bool)
    (hlen : mask.length = floors.length) :
    (List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0)
      floors mask).sum =
      (floors.sum : Int) +
        ((mask.map (fun b => if b then (1 : Nat) else 0)).sum : Int) :=
  plan1_zipWith_share_sum floors mask hlen

theorem tmp_bridge_test (A : Nat) (ratios : List Nat) (hS : 0 < ratios.sum) : True := by
  have hbridge := mask_sum_cast3 (choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum))
  have hcount := plan3_choose_count_initial A ratios hS
  have hIntEq : ((choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum)).map (fun b => if b then (1:Int) else 0)).sum = ((A - (List.map (fun r => A * r / ratios.sum) ratios).sum : Nat) : Int) := by
    rw [← hbridge, hcount]
  trivial

theorem tmp_norm_check (mask : List Bool) :
    (mask.map (fun b => if b then ((1:Nat):Int) else 0)).sum = (mask.map (fun b => if b then (1:Int) else 0)).sum := by
  induction mask with
  | nil => simp
  | cons hd tl ih => cases hd <;> simp_all

theorem tmp_plan1h (A : Nat) (ratios : List Nat) (hS : 0 < ratios.sum) :
    (allocateNonneg A ratios ratios.sum).sum = (A : Int) := by
  have hlen : (choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum)).length = (List.map (fun r => A * r / ratios.sum) ratios).length := by
    rw [plan0_choose_length]; simp
  have hzip := plan1_zipWith_share_sum (List.map (fun r => A * r / ratios.sum) ratios)
    (choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum)) hlen
  have hcount := plan3_choose_count_initial A ratios hS
  have hbridge := mask_sum_cast3 (choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum))
  have hIntEq : ((choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum)).map (fun b => if b then (1:Int) else 0)).sum = ((A - (List.map (fun r => A * r / ratios.sum) ratios).sum : Nat) : Int) := by
    rw [← hbridge, hcount]
  have hnorm := tmp_norm_check (choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum))
  have hgoal : (allocateNonneg A ratios ratios.sum).sum =
    (List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0) (List.map (fun r => A * r / ratios.sum) ratios)
      (choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum))).sum := by
    unfold allocateNonneg; simp only
  rw [hgoal, hzip, hnorm, hIntEq]
  have hNat : (List.map (fun r => A * r / ratios.sum) ratios).sum + (A - (List.map (fun r => A * r / ratios.sum) ratios).sum) = A := by
    have hle := floors_sum_le_of_sum_eq2 A ratios hS
    omega
  omega

theorem plan1_allocateNonneg_sum_eq (A : Nat) (ratios : List Nat) (hS : 0 < ratios.sum) :
    (allocateNonneg A ratios ratios.sum).sum = (A : Int) := by
  have hlen : (choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum)).length = (List.map (fun r => A * r / ratios.sum) ratios).length := by
    rw [plan0_choose_length]; simp
  have hzip := plan1_zipWith_share_sum (List.map (fun r => A * r / ratios.sum) ratios)
    (choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum)) hlen
  have hcount := plan3_choose_count_initial A ratios hS
  have hbridge := mask_sum_cast3 (choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum))
  have hIntEq : ((choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum)).map (fun b => if b then (1:Int) else 0)).sum = ((A - (List.map (fun r => A * r / ratios.sum) ratios).sum : Nat) : Int) := by
    rw [← hbridge, hcount]
  have hnorm := tmp_norm_check (choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum))
  have hgoal : (allocateNonneg A ratios ratios.sum).sum =
    (List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0) (List.map (fun r => A * r / ratios.sum) ratios)
      (choose (List.map (fun r => A * r % ratios.sum) ratios) (A - (List.map (fun r => A * r / ratios.sum) ratios).sum))).sum := by
    unfold allocateNonneg; simp only
  rw [hgoal, hzip, hnorm, hIntEq]
  have hNat : (List.map (fun r => A * r / ratios.sum) ratios).sum + (A - (List.map (fun r => A * r / ratios.sum) ratios).sum) = A := by
    have hle := floors_sum_le_of_sum_eq2 A ratios hS
    omega
  omega

theorem probe_natabs_pos (a : Int) (h : 0 ≤ a) : ((a.natAbs : Nat) : Int) = a := by
  exact Int.natAbs_of_nonneg h

theorem aux_sum_neg3 (l : List Int) : (l.map (fun x => -x)).sum = -l.sum := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem probe_natabs1 (a : Int) (h : 0 ≤ a) : ((a.natAbs : Nat) : Int) = a :=
  Int.natAbs_of_nonneg h

theorem probe_natabs2 (a : Int) (h : a < 0) : ((a.natAbs : Nat) : Int) = -a := by
  have h1 : 0 ≤ -a := by omega
  have h2 : (-a).natAbs = a.natAbs := Int.natAbs_neg a
  rw [← h2]
  exact Int.natAbs_of_nonneg h1

theorem w_q1 : True := trivial
#check @List.getElem?_map
#check @List.getElem?_zipWith
#check @List.getElem?_set
#check @List.getElem_map
#check @List.getElem_zipWith
#check @List.getElem_set

theorem w_ge_aux_base (start : Nat) (best : Option (Nat × Nat)) :
    findMaxAux [] ([] : List Bool) start best = best := by simp [findMaxAux]

theorem w_ge_step_true (r : Nat) (rs : List Nat) (c : List Bool) (start : Nat) (best : Option (Nat × Nat)) :
    findMaxAux (r :: rs) (true :: c) start best = findMaxAux rs c (start+1) best := aux_step_true r rs c start best

theorem w_avail_cons2 (r : Nat) (rs : List Nat) (c : Bool) (cs : List Bool) :
    (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) (r :: rs) (c :: cs)).sum =
    (if c then (0:Nat) else if 0 < r then 1 else 0) + (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rs cs).sum := aux_avail_cons r rs c cs













theorem plan4_chooseIter_true_rem_pos_aux_set (mask : List Bool) (idx i : Nat)
    (h : ((mask.set idx true)[i]?) = some true) :
    mask[i]? = some true ∨ i = idx := by
  have h2 := @List.getElem?_set Bool mask idx i true
  rw [h2] at h
  by_cases heq : idx = i
  · exact Or.inr heq.symm
  · left
    simp [heq] at h
    exact h

theorem plan4_chooseIter_true_rem_pos_aux_get (rems : List Nat) (idx : Nat) (val : Nat)
    (hrem : rems[idx]? = some val) (hpos : 0 < val) (i : Nat) (heq : i = idx) :
    ∃ v, rems[i]? = some v ∧ 0 < v := by
  subst heq
  exact ⟨val, hrem, hpos⟩

theorem plan4_findMax_some_props (rems : List Nat) (mask : List Bool)
    (hlen : mask.length = rems.length)
    (idx val : Nat)
    (hfind : findMaxAux rems mask 0 none = some (idx, val)) :
    mask[idx]? = some false ∧ rems[idx]? = some val ∧ 0 < val := by
  have hne : (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rems mask).sum ≠ 0 := by
    intro h0
    have hbest := aux_findMaxAux_eq_best_of_avail_zero3 rems mask 0 none hlen h0
    rw [hfind] at hbest
    simp at hbest
  have hpos : 0 < (List.zipWith (fun r c => if c then (0:Nat) else if 0 < r then 1 else 0) rems mask).sum :=
    Nat.pos_of_ne_zero hne
  obtain ⟨j, w, hjfind, hwpos, hcase⟩ := plan3_findMaxAux_general_proof4 rems mask 0 none hlen hpos
  have h2 : some (idx, val) = some (j, w) := by rw [← hfind, hjfind]
  have heq : (idx, val) = (j, w) := Option.some_inj.mp h2
  have hidx : idx = j := congrArg Prod.fst heq
  have hval : val = w := congrArg Prod.snd heq
  rcases hcase with ⟨bi, br, hcontra, _, _⟩ | ⟨rel, hidx2, _hlt, hmask, hrem⟩
  · simp at hcontra
  · have hrel : j = rel := by omega
    have hidxrel : idx = rel := hidx.trans hrel
    have hmask' : mask[idx]? = some false := by rw [hidxrel]; exact hmask
    have hrem' : rems[idx]? = some val := by rw [hidxrel, hval]; exact hrem
    have hwpos' : 0 < val := by rw [hval]; exact hwpos
    exact ⟨hmask', hrem', hwpos'⟩

theorem probe_choose_step (rems : List Nat) (mask : List Bool) (k : Nat) :
    chooseIter rems mask (k+1) =
      match findMaxAux rems mask 0 none with
      | none => mask
      | some (idx, _) => chooseIter rems (mask.set idx true) k := by
  rw [chooseIter.eq_2]
#check @chooseIter.eq_1
#check @chooseIter.eq_2

theorem plan4_chooseIter_true_rem_pos (rems : List Nat) (mask : List Bool) (k : Nat)
    (i : Nat) (hlen : mask.length = rems.length)
    (h : (chooseIter rems mask k)[i]? = some true) :
    mask[i]? = some true ∨ ∃ v, rems[i]? = some v ∧ 0 < v := by
  induction k generalizing mask with
  | zero =>
    simp [chooseIter] at h
    exact Or.inl h
  | succ k ih =>
    rw [probe_choose_step] at h
    cases hfind : findMaxAux rems mask 0 none with
    | none =>
      simp [hfind] at h
      exact Or.inl h
    | some p =>
      obtain ⟨idx, val⟩ := p
      simp only [hfind] at h
      have hfind' : findMaxAux rems mask 0 none = some (idx, val) := hfind
      have hprops := plan4_findMax_some_props rems mask hlen idx val hfind'
      obtain ⟨hmaskF, hrem, hpos⟩ := hprops
      have hlen' : (mask.set idx true).length = rems.length := by simp [hlen]
      have hih := ih (mask.set idx true) hlen' h
      rcases hih with htrue | ⟨v, hremv, hvpos⟩
      · have h2 := plan4_chooseIter_true_rem_pos_aux_set mask idx i htrue
        rcases h2 with hleft | heq
        · exact Or.inl hleft
        · subst heq
          exact Or.inr ⟨val, hrem, hpos⟩
      · exact Or.inr ⟨v, hremv, hvpos⟩

theorem tmp_check_mem_rep : True := trivial
#check @List.mem_replicate
#check @List.getElem?_replicate
#check @List.replicate_succ

theorem tmp_rep_false_get (n : Nat) (j : Nat) : (List.replicate n (false : Bool))[j]? ≠ some true := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ]
    cases j with
    | zero => simp
    | succ j => simpa using ih j

theorem plan4_choose_true_rem_pos (rems : List Nat) (k : Nat) (i : Nat)
    (h : (choose rems k)[i]? = some true) :
    ∃ v, rems[i]? = some v ∧ 0 < v := by
  unfold choose at h
  have hlen : (List.replicate rems.length false).length = rems.length := by simp
  have hor := plan4_chooseIter_true_rem_pos rems (List.replicate rems.length false) k i hlen h
  rcases hor with hrep | hex
  · exfalso
    exact tmp_rep_false_get rems.length i hrep
  · exact hex

theorem probe_get_map (f : Nat → Nat) (l : List Nat) (i : Nat) : (l.map f)[i]? = Option.map f (l[i]?) := by simp
#check @List.getElem?_map
#check @List.getElem_map

theorem chk_zip_get : True := trivial
#check @List.getElem?_zipWith
#check @List.getElem?_map

theorem chk_map_get : True := trivial
#check @List.getElem?_map

theorem chk_names2 : True := trivial
#check List.getElem?_map
#check List.getElem?_zipWith
#check List.getElem_map
#check List.getElem_zipWith

theorem probe_list_get1 : (([1,2] : List Nat)[0]? = some 1) := by simp

theorem probe_list_get2 : (([1,2] : List Nat)[1]? = some 2) := by simp

theorem probe_list_map : (([1,2].map (· + 1))[0]? = some 2) := by simp

theorem sig_probe : True := trivial
#check @List.getElem?_map
#check @List.getElem_map
#check @List.getElem?_zipWith

theorem plan5_length_of_getElem (l : List Nat) (i : Nat) (r : Nat)
    (h : l[i]? = some r) : i < l.length := by
  induction l generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero => simp
    | succ n => simp at h ⊢; exact ih n h












theorem plan5_length_of_getElem_probe3 (l : List Nat) (i : Nat) (r : Nat)
    (h : l[i]? = some r) : i < l.length := by
  induction l generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero => simp
    | succ n => simp at h ⊢; exact ih n h

theorem plan5_map_div_getElem_aux_probeA (A S : Nat) (ratios : List Nat) (i : Nat) (r : Nat)
    (hr : ratios[i]? = some r) :
    (ratios.map (fun x => (A * x) / S))[i]? = some ((A * r) / S) := by
  have h : Option.map (fun x => (A * x) / S) (ratios[i]?) = Option.map (fun x => (A * x) / S) (some r) := by rw [hr]
  have h2 : Option.map (fun x => (A * x) / S) (ratios[i]?) = (ratios.map (fun x => (A * x) / S))[i]? := by
    simp
  rw [h2] at h
  simpa using h

theorem plan5_map_div_getElem (A S : Nat) (ratios : List Nat) (i : Nat) (r : Nat)
    (hr : ratios[i]? = some r) :
    (ratios.map (fun x => (A * x) / S))[i]? = some ((A * r) / S) := by
  have h : Option.map (fun x => (A * x) / S) (ratios[i]?) = Option.map (fun x => (A * x) / S) (some r) := by rw [hr]
  have h2 : Option.map (fun x => (A * x) / S) (ratios[i]?) = (ratios.map (fun x => (A * x) / S))[i]? := by simp
  rw [h2] at h
  simpa using h

theorem plan5_map_mod_getElem_aux_tmp (A S : Nat) (ratios : List Nat) (i : Nat) (r : Nat)
    (hr : ratios[i]? = some r) :
    (ratios.map (fun x => (A * x) % S))[i]? = some ((A * r) % S) := by
  have h : Option.map (fun x => (A * x) % S) (ratios[i]?) = Option.map (fun x => (A * x) % S) (some r) := by rw [hr]
  have h2 : Option.map (fun x => (A * x) % S) (ratios[i]?) = (ratios.map (fun x => (A * x) % S))[i]? := by simp
  rw [h2] at h
  simpa using h

theorem plan5_map_mod_getElem (A S : Nat) (ratios : List Nat) (i : Nat) (r : Nat)
    (hr : ratios[i]? = some r) :
    (ratios.map (fun x => (A * x) % S))[i]? = some ((A * r) % S) := by
  have h : Option.map (fun x => (A * x) % S) (ratios[i]?) = Option.map (fun x => (A * x) % S) (some r) := by rw [hr]
  have h2 : Option.map (fun x => (A * x) % S) (ratios[i]?) = (ratios.map (fun x => (A * x) % S))[i]? := by simp
  rw [h2] at h
  simpa using h

theorem plan5_zipWith_share_getElem (floors : List Nat) (mask : List Bool)
    (i : Nat) (f : Nat) (b : Bool)
    (hf : floors[i]? = some f) (hb : mask[i]? = some b) :
    (List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0)
      floors mask)[i]? =
      some ((f : Int) + if b then (1 : Int) else 0) := by
  induction floors generalizing mask i f b with
  | nil =>
    simp at hf
  | cons f0 fs ih =>
    match mask with
    | [] =>
      simp at hb
    | m0 :: ms =>
      cases i with
      | zero =>
        simp at hf hb ⊢
        obtain rfl := hf
        obtain rfl := hb
        rfl
      | succ n =>
        simp at hf hb ⊢
        exact ih ms n f b hf hb

theorem plan5_aux_exists2 (l : List Bool) : ∀ (j : Nat), j < l.length → ∃ b : Bool, l[j]? = some b := by
  induction l with
  | nil => intro j h; simp at h
  | cons hd tl ih =>
    intro j h
    cases j with
    | zero => exact ⟨hd, by simp⟩
    | succ n =>
      simp only [List.length_cons] at h
      have hlt : n < tl.length := by omega
      obtain ⟨b, hb⟩ := ih n hlt
      exact ⟨b, by simpa using hb⟩

theorem plan5_choose_getElem_exists (rems : List Nat) (k i : Nat)
    (hi : i < rems.length) :
    ∃ b : Bool, (choose rems k)[i]? = some b := by
  have hlen : (choose rems k).length = rems.length := plan0_choose_length rems k
  have hi2 : i < (choose rems k).length := hlen ▸ hi
  exact plan5_aux_exists2 (choose rems k) i hi2

theorem plan5_choose_true_mod_pos (A S : Nat) (ratios : List Nat) (k i : Nat)
    (r : Nat) (hr : ratios[i]? = some r)
    (h : (choose (ratios.map (fun x => (A * x) % S)) k)[i]? = some true) :
    0 < (A * r) % S := by
  obtain ⟨v, hv_get, hv_pos⟩ := plan4_choose_true_rem_pos (ratios.map (fun x => (A * x) % S)) k i h
  have hmap := plan5_map_mod_getElem A S ratios i r hr
  rw [hmap] at hv_get
  simp at hv_get
  omega

theorem probe_zip_type : True := by
  have h := @plan5_zipWith_share_getElem
  trivial

theorem probe_unfold_aux (A : Nat) (ratios : List Nat) (S : Nat) (i : Nat) (r : Nat)
    (hr : ratios[i]? = some r) : True := by
  have h1 : (ratios.map (fun x => (A * x) / S))[i]? = some ((A * r) / S) :=
    plan5_map_div_getElem A S ratios i r hr
  trivial

theorem plan4_allocateNonneg_getElem (A : Nat) (ratios : List Nat) (S : Nat)
    (i : Nat) (r : Nat) (hr : ratios[i]? = some r) :
    ∃ b : Bool, (allocateNonneg A ratios S)[i]? =
      some (((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) ∧
      (b = true → 0 < (A * r) % S) := by
  have hi : i < ratios.length :=
    plan5_length_of_getElem_probe3 ratios i r hr
  have hfloors : (ratios.map (fun x => (A * x) / S))[i]? = some ((A * r) / S) :=
    plan5_map_div_getElem A S ratios i r hr
  have hi_rems : i < (ratios.map (fun x => (A * x) % S)).length := by
    simp only [List.length_map]
    exact hi
  obtain ⟨b, Hb⟩ := plan5_choose_getElem_exists
    (ratios.map (fun x => (A * x) % S))
    (A - (ratios.map (fun x => (A * x) / S)).sum) i hi_rems
  have Hzip := plan5_zipWith_share_getElem
    (ratios.map (fun x => (A * x) / S))
    (choose (ratios.map (fun x => (A * x) % S))
      (A - (ratios.map (fun x => (A * x) / S)).sum))
    i ((A * r) / S) b hfloors Hb
  have heq : allocateNonneg A ratios S =
    List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0)
      (ratios.map (fun x => (A * x) / S))
      (choose (ratios.map (fun x => (A * x) % S))
        (A - (ratios.map (fun x => (A * x) / S)).sum)) := rfl
  rw [heq]
  exact ⟨b, Hzip, fun hbt => plan5_choose_true_mod_pos A S ratios
    (A - (ratios.map (fun x => (A * x) / S)).sum) i r hr (hbt ▸ Hb)⟩

theorem snippet_omega_check (a : Int) (h : 0 < a) : 0 ≤ a := by omega

theorem snippet_cast_add (x y : Nat) : ((x + y : Nat) : Int) = (x : Int) + (y : Int) := by simp

theorem chkA (x y : Nat) : ((x + y : Nat) : Int) = (x : Int) + (y : Int) := by
  rw [Int.natCast_add]

theorem plan6_rem_bounds_int (A S r : Nat) (hS : 0 < S) :
    0 ≤ ((A * r % S : Nat) : Int) ∧ ((A * r % S : Nat) : Int) < (S : Int) := by
  constructor
  · omega
  · have h : A * r % S < S := Nat.mod_lt _ hS
    exact_mod_cast h






theorem plan6_excess_add_one (A S r : Nat) :
    (((A * r / S : Nat) : Int) + 1) * (S : Int) - (A : Int) * (r : Int) =
      (S : Int) - ((A * r % S : Nat) : Int) := by
  have hNat : S * ((A * r) / S) + (A * r) % S = A * r := Nat.div_add_mod (A * r) S
  have hcast : ((S * ((A * r) / S) + (A * r) % S : Nat) : Int) =
      (S : Int) * ((A * r / S : Nat) : Int) + ((A * r % S : Nat) : Int) := by
    rw [Int.natCast_add, Int.natCast_mul]
  have hAr : (((A * r : Nat)) : Int) = (A : Int) * (r : Int) := by
    rw [Int.natCast_mul]
  have h2 : ((S * ((A * r) / S) + (A * r) % S : Nat) : Int) = (((A * r : Nat)) : Int) := by
    rw [hNat]
  have hdiv : ((A * r / S : Nat) : Int) * (S : Int) + ((A * r % S : Nat) : Int) =
      (A : Int) * (r : Int) := by
    have hcomm : ((A * r / S : Nat) : Int) * (S : Int) = (S : Int) * ((A * r / S : Nat) : Int) :=
      Int.mul_comm _ _
    rw [hcomm]
    rw [← hcast, h2, hAr]
  have he : ((((A * r / S : Nat) : Int) + 1) * (S : Int) = ((A * r / S : Nat) : Int) * (S : Int) + (S : Int)) := by
    rw [Int.add_mul, Int.one_mul]
  rw [he]
  omega


theorem plan6_rem_bounds_int_test (A S r : Nat) (hS : 0 < S) :
    0 ≤ ((A * r % S : Nat) : Int) ∧ ((A * r % S : Nat) : Int) < (S : Int) := by
  constructor
  · omega
  · have h : A * r % S < S := Nat.mod_lt _ hS
    exact_mod_cast h

theorem tmp_divmod_cast_probe (A S r : Nat) :
    ((S * ((A * r) / S) + (A * r) % S : Nat) : Int) = ((A * r : Nat) : Int) := by
  have h : S * ((A * r) / S) + (A * r) % S = A * r := Nat.div_add_mod (A * r) S
  rw [h]

theorem tmp_cast_add_probe (x y : Nat) : ((x + y : Nat) : Int) = (x : Int) + (y : Int) := by
  simp

theorem tmp_int_comm_probe (x y : Int) : x * y = y * x := by
  exact Int.mul_comm x y

theorem plan6_div_mod_eq_int (A S r : Nat) :
    ((A * r / S : Nat) : Int) * (S : Int) + ((A * r % S : Nat) : Int) =
      (A : Int) * (r : Int) := by
  have h : S * ((A * r) / S) + (A * r) % S = A * r := Nat.div_add_mod (A * r) S
  have hcast : ((S * ((A * r) / S) + (A * r) % S : Nat) : Int) =
      (S : Int) * ((A * r / S : Nat) : Int) + ((A * r % S : Nat) : Int) := by
    rw [Int.natCast_add, Int.natCast_mul]
  have hAr : (((A * r : Nat)) : Int) = (A : Int) * (r : Int) := by
    rw [Int.natCast_mul]
  have h2 : ((S * ((A * r) / S) + (A * r) % S : Nat) : Int) = (((A * r : Nat)) : Int) := by
    rw [h]
  rw [hcast, hAr] at h2
  have hcomm : ((A * r / S : Nat) : Int) * (S : Int) = (S : Int) * ((A * r / S : Nat) : Int) :=
    Int.mul_comm _ _
  rw [hcomm]
  exact h2

theorem tmp_add0_probe (x : Int) : x + 0 = x := by simp

theorem tmp_add0_probe2 (x : Nat) : x + 0 = x := by simp

theorem plan6_excess_add_zero (A S r : Nat) :
    (((A * r / S : Nat) : Int) + 0) * (S : Int) - (A : Int) * (r : Int) =
      -((A * r % S : Nat) : Int) := by
  have h := plan6_div_mod_eq_int A S r
  simp at h ⊢
  omega

theorem plan6_excess_add_one_proof (A S r : Nat) :
    (((A * r / S : Nat) : Int) + 1) * (S : Int) - (A : Int) * (r : Int) =
      (S : Int) - ((A * r % S : Nat) : Int) := by
  have h := plan6_div_mod_eq_int A S r
  have he : ((((A * r / S : Nat) : Int) + 1) * (S : Int) = ((A * r / S : Nat) : Int) * (S : Int) + (S : Int)) := by
    rw [Int.add_mul, Int.one_mul]
  rw [he]
  omega

theorem plan6_excess_add_one_inline (A S r : Nat) :
    (((A * r / S : Nat) : Int) + 1) * (S : Int) - (A : Int) * (r : Int) =
      (S : Int) - ((A * r % S : Nat) : Int) := by
  have hNat : S * ((A * r) / S) + (A * r) % S = A * r := Nat.div_add_mod (A * r) S
  have hcast : ((S * ((A * r) / S) + (A * r) % S : Nat) : Int) =
      (S : Int) * ((A * r / S : Nat) : Int) + ((A * r % S : Nat) : Int) := by
    rw [Int.natCast_add, Int.natCast_mul]
  have hAr : (((A * r : Nat)) : Int) = (A : Int) * (r : Int) := by
    rw [Int.natCast_mul]
  have h2 : ((S * ((A * r) / S) + (A * r) % S : Nat) : Int) = (((A * r : Nat)) : Int) := by
    rw [hNat]
  have hdiv : ((A * r / S : Nat) : Int) * (S : Int) + ((A * r % S : Nat) : Int) =
      (A : Int) * (r : Int) := by
    have hcomm : ((A * r / S : Nat) : Int) * (S : Int) = (S : Int) * ((A * r / S : Nat) : Int) :=
      Int.mul_comm _ _
    rw [hcomm]
    rw [← hcast, h2, hAr]
  have he : ((((A * r / S : Nat) : Int) + 1) * (S : Int) = ((A * r / S : Nat) : Int) * (S : Int) + (S : Int)) := by
    rw [Int.add_mul, Int.one_mul]
  rw [he]
  omega

theorem tmp_if_red1 : (if (false : Bool) then (1 : Int) else (0 : Int)) = 0 := rfl

theorem tmp_if_red2 : (if (true : Bool) then (1 : Int) else (0 : Int)) = 1 := rfl

theorem tmp_rw_if_false (A S r : Nat) :
    ((((A * r / S : Nat) : Int) + if (false : Bool) then (1 : Int) else 0) * (S : Int)
        - (A : Int) * (r : Int)) =
    ((((A * r / S : Nat) : Int) + (0 : Int)) * (S : Int)
        - (A : Int) * (r : Int)) := by
  have hif : (if (false : Bool) then (1 : Int) else (0 : Int)) = 0 := rfl
  rw [hif]

theorem tmp_cases_keep (A S r : Nat) (b : Bool) :
    ((((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) * (S : Int)
        - (A : Int) * (r : Int)) =
    ((((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) * (S : Int)
        - (A : Int) * (r : Int)) := by rfl

theorem tmp_false_rw (A S r : Nat) :
    ((((A * r / S : Nat) : Int) + if (false : Bool) then (1 : Int) else 0) * (S : Int)
        - (A : Int) * (r : Int)) =
    ((((A * r / S : Nat) : Int)) * (S : Int) - (A : Int) * (r : Int)) := by
  have hif : (if (false : Bool) then (1 : Int) else (0 : Int)) = 0 := rfl
  rw [hif]
  simp

theorem plan4_floor_succ_excess_bounds (A S r : Nat) (hS : 0 < S) (b : Bool)
    (hb : b = true → 0 < (A * r) % S) :
    -(S : Int) < (((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) * (S : Int)
        - (A : Int) * (r : Int) ∧
    (((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) * (S : Int)
        - (A : Int) * (r : Int) < (S : Int) := by
  have hdiv := plan6_div_mod_eq_int A S r
  have hrem := plan6_rem_bounds_int A S r hS
  obtain ⟨hrem_nonneg, hrem_lt⟩ := hrem
  cases b with
  | false =>
    have hif : (if (false : Bool) then (1 : Int) else (0 : Int)) = 0 := rfl
    have hgoal : ((((A * r / S : Nat) : Int) + if (false : Bool) then (1 : Int) else 0) * (S : Int)
        - (A : Int) * (r : Int)) = (((A * r / S : Nat) : Int)) * (S : Int) - (A : Int) * (r : Int) := by
      rw [hif, Int.add_zero]
    rw [hgoal]
    omega
  | true =>
    have hif : (if (true : Bool) then (1 : Int) else (0 : Int)) = 1 := rfl
    have hgoal : ((((A * r / S : Nat) : Int) + if (true : Bool) then (1 : Int) else 0) * (S : Int)
        - (A : Int) * (r : Int)) = ((((A * r / S : Nat) : Int)) * (S : Int) + (S : Int) - (A : Int) * (r : Int)) := by
      rw [hif]
      rw [Int.add_mul, Int.one_mul]
    rw [hgoal]
    have hpos : 0 < (A * r) % S := hb rfl
    have hposI : (0 : Int) < ((A * r % S : Nat) : Int) := by exact_mod_cast hpos
    omega

theorem tmp_probe2a (l : List Int) (i : Nat) (h : i < l.length) : l[i]? = some l[i] := by simp [h]
#check @List.getElem?_eq_getElem

theorem plan4_within_one_allocateNonneg_aux_test (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    WithinOneUnitOn (A : Int) ratios (allocateNonneg A ratios ratios.sum) := by
  unfold WithinOneUnitOn
  intro i hx hr
  have hr_get : ratios[i]? = some ratios[i] := by simp [hr]
  obtain ⟨b, hb_get, hb_pos⟩ := plan4_allocateNonneg_getElem A ratios ratios.sum i ratios[i] hr_get
  have hshare_get : (allocateNonneg A ratios ratios.sum)[i]? = some ((allocateNonneg A ratios ratios.sum)[i]) := by
    simp [hx]
  rw [hshare_get] at hb_get
  have hshare_eq : (allocateNonneg A ratios ratios.sum)[i] =
      (((A * ratios[i] / ratios.sum : Nat) : Int) + if b then (1 : Int) else 0) := Option.some_inj.mp hb_get
  have hb : b = true → 0 < (A * ratios[i]) % ratios.sum := hb_pos
  have hbound := plan4_floor_succ_excess_bounds A ratios.sum ratios[i] hS b hb
  unfold excess
  rw [hshare_eq]
  exact hbound

theorem plan4_within_one_allocateNonneg (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    WithinOneUnitOn (A : Int) ratios (allocateNonneg A ratios ratios.sum) := by
  unfold WithinOneUnitOn
  intro i hx hr
  have hr_get : ratios[i]? = some ratios[i] := by simp [hr]
  obtain ⟨b, hb_get, hb_pos⟩ := plan4_allocateNonneg_getElem A ratios ratios.sum i ratios[i] hr_get
  have hshare_get : (allocateNonneg A ratios ratios.sum)[i]? = some ((allocateNonneg A ratios ratios.sum)[i]) := by
    simp [hx]
  rw [hshare_get] at hb_get
  have hshare_eq : (allocateNonneg A ratios ratios.sum)[i] =
      (((A * ratios[i] / ratios.sum : Nat) : Int) + if b then (1 : Int) else 0) := Option.some_inj.mp hb_get
  have hb : b = true → 0 < (A * ratios[i]) % ratios.sum := hb_pos
  have hbound := plan4_floor_succ_excess_bounds A ratios.sum ratios[i] hS b hb
  unfold excess
  rw [hshare_eq]
  exact hbound

theorem probe_int_lemmas3 : True := trivial
#check @Int.neg_mul
#check @Int.mul_neg
#check @Int.neg_sub





theorem plan7_getElem_map_neg (l : List Int) (i : Nat)
    (hx : i < l.length) (hxm : i < (l.map (fun x => -x)).length) :
    (l.map (fun x => -x))[i] = - l[i] := by simp_all




theorem tmp_probe_neg_lemmas : True := trivial
#check @Int.neg_mul
#check @Int.mul_neg
#check @Int.neg_sub
#check @Int.sub_eq_add_neg

theorem plan7_excess_neg (A : Int) (S : Nat) (x : Int) (r : Nat) :
    excess (-A) S (-x) r = - excess A S x r := by
  unfold excess
  simp only [Int.neg_mul, Int.neg_sub]
  omega

theorem plan7_neg_bounds (S : Nat) (e : Int)
    (h1 : -(S : Int) < e) (h2 : e < (S : Int)) :
    -(S : Int) < -e ∧ -e < (S : Int) := by omega

theorem plan7_getElem_map_neg_probe (l : List Int) (i : Nat)
    (hx : i < l.length) :
    (l.map (fun x => -x))[i]'(by simpa using hx) = - l[i] := by
  simp

theorem plan7_getElem_map_neg_auxcheck (l : List Int) (i : Nat)
    (hx : i < l.length) (hxm : i < (l.map (fun x => -x)).length) :
    (l.map (fun x => -x))[i] = - l[i] := by
  simp_all

theorem plan7_withinOneUnitOn_neg (A : Int) (ratios : List Nat) (shares : List Int)
    (h : WithinOneUnitOn A ratios shares) :
    WithinOneUnitOn (-A) ratios (shares.map (fun x => -x)) := by
  unfold WithinOneUnitOn at h ⊢
  intro i hx hr
  have hlen : (shares.map (fun x => -x)).length = shares.length := by simp
  have hx0 : i < shares.length := by omega
  have hg : (shares.map (fun x => -x))[i] = -shares[i] := by simp
  have hbound := h i hx0 hr
  have hex : excess (-A) ratios.sum ((shares.map (fun x => -x))[i]) ratios[i] = - excess A ratios.sum shares[i] ratios[i] := by
    rw [hg]
    exact plan7_excess_neg A ratios.sum shares[i] ratios[i]
  rw [hex]
  exact plan7_neg_bounds ratios.sum (excess A ratios.sum shares[i] ratios[i]) hbound.1 hbound.2

theorem plan4_within_one_allocateNonneg_neg_proof (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    WithinOneUnitOn (-(A : Int)) ratios
      ((allocateNonneg A ratios ratios.sum).map (fun x => -x)) := by
  have h := plan4_within_one_allocateNonneg A ratios hS
  exact plan7_withinOneUnitOn_neg (A : Int) ratios (allocateNonneg A ratios ratios.sum) h

theorem plan4_neg_test_tmp (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    WithinOneUnitOn (-(A : Int)) ratios
      ((allocateNonneg A ratios ratios.sum).map (fun x => -x)) := by
  have h := plan4_within_one_allocateNonneg A ratios hS
  exact plan7_withinOneUnitOn_neg (A : Int) ratios (allocateNonneg A ratios ratios.sum) h

theorem plan4_neg_early_inline (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    WithinOneUnitOn (-(A : Int)) ratios
      ((allocateNonneg A ratios ratios.sum).map (fun x => -x)) := by
  have h := plan4_within_one_allocateNonneg A ratios hS
  unfold WithinOneUnitOn at h ⊢
  intro i hx hr
  have hlen : ((allocateNonneg A ratios ratios.sum).map (fun x => -x)).length =
      (allocateNonneg A ratios ratios.sum).length := by simp
  have hx0 : i < (allocateNonneg A ratios ratios.sum).length := by omega
  have hg : (((allocateNonneg A ratios ratios.sum).map (fun x => -x))[i] =
      - (allocateNonneg A ratios ratios.sum)[i]) := by simp
  have hbound := h i hx0 hr
  have hex : excess (-(A : Int)) ratios.sum
      (((allocateNonneg A ratios ratios.sum).map (fun x => -x))[i]) ratios[i]
      = - excess (A : Int) ratios.sum ((allocateNonneg A ratios ratios.sum)[i]) ratios[i] := by
    rw [hg]
    unfold excess
    simp only [Int.neg_mul, Int.neg_sub]
    omega
  rw [hex]
  omega

theorem req_within_one_unit_attempt4 : WithinOneUnit allocate := by
  intro amount ratios shares h
  unfold allocate at h
  by_cases hcond : ratios = [] ∨ ratios.sum = 0
  · simp [hcond] at h
  · simp only [hcond, ↓reduceIte] at h
    have hSne : ratios.sum ≠ 0 := fun he => hcond (Or.inr he)
    have hSpos : 0 < ratios.sum := Nat.pos_of_ne_zero hSne
    by_cases h0 : 0 ≤ amount
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      rw [← heq]
      have hA : ((amount.natAbs : Nat) : Int) = amount := Int.natAbs_of_nonneg h0
      have hW := plan4_within_one_allocateNonneg amount.natAbs ratios hSpos
      rw [hA] at hW
      exact hW
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      have hpos : 0 ≤ -amount := by omega
      have h1 : (((-amount).natAbs : Nat) : Int) = -amount := Int.natAbs_of_nonneg hpos
      have h2 : (-amount).natAbs = amount.natAbs := Int.natAbs_neg amount
      rw [h2] at h1
      have hAneg : ((amount.natAbs : Nat) : Int) = -amount := h1
      have ham' : -((amount.natAbs : Nat) : Int) = amount := by omega
      have hW := plan4_neg_early_inline amount.natAbs ratios hSpos
      rw [ham'] at hW
      rw [← heq]
      exact hW

theorem req_within_one_unit_final_inline : WithinOneUnit allocate := by
  intro amount ratios shares h
  unfold allocate at h
  by_cases hcond : ratios = [] ∨ ratios.sum = 0
  · simp [hcond] at h
  · simp only [hcond, ↓reduceIte] at h
    have hSne : ratios.sum ≠ 0 := fun he => hcond (Or.inr he)
    have hSpos : 0 < ratios.sum := Nat.pos_of_ne_zero hSne
    by_cases h0 : 0 ≤ amount
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      rw [← heq]
      have hA : ((amount.natAbs : Nat) : Int) = amount := Int.natAbs_of_nonneg h0
      have hW := plan4_within_one_allocateNonneg amount.natAbs ratios hSpos
      rw [hA] at hW
      exact hW
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      rw [← heq]
      have hW0 := plan4_within_one_allocateNonneg amount.natAbs ratios hSpos
      unfold WithinOneUnitOn at hW0 ⊢
      intro i hx hr
      have hlen : ((allocateNonneg amount.natAbs ratios ratios.sum).map (fun x => -x)).length =
          (allocateNonneg amount.natAbs ratios ratios.sum).length := by simp
      have hx0 : i < (allocateNonneg amount.natAbs ratios ratios.sum).length := by omega
      have hg : (((allocateNonneg amount.natAbs ratios ratios.sum).map (fun x => -x))[i] =
          - (allocateNonneg amount.natAbs ratios ratios.sum)[i]) := by simp
      have hbound := hW0 i hx0 hr
      have hpos : 0 ≤ -amount := by omega
      have h1 : (((-amount).natAbs : Nat) : Int) = -amount := Int.natAbs_of_nonneg hpos
      have h2 : (-amount).natAbs = amount.natAbs := Int.natAbs_neg amount
      rw [h2] at h1
      have hAneg : ((amount.natAbs : Nat) : Int) = -amount := h1
      have hex : excess amount ratios.sum
          (((allocateNonneg amount.natAbs ratios ratios.sum).map (fun x => -x))[i]) ratios[i]
          = - excess ((amount.natAbs : Nat) : Int) ratios.sum
            ((allocateNonneg amount.natAbs ratios ratios.sum)[i]) ratios[i] := by
        rw [hg, hAneg]
        unfold excess
        simp only [Int.neg_mul, Int.neg_sub]
        omega
      rw [hex]
      omega

theorem planZ_allocNonneg_zero4 (A : Nat) (ratios : List Nat) (S : Nat) (i : Nat)
    (hx : i < (allocateNonneg A ratios S).length) (hr : i < ratios.length)
    (hr0 : ratios[i] = 0) :
    (allocateNonneg A ratios S)[i] = 0 := by
  have hr_get : ratios[i]? = some ratios[i] := by simp [hr]
  obtain ⟨b, hb_get, hb_pos⟩ := plan4_allocateNonneg_getElem A ratios S i ratios[i] hr_get
  have hshare_get : (allocateNonneg A ratios S)[i]? = some ((allocateNonneg A ratios S)[i]) := by simp [hx]
  rw [hshare_get] at hb_get
  have hshare_eq : (allocateNonneg A ratios S)[i] =
      (((A * ratios[i] / S : Nat) : Int) + if b then (1 : Int) else 0) := Option.some_inj.mp hb_get
  rw [hshare_eq, hr0]
  simp only [Nat.mul_zero, Nat.zero_div, Int.natCast_zero, Int.zero_add]
  have hb_false : b = false := by
    cases b with
    | false => rfl
    | true =>
      exfalso
      have hpos := hb_pos rfl
      rw [hr0] at hpos
      simp at hpos
  simp [hb_false]

theorem sgn_nonneg_aux (floors : List Nat) (mask : List Bool) (x : Int)
    (h : x ∈ List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0) floors mask) :
    0 ≤ x := by
  induction floors generalizing mask with
  | nil =>
    cases mask with
    | nil => simp at h
    | cons hd tl => simp at h
  | cons f fs ih =>
    cases mask with
    | nil => simp at h
    | cons m ms =>
      simp only [List.zipWith_cons_cons] at h
      simp only [List.mem_cons] at h
      rcases h with rfl | htail
      · cases m <;> simp <;> omega
      · exact ih ms htail

theorem sgn_allocNonneg_nonneg (A : Nat) (ratios : List Nat) (S : Nat) (x : Int)
    (h : x ∈ allocateNonneg A ratios S) : 0 ≤ x := by
  unfold allocateNonneg at h
  simp only at h
  exact sgn_nonneg_aux _ _ x h

theorem sgn_list_sum_nonneg (l : List Int) (hnn : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.sum_cons]
    have hhd : 0 ≤ hd := hnn hd (by simp)
    have htl : 0 ≤ tl.sum := ih (fun x hx => hnn x (List.mem_cons_of_mem _ hx))
    omega

theorem sgn_sum_zero_mem_zero (l : List Int) (hsum : l.sum = 0) (hnn : ∀ x ∈ l, 0 ≤ x) (y : Int) (hy : y ∈ l) : y = 0 := by
  induction l with
  | nil => simp at hy
  | cons hd tl ih =>
    simp only [List.mem_cons] at hy
    simp only [List.sum_cons] at hsum
    have hhd : 0 ≤ hd := hnn hd (by simp)
    have htl_nn : ∀ x ∈ tl, 0 ≤ x := fun x hx => hnn x (List.mem_cons_of_mem _ hx)
    have htl_sum_nonneg : 0 ≤ tl.sum := sgn_list_sum_nonneg tl htl_nn
    have htl_sum : tl.sum = 0 := by omega
    rcases hy with rfl | hmem
    · omega
    · exact ih htl_sum htl_nn hmem

theorem sgn_neg_mem2 (l : List Int) (y : Int) (h : y ∈ l.map (fun x => -x)) : ∃ z, z ∈ l ∧ y = -z := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
  exact ⟨a, ha, rfl⟩









theorem plan8_mem_map_neg_le_zero (l : List Int) (x : Int)
    (hx : x ∈ l.map (fun y => -y)) (hnn : ∀ y ∈ l, 0 ≤ y) :
    x ≤ 0 := by
  obtain ⟨z, hz, rfl⟩ := sgn_neg_mem2 l _ hx
  have h := hnn z hz
  omega

theorem plan8_allocateNonneg_zero_mem_eq_zero (ratios : List Nat) (x : Int)
    (hS : 0 < ratios.sum) (hx : x ∈ allocateNonneg 0 ratios ratios.sum) :
    x = 0 := by
  have hsum : (allocateNonneg 0 ratios ratios.sum).sum = 0 := by
    have h := plan1_allocateNonneg_sum_eq 0 ratios hS
    simpa using h
  have hnn : ∀ y ∈ allocateNonneg 0 ratios ratios.sum, 0 ≤ y := fun y hy =>
    sgn_allocNonneg_nonneg 0 ratios ratios.sum y hy
  exact sgn_sum_zero_mem_zero _ hsum hnn x hx

theorem plan8_signOn_of_allocateNonneg (amount : Int) (ratios : List Nat)
    (shares : List Int) (hS : 0 < ratios.sum) (hamt : 0 ≤ amount)
    (hshares : shares = allocateNonneg amount.natAbs ratios ratios.sum) :
    SignOn amount shares := by
  unfold SignOn
  intro x hx
  have hx' : x ∈ allocateNonneg amount.natAbs ratios ratios.sum := by
    rw [← hshares]; exact hx
  have hnn : 0 ≤ x := sgn_allocNonneg_nonneg amount.natAbs ratios ratios.sum x hx'
  constructor
  · intro _
    exact hnn
  · intro hle
    have hzero : amount = 0 := by omega
    subst hzero
    simp at hx'
    have hx0 : x = 0 := plan8_allocateNonneg_zero_mem_eq_zero ratios x hS hx'
    omega

theorem plan8_signOn_of_allocateNonneg_map_neg (amount : Int) (ratios : List Nat)
    (shares : List Int) (hamt : amount < 0)
    (hshares : shares =
      (allocateNonneg amount.natAbs ratios ratios.sum).map (fun x => -x)) :
    SignOn amount shares := by
  unfold SignOn
  intro x hx
  have hx' : x ∈ (allocateNonneg amount.natAbs ratios ratios.sum).map (fun y => -y) := by
    rw [← hshares]
    exact hx
  have hnn : ∀ y ∈ allocateNonneg amount.natAbs ratios ratios.sum, 0 ≤ y :=
    fun y hy => sgn_allocNonneg_nonneg amount.natAbs ratios ratios.sum y hy
  constructor
  · intro hge
    exfalso
    omega
  · intro _
    exact plan8_mem_map_neg_le_zero (allocateNonneg amount.natAbs ratios ratios.sum) x hx' hnn

theorem lr_findMax_best_le (rems : List Nat) (mask : List Bool) (start : Nat) (bi br idx val : Nat)
    (hfind : findMaxAux rems mask start (some (bi, br)) = some (idx, val)) :
    br ≤ val := by
  induction rems generalizing mask start bi br idx val with
  | nil =>
    match mask with
    | [] =>
      have h2 : (some (bi, br) : Option (Nat × Nat)) = some (idx, val) := by simpa [findMaxAux] using hfind
      have heq : (bi, br) = (idx, val) := Option.some_inj.mp h2
      have : br = val := congrArg Prod.snd heq
      omega
    | hd :: tl =>
      have h2 : (some (bi, br) : Option (Nat × Nat)) = some (idx, val) := by simpa [findMaxAux] using hfind
      have heq : (bi, br) = (idx, val) := Option.some_inj.mp h2
      have : br = val := congrArg Prod.snd heq
      omega
  | cons r rs ih =>
    match mask with
    | [] =>
      have h2 : (some (bi, br) : Option (Nat × Nat)) = some (idx, val) := by simpa [findMaxAux] using hfind
      have heq : (bi, br) = (idx, val) := Option.some_inj.mp h2
      have : br = val := congrArg Prod.snd heq
      omega
    | c :: cs =>
      by_cases hc : c = true
      · subst hc
        have hstep : findMaxAux (r :: rs) (true :: cs) start (some (bi, br)) = findMaxAux rs cs (start+1) (some (bi, br)) := by simp [findMaxAux]
        rw [hstep] at hfind
        exact ih cs (start+1) bi br idx val hfind
      · have hcF : c = false := by cases c with | true => simp at hc | false => rfl
        subst hcF
        by_cases hr0 : r = 0
        · subst hr0
          have hstep : findMaxAux (0 :: rs) (false :: cs) start (some (bi, br)) = findMaxAux rs cs (start+1) (some (bi, br)) := by simp [findMaxAux]
          rw [hstep] at hfind
          exact ih cs (start+1) bi br idx val hfind
        · have hbeq : (r == 0) = false := by simp [hr0]
          have hstep : findMaxAux (r :: rs) (false :: cs) start (some (bi, br)) =
            findMaxAux rs cs (start+1) (if br < r then some (start, r) else some (bi, br)) := by simp [findMaxAux, hbeq]
          rw [hstep] at hfind
          by_cases hbr : br < r
          · simp [hbr] at hfind
            have h1 := ih (mask := cs) (start := start+1) (bi := start) (br := r) (idx := idx) (val := val) hfind
            omega
          · simp [hbr] at hfind
            exact ih cs (start+1) bi br idx val hfind

theorem lr_step_some_aux (r : Nat) (rs : List Nat) (cs : List Bool) (start bi br : Nat)
    (hbeq : (r == 0) = false) :
    findMaxAux (r :: rs) (false :: cs) start (some (bi, br)) =
    findMaxAux rs cs (start+1) (if br < r then some (start, r) else some (bi, br)) := by
  simp [findMaxAux, hbeq]

theorem lr_step_none_aux (r : Nat) (rs : List Nat) (cs : List Bool) (start : Nat)
    (hbeq : (r == 0) = false) :
    findMaxAux (r :: rs) (false :: cs) start none =
    findMaxAux rs cs (start+1) (some (start, r)) := by
  simp [findMaxAux, hbeq]

theorem lr_findMax_avail_le (rems : List Nat) (mask : List Bool) (start : Nat) (best : Option (Nat × Nat)) (idx val : Nat)
    (hfind : findMaxAux rems mask start best = some (idx, val)) :
    ∀ (rel : Nat) (v : Nat), mask[rel]? = some false → rems[rel]? = some v → 0 < v → v ≤ val := by
  induction rems generalizing mask start best idx val with
  | nil =>
    intro rel v hmask hrem hpos
    simp at hrem
  | cons r rs ih =>
    intro rel v hmask hrem hpos
    match mask with
    | [] => simp at hmask
    | c :: cs =>
      by_cases hc : c = true
      · subst hc
        have hstep : findMaxAux (r :: rs) (true :: cs) start best = findMaxAux rs cs (start+1) best := aux_step_true r rs cs start best
        rw [hstep] at hfind
        cases rel with
        | zero => simp at hmask
        | succ n =>
          simp at hmask hrem
          exact ih cs (start+1) best idx val hfind n v hmask hrem hpos
      · have hcF : c = false := by cases c with | true => simp at hc | false => rfl
        subst hcF
        by_cases hr0 : r = 0
        · subst hr0
          have hstep : findMaxAux (0 :: rs) (false :: cs) start best = findMaxAux rs cs (start+1) best := aux_step_false_zero rs cs start best
          rw [hstep] at hfind
          cases rel with
          | zero => simp at hrem; omega
          | succ n =>
            simp at hmask hrem
            exact ih cs (start+1) best idx val hfind n v hmask hrem hpos
        · have hbeq : (r == 0) = false := by simp [hr0]
          cases best with
          | none =>
            have hstep := lr_step_none_aux r rs cs start hbeq
            rw [hstep] at hfind
            cases rel with
            | zero =>
              have hr_eq : r = v := by simpa using hrem
              have hle := lr_findMax_best_le rs cs (start+1) start r idx val hfind
              omega
            | succ n =>
              simp at hmask hrem
              exact ih cs (start+1) (some (start, r)) idx val hfind n v hmask hrem hpos
          | some pr =>
            obtain ⟨bi, br⟩ := pr
            have hstep := lr_step_some_aux r rs cs start bi br hbeq
            rw [hstep] at hfind
            by_cases hbr : br < r
            · simp [hbr] at hfind
              cases rel with
              | zero =>
                have hr_eq : r = v := by simpa using hrem
                have hle := lr_findMax_best_le rs cs (start+1) start r idx val hfind
                omega
              | succ n =>
                simp at hmask hrem
                exact ih cs (start+1) (some (start, r)) idx val hfind n v hmask hrem hpos
            · simp [hbr] at hfind
              cases rel with
              | zero =>
                have hr_eq : r = v := by simpa using hrem
                have hble := lr_findMax_best_le rs cs (start+1) bi br idx val hfind
                omega
              | succ n =>
                simp at hmask hrem
                exact ih cs (start+1) (some (bi, br)) idx val hfind n v hmask hrem hpos

theorem lr_chooseIter_chosen_max2 (rems : List Nat) (mask : List Bool)
    (idx val : Nat) (hfind : findMaxAux rems mask 0 none = some (idx, val)) (rel : Nat) (v : Nat)
    (hmask : mask[rel]? = some false) (hrem : rems[rel]? = some v) (hpos : 0 < v) :
    v ≤ val :=
  lr_findMax_avail_le rems mask 0 none idx val hfind rel v hmask hrem hpos











theorem snippet_getset_probe (l : List Bool) (n m : Nat) (a : Bool) : True := by
  have h := @List.getElem?_set Bool l n m a
  trivial
#check @List.getElem?_set
#check @List.getElem_set

theorem bool_len_of_get (l : List Bool) (i : Nat) (b : Bool)
    (h : l[i]? = some b) : i < l.length := by
  induction l generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero => simp
    | succ n => simp at h ⊢; exact ih n h

theorem set_get_same_bool (mask : List Bool) (idx : Nat) (h : idx < mask.length) :
    (mask.set idx true)[idx]? = some true := by
  have h2 : (mask.set idx true)[idx]? = if idx = idx then if idx < mask.length then some true else none else mask[idx]? := @List.getElem?_set Bool mask idx idx true
  rw [h2]
  simp [h]

theorem set_get_other_bool (mask : List Bool) (idx i : Nat) (hne : i ≠ idx) :
    (mask.set idx true)[i]? = mask[i]? := by
  have h2 : (mask.set idx true)[i]? = if idx = i then if idx < mask.length then some true else none else mask[i]? := @List.getElem?_set Bool mask idx i true
  rw [h2]
  simp [Ne.symm hne]

theorem chooseIter_true_stable4 (rems : List Nat) (mask : List Bool) (k i : Nat)
    (h : mask[i]? = some true) :
    (chooseIter rems mask k)[i]? = some true := by
  induction k generalizing mask with
  | zero => simpa [chooseIter] using h
  | succ k ih =>
    cases hfm : findMaxAux rems mask 0 none with
    | none =>
      have h2 := chooseIter.eq_2 rems mask k
      rw [hfm] at h2
      simp only at h2
      rw [h2]
      exact h
    | some q =>
      have h2 := chooseIter.eq_2 rems mask k
      rw [hfm] at h2
      simp only at h2
      rw [h2]
      obtain ⟨idx, val⟩ := q
      have hfm2 : findMaxAux rems mask 0 none = some (idx, val) := hfm
      apply ih
      by_cases heq : i = idx
      · have hlt : i < mask.length := bool_len_of_get mask i true h
        have heq2 : (mask.set idx true)[i]? = (mask.set i true)[i]? := by rw [heq]
        rw [heq2]
        exact set_get_same_bool mask i hlt
      · rw [set_get_other_bool mask idx i heq]
        exact h

theorem chooseIter_false_implies_mask_not_true (rems : List Nat) (mask : List Bool) (k j : Nat)
    (hj_final : (chooseIter rems mask k)[j]? = some false) :
    mask[j]? ≠ some true := by
  intro htrue
  have hst := chooseIter_true_stable4 rems mask k j htrue
  rw [hj_final] at hst
  simp at hst

theorem mask_false_of_final_false_aux (rems : List Nat) (mask : List Bool) (k j : Nat)
    (hlen : mask.length = rems.length)
    (hj_rem : rems[j]? = some 0 ∨ ∃ v, rems[j]? = some v)
    (hj_final : (chooseIter rems mask k)[j]? = some false) :
    mask[j]? = some false := by
  have hnottrue : mask[j]? ≠ some true :=
    chooseIter_false_implies_mask_not_true rems mask k j hj_final
  have hlt : j < mask.length := by
    have hlt2 : j < rems.length := by
      rcases hj_rem with h0 | ⟨v, hv⟩
      · exact plan5_length_of_getElem_probe3 rems j 0 h0
      · exact plan5_length_of_getElem_probe3 rems j v hv
    omega
  obtain ⟨b, hb⟩ := plan5_aux_exists2 mask j hlt
  rw [hb] at hnottrue
  cases b with
  | true => simp at hnottrue
  | false => exact hb

theorem lr_dom_nest_test (rems : List Nat) (mask : List Bool) (k : Nat) : True := by
  induction k generalizing mask with
  | zero => trivial
  | succ k ih =>
    cases hfm : findMaxAux rems mask 0 none
    · trivial
    · trivial

theorem probe_choose_eq : True := trivial
#check @chooseIter.eq_1
#check @chooseIter.eq_2
#check chooseIter

theorem plan9_dominates_general5 (rems : List Nat) (mask : List Bool)
    (k i j : Nat) (vi vj : Nat)
    (hlen : mask.length = rems.length)
    (hi_mask : mask[i]? = some false)
    (hj_mask : mask[j]? = some false)
    (hi_rem : rems[i]? = some vi)
    (hj_rem : rems[j]? = some vj)
    (hj_pos : 0 < vj)
    (hi_final : (chooseIter rems mask k)[i]? = some true)
    (hj_final : (chooseIter rems mask k)[j]? = some false) :
    vj ≤ vi := by
  induction k generalizing mask i j vi vj with
  | zero =>
    simp [chooseIter] at hi_final
    rw [hi_final] at hi_mask
    simp at hi_mask
  | succ k ih =>
    cases hfm : findMaxAux rems mask 0 none with
    | none =>
      have e1 : chooseIter rems mask (k+1) = mask := by simp only [chooseIter, hfm]
      rw [e1] at hi_final hj_final
      rw [hi_final] at hi_mask
      simp at hi_mask
    | some pair =>
      have e2 : chooseIter rems mask (k+1) = chooseIter rems (mask.set pair.1 true) k := by
        simp only [chooseIter, hfm]
      rw [e2] at hi_final hj_final
      obtain ⟨hmaskF, hremV, hposV⟩ := plan4_findMax_some_props rems mask hlen pair.1 pair.2 hfm
      have hlen' : (mask.set pair.1 true).length = rems.length := by simp [hlen]
      by_cases hii : i = pair.1
      · subst hii
        have hvi_eq : vi = pair.2 := Option.some_inj.mp (hi_rem.symm.trans hremV)
        rw [hvi_eq]
        exact lr_findMax_avail_le rems mask 0 none pair.1 pair.2 hfm j vj hj_mask hj_rem hj_pos
      · have hi_mask' : (mask.set pair.1 true)[i]? = some false := by
          rw [set_get_other_bool mask pair.1 i hii]
          exact hi_mask
        by_cases hjj : j = pair.1
        · subst hjj
          have hlt : pair.1 < mask.length := bool_len_of_get mask pair.1 false hmaskF
          have hsettrue : (mask.set pair.1 true)[pair.1]? = some true :=
            set_get_same_bool mask pair.1 hlt
          have hstab := chooseIter_true_stable4 rems (mask.set pair.1 true) k pair.1 hsettrue
          rw [hstab] at hj_final
          simp at hj_final
        · have hj_mask' : (mask.set pair.1 true)[j]? = some false := by
            rw [set_get_other_bool mask pair.1 j hjj]
            exact hj_mask
          exact ih (mask.set pair.1 true) i j vi vj hlen' hi_mask' hj_mask' hi_rem hj_rem hj_pos hi_final hj_final













theorem plan0_lr_allocateNonneg_getElem (A : Nat) (ratios : List Nat) (S : Nat)
    (i : Nat) (r : Nat) (hr : ratios[i]? = some r) :
    ∃ b : Bool,
      (choose (ratios.map (fun x => (A * x) % S))
        (A - (ratios.map (fun x => (A * x) / S)).sum))[i]? = some b ∧
      (allocateNonneg A ratios S)[i]? =
        some (((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) ∧
      (b = true → 0 < (A * r) % S) := by
  have hi : i < ratios.length :=
    plan5_length_of_getElem_probe3 ratios i r hr
  have hfloors : (ratios.map (fun x => (A * x) / S))[i]? = some ((A * r) / S) :=
    plan5_map_div_getElem A S ratios i r hr
  have hi_rems : i < (ratios.map (fun x => (A * x) % S)).length := by
    simp only [List.length_map]
    exact hi
  obtain ⟨b, Hb⟩ := plan5_choose_getElem_exists
    (ratios.map (fun x => (A * x) % S))
    (A - (ratios.map (fun x => (A * x) / S)).sum) i hi_rems
  have Hzip := plan5_zipWith_share_getElem
    (ratios.map (fun x => (A * x) / S))
    (choose (ratios.map (fun x => (A * x) % S))
      (A - (ratios.map (fun x => (A * x) / S)).sum))
    i ((A * r) / S) b hfloors Hb
  have heq : allocateNonneg A ratios S =
    List.zipWith (fun (f : Nat) (b : Bool) => (f : Int) + if b then 1 else 0)
      (ratios.map (fun x => (A * x) / S))
      (choose (ratios.map (fun x => (A * x) % S))
        (A - (ratios.map (fun x => (A * x) / S)).sum)) := by
    unfold allocateNonneg
    simp only
  rw [heq]
  exact ⟨b, Hb, Hzip, fun hbt => plan5_choose_true_mod_pos A S ratios
    (A - (ratios.map (fun x => (A * x) / S)).sum) i r hr (hbt ▸ Hb)⟩

theorem my_replicate_get_false_aux (n i : Nat) (h : i < n) :
    (List.replicate n (false : Bool))[i]? = some false := by
  induction n generalizing i with
  | zero => simp at h
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.replicate_succ] at h ⊢
      have h2 : i < n := by omega
      have hcon : ((false :: List.replicate n false)[i + 1]? = (List.replicate n false)[i]?) := by simp
      rw [hcon]
      exact ih i h2

theorem plan0_lr_choose_dominates_proof_attempt (rems : List Nat) (k i j : Nat) (vi vj : Nat)
    (hi_rem : rems[i]? = some vi) (hj_rem : rems[j]? = some vj)
    (hj_pos : 0 < vj)
    (hi_final : (choose rems k)[i]? = some true)
    (hj_final : (choose rems k)[j]? = some false) :
    vj ≤ vi := by
  have hi_lt : i < rems.length := plan5_length_of_getElem_probe3 rems i vi hi_rem
  have hj_lt : j < rems.length := plan5_length_of_getElem_probe3 rems j vj hj_rem
  have hlen : (List.replicate rems.length false).length = rems.length := by simp
  have hi_mask : (List.replicate rems.length false)[i]? = some false :=
    my_replicate_get_false_aux rems.length i (by omega)
  have hj_mask : (List.replicate rems.length false)[j]? = some false :=
    my_replicate_get_false_aux rems.length j (by omega)
  have hi_f : (chooseIter rems (List.replicate rems.length false) k)[i]? = some true := hi_final
  have hj_f : (chooseIter rems (List.replicate rems.length false) k)[j]? = some false := hj_final
  exact plan9_dominates_general5 rems (List.replicate rems.length false) k i j vi vj hlen hi_mask hj_mask hi_rem hj_rem hj_pos hi_f hj_f

theorem my_rep_get_aux2 (n i : Nat) (h : i < n) :
    (List.replicate n (false : Bool))[i]? = some false := by
  induction n generalizing i with
  | zero => simp at h
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.replicate_succ] at h ⊢
      have h2 : i < n := by omega
      have hcon : ((false :: List.replicate n false)[i + 1]? = (List.replicate n false)[i]?) := by simp
      rw [hcon]
      exact ih i h2

theorem plan0_lr_choose_dominates (rems : List Nat) (k i j : Nat) (vi vj : Nat)
    (hi_rem : rems[i]? = some vi) (hj_rem : rems[j]? = some vj)
    (hj_pos : 0 < vj)
    (hi_final : (choose rems k)[i]? = some true)
    (hj_final : (choose rems k)[j]? = some false) :
    vj ≤ vi := by
  have hi_lt : i < rems.length := plan5_length_of_getElem_probe3 rems i vi hi_rem
  have hj_lt : j < rems.length := plan5_length_of_getElem_probe3 rems j vj hj_rem
  have hlen : (List.replicate rems.length false).length = rems.length := by simp
  have hi_mask : (List.replicate rems.length false)[i]? = some false :=
    my_rep_get_aux2 rems.length i (by omega)
  have hj_mask : (List.replicate rems.length false)[j]? = some false :=
    my_rep_get_aux2 rems.length j (by omega)
  exact plan9_dominates_general5 rems (List.replicate rems.length false) k i j vi vj hlen hi_mask hj_mask hi_rem hj_rem hj_pos hi_final hj_final

theorem tmp_excess_formula_test4 (A S r : Nat) (b : Bool) :
    excess (A : Int) S (((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) r =
      if b then (S : Int) - ((A * r % S : Nat) : Int)
      else -((A * r % S : Nat) : Int) := by
  unfold excess
  cases b <;> simp
  · exact plan6_excess_add_zero A S r
  · exact plan6_excess_add_one A S r

theorem plan0_lr_excess_formula (A S r : Nat) (b : Bool) :
    excess (A : Int) S (((A * r / S : Nat) : Int) + if b then (1 : Int) else 0) r =
      if b then (S : Int) - ((A * r % S : Nat) : Int)
      else -((A * r % S : Nat) : Int) := by
  unfold excess
  cases b <;> simp
  · exact plan6_excess_add_zero A S r
  · exact plan6_excess_add_one A S r

theorem tmp_branch2 (bi : Bool) (e : Int) (rem : Int)
    (hei : e = (if bi then (10 : Int) - rem else -rem))
    (hpos : 0 < e) (hnn : 0 ≤ rem) :
    bi = true := by
  cases h : bi with
  | false =>
    simp [h] at hei
    omega
  | true => rfl

theorem tmp_case_test2 (bi : Bool) (e : Int) (rem : Int)
    (hei : e = (if bi then (10 : Int) - rem else -rem))
    (hpos : 0 < e) (hnn : 0 ≤ rem) :
    bi = true := by
  cases bi with
  | false =>
    simp at hei
    omega
  | true => rfl

theorem plan0_lr_pair_bound (A : Nat) (ratios : List Nat) (hS : 0 < ratios.sum)
    (i : Nat) (hi : i < (allocateNonneg A ratios ratios.sum).length)
    (hri : i < ratios.length)
    (j : Nat) (hj : j < (allocateNonneg A ratios ratios.sum).length)
    (hrj : j < ratios.length)
    (hpos : 0 < excess (A : Int) ratios.sum
      (allocateNonneg A ratios ratios.sum)[i] ratios[i])
    (hneg : excess (A : Int) ratios.sum
      (allocateNonneg A ratios ratios.sum)[j] ratios[j] < 0) :
    excess (A : Int) ratios.sum (allocateNonneg A ratios ratios.sum)[i] ratios[i] -
      excess (A : Int) ratios.sum (allocateNonneg A ratios ratios.sum)[j] ratios[j] ≤
      (ratios.sum : Int) := by
  have hi_get : ratios[i]? = some ratios[i] := by simp [hri]
  have hj_get : ratios[j]? = some ratios[j] := by simp [hrj]
  obtain ⟨bi, hbi_choose, hbi_share, hbi_pos⟩ :=
    plan0_lr_allocateNonneg_getElem A ratios ratios.sum i ratios[i] hi_get
  obtain ⟨bj, hbj_choose, hbj_share, hbj_pos⟩ :=
    plan0_lr_allocateNonneg_getElem A ratios ratios.sum j ratios[j] hj_get
  have hi_some : (allocateNonneg A ratios ratios.sum)[i]? = some ((allocateNonneg A ratios ratios.sum)[i]) := by simp [hi]
  have hj_some : (allocateNonneg A ratios ratios.sum)[j]? = some ((allocateNonneg A ratios ratios.sum)[j]) := by simp [hj]
  rw [hi_some] at hbi_share
  rw [hj_some] at hbj_share
  have hi_share : (allocateNonneg A ratios ratios.sum)[i] = (((A * ratios[i] / ratios.sum : Nat) : Int) + if bi then (1 : Int) else 0) := Option.some_inj.mp hbi_share
  have hj_share : (allocateNonneg A ratios ratios.sum)[j] = (((A * ratios[j] / ratios.sum : Nat) : Int) + if bj then (1 : Int) else 0) := Option.some_inj.mp hbj_share
  have hei : excess (A : Int) ratios.sum (allocateNonneg A ratios ratios.sum)[i] ratios[i] =
      (if bi then (ratios.sum : Int) - ((A * ratios[i] % ratios.sum : Nat) : Int)
      else -((A * ratios[i] % ratios.sum : Nat) : Int)) := by
    rw [hi_share]
    exact plan0_lr_excess_formula A ratios.sum ratios[i] bi
  have hbi_true : bi = true := by
    cases h : bi with
    | false =>
      have hei2 : excess (A : Int) ratios.sum (allocateNonneg A ratios ratios.sum)[i] ratios[i] =
        -((A * ratios[i] % ratios.sum : Nat) : Int) := by simp [h] at hei; exact hei
      rw [hei2] at hpos
      have hnn : (0 : Int) ≤ ((A * ratios[i] % ratios.sum : Nat) : Int) := by omega
      omega
    | true => rfl
  have hej : excess (A : Int) ratios.sum (allocateNonneg A ratios ratios.sum)[j] ratios[j] =
      (if bj then (ratios.sum : Int) - ((A * ratios[j] % ratios.sum : Nat) : Int)
      else -((A * ratios[j] % ratios.sum : Nat) : Int)) := by
    rw [hj_share]
    exact plan0_lr_excess_formula A ratios.sum ratios[j] bj
  have hbj_false : bj = false := by
    cases h : bj with
    | false => rfl
    | true =>
      have hej2 : excess (A : Int) ratios.sum (allocateNonneg A ratios ratios.sum)[j] ratios[j] =
        (ratios.sum : Int) - ((A * ratios[j] % ratios.sum : Nat) : Int) := by simp [h] at hej; exact hej
      rw [hej2] at hneg
      have hnn : (0 : Int) ≤ ((A * ratios[j] % ratios.sum : Nat) : Int) := by omega
      have hlt : ((A * ratios[j] % ratios.sum : Nat) : Int) < (ratios.sum : Int) := by
        have hh : A * ratios[j] % ratios.sum < ratios.sum := Nat.mod_lt _ hS
        exact_mod_cast hh
      omega
  rw [hbi_true] at hei hbi_choose
  rw [hbj_false] at hej hbj_choose
  simp only at hei hej
  have hrem_j_pos : 0 < A * ratios[j] % ratios.sum := by
    rw [hej] at hneg
    have hnn : (0 : Int) ≤ ((A * ratios[j] % ratios.sum : Nat) : Int) := by omega
    have hposI : (0 : Int) < ((A * ratios[j] % ratios.sum : Nat) : Int) := by omega
    exact_mod_cast hposI
  have hi_rem : (ratios.map (fun x => (A * x) % ratios.sum))[i]? = some (A * ratios[i] % ratios.sum) :=
    plan5_map_mod_getElem A ratios.sum ratios i ratios[i] hi_get
  have hj_rem : (ratios.map (fun x => (A * x) % ratios.sum))[j]? = some (A * ratios[j] % ratios.sum) :=
    plan5_map_mod_getElem A ratios.sum ratios j ratios[j] hj_get
  have hdom : A * ratios[j] % ratios.sum ≤ A * ratios[i] % ratios.sum :=
    plan0_lr_choose_dominates (ratios.map (fun x => (A * x) % ratios.sum))
      (A - (ratios.map (fun x => (A * x) / ratios.sum)).sum) i j
      (A * ratios[i] % ratios.sum) (A * ratios[j] % ratios.sum)
      hi_rem hj_rem hrem_j_pos hbi_choose hbj_choose
  have hdomI : ((A * ratios[j] % ratios.sum : Nat) : Int) ≤ ((A * ratios[i] % ratios.sum : Nat) : Int) := by
    exact_mod_cast hdom
  rw [hei, hej]
  omega

theorem plan0_lr_allocateNonneg_aux (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    LargestRemainderOn (A : Int) ratios (allocateNonneg A ratios ratios.sum) := by
  unfold LargestRemainderOn
  intro i hi hri j hj hrj hpos hneg
  exact plan0_lr_pair_bound A ratios hS i hi hri j hj hrj hpos hneg

theorem plan0_lr_allocateNonneg_full (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    LargestRemainderOn (A : Int) ratios (allocateNonneg A ratios ratios.sum) := by
  unfold LargestRemainderOn
  intro i hi hri j hj hrj hpos hneg
  exact plan0_lr_pair_bound A ratios hS i hi hri j hj hrj hpos hneg

theorem plan0_lr_allocateNonneg_check (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    LargestRemainderOn (A : Int) ratios (allocateNonneg A ratios ratios.sum) := by
  unfold LargestRemainderOn
  intro i hi hri j hj hrj hpos hneg
  exact plan0_lr_pair_bound A ratios hS i hi hri j hj hrj hpos hneg

theorem plan0_lr_allocateNonneg (A : Nat) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    LargestRemainderOn (A : Int) ratios (allocateNonneg A ratios ratios.sum) := by
  unfold LargestRemainderOn
  intro i hi hri j hj hrj hpos hneg
  exact plan0_lr_pair_bound A ratios hS i hi hri j hj hrj hpos hneg

theorem plan0_lr_neg_transfer (A : Int) (ratios : List Nat) (shares : List Int)
    (h : LargestRemainderOn A ratios shares) :
    LargestRemainderOn (-A) ratios (shares.map (fun x => -x)) := by
  unfold LargestRemainderOn at h ⊢
  intro i hi hri j hj hrj hpos hneg
  have hlen : (shares.map (fun x => -x)).length = shares.length := by simp
  have hi0 : i < shares.length := hlen ▸ hi
  have hj0 : j < shares.length := hlen ▸ hj
  have hgi : (shares.map (fun x => -x))[i] = -shares[i] := by simp
  have hgj : (shares.map (fun x => -x))[j] = -shares[j] := by simp
  have hex_i : excess (-A) ratios.sum ((shares.map (fun x => -x))[i]) ratios[i] =
      - excess A ratios.sum shares[i] ratios[i] := by
    rw [hgi]
    exact plan7_excess_neg A ratios.sum shares[i] ratios[i]
  have hex_j : excess (-A) ratios.sum ((shares.map (fun x => -x))[j]) ratios[j] =
      - excess A ratios.sum shares[j] ratios[j] := by
    rw [hgj]
    exact plan7_excess_neg A ratios.sum shares[j] ratios[j]
  rw [hex_i] at hpos
  rw [hex_j] at hneg
  have hpos' : 0 < excess A ratios.sum shares[j] ratios[j] := by omega
  have hneg' : excess A ratios.sum shares[i] ratios[i] < 0 := by omega
  have hbound := h j hj0 hrj i hi0 hri hpos' hneg'
  omega

theorem req_largest_remainder_direct_test : LargestRemainder allocate := by
  intro amount ratios shares h
  unfold allocate at h
  by_cases hcond : ratios = [] ∨ ratios.sum = 0
  · simp [hcond] at h
  · simp only [hcond, ↓reduceIte] at h
    have hSne : ratios.sum ≠ 0 := fun he => hcond (Or.inr he)
    have hSpos : 0 < ratios.sum := Nat.pos_of_ne_zero hSne
    by_cases h0 : 0 ≤ amount
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      rw [← heq]
      have hA : ((amount.natAbs : Nat) : Int) = amount := Int.natAbs_of_nonneg h0
      have hW := plan0_lr_allocateNonneg amount.natAbs ratios hSpos
      rw [hA] at hW
      exact hW
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      rw [← heq]
      have hW0 := plan0_lr_allocateNonneg amount.natAbs ratios hSpos
      have hWneg := plan0_lr_neg_transfer ((amount.natAbs : Nat) : Int) ratios
        (allocateNonneg amount.natAbs ratios ratios.sum) hW0
      have hpos : 0 ≤ -amount := by omega
      have h1 : (((-amount).natAbs : Nat) : Int) = -amount := Int.natAbs_of_nonneg hpos
      have h2 : (-amount).natAbs = amount.natAbs := Int.natAbs_neg amount
      rw [h2] at h1
      have hAneg : ((amount.natAbs : Nat) : Int) = -amount := h1
      have ham : -((amount.natAbs : Nat) : Int) = amount := by omega
      rw [ham] at hWneg
      exact hWneg

theorem req_valid_succeeds : ValidSucceeds allocate := by
  unfold ValidSucceeds Valid allocate
  intro amount ratios h
  obtain ⟨hne, hpos⟩ := h
  simp only [hne, false_or]
  have hS : ratios.sum ≠ 0 := by omega
  simp only [hS, ↓reduceIte]
  by_cases h0 : 0 ≤ amount <;> simp [h0]

theorem req_invalid_fails : InvalidFails allocate := by
  unfold InvalidFails Valid allocate
  intro amount ratios h
  by_cases he : ratios = []
  · simp [he]
  · have h2 : ¬ (0 < ratios.sum) := fun hp => h ⟨he, hp⟩
    have h3 : ratios.sum = 0 := Nat.eq_zero_of_not_pos h2
    simp [he, h3]

theorem req_one_share_each : OneShareEach allocate := plan0_one_share_each

theorem req_conservation : Conserves allocate := by
  intro amount ratios shares h
  unfold ConservesOn
  unfold allocate at h
  by_cases hcond : ratios = [] ∨ ratios.sum = 0
  · simp [hcond] at h
  · simp only [hcond, ↓reduceIte] at h
    have hne : ratios ≠ [] := fun he => hcond (Or.inl he)
    have hSne : ratios.sum ≠ 0 := fun he => hcond (Or.inr he)
    have hSpos : 0 < ratios.sum := Nat.pos_of_ne_zero hSne
    have hsum := plan1_allocateNonneg_sum_eq amount.natAbs ratios hSpos
    by_cases h0 : 0 ≤ amount
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      rw [← heq]
      rw [hsum]
      exact Int.natAbs_of_nonneg h0
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      rw [← heq]
      rw [aux_sum_neg3, hsum]
      have hpos : 0 ≤ -amount := by omega
      have h1 : (((-amount).natAbs : Nat) : Int) = -amount := Int.natAbs_of_nonneg hpos
      have h2 : (-amount).natAbs = amount.natAbs := Int.natAbs_neg amount
      rw [h2] at h1
      omega

theorem req_within_one_unit : WithinOneUnit allocate := by
  intro amount ratios shares h
  unfold allocate at h
  by_cases hcond : ratios = [] ∨ ratios.sum = 0
  · simp [hcond] at h
  · simp only [hcond, ↓reduceIte] at h
    have hSne : ratios.sum ≠ 0 := fun he => hcond (Or.inr he)
    have hSpos : 0 < ratios.sum := Nat.pos_of_ne_zero hSne
    by_cases h0 : 0 ≤ amount
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      rw [← heq]
      have hA : ((amount.natAbs : Nat) : Int) = amount := Int.natAbs_of_nonneg h0
      have hW := plan4_within_one_allocateNonneg amount.natAbs ratios hSpos
      rw [hA] at hW
      exact hW
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      rw [← heq]
      have hW0 := plan4_within_one_allocateNonneg amount.natAbs ratios hSpos
      unfold WithinOneUnitOn at hW0 ⊢
      intro i hx hr
      have hlen : ((allocateNonneg amount.natAbs ratios ratios.sum).map (fun x => -x)).length =
          (allocateNonneg amount.natAbs ratios ratios.sum).length := by simp
      have hx0 : i < (allocateNonneg amount.natAbs ratios ratios.sum).length := by omega
      have hg : (((allocateNonneg amount.natAbs ratios ratios.sum).map (fun x => -x))[i] =
          - (allocateNonneg amount.natAbs ratios ratios.sum)[i]) := by simp
      have hbound := hW0 i hx0 hr
      have hpos : 0 ≤ -amount := by omega
      have h1 : (((-amount).natAbs : Nat) : Int) = -amount := Int.natAbs_of_nonneg hpos
      have h2 : (-amount).natAbs = amount.natAbs := Int.natAbs_neg amount
      rw [h2] at h1
      have hAneg : ((amount.natAbs : Nat) : Int) = -amount := h1
      have hex : excess amount ratios.sum
          (((allocateNonneg amount.natAbs ratios ratios.sum).map (fun x => -x))[i]) ratios[i]
          = - excess ((amount.natAbs : Nat) : Int) ratios.sum
            ((allocateNonneg amount.natAbs ratios ratios.sum)[i]) ratios[i] := by
        rw [hg, hAneg]
        unfold excess
        simp only [Int.neg_mul, Int.neg_sub]
        omega
      rw [hex]
      omega

theorem req_zero_ratio : ZeroRatio allocate := by
  intro amount ratios shares h
  unfold allocate at h
  by_cases hcond : ratios = [] ∨ ratios.sum = 0
  · simp [hcond] at h
  · simp only [hcond, ↓reduceIte] at h
    have hSpos : 0 < ratios.sum := Nat.pos_of_ne_zero (fun he => hcond (Or.inr he))
    unfold ZeroRatioOn
    intro i hx hr hr0
    by_cases h0 : 0 ≤ amount
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      have hi_len : i < (allocateNonneg amount.natAbs ratios ratios.sum).length := by
        rw [plan0_allocateNonneg_length]; exact hr
      have hval : (allocateNonneg amount.natAbs ratios ratios.sum)[i] = 0 :=
        planZ_allocNonneg_zero4 amount.natAbs ratios ratios.sum i hi_len hr hr0
      have hget : shares[i]? = (allocateNonneg amount.natAbs ratios ratios.sum)[i]? := by
        rw [heq]
      have h1 : shares[i]? = some (0 : Int) := by
        rw [hget, List.getElem?_eq_getElem hi_len, hval]
      have h2 : shares[i]? = some shares[i] := List.getElem?_eq_getElem hx
      rw [h2] at h1
      exact Option.some_inj.mp h1
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      have hi_len : i < (allocateNonneg amount.natAbs ratios ratios.sum).length := by
        rw [plan0_allocateNonneg_length]; exact hr
      have hval : (allocateNonneg amount.natAbs ratios ratios.sum)[i] = 0 :=
        planZ_allocNonneg_zero4 amount.natAbs ratios ratios.sum i hi_len hr hr0
      have hget : shares[i]? = ((allocateNonneg amount.natAbs ratios ratios.sum).map (fun x => -x))[i]? := by
        rw [heq]
      have hmaplen : i < ((allocateNonneg amount.natAbs ratios ratios.sum).map (fun x => -x)).length := by
        simp only [List.length_map]; exact hi_len
      have h1 : shares[i]? = some (0 : Int) := by
        rw [hget, List.getElem?_eq_getElem hmaplen]
        simp [List.getElem_map, hval]
      have h2 : shares[i]? = some shares[i] := List.getElem?_eq_getElem hx
      rw [h2] at h1
      exact Option.some_inj.mp h1

theorem req_sign : Sign allocate := by
  intro amount ratios shares h
  unfold allocate at h
  by_cases hcond : ratios = [] ∨ ratios.sum = 0
  · simp [hcond] at h
  · simp only [hcond, ↓reduceIte] at h
    have hSpos : 0 < ratios.sum := Nat.pos_of_ne_zero (fun he => hcond (Or.inr he))
    by_cases h0 : 0 ≤ amount
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      exact plan8_signOn_of_allocateNonneg amount ratios shares hSpos h0 heq.symm
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      have hlt : amount < 0 := by omega
      exact plan8_signOn_of_allocateNonneg_map_neg amount ratios shares hlt heq.symm

theorem req_largest_remainder : LargestRemainder allocate := by
  intro amount ratios shares h
  unfold allocate at h
  by_cases hcond : ratios = [] ∨ ratios.sum = 0
  · simp [hcond] at h
  · simp only [hcond, ↓reduceIte] at h
    have hSne : ratios.sum ≠ 0 := fun he => hcond (Or.inr he)
    have hSpos : 0 < ratios.sum := Nat.pos_of_ne_zero hSne
    by_cases h0 : 0 ≤ amount
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      rw [← heq]
      have hA : ((amount.natAbs : Nat) : Int) = amount := Int.natAbs_of_nonneg h0
      have hW := plan0_lr_allocateNonneg amount.natAbs ratios hSpos
      rw [hA] at hW
      exact hW
    · simp only [h0, ↓reduceIte] at h
      have heq := Option.some_inj.mp h
      rw [← heq]
      have hW0 := plan0_lr_allocateNonneg amount.natAbs ratios hSpos
      have hWneg := plan0_lr_neg_transfer ((amount.natAbs : Nat) : Int) ratios
        (allocateNonneg amount.natAbs ratios ratios.sum) hW0
      have hpos : 0 ≤ -amount := by omega
      have h1 : (((-amount).natAbs : Nat) : Int) = -amount := Int.natAbs_of_nonneg hpos
      have h2 : (-amount).natAbs = amount.natAbs := Int.natAbs_neg amount
      rw [h2] at h1
      have hAneg : ((amount.natAbs : Nat) : Int) = -amount := h1
      have ham : -((amount.natAbs : Nat) : Int) = amount := by omega
      rw [ham] at hWneg
      exact hWneg

end Allocation
