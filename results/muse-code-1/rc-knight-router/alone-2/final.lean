import OrderRouter.Spec
import OrderRouter.Lemmas

namespace OrderRouter

def step : Impl := fun _ s e =>
  match e with
  | .parent q f =>
    ({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ }, [])
  | .route id liq =>
    let p := s.parents id
    let c := min liq (p.qty - p.sent)
    if id < s.nParents ∧ 0 < c then
      ({ s with parents := upd s.parents id { p with sent := p.sent + c },
                nChildren := s.nChildren + 1,
                children := upd s.children s.nChildren ⟨id, c, 0⟩ }, [⟨id, c⟩])
    else (s, [])
  | .ack _ => (s, [])
  | .fill k q =>
    if k < s.nChildren then
      let c := s.children k
      let x := min q (c.qty - c.done)
      let p := s.parents c.parent
      ({ s with parents := upd s.parents c.parent { p with cum := p.cum + x },
                children := upd s.children k { c with done := c.done + x } }, [])
    else (s, [])

theorem sentFor_zero_of_nomatch (l : List Kid) (id : Nat)
    (h : ∀ k ∈ l, k.parent ≠ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent ≠ id := h a (by simp)
    simp [ha]
    exact ih (fun k hk => h k (by simp [hk]))

theorem execFor_zero_of_nomatch (l : List Kid) (id : Nat)
    (h : ∀ k ∈ l, k.parent ≠ id) : execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent ≠ id := h a (by simp)
    simp [ha]
    exact ih (fun k hk => h k (by simp [hk]))

def Inv (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders
  ∧ x.st.nChildren = x.tr.kids.length
  ∧ (∀ id, id < x.st.nParents → (x.st.parents id).qty = x.tr.qty id)
  ∧ (∀ id, id < x.st.nParents → (x.st.parents id).sent = x.tr.sent id)
  ∧ (∀ id, id < x.st.nParents → (x.st.parents id).cum = x.tr.exec id)
  ∧ (∀ k, k < x.st.nChildren → (x.st.children k).parent < x.st.nParents)
  ∧ (∀ k, k < x.st.nChildren → x.tr.kids[k]? = some (Kid.mk (x.st.children k).parent (x.st.children k).qty (x.st.children k).done))
  ∧ (∀ id, id < x.st.nParents → (x.st.parents id).sent ≤ (x.st.parents id).qty)
  ∧ (∀ k, k < x.st.nChildren → (x.st.children k).done ≤ (x.st.children k).qty)

theorem inv_start : Inv start := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id h; simp [start, init] at h
  · intro id h; simp [start, init] at h
  · intro id h; simp [start, init] at h
  · intro k h; simp [start, init] at h
  · intro k h; simp [start, init] at h
  · intro id h; simp [start, init] at h
  · intro k h; simp [start, init] at h

theorem idx_lt_of_some (l : List Kid) (i : Nat) (k : Kid)
    (h : l[i]? = some k) : i < l.length := by
  have hne : l[i]? ≠ none := by
    rw [h]
    exact Option.some_ne_none _
  have hle : ¬ l.length ≤ i := fun hle => hne (List.getElem?_eq_none_iff.mpr hle)
  omega

theorem mem_parent_lt (x : Sys) (hx : Inv x) (k : Kid) (hm : k ∈ x.tr.kids)
    : k.parent < x.st.nParents := by
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hCP, hKid, hSL, hDL⟩ := hx
  obtain ⟨i, hi⟩ := (List.mem_iff_getElem?.mp hm)
  have hlt : i < x.tr.kids.length := idx_lt_of_some x.tr.kids i k hi
  have hlt2 : i < x.st.nChildren := by omega
  have hki := hKid i hlt2
  rw [hi] at hki
  have heq : k = Kid.mk (x.st.children i).parent (x.st.children i).qty (x.st.children i).done := by
    exact Option.some_inj.mp hki
  rw [heq]
  exact hCP i hlt2

theorem inv_parent (b : Build) (x : Sys) (q : Nat) (f : Bool) (hx : Inv x)
    : Inv (advance step b x (.parent q f)) := by
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hCP, hKid, hSL, hDL⟩ := hx
  simp only [advance, step, Truth.observe, Truth.record, List.map_nil, List.append_nil]
  refine ⟨by (show x.st.nParents + 1 = x.tr.nOrders + 1; omega), hNC, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id hid
    have hid' : id < x.st.nParents + 1 := hid
    by_cases heq : id = x.st.nParents
    · subst heq
      simp [upd, hNP]
    · have hid2 : id < x.st.nParents := by omega
      have hq := hQty id hid2
      have hne : id ≠ x.tr.nOrders := by omega
      simp [upd, heq, hne, hq]
  · intro id hid
    have hid' : id < x.st.nParents + 1 := hid
    by_cases heq : id = x.st.nParents
    · subst heq
      have hnom : ∀ k ∈ x.tr.kids, k.parent ≠ x.st.nParents := by
        intro k hm
        have hlt := mem_parent_lt ⟨x.st, x.tr⟩ ⟨hNP, hNC, hQty, hSent, hCum, hCP, hKid, hSL, hDL⟩ k hm
        have hlt' : k.parent < x.st.nParents := hlt
        omega
      have hz := (sentFor_zero_of_nomatch x.tr.kids x.st.nParents hnom).symm
      simp [upd, Truth.sent, hz]
    · have hid2 : id < x.st.nParents := by omega
      have hs := hSent id hid2
      have heq2 : (upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ id).sent = (x.st.parents id).sent := by
        simp [upd, heq]
      have hz2 : ({ nOrders := x.tr.nOrders + 1, qty := upd x.tr.qty x.tr.nOrders q, kids := x.tr.kids } : Truth).sent id = x.tr.sent id := by
        simp [Truth.sent]
      rw [heq2, hz2]
      exact hs
  · intro id hid
    have hid' : id < x.st.nParents + 1 := hid
    by_cases heq : id = x.st.nParents
    · subst heq
      have hnom : ∀ k ∈ x.tr.kids, k.parent ≠ x.st.nParents := by
        intro k hm
        have hlt := mem_parent_lt ⟨x.st, x.tr⟩ ⟨hNP, hNC, hQty, hSent, hCum, hCP, hKid, hSL, hDL⟩ k hm
        have hlt' : k.parent < x.st.nParents := hlt
        omega
      have hz := (execFor_zero_of_nomatch x.tr.kids x.st.nParents hnom).symm
      simp [upd, Truth.exec, hz]
    · have hid2 : id < x.st.nParents := by omega
      have hc := hCum id hid2
      have heq2 : (upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ id).cum = (x.st.parents id).cum := by
        simp [upd, heq]
      have hz2 : ({ nOrders := x.tr.nOrders + 1, qty := upd x.tr.qty x.tr.nOrders q, kids := x.tr.kids } : Truth).exec id = x.tr.exec id := by
        simp [Truth.exec]
      rw [heq2, hz2]
      exact hc
  · intro k hk
    have hk' : k < x.st.nChildren := hk
    have hkp : (x.st.children k).parent < x.st.nParents := hCP k hk'
    have hgoal : (x.st.children k).parent < x.st.nParents + 1 := by omega
    exact hgoal
  · intro k hk
    have hk2 : k < x.st.nChildren := hk
    have hkk := hKid k hk2
    have hlt : k < x.tr.kids.length := by omega
    simpa [hlt] using hkk
  · intro id hid
    have hid' : id < x.st.nParents + 1 := hid
    by_cases heq : id = x.st.nParents
    · subst heq
      simp [upd]
    · have hid2 : id < x.st.nParents := by omega
      have hs := hSL id hid2
      simp [upd, heq] at hs ⊢
      exact hs
  · intro k hk
    have hk' : k < x.st.nChildren := hk
    exact hDL k hk'

theorem inv_ack (b : Build) (x : Sys) (k : Nat) (hx : Inv x)
    : Inv (advance step b x (.ack k)) := by
  simp only [advance, step, Truth.observe, Truth.record, List.map_nil, List.append_nil]
  exact hx

theorem inv_route (b : Build) (x : Sys) (id liq : Nat) (hx : Inv x)
    : Inv (advance step b x (.route id liq)) := by
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hCP, hKid, hSL, hDL⟩ := hx
  by_cases hcond : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · have hid : id < x.st.nParents := hcond.1
    have hq := hQty id hid
    have hs := hSent id hid
    have hc := hCum id hid
    have hsl := hSL id hid
    simp only [advance, step, Truth.observe, Truth.record]
    simp [hcond]
    refine ⟨hNP, by simp [List.length_append, hNC], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro id' hid'
      have hid'' : id' < x.st.nParents := hid'
      have hq0 := hQty id' hid''
      by_cases heq : id' = id
      · subst heq
        simp [upd, hq0]
      · simp [upd, heq, hq0]
    · intro id' hid'
      have hid'' : id' < x.st.nParents := hid'
      have hs0 := hSent id' hid''
      by_cases heq : id' = id
      · rw [heq] at hs0 ⊢
        have hshow : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } id).sent = (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) := by
          simp [upd]
        have htr : ({ nOrders := x.tr.nOrders, qty := x.tr.qty, kids := x.tr.kids ++ [{ parent := id, qty := min liq ((x.st.parents id).qty - (x.st.parents id).sent), done := 0 }] } : Truth).sent id = x.tr.sent id + min liq ((x.st.parents id).qty - (x.st.parents id).sent) := by
          simp [Truth.sent, sentFor_append, hs]
        rw [hshow, htr]
        exact hs.symm ▸ rfl
      · have hshow : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } id').sent = (x.st.parents id').sent := by
          simp [upd, heq]
        have hne : id ≠ id' := fun h => heq h.symm
        have htr : ({ nOrders := x.tr.nOrders, qty := x.tr.qty, kids := x.tr.kids ++ [{ parent := id, qty := min liq ((x.st.parents id).qty - (x.st.parents id).sent), done := 0 }] } : Truth).sent id' = x.tr.sent id' := by
          simp [Truth.sent, sentFor_append, hne]
        rw [hshow, htr]
        exact hs0
    · intro id' hid'
      have hid'' : id' < x.st.nParents := hid'
      have hc0 := hCum id' hid''
      have hshow : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } id').cum = (x.st.parents id').cum := by
        by_cases heq : id' = id
        · subst heq; simp [upd]
        · simp [upd, heq]
      have htr : ({ nOrders := x.tr.nOrders, qty := x.tr.qty, kids := x.tr.kids ++ [{ parent := id, qty := min liq ((x.st.parents id).qty - (x.st.parents id).sent), done := 0 }] } : Truth).exec id' = x.tr.exec id' := by
        simp [Truth.exec, execFor_append]
      rw [hshow, htr]
      exact hc0
    · intro k hk
      have hk' : k < x.st.nChildren + 1 := hk
      by_cases heq : k = x.st.nChildren
      · subst heq
        simpa [upd] using hid
      · have hk2 : k < x.st.nChildren := by omega
        have hcp := hCP k hk2
        simpa [upd, heq] using hcp
    · intro k hk
      have hk' : k < x.st.nChildren + 1 := hk
      by_cases heq : k = x.st.nChildren
      · subst heq
        have hlen : (x.tr.kids ++ [(Kid.mk id (min liq ((x.st.parents id).qty - (x.st.parents id).sent)) 0 : Kid)])[x.st.nChildren]? = some (Kid.mk id (min liq ((x.st.parents id).qty - (x.st.parents id).sent)) 0) := by
          have h1 : x.st.nChildren < (x.tr.kids ++ [(Kid.mk id (min liq ((x.st.parents id).qty - (x.st.parents id).sent)) 0 : Kid)]).length := by
            simp [List.length_append, hNC]
          have h2 : (x.tr.kids ++ [(Kid.mk id (min liq ((x.st.parents id).qty - (x.st.parents id).sent)) 0 : Kid)])[x.st.nChildren]? = ([(Kid.mk id (min liq ((x.st.parents id).qty - (x.st.parents id).sent)) 0 : Kid)])[x.st.nChildren - x.tr.kids.length]? := by
            rw [List.getElem?_append]
            have : ¬ x.st.nChildren < x.tr.kids.length := by omega
            simp [this]
          rw [h2]
          have h3 : x.st.nChildren - x.tr.kids.length = 0 := by omega
          rw [h3]
          rfl
        simpa [upd] using hlen
      · have hk2 : k < x.st.nChildren := by omega
        have hkk := hKid k hk2
        have hget : (x.tr.kids ++ [{ parent := id, qty := min liq ((x.st.parents id).qty - (x.st.parents id).sent), done := 0 }])[k]? = x.tr.kids[k]? := by
          rw [List.getElem?_append]
          have : k < x.tr.kids.length := by omega
          simp [this]
        simpa [upd, heq, hget] using hkk
    · intro id' hid'
      have hid'' : id' < x.st.nParents := hid'
      have hs0 := hSL id' hid''
      have hq0 := hQty id' hid''
      by_cases heq : id' = id
      · rw [heq] at hs0 hq0 ⊢
        have hle : min liq ((x.st.parents id).qty - (x.st.parents id).sent) ≤ (x.st.parents id).qty - (x.st.parents id).sent :=
          Nat.min_le_right _ _
        have hshow : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } id).sent = (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) := by
          simp [upd]
        rw [hshow]
        simp [upd] at ⊢
        omega
      · have hshow : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } id').sent = (x.st.parents id').sent := by
          simp [upd, heq]
        have hqq : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } id').qty = (x.st.parents id').qty := by
          simp [upd, heq]
        rw [hshow, hqq]
        exact hs0
    · intro k hk
      have hk' : k < x.st.nChildren + 1 := hk
      by_cases heq : k = x.st.nChildren
      · subst heq
        simp [upd]
      · have hk2 : k < x.st.nChildren := by omega
        have hdl := hDL k hk2
        simpa [upd, heq] using hdl
  · simp only [advance, step, Truth.observe, Truth.record] at *
    simp [hcond] at *
    exact ⟨hNP, hNC, hQty, hSent, hCum, hCP, hKid, hSL, hDL⟩

theorem inv_fill (b : Build) (x : Sys) (k q : Nat) (hx : Inv x)
    : Inv (advance step b x (.fill k q)) := by
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hCP, hKid, hSL, hDL⟩ := hx
  by_cases hcond : k < x.st.nChildren
  · have hkp := hCP k hcond
    have hkk := hKid k hcond
    have hltK : k < x.tr.kids.length := by omega
    have hdl0 := hDL k hcond
    simp only [advance, step, Truth.observe, Truth.record]
    simp [hcond, hkk]
    refine ⟨hNP, by simpa [List.length_set] using hNC, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro id' hid'
      have hid'' : id' < x.st.nParents := hid'
      have hq0 := hQty id' hid''
      by_cases heq : id' = (x.st.children k).parent
      · subst heq
        simp [upd, hq0]
      · simp [upd, heq, hq0]
    · intro id' hid'
      have hid'' : id' < x.st.nParents := hid'
      have hs0 := hSent id' hid''
      have hshow : (upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) } id').sent = (x.st.parents id').sent := by
        by_cases heq : id' = (x.st.children k).parent
        · subst heq; simp [upd]
        · simp [upd, heq]
      have htr : ({ nOrders := x.tr.nOrders, qty := x.tr.qty, kids := x.tr.kids.set k { parent := (x.st.children k).parent, qty := (x.st.children k).qty, done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } } : Truth).sent id' = x.tr.sent id' := by
        simp only [Truth.sent]
        exact sentFor_set_done x.tr.kids k _ _ hkk id'
      rw [hshow, htr]
      exact hs0
    · intro id' hid'
      have hid'' : id' < x.st.nParents := hid'
      have hc0 := hCum id' hid''
      have hshow : (upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) } id').cum = (x.st.parents id').cum + (if (x.st.children k).parent = id' then min q ((x.st.children k).qty - (x.st.children k).done) else 0) := by
        by_cases heq : id' = (x.st.children k).parent
        · subst heq; simp [upd]
        · simp [upd, heq, Ne.symm heq]
      have htr : ({ nOrders := x.tr.nOrders, qty := x.tr.qty, kids := x.tr.kids.set k { parent := (x.st.children k).parent, qty := (x.st.children k).qty, done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } } : Truth).exec id' = x.tr.exec id' + (if (x.st.children k).parent = id' then min q ((x.st.children k).qty - (x.st.children k).done) else 0) := by
        simp only [Truth.exec]
        have := execFor_set_done x.tr.kids k { parent := (x.st.children k).parent, qty := (x.st.children k).qty, done := (x.st.children k).done } (min q ((x.st.children k).qty - (x.st.children k).done)) hkk id'
        simpa using this
      rw [hshow, htr, hc0]
    · intro j hj
      have hj' : j < x.st.nChildren := hj
      by_cases heq : j = k
      · rw [heq]
        simpa [upd] using hkp
      · have hcp0 := hCP j hj'
        simpa [upd, heq] using hcp0
    · intro j hj
      have hj' : j < x.st.nChildren := hj
      by_cases heq : j = k
      · rw [heq]
        have hget : (x.tr.kids.set k { parent := (x.st.children k).parent, qty := (x.st.children k).qty, done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) })[k]? = some { parent := (x.st.children k).parent, qty := (x.st.children k).qty, done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } := by
          rw [List.getElem?_set]
          simp [hltK]
        have hch : (upd x.st.children k { parent := (x.st.children k).parent, qty := (x.st.children k).qty, done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } k) = { parent := (x.st.children k).parent, qty := (x.st.children k).qty, done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } := by
          simp [upd]
        simp [hget, hch]
      · have hjk : k ≠ j := fun h => heq h.symm
        have hget : (x.tr.kids.set k { parent := (x.st.children k).parent, qty := (x.st.children k).qty, done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) })[j]? = x.tr.kids[j]? := by
          rw [List.getElem?_set]
          simp [hjk]
        have hkkj := hKid j hj'
        have hch : (upd x.st.children k { parent := (x.st.children k).parent, qty := (x.st.children k).qty, done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } j) = x.st.children j := by
          simp [upd, heq]
        simpa [hget, hch] using hkkj
    · intro id' hid'
      have hid'' : id' < x.st.nParents := hid'
      have hs0 := hSL id' hid''
      have hshowS : (upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) } id').sent = (x.st.parents id').sent := by
        by_cases heq : id' = (x.st.children k).parent
        · subst heq; simp [upd]
        · simp [upd, heq]
      have hshowQ : (upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) } id').qty = (x.st.parents id').qty := by
        by_cases heq : id' = (x.st.children k).parent
        · subst heq; simp [upd]
        · simp [upd, heq]
      rw [hshowS, hshowQ]
      exact hs0
    · intro j hj
      have hj' : j < x.st.nChildren := hj
      by_cases heq : j = k
      · rw [heq]
        have hle : min q ((x.st.children k).qty - (x.st.children k).done) ≤ (x.st.children k).qty - (x.st.children k).done :=
          Nat.min_le_right _ _
        have hshowD : (upd x.st.children k { parent := (x.st.children k).parent, qty := (x.st.children k).qty, done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } k).done = (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) := by
          simp [upd]
        have hshowQ : (upd x.st.children k { parent := (x.st.children k).parent, qty := (x.st.children k).qty, done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } k).qty = (x.st.children k).qty := by
          simp [upd]
        rw [hshowD, hshowQ]
        omega
      · have hj2 : j < x.st.nChildren := by omega
        have hdl := hDL j hj2
        simpa [upd, heq] using hdl
  · have hlen : x.tr.kids.length ≤ k := by omega
    have hnone : x.tr.kids[k]? = none := List.getElem?_eq_none_iff.mpr hlen
    simp only [advance, step, Truth.observe, Truth.record]
    simp [hcond, hnone]
    exact ⟨hNP, hNC, hQty, hSent, hCum, hCP, hKid, hSL, hDL⟩

theorem inv_step (b : Build) (x : Sys) (e : Event) (hx : Inv x)
    : Inv (advance step b x e) := by
  cases e with
  | parent q f => exact inv_parent b x q f hx
  | route id liq => exact inv_route b x id liq hx
  | ack k => exact inv_ack b x k hx
  | fill k q => exact inv_fill b x k q hx

theorem inv_hold (b : Build) (evs : List Event) : Inv (run step b evs) :=
  run_induction step b Inv inv_start (fun x e hx => inv_step b x e hx) evs

theorem req_fill_accounting : FillAccounting step := by
  intro b evs id hid
  have hx := inv_hold b evs
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hCP, hKid, hSL, hDL⟩ := hx
  have hid2 : id < (run step b evs).st.nParents := by omega
  exact hCum id hid2

theorem req_never_overroute : NeverOverroute step := by
  intro b evs id
  have hx := inv_hold b evs
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hCP, hKid, hSL, hDL⟩ := hx
  by_cases hid : id < (run step b evs).tr.nOrders
  · have hid2 : id < (run step b evs).st.nParents := by omega
    have hs := hSent id hid2
    have hq := hQty id hid2
    have hsl := hSL id hid2
    omega
  · have hnom : ∀ k ∈ (run step b evs).tr.kids, k.parent ≠ id := by
      intro k hm
      have hlt := mem_parent_lt (run step b evs) ⟨hNP, hNC, hQty, hSent, hCum, hCP, hKid, hSL, hDL⟩ k hm
      omega
    have hz := sentFor_zero_of_nomatch (run step b evs).tr.kids id hnom
    simp [Truth.sent, hz]

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  exact Nat.le_trans (exec_le_sent step b evs id) (req_never_overroute b evs id)

theorem req_routes_available : RoutesAvailable step := by
  intro b evs id liq
  have hx := inv_hold b evs
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hCP, hKid, hSL, hDL⟩ := hx
  have hst : (step b (run step b evs).st (.route id liq)).2 =
      if id < (run step b evs).st.nParents ∧ 0 < min liq (((run step b evs).st.parents id).qty - ((run step b evs).st.parents id).sent) then
        [⟨id, min liq (((run step b evs).st.parents id).qty - ((run step b evs).st.parents id).sent)⟩]
      else [] := by
    simp only [step]
    by_cases hc : (id < (run step b evs).st.nParents ∧ 0 < min liq (((run step b evs).st.parents id).qty - ((run step b evs).st.parents id).sent))
    · simp [hc]
    · simp [hc]
  have htr : expectedRoute (run step b evs).tr id liq =
      if id < (run step b evs).tr.nOrders ∧ 0 < min liq ((run step b evs).tr.qty id - (run step b evs).tr.sent id) then
        [⟨id, min liq ((run step b evs).tr.qty id - (run step b evs).tr.sent id)⟩]
      else [] := by
    simp [expectedRoute]
  rw [hst, htr]
  by_cases hid : id < (run step b evs).st.nParents
  · have hq := hQty id hid
    have hs := hSent id hid
    rw [hNP, hq, hs]
  · have hid2 : ¬ id < (run step b evs).tr.nOrders := by omega
    simp [hid, hid2]
theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e id hexec c hmem
  cases e with
  | parent q f =>
    simp [step] at hmem
  | ack k =>
    simp [step] at hmem
  | fill k q =>
    simp only [step] at hmem
    by_cases hc : k < (run step b evs).st.nChildren
    · simp [hc] at hmem
    · simp [hc] at hmem
  | route j liq =>
    have hroute := req_routes_available b evs j liq
    rw [hroute] at hmem
    have hexp : expectedRoute (run step b evs).tr j liq =
        (if j < (run step b evs).tr.nOrders ∧ 0 < min liq ((run step b evs).tr.qty j - (run step b evs).tr.sent j) then
          [⟨j, min liq ((run step b evs).tr.qty j - (run step b evs).tr.sent j)⟩]
        else []) := by
      simp [expectedRoute]
    rw [hexp] at hmem
    split at hmem
    · next hcond =>
      simp at hmem
      rw [hmem]
      simp
      intro heq
      rw [heq] at hcond
      have hsent := req_never_overroute b evs id
      have hexle := exec_le_sent step b evs id
      have hle2 : (run step b evs).tr.qty id ≤ (run step b evs).tr.sent id := hexec ▸ hexle
      have hseq : (run step b evs).tr.sent id = (run step b evs).tr.qty id :=
        Nat.le_antisymm hsent hle2
      rw [hseq, Nat.sub_self] at hcond
      simp at hcond
    · simp at hmem
theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  constructor
  · simp [normalOrder, run, advance, step, Truth.observe, Truth.record, Truth.empty, start, init, upd]
  · simp [normalOrder, run, advance, step, Truth.observe, Truth.record, Truth.empty, start, init, upd, Truth.exec, execFor]

end OrderRouter
