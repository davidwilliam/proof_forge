import OrderRouter.Spec
import OrderRouter.Lemmas
/-!
Fixed router: every parent order takes the sent-capped path and every execution
report advances the cumulative quantity.
-/
namespace OrderRouter

/-- Regular and RLP paths: send the available liquidity capped at the shares not yet sent. -/
def routeBySent (s : State) (id liq : Nat) : State × List Child :=
  let p := s.parents id
  let c := min liq (p.qty - p.sent)
  if id < s.nParents ∧ 0 < c then
    ({ s with parents := upd s.parents id { p with sent := p.sent + c },
              nChildren := s.nChildren + 1,
              children := upd s.children s.nChildren ⟨id, c, 0⟩ }, [⟨id, c⟩])
  else (s, [])

def step : Impl := fun _ s e =>
  match e with
  | .parent q f =>
    ({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ }, [])
  | .route id liq => routeBySent s id liq
  | .ack _ => (s, [])
  | .fill k q =>
    if k < s.nChildren then
      let c := s.children k
      let x := min q (c.qty - c.done)
      let p := s.parents c.parent
      let p' := { p with cum := p.cum + x }
      ({ s with parents := upd s.parents c.parent p',
                children := upd s.children k { c with done := c.done + x } }, [])
    else (s, [])

@[simp] theorem upd_same {α : Type} (f : Nat → α) (k : Nat) (v : α) :
    upd f k v k = v := by simp [upd]

theorem upd_diff {α : Type} (f : Nat → α) (k j : Nat) (v : α) (h : j ≠ k) :
    upd f k v j = f j := by simp [upd, h]

theorem upd_diff' {α : Type} (f : Nat → α) (k j : Nat) (v : α) (h : k ≠ j) :
    upd f k v j = f j := by
  have h2 : j ≠ k := fun he => h he.symm
  simp [upd, h2]

/-- Shares sent for a fresh parent id are zero when all kids belong to older parents. -/
theorem sentFor_fresh (l : List Kid) (N id : Nat) (hb : ∀ k ∈ l, k.parent < N)
    (hN : N ≤ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent < N := hb a (by simp)
    have rest : ∀ k ∈ as, k.parent < N :=
      fun k hk => hb k (by simp [hk])
    have ihr := ih rest
    by_cases h : a.parent = id
    · subst h; omega
    · simp [h, ihr]

/-- Shares executed for a fresh parent id are zero when all kids belong to older parents. -/
theorem execFor_fresh (l : List Kid) (N id : Nat) (hb : ∀ k ∈ l, k.parent < N)
    (hN : N ≤ id) : execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent < N := hb a (by simp)
    have rest : ∀ k ∈ as, k.parent < N :=
      fun k hk => hb k (by simp [hk])
    have ihr := ih rest
    by_cases h : a.parent = id
    · subst h; omega
    · simp [h, ihr]

@[simp] theorem sentFor_single (pid c : Nat) (j : Nat) :
    sentFor [⟨pid, c, 0⟩] j = (if pid = j then c else 0) := by
  simp [sentFor_cons, sentFor_nil]

@[simp] theorem execFor_single_zero (pid c : Nat) (j : Nat) :
    execFor [⟨pid, c, 0⟩] j = 0 := by
  simp [execFor_cons, execFor_nil]

theorem if_flip {a b : Nat} {x y : Nat} (h : a = b) :
    (if a = b then x else y) = x := by simp [h]

theorem sent_append_single (l : List Kid) (pid c : Nat) (j : Nat) :
    sentFor (l ++ [⟨pid, c, 0⟩]) j = sentFor l j + (if pid = j then c else 0) := by
  simp [sentFor_append]

theorem exec_append_single_zero (l : List Kid) (pid c : Nat) (j : Nat) :
    execFor (l ++ [⟨pid, c, 0⟩]) j = execFor l j := by
  simp [execFor_append]

/-- Joint router/venue invariant. -/
def Inv (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ id, id < x.st.nParents → (x.st.parents id).qty = x.tr.qty id) ∧
  (∀ id, (x.st.parents id).sent = x.tr.sent id) ∧
  (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
  (∀ k c, x.tr.kids[k]? = some c →
    x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
  (∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) ∧
  (∀ id, x.tr.sent id ≤ x.tr.qty id)

theorem inv_start : Inv start := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id h; simp [start, init] at h
  · intro id; simp [start, init, Truth.empty, Truth.sent, sentFor_nil]
  · intro id; simp [start, init, Truth.empty, Truth.exec, execFor_nil]
  · intro k c h
    have : k < ([] : List Kid).length := by
      have h' : ([] : List Kid)[k]? = some c := by simpa [start, Truth.empty] using h
      by_cases hk : k < ([] : List Kid).length
      · exact hk
      · have hnone : ([] : List Kid)[k]? = none :=
          List.getElem?_eq_none (Nat.le_of_not_gt hk)
        rw [hnone] at h'
        cases h'
    simp at this
  · intro k h; simp [start, Truth.empty] at h
  · intro id; simp [start, init, Truth.empty, Truth.sent, sentFor_nil]

theorem inv_parent (b : Build) (x : Sys) (hx : Inv x) (q : Nat) (f : Bool) :
    Inv (advance step b x (.parent q f)) := by
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hChild, hBnd, hSentLe⟩ := hx
  simp only [advance, step, Truth.observe, Truth.record]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp; omega
  · simpa using hNC.symm ▸ rfl
  · intro id h
    simp only at h ⊢
    by_cases he : id = x.st.nParents
    · subst he
      rw [upd_same]
      rw [hNP]
      simp [upd_same]
    · rw [upd_diff _ _ _ _ he]
      have hlt : id < x.st.nParents := by omega
      have h1 := hQty id hlt
      have h2 : (upd x.tr.qty x.tr.nOrders q) id = x.tr.qty id := by
        have hne : id ≠ x.tr.nOrders := by omega
        exact upd_diff _ _ _ _ hne
      rw [hNP] at hlt
      simp [h1, h2]
  · intro id
    simp only
    by_cases he : id = x.st.nParents
    · subst he
      rw [upd_same]
      have h0 : sentFor x.tr.kids x.st.nParents = 0 :=
        sentFor_fresh x.tr.kids x.tr.nOrders x.st.nParents hBnd (by omega)
      simp [Truth.sent, h0.symm]
    · rw [upd_diff _ _ _ _ he]
      have hse := hSent id
      simp [Truth.sent, hse]
  · intro id
    simp only
    by_cases he : id = x.st.nParents
    · subst he
      rw [upd_same]
      have h0 : execFor x.tr.kids x.st.nParents = 0 :=
        execFor_fresh x.tr.kids x.tr.nOrders x.st.nParents hBnd (by omega)
      simp [Truth.exec, h0.symm]
    · rw [upd_diff _ _ _ _ he]
      have hce := hCum id
      simp [Truth.exec, hce]
  · intro k c h
    simp only [List.map_nil, List.append_nil] at h ⊢
    exact hChild k c h
  · intro k hk
    simp only [List.map_nil, List.append_nil] at hk
    simp only at ⊢
    have hkb := hBnd k hk
    omega
  · intro id
    simp only
    by_cases he : id = x.tr.nOrders
    · subst he
      have h0 : sentFor x.tr.kids x.tr.nOrders = 0 :=
        sentFor_fresh x.tr.kids x.tr.nOrders x.tr.nOrders hBnd (by omega)
      simp [Truth.sent, h0, upd_same]
    · have hqty : (upd x.tr.qty x.tr.nOrders q) id = x.tr.qty id :=
        upd_diff _ _ _ _ he
      simp [Truth.sent, hqty]
      exact hSentLe id

theorem inv_ack (b : Build) (x : Sys) (hx : Inv x) (k : Nat) :
    Inv (advance step b x (.ack k)) := by
  simpa [advance, step, Truth.observe, Truth.record,
    List.map_nil, List.append_nil] using hx

theorem route_pos (s : State) (id liq : Nat)
    (h1 : id < s.nParents)
    (h2 : 0 < min liq ((s.parents id).qty - (s.parents id).sent)) :
    routeBySent s id liq =
      ({ s with parents := upd s.parents id { s.parents id with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) },
                nChildren := s.nChildren + 1,
                children := upd s.children s.nChildren ⟨id, min liq ((s.parents id).qty - (s.parents id).sent), 0⟩ },
        [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩]) := by
  unfold routeBySent
  simp [h1, h2]

theorem route_neg (s : State) (id liq : Nat)
    (h : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    routeBySent s id liq = (s, []) := by
  unfold routeBySent
  simp [h]

theorem inv_route_pos (b : Build) (x : Sys) (hx : Inv x) (id liq : Nat)
    (hcond : id < x.st.nParents ∧
      0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    Inv (advance step b x (.route id liq)) := by
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hChild, hBnd, hSentLe⟩ := hx
  have hadv : advance step b x (.route id liq) =
    ⟨(routeBySent x.st id liq).1,
     (x.tr.observe (.route id liq)).record (routeBySent x.st id liq).2⟩ := rfl
  have hobs : x.tr.observe (.route id liq) = x.tr := rfl
  obtain ⟨h1, h2⟩ := hcond
  have hRT := route_pos x.st id liq h1 h2
  have hQtyid := hQty id h1
  have hSentid : (x.st.parents id).sent = sentFor x.tr.kids id := hSent id
  rw [hadv, hRT, hobs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show x.st.nParents = x.tr.nOrders
    exact hNP
  · show x.st.nChildren + 1 =
        (x.tr.kids ++ ([⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] : List Kid)).length
    simp [hNC]
  · intro j hj
    simp only [Truth.record] at hj ⊢
    by_cases he : j = id
    · subst he
      rw [upd_same]
      exact hQtyid
    · rw [upd_diff _ _ _ _ he]
      exact hQty j hj
  · intro j
    simp only [Truth.record, Truth.sent, List.map_cons, List.map_nil] at ⊢
    by_cases he : j = id
    · subst he
      simp [upd_same, sent_append_single, hSentid]
    · have hne : id ≠ j := fun he2 => he he2.symm
      have hSj : (x.st.parents j).sent = sentFor x.tr.kids j := hSent j
      simp [upd_diff _ _ _ _ he, sent_append_single, hne, hSj]
  · intro j
    simp only [Truth.record, Truth.exec, List.map_cons, List.map_nil] at ⊢
    by_cases he : j = id
    · rw [he, upd_same, exec_append_single_zero]
      exact hCum id
    · rw [upd_diff _ _ _ _ he, exec_append_single_zero]
      exact hCum j
  · intro k c' hkk
    simp only [Truth.record, List.map_cons, List.map_nil] at hkk ⊢
    by_cases he : k = x.st.nChildren
    · subst he
      rw [upd_same]
      have h1k : (x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩])[x.st.nChildren]? =
          some c' := hkk
      rw [hNC] at h1k
      have h2k : (x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩])[x.tr.kids.length]? =
          some (⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ : Kid) := by
        have happ := List.getElem?_append_right (l₁ := x.tr.kids)
          (l₂ := [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩])
          (i := x.tr.kids.length) (Nat.le_refl _)
        simpa using happ
      rw [h2k] at h1k
      have hce : c' =
          (⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ : Kid) :=
        (Option.some_inj.mp h1k).symm
      rw [hce]
    · rw [upd_diff _ _ _ _ he]
      have hne : k ≠ x.tr.kids.length := by omega
      have hmem : k < (x.tr.kids ++
          ([⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] : List Kid)).length := by
        by_cases hk' : k < (x.tr.kids ++
            ([⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] : List Kid)).length
        · exact hk'
        · have hnone := List.getElem?_eq_none (Nat.le_of_not_gt hk')
          rw [hnone] at hkk
          cases hkk
      have hlt : k < x.tr.kids.length := by
        simp at hmem
        omega
      have happ := List.getElem?_append_left (l₁ := x.tr.kids)
        (l₂ := [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩])
        (i := k) hlt
      rw [happ] at hkk
      exact hChild k c' hkk
  · intro k' hk'
    simp only [Truth.record, List.map_cons, List.map_nil] at hk' ⊢
    simp only [List.mem_append] at hk'
    rcases hk' with hk' | hk'
    · exact hBnd k' hk'
    · simp at hk'
      subst hk'
      show id < x.tr.nOrders
      omega
  · intro j
    simp only [Truth.record, Truth.sent, List.map_cons, List.map_nil] at ⊢
    rw [sent_append_single]
    have hle2 : sentFor x.tr.kids j ≤ x.tr.qty j := hSentLe j
    have hSid : (x.st.parents id).sent = sentFor x.tr.kids id := hSent id
    by_cases he : j = id
    · subst he
      rw [if_pos rfl]
      omega
    · have hne : id ≠ j := fun he2 => he he2.symm
      have hif : (if id = j then
          min liq ((x.st.parents id).qty - (x.st.parents id).sent) else 0) = 0 :=
        if_neg hne
      rw [hif, Nat.add_zero]
      exact hle2

theorem inv_route_neg (b : Build) (x : Sys) (hx : Inv x) (id liq : Nat)
    (hcond : ¬(id < x.st.nParents ∧
      0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent))) :
    Inv (advance step b x (.route id liq)) := by
  have hadv : advance step b x (.route id liq) =
    ⟨(routeBySent x.st id liq).1,
     (x.tr.observe (.route id liq)).record (routeBySent x.st id liq).2⟩ := rfl
  have hobs : x.tr.observe (.route id liq) = x.tr := rfl
  have hRT := route_neg x.st id liq hcond
  rw [hadv, hRT, hobs]
  simpa [Truth.record, List.map_nil, List.append_nil] using hx

theorem inv_route (b : Build) (x : Sys) (hx : Inv x) (id liq : Nat) :
    Inv (advance step b x (.route id liq)) := by
  by_cases hcond : id < x.st.nParents ∧
      0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · exact inv_route_pos b x hx id liq hcond
  · exact inv_route_neg b x hx id liq hcond

theorem fill_pos (b : Build) (s : State) (k q : Nat) (h : k < s.nChildren) :
    step b s (.fill k q) =
      ({ s with parents := upd s.parents (s.children k).parent { s.parents (s.children k).parent with cum := (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) },
                children := upd s.children k { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) } }, []) := by
  unfold step
  simp [h]

theorem fill_neg (b : Build) (s : State) (k q : Nat) (h : ¬ k < s.nChildren) :
    step b s (.fill k q) = (s, []) := by
  unfold step
  simp [h]

theorem inv_fill (b : Build) (x : Sys) (hx : Inv x) (k q : Nat) :
    Inv (advance step b x (.fill k q)) := by
  have hadv : advance step b x (.fill k q) =
    ⟨(step b x.st (.fill k q)).1,
     (x.tr.observe (.fill k q)).record (step b x.st (.fill k q)).2⟩ := rfl
  by_cases hcond : k < x.st.nChildren
  · obtain ⟨hNP, hNC, hQty, hSent, hCum, hChild, hBnd, hSentLe⟩ := hx
    have hlen : k < x.tr.kids.length := by omega
    have hex : ∃ c, x.tr.kids[k]? = some c :=
      ⟨_, List.getElem?_eq_getElem hlen⟩
    obtain ⟨cT, hcT⟩ := hex
    have hChildk := hChild k cT hcT
    have hRT := fill_pos b x.st k q hcond
    have hobs : x.tr.observe (.fill k q) =
        { x.tr with kids :=
            x.tr.kids.set k { cT with done := cT.done + min q (cT.qty - cT.done) } } := by
      simp [Truth.observe, hcT]
    rw [hadv, hRT, hobs, hChildk]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hNP
    · simpa [Truth.record, List.map_nil, List.append_nil, List.length_set] using hNC
    · intro j hj
      simp only [Truth.record, List.map_nil, List.append_nil] at hj ⊢
      by_cases he : j = cT.parent
      · subst he
        rw [upd_same]
        have hmem : cT ∈ x.tr.kids := List.mem_of_getElem? hcT
        have hlt : cT.parent < x.st.nParents := by
          have hb := hBnd cT hmem
          omega
        exact hQty _ hlt
      · rw [upd_diff _ _ _ _ he]
        exact hQty j hj
    · intro j
      simp only [Truth.record, Truth.sent, List.map_nil, List.append_nil] at ⊢
      have hsd : sentFor (x.tr.kids.set k {cT with done := cT.done + min q (cT.qty - cT.done)}) j
          = sentFor x.tr.kids j :=
        sentFor_set_done _ _ _ _ hcT _
      rw [hsd]
      by_cases he : j = cT.parent
      · subst he
        rw [upd_same]
        exact hSent _
      · rw [upd_diff _ _ _ _ he]
        exact hSent j
    · intro j
      simp only [Truth.record, Truth.exec, List.map_nil, List.append_nil] at ⊢
      have hed : execFor (x.tr.kids.set k {cT with done := cT.done + min q (cT.qty - cT.done)}) j
          = execFor x.tr.kids j + (if cT.parent = j then min q (cT.qty - cT.done) else 0) :=
        execFor_set_done _ _ _ _ hcT _
      rw [hed]
      by_cases he : j = cT.parent
      · rw [he, upd_same]
        show (x.st.parents cT.parent).cum + min q (cT.qty - cT.done) = _
        rw [if_pos rfl]
        have hC : (x.st.parents cT.parent).cum = execFor x.tr.kids cT.parent :=
          hCum cT.parent
        omega
      · rw [upd_diff _ _ _ _ he]
        have hCj : (x.st.parents j).cum = execFor x.tr.kids j := hCum j
        have hne : cT.parent ≠ j := fun e2 => he e2.symm
        rw [if_neg hne, Nat.add_zero]
        exact hCj
    · intro k' c' hkk
      simp only [Truth.record, List.map_nil, List.append_nil] at hkk ⊢
      by_cases he : k' = k
      · subst k'
        rw [upd_same]
        have hget : (x.tr.kids.set k {cT with done := cT.done + min q (cT.qty - cT.done)})[k]? =
            some {cT with done := cT.done + min q (cT.qty - cT.done)} :=
          List.getElem?_set_self (by omega)
        rw [hget] at hkk
        have hce : c' =
            {cT with done := cT.done + min q (cT.qty - cT.done)} :=
          (Option.some_inj.mp hkk).symm
        rw [hce]
      · rw [upd_diff _ _ _ _ he]
        have hne : k ≠ k' := fun e => he e.symm
        have happ : (x.tr.kids.set k {cT with done := cT.done + min q (cT.qty - cT.done)})[k']?
            = x.tr.kids[k']? :=
          List.getElem?_set_ne hne
        rw [happ] at hkk
        exact hChild k' c' hkk
    · intro k' hk'
      simp only [Truth.record, List.map_nil, List.append_nil] at hk' ⊢
      rcases List.mem_or_eq_of_mem_set hk' with hk' | rfl
      · exact hBnd k' hk'
      · have hmem : cT ∈ x.tr.kids := List.mem_of_getElem? hcT
        have hb := hBnd cT hmem
        exact hb
    · intro j
      simp only [Truth.record, Truth.sent, List.map_nil, List.append_nil] at ⊢
      have hsd : sentFor (x.tr.kids.set k {cT with done := cT.done + min q (cT.qty - cT.done)}) j
          = sentFor x.tr.kids j :=
        sentFor_set_done _ _ _ _ hcT _
      rw [hsd]
      exact hSentLe j
  · have hNC : x.st.nChildren = x.tr.kids.length := hx.2.1
    have hnone : x.tr.kids[k]? = none :=
      List.getElem?_eq_none (by omega)
    have hRT := fill_neg b x.st k q hcond
    have hobs : x.tr.observe (.fill k q) = x.tr := by
      simp [Truth.observe, hnone]
    rw [hadv, hRT, hobs]
    simpa [Truth.record, List.map_nil, List.append_nil] using hx

theorem inv_all (b : Build) (x : Sys) (e : Event) (hx : Inv x) :
    Inv (advance step b x e) := by
  cases e with
  | parent q f => exact inv_parent b x hx q f
  | route id liq => exact inv_route b x hx id liq
  | ack k => exact inv_ack b x hx k
  | fill k q => exact inv_fill b x hx k q

theorem inv_run (b : Build) (evs : List Event) : Inv (run step b evs) :=
  run_induction step b Inv inv_start (fun x e hx => inv_all b x e hx) evs

theorem expected_pos (t : Truth) (id liq : Nat) (h1 : id < t.nOrders)
    (h2 : 0 < min liq (t.qty id - t.sent id)) :
    expectedRoute t id liq = [⟨id, min liq (t.qty id - t.sent id)⟩] := by
  unfold expectedRoute
  simp [h1, h2]

theorem expected_neg (t : Truth) (id liq : Nat)
    (h : ¬ (id < t.nOrders ∧ 0 < min liq (t.qty id - t.sent id))) :
    expectedRoute t id liq = [] := by
  unfold expectedRoute
  simp [h]

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> refine ⟨?_, ?_⟩ <;> rfl

theorem req_routes_available : RoutesAvailable step := by
  intro b evs id liq
  have hx := inv_run b evs
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hChild, hBnd, hSentLe⟩ := hx
  have e1 : step b (run step b evs).st (.route id liq)
      = routeBySent (run step b evs).st id liq := rfl
  have e2 : (routeBySent (run step b evs).st id liq).2
      = expectedRoute (run step b evs).tr id liq := by
    by_cases hcond : id < (run step b evs).st.nParents ∧
        0 < min liq (((run step b evs).st.parents id).qty - ((run step b evs).st.parents id).sent)
    · obtain ⟨h1, h2⟩ := hcond
      have hQtyid := hQty id h1
      have hSentid := hSent id
      have g1 : id < (run step b evs).tr.nOrders := by omega
      have g2 : 0 < min liq ((run step b evs).tr.qty id - (run step b evs).tr.sent id) := by
        rw [← hQtyid, ← hSentid]
        exact h2
      have r2 : (routeBySent (run step b evs).st id liq).2
          = [⟨id, min liq (((run step b evs).st.parents id).qty - ((run step b evs).st.parents id).sent)⟩] := by
        rw [route_pos _ _ _ h1 h2]
      have t2 : expectedRoute (run step b evs).tr id liq
          = [⟨id, min liq ((run step b evs).tr.qty id - (run step b evs).tr.sent id)⟩] :=
        expected_pos _ _ _ g1 g2
      have hc : min liq (((run step b evs).st.parents id).qty - ((run step b evs).st.parents id).sent)
          = min liq ((run step b evs).tr.qty id - (run step b evs).tr.sent id) := by
        rw [hQtyid, hSentid]
      rw [r2, t2, hc]
    · have r2 : (routeBySent (run step b evs).st id liq).2 = ([] : List Child) := by
        rw [route_neg _ _ _ hcond]
      have gneg : ¬ (id < (run step b evs).tr.nOrders ∧
          0 < min liq ((run step b evs).tr.qty id - (run step b evs).tr.sent id)) := by
        intro hc
        obtain ⟨g1, g2⟩ := hc
        have s1 : id < (run step b evs).st.nParents := by omega
        have hQ := hQty id s1
        have hS := hSent id
        have s2 : 0 < min liq (((run step b evs).st.parents id).qty - ((run step b evs).st.parents id).sent) := by
          rw [hQ, hS]
          exact g2
        exact hcond ⟨s1, s2⟩
      have t2 : expectedRoute (run step b evs).tr id liq = [] :=
        expected_neg _ _ _ gneg
      rw [r2, t2]
  rw [e1]
  exact e2

theorem req_never_overroute : NeverOverroute step := by
  intro b evs id
  have hx := inv_run b evs
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hChild, hBnd, hSentLe⟩ := hx
  exact hSentLe id

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e id hexec c hc
  have hx := inv_run b evs
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hChild, hBnd, hSentLe⟩ := hx
  have hle1 := exec_le_sent step b evs id
  have hle2 := hSentLe id
  have hsent : (run step b evs).tr.sent id = (run step b evs).tr.qty id := by omega
  cases e with
  | parent q f =>
    have e2 : (step b (run step b evs).st (.parent q f)).2 = [] := rfl
    rw [e2] at hc
    simp at hc
  | route j liq =>
    have hRA := req_routes_available b evs j liq
    rw [hRA] at hc
    simp only [expectedRoute] at hc
    by_cases hg : j < (run step b evs).tr.nOrders ∧
        0 < min liq ((run step b evs).tr.qty j - (run step b evs).tr.sent j)
    · rw [if_pos hg] at hc
      simp only [List.mem_singleton] at hc
      have hne : j ≠ id := by
        intro heq
        rw [heq] at hg
        obtain ⟨g1, g2⟩ := hg
        rw [hsent] at g2
        simp at g2
      rw [hc]
      exact hne
    · rw [if_neg hg] at hc
      simp at hc
  | ack k =>
    have e2 : (step b (run step b evs).st (.ack k)).2 = [] := rfl
    rw [e2] at hc
    simp at hc
  | fill k q =>
    have e2 : (step b (run step b evs).st (.fill k q)).2 = [] := by
      by_cases h : k < (run step b evs).st.nChildren
      · rw [fill_pos b _ _ _ h]
      · rw [fill_neg b _ _ _ h]
    rw [e2] at hc
    simp at hc

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  have hx := inv_run b evs
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hChild, hBnd, hSentLe⟩ := hx
  have h1 := exec_le_sent step b evs id
  have h2 := hSentLe id
  omega

theorem req_fill_accounting : FillAccounting step := by
  intro b evs id _
  have hx := inv_run b evs
  obtain ⟨hNP, hNC, hQty, hSent, hCum, hChild, hBnd, hSentLe⟩ := hx
  exact hCum id

end OrderRouter
