import OrderRouter.Spec
import OrderRouter.Lemmas
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

theorem upd_same {α : Type} (f : Nat → α) (k : Nat) (v : α) :
    upd f k v k = v := by simp [upd]

theorem upd_ne {α : Type} (f : Nat → α) (k : Nat) (v : α) (j : Nat) (h : j ≠ k) :
    upd f k v j = f j := by simp [upd, h]

theorem sentFor_zero_of_ne (l : List Kid) (id : Nat)
    (h : ∀ k ∈ l, k.parent ≠ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent ≠ id := h a (by simp)
    have iht : sentFor as id = 0 := ih (fun k hk => h k (by simp [hk]))
    simp [ha, iht]

theorem execFor_zero_of_ne (l : List Kid) (id : Nat)
    (h : ∀ k ∈ l, k.parent ≠ id) : execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent ≠ id := h a (by simp)
    have iht : execFor as id = 0 := ih (fun k hk => h k (by simp [hk]))
    simp [ha, iht]

theorem sentFor_append_single (l : List Kid) (pid c pid0 : Nat) :
    sentFor (l ++ [⟨pid, c, 0⟩]) pid0
      = sentFor l pid0 + (if pid = pid0 then c else 0) := by
  simp [sentFor_append]

theorem execFor_append_single (l : List Kid) (pid c pid0 : Nat) :
    execFor (l ++ [⟨pid, c, 0⟩]) pid0 = execFor l pid0 := by
  have h1 : execFor ([⟨pid, c, 0⟩] : List Kid) pid0 = 0 := by
    by_cases h : pid = pid0 <;> simp [h]
  simp [execFor_append, h1]

theorem get_append_new (l : List Kid) (v : Kid) :
    (l ++ [v])[l.length]? = some v := by
  have hle : l.length ≤ l.length := by omega
  have h := List.getElem?_append_right (l₁ := l) (l₂ := [v]) (i := l.length) hle
  have hsub : l.length - l.length = 0 := by omega
  rw [hsub] at h
  simpa using h

/-- Master invariant linking router state to ground truth. -/
def Inv (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders
  ∧ (∀ id, (x.st.parents id).qty = x.tr.qty id)
  ∧ (∀ id, id < x.tr.nOrders → (x.st.parents id).sent = x.tr.sent id)
  ∧ (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id)
  ∧ (∀ id, id < x.tr.nOrders → (x.st.parents id).sent ≤ (x.st.parents id).qty)
  ∧ x.st.nChildren = x.tr.kids.length
  ∧ (∀ k (h : k < x.st.nChildren),
      x.tr.kids[k]? = some ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done⟩)
  ∧ (∀ k (h : k < x.st.nChildren), (x.st.children k).parent < x.tr.nOrders)
  ∧ (∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)

theorem record_nil (t : Truth) : t.record [] = t := by
  cases t with
  | mk nOrders qty kids => simp [Truth.record]

theorem observe_route (t : Truth) (id liq : Nat) :
    t.observe (.route id liq) = t := rfl

theorem observe_ack (t : Truth) (k : Nat) : t.observe (.ack k) = t := rfl

theorem inv_start : Inv start := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro id; rfl
  · intro id h
    have h0 : id < 0 := by simpa [start, Truth.empty] using h
    omega
  · intro id h
    have h0 : id < 0 := by simpa [start, Truth.empty] using h
    omega
  · intro id h
    have h0 : id < 0 := by simpa [start, Truth.empty] using h
    omega
  · intro k h
    have h0 : k < 0 := by simpa [start, init] using h
    omega
  · intro k h
    have h0 : k < 0 := by simpa [start, init] using h
    omega
  · intro k hk
    simp [start, Truth.empty] at hk

theorem inv_parent (b : Build) (x : Sys) (q : Nat) (f : Bool) (hx : Inv x) :
    Inv (advance step b x (.parent q f)) := by
  obtain ⟨hNP, hQty, hSent, hCum, hLe, hLen, hChild, hPar, hMem⟩ := hx
  have hSt : ({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State).nChildren = x.st.nChildren := rfl
  have hStCh : ∀ k, (({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State).children k) = x.st.children k := fun k => rfl
  have hstep1 : (step b x.st (.parent q f)).1 = ({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State) := rfl
  have hstep2 : (step b x.st (.parent q f)).2 = ([] : List Child) := rfl
  have hadv : advance step b x (.parent q f) = (⟨({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State), x.tr.observe (.parent q f)⟩ : Sys) := by
    simp [advance, hstep1, hstep2, record_nil]
  rw [hadv]
  have hObsKids : (x.tr.observe (.parent q f)).kids = x.tr.kids := rfl
  have hObsN : (x.tr.observe (.parent q f)).nOrders = x.tr.nOrders + 1 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show x.st.nParents + 1 = (x.tr.observe (.parent q f)).nOrders
    rw [hObsN, hNP]
  · intro id0
    show ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0).qty
      = (x.tr.observe (.parent q f)).qty id0
    by_cases heq : id0 = x.st.nParents
    · subst heq
      have e1 : ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) x.st.nParents).qty = q := by
        rw [upd_same]
      have e2 : (x.tr.observe (.parent q f)).qty x.tr.nOrders = q := by
        show upd x.tr.qty x.tr.nOrders q x.tr.nOrders = q
        exact upd_same _ _ _
      have hrw : x.st.nParents = x.tr.nOrders := hNP
      rw [e1, hrw, e2]
    · have hleft : ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0).qty
          = (x.st.parents id0).qty := by
        have h : (upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0
            = x.st.parents id0 := upd_ne _ _ _ _ heq
        rw [h]
      have hright : (x.tr.observe (.parent q f)).qty id0
          = x.tr.qty id0 := by
        have hrw : x.st.nParents = x.tr.nOrders := hNP
        have h2 : id0 ≠ x.tr.nOrders := by omega
        show upd x.tr.qty x.tr.nOrders q id0 = x.tr.qty id0
        exact upd_ne _ _ _ _ h2
      rw [hleft, hright, hQty]
  · intro id0 hlt
    show ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0).sent
      = (x.tr.observe (.parent q f)).sent id0
    have hsentObs : (x.tr.observe (.parent q f)).sent id0 = x.tr.sent id0 := by
      show sentFor (x.tr.observe (.parent q f)).kids id0 = sentFor x.tr.kids id0
      rw [hObsKids]
    rw [hsentObs]
    by_cases heq : id0 = x.st.nParents
    · subst heq
      have hleft0 : ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) x.st.nParents).sent = 0 := by
        rw [upd_same]
      rw [hleft0]
      have h0 : x.tr.sent x.st.nParents = 0 := by
        apply sentFor_zero_of_ne
        intro k hk
        have hlt' : k.parent < x.tr.nOrders := hMem k hk
        omega
      omega
    · have hleft : ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0).sent
          = (x.st.parents id0).sent := by
        have h : (upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0
            = x.st.parents id0 := upd_ne _ _ _ _ heq
        rw [h]
      rw [hleft]
      have hlt' : id0 < (x.tr.observe (.parent q f)).nOrders := hlt
      rw [hObsN] at hlt'
      have hid : id0 < x.tr.nOrders := by omega
      exact hSent id0 hid
  · intro id0 hlt
    show ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0).cum
      = (x.tr.observe (.parent q f)).exec id0
    have hexecObs : (x.tr.observe (.parent q f)).exec id0 = x.tr.exec id0 := by
      show execFor (x.tr.observe (.parent q f)).kids id0 = execFor x.tr.kids id0
      rw [hObsKids]
    rw [hexecObs]
    by_cases heq : id0 = x.st.nParents
    · subst heq
      have hleft0 : ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) x.st.nParents).cum = 0 := by
        rw [upd_same]
      rw [hleft0]
      have h0 : x.tr.exec x.st.nParents = 0 := by
        apply execFor_zero_of_ne
        intro k hk
        have hlt' : k.parent < x.tr.nOrders := hMem k hk
        omega
      omega
    · have hleft : ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0).cum
          = (x.st.parents id0).cum := by
        have h : (upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0
            = x.st.parents id0 := upd_ne _ _ _ _ heq
        rw [h]
      rw [hleft]
      have hlt' : id0 < (x.tr.observe (.parent q f)).nOrders := hlt
      rw [hObsN] at hlt'
      have hid : id0 < x.tr.nOrders := by omega
      exact hCum id0 hid
  · intro id0 hlt
    show ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0).sent
      ≤ ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0).qty
    by_cases heq : id0 = x.st.nParents
    · subst heq
      rw [upd_same]
      show (0 : Nat) ≤ q
      exact Nat.zero_le _
    · have hleft : ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0).sent
          = (x.st.parents id0).sent := by
        have h : (upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0
            = x.st.parents id0 := upd_ne _ _ _ _ heq
        rw [h]
      have hleftq : ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0).qty
          = (x.st.parents id0).qty := by
        have h : (upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id0
            = x.st.parents id0 := upd_ne _ _ _ _ heq
        rw [h]
      rw [hleft, hleftq]
      have hlt' : id0 < (x.tr.observe (.parent q f)).nOrders := hlt
      rw [hObsN] at hlt'
      have hid : id0 < x.tr.nOrders := by omega
      exact hLe id0 hid
  · show x.st.nChildren = (x.tr.observe (.parent q f)).kids.length
    rw [hObsKids, hLen]
  · intro k hk
    have hk' : k < x.st.nChildren := hk
    have h := hChild k hk'
    simpa [hObsKids, hStCh] using h
  · intro k hk
    have hk' : k < x.st.nChildren := hk
    have h := hPar k hk'
    have e : (({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State).children k).parent = (x.st.children k).parent := rfl
    have hgoal : (x.st.children k).parent < x.tr.nOrders + 1 := by omega
    simpa [hObsN, e] using hgoal
  · intro k hk
    have hk' : k ∈ x.tr.kids := by simpa [hObsKids] using hk
    have h := hMem k hk'
    rw [hObsN]
    omega

theorem inv_ack (b : Build) (x : Sys) (k : Nat) (hx : Inv x) :
    Inv (advance step b x (.ack k)) := by
  have h1 : (step b x.st (.ack k)).1 = x.st := rfl
  have h2 : (step b x.st (.ack k)).2 = ([] : List Child) := rfl
  have hadv : advance step b x (.ack k) = x := by
    simp [advance, h1, h2, observe_ack, record_nil]
  rw [hadv]
  exact hx

theorem routeBySent_fst_of_false (s : State) (id liq : Nat)
    (h : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    (routeBySent s id liq).1 = s := by
  unfold routeBySent
  simp [h]

theorem routeBySent_snd_of_false (s : State) (id liq : Nat)
    (h : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    (routeBySent s id liq).2 = [] := by
  unfold routeBySent
  simp [h]

theorem routeBySent_fst_of_true (s : State) (id liq : Nat)
    (h : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) :
    (routeBySent s id liq).1
      = ({ s with parents := upd s.parents id { (s.parents id) with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) }, nChildren := s.nChildren + 1, children := upd s.children s.nChildren ⟨id, min liq ((s.parents id).qty - (s.parents id).sent), 0⟩ } : State) := by
  unfold routeBySent
  simp [h]

theorem routeBySent_snd_of_true (s : State) (id liq : Nat)
    (h : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) :
    (routeBySent s id liq).2 = [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] := by
  unfold routeBySent
  simp [h]

theorem step_fill_fst_of_false (b : Build) (s : State) (k q : Nat)
    (h : ¬ k < s.nChildren) :
    (step b s (.fill k q)).1 = s := by
  unfold step
  simp [h]

theorem step_fill_snd_of_false (b : Build) (s : State) (k q : Nat)
    (h : ¬ k < s.nChildren) :
    (step b s (.fill k q)).2 = [] := by
  unfold step
  simp [h]

theorem step_fill_fst_of_true (b : Build) (s : State) (k q : Nat)
    (h : k < s.nChildren) :
    (step b s (.fill k q)).1
      = (({ s with parents := upd s.parents (s.children k).parent { (s.parents (s.children k).parent) with cum := (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) }, children := upd s.children k { (s.children k) with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) } } : State)) := by
  unfold step
  simp [h]

theorem step_fill_snd_of_true (b : Build) (s : State) (k q : Nat)
    (h : k < s.nChildren) :
    (step b s (.fill k q)).2 = ([] : List Child) := by
  unfold step
  simp [h]

theorem inv_route (b : Build) (x : Sys) (id liq : Nat) (hx : Inv x) :
    Inv (advance step b x (.route id liq)) := by
  obtain ⟨hNP, hQty, hSent, hCum, hLe, hLen, hChild, hPar, hMem⟩ := hx
  have hstep : step b x.st (.route id liq) = routeBySent x.st id liq := rfl
  by_cases hcond : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · have hr1 := routeBySent_fst_of_true x.st id liq hcond
    have hr2 := routeBySent_snd_of_true x.st id liq hcond
    have hadv : advance step b x (.route id liq)
        = ⟨(routeBySent x.st id liq).1, x.tr.record (routeBySent x.st id liq).2⟩ := by
      simp [advance, hstep, observe_route]
    rw [hadv, hr1, hr2]
    have hid : id < x.tr.nOrders := by omega
    have hleId : (x.st.parents id).sent ≤ (x.st.parents id).qty := hLe id hid
    have hsentId : (x.st.parents id).sent = x.tr.sent id := hSent id hid
    have hqtyId : (x.st.parents id).qty = x.tr.qty id := hQty id
    have hRecN : (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).nOrders = x.tr.nOrders := rfl
    have hRecKids : (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).kids = x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] := rfl
    have hStN : (({ x.st with parents := upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }, nChildren := x.st.nChildren + 1, children := upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ } : State).nParents) = x.st.nParents := rfl
    have hStCh : ∀ k, (({ x.st with parents := upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }, nChildren := x.st.nChildren + 1, children := upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ } : State).children k) = (upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩) k := fun k => rfl
    have hStNC : (({ x.st with parents := upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }, nChildren := x.st.nChildren + 1, children := upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ } : State).nChildren) = x.st.nChildren + 1 := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (({ x.st with parents := upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }, nChildren := x.st.nChildren + 1, children := upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ } : State).nParents) = (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).nOrders
      rw [hStN, hRecN, hNP]
    · intro id0
      show ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0).qty = (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).qty id0
      have hrec : (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).qty id0 = x.tr.qty id0 := rfl
      rw [hrec]
      by_cases heq : id = id0
      · subst heq
        rw [upd_same]
        exact hqtyId
      · have hleft : ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0).qty = (x.st.parents id0).qty := by
          have h : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0 = x.st.parents id0 := upd_ne _ _ _ _ (Ne.symm heq)
          rw [h]
        rw [hleft, hQty]
    · intro id0 hlt
      show ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0).sent = (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).sent id0
      have hsentRec : (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).sent id0 = sentFor (x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩]) id0 := rfl
      rw [hsentRec, sentFor_append_single]
      have hltOld : id0 < x.tr.nOrders := by simpa [hRecN] using hlt
      by_cases heq : id = id0
      · subst heq
        have hleft : ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id).sent = (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) := by
          rw [upd_same]
        have h1 : (x.st.parents id).sent = sentFor x.tr.kids id := by
          simpa [Truth.sent] using hsentId
        rw [hleft, h1]
        simp
      · have hleft : ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0).sent = (x.st.parents id0).sent := by
          have h : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0 = x.st.parents id0 := upd_ne _ _ _ _ (Ne.symm heq)
          rw [h]
        rw [hleft]
        have h1 : (x.st.parents id0).sent = sentFor x.tr.kids id0 := by
          have h := hSent id0 hltOld
          simpa [Truth.sent] using h
        rw [h1]
        simp [heq]
    · intro id0 hlt
      show ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0).cum = (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).exec id0
      have hexecRec : (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).exec id0 = execFor (x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩]) id0 := rfl
      rw [hexecRec, execFor_append_single]
      have hltOld : id0 < x.tr.nOrders := by simpa [hRecN] using hlt
      by_cases heq : id = id0
      · subst heq
        have hleft : ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id).cum = (x.st.parents id).cum := by
          rw [upd_same]
        rw [hleft]
        exact hCum id hltOld
      · have hleft : ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0).cum = (x.st.parents id0).cum := by
          have h : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0 = x.st.parents id0 := upd_ne _ _ _ _ (Ne.symm heq)
          rw [h]
        rw [hleft]
        exact hCum id0 hltOld
    · intro id0 hlt
      show ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0).sent ≤ ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0).qty
      have hltOld : id0 < x.tr.nOrders := by simpa [hRecN] using hlt
      by_cases heq : id = id0
      · subst heq
        have hleft : ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id).sent = (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) := by
          rw [upd_same]
        have hleftq : ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id).qty = (x.st.parents id).qty := by
          rw [upd_same]
        rw [hleft, hleftq]
        omega
      · have hleft : ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0).sent = (x.st.parents id0).sent := by
          have h : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0 = x.st.parents id0 := upd_ne _ _ _ _ (Ne.symm heq)
          rw [h]
        have hleftq : ((upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0).qty = (x.st.parents id0).qty := by
          have h : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) id0 = x.st.parents id0 := upd_ne _ _ _ _ (Ne.symm heq)
          rw [h]
        rw [hleft, hleftq]
        exact hLe id0 hltOld
    · show (({ x.st with parents := upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }, nChildren := x.st.nChildren + 1, children := upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ } : State).nChildren) = (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).kids.length
      rw [hStNC, hRecKids, List.length_append, hLen]
      simp
    · intro k hk
      have hk' : k < x.st.nChildren + 1 := by simpa [hStNC] using hk
      by_cases heq : k = x.st.nChildren
      · subst heq
        have e1 : (x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩])[x.st.nChildren]? = some ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ := by
          rw [hLen]
          exact get_append_new _ _
        have e2 : ((upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩) x.st.nChildren) = ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ := upd_same _ _ _
        have hkk : (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).kids[x.st.nChildren]? = some ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ := by
          simpa [hRecKids] using e1
        simpa [hStCh, e2] using hkk
      · have hkOld : k < x.st.nChildren := by omega
        have h := hChild k hkOld
        have eOld : (x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩])[k]? = x.tr.kids[k]? := List.getElem?_append_left (by omega)
        have eCh : ((upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩) k) = x.st.children k := upd_ne _ _ _ _ heq
        have hkk : (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).kids[k]? = x.tr.kids[k]? := by
          simpa [hRecKids] using eOld
        simpa [hkk, hStCh, eCh] using h
    · intro k hk
      have hk' : k < x.st.nChildren + 1 := by simpa [hStNC] using hk
      by_cases heq : k = x.st.nChildren
      · subst heq
        have hkk : (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).nOrders = x.tr.nOrders := hRecN
        rw [hkk]
        have e2 : ((upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩) x.st.nChildren).parent = id := by
          rw [upd_same]
        have eS : ((({ x.st with parents := upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }, nChildren := x.st.nChildren + 1, children := upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ } : State).children x.st.nChildren).parent) = id := by
          simpa using e2
        rw [eS]
        exact hid
      · have hkOld : k < x.st.nChildren := by omega
        have h := hPar k hkOld
        have eCh : ((upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩) k).parent = (x.st.children k).parent := by
          rw [upd_ne _ _ _ _ heq]
        have hkk : (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).nOrders = x.tr.nOrders := hRecN
        have eS : ((({ x.st with parents := upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }, nChildren := x.st.nChildren + 1, children := upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ } : State).children k).parent) = (x.st.children k).parent := by
          simpa [hStCh] using eCh
        rw [eS, hkk]
        exact h
    · intro k hk
      have hkMem : k ∈ x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] := by
        simpa [hRecKids] using hk
      have hkk : (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]).nOrders = x.tr.nOrders := hRecN
      rw [hkk]
      rcases List.mem_append.mp hkMem with hm | hm
      · exact hMem k hm
      · simp at hm
        rw [hm]
        exact hid
  · have hr1 := routeBySent_fst_of_false x.st id liq hcond
    have hr2 := routeBySent_snd_of_false x.st id liq hcond
    have hstep2 : step b x.st (.route id liq) = routeBySent x.st id liq := hstep
    have hadv : advance step b x (.route id liq) = x := by
      simp [advance, hstep2, hr1, hr2, observe_route, record_nil]
    rw [hadv]
    exact ⟨hNP, hQty, hSent, hCum, hLe, hLen, hChild, hPar, hMem⟩

theorem inv_fill (b : Build) (x : Sys) (k q : Nat) (hx : Inv x) :
    Inv (advance step b x (.fill k q)) := by
  obtain ⟨hNP, hQty, hSent, hCum, hLe, hLen, hChild, hPar, hMem⟩ := hx
  by_cases hk : k < x.st.nChildren
  · have hkid : x.tr.kids[k]? = some ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done⟩ := hChild k hk
    have hr1 := step_fill_fst_of_true b x.st k q hk
    have hr2 := step_fill_snd_of_true b x.st k q hk
    have hObs : x.tr.observe (.fill k q) = ({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth) := by
      simp [Truth.observe, hkid]
    have hadv : advance step b x (.fill k q) = (⟨(({ x.st with parents := upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }, children := upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } } : State)), ({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth)⟩ : Sys) := by
      simp [advance, hr1, hr2, hObs, record_nil]
    rw [hadv]
    have hPidLt : (x.st.children k).parent < x.tr.nOrders := hPar k hk
    have hPidEq : (x.st.parents (x.st.children k).parent).qty = x.tr.qty (x.st.children k).parent := hQty _
    have hRecN : (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).nOrders) = x.tr.nOrders := rfl
    have hRecQty : ∀ id0, (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).qty id0) = x.tr.qty id0 := fun id0 => rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (({ x.st with parents := upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }, children := upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } } : State).nParents) = (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).nOrders)
      simpa [hRecN] using hNP
    · intro id0
      show ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0).qty = (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).qty id0)
      rw [hRecQty]
      by_cases heq : id0 = (x.st.children k).parent
      · subst heq
        rw [upd_same]
        exact hPidEq
      · have hleft : ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0).qty = (x.st.parents id0).qty := by
          have h : (upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0 = x.st.parents id0 := upd_ne _ _ _ _ heq
          rw [h]
        rw [hleft, hQty]
    · intro id0 hlt
      show ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0).sent = (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).sent id0)
      have hsentRec : (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).sent id0) = sentFor (x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩) id0 := rfl
      rw [hsentRec]
      have hsentOld : sentFor (x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩) id0 = sentFor x.tr.kids id0 :=
        sentFor_set_done _ _ _ _ hkid id0
      rw [hsentOld]
      have hltOld : id0 < x.tr.nOrders := by simpa [hRecN] using hlt
      by_cases heq : id0 = (x.st.children k).parent
      · subst heq
        have hleft : ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) (x.st.children k).parent).sent = (x.st.parents (x.st.children k).parent).sent := by
          rw [upd_same]
        rw [hleft]
        exact hSent _ hltOld
      · have hleft : ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0).sent = (x.st.parents id0).sent := by
          have h : (upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0 = x.st.parents id0 := upd_ne _ _ _ _ heq
          rw [h]
        rw [hleft]
        exact hSent _ hltOld
    · intro id0 hlt
      show ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0).cum = (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).exec id0)
      have hexecRec : (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).exec id0) = execFor (x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩) id0 := rfl
      rw [hexecRec]
      have hexecOld : execFor (x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩) id0 = execFor x.tr.kids id0 + (if (x.st.children k).parent = id0 then min q ((x.st.children k).qty - (x.st.children k).done) else 0) :=
        execFor_set_done _ _ _ _ hkid id0
      rw [hexecOld]
      have hltOld : id0 < x.tr.nOrders := by simpa [hRecN] using hlt
      by_cases heq : id0 = (x.st.children k).parent
      · subst heq
        have hleft : ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) (x.st.children k).parent).cum = (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) := by
          rw [upd_same]
        have h1 : (x.st.parents (x.st.children k).parent).cum = execFor x.tr.kids (x.st.children k).parent := by
          simpa [Truth.exec] using hCum _ hltOld
        rw [hleft, h1]
        simp
      · have hleft : ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0).cum = (x.st.parents id0).cum := by
          have h : (upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0 = x.st.parents id0 := upd_ne _ _ _ _ heq
          rw [h]
        have h1 : (x.st.parents id0).cum = execFor x.tr.kids id0 := by
          simpa [Truth.exec] using hCum id0 hltOld
        rw [hleft, h1]
        simp [(Ne.symm heq)]
    · intro id0 hlt
      show ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0).sent ≤ ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0).qty
      have hltOld : id0 < x.tr.nOrders := by simpa [hRecN] using hlt
      by_cases heq : id0 = (x.st.children k).parent
      · subst heq
        have hleft : ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) (x.st.children k).parent).sent = (x.st.parents (x.st.children k).parent).sent := by
          rw [upd_same]
        have hleftq : ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) (x.st.children k).parent).qty = (x.st.parents (x.st.children k).parent).qty := by
          rw [upd_same]
        rw [hleft, hleftq]
        exact hLe _ hltOld
      · have hleft : ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0).sent = (x.st.parents id0).sent := by
          have h : (upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0 = x.st.parents id0 := upd_ne _ _ _ _ heq
          rw [h]
        have hleftq : ((upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0).qty = (x.st.parents id0).qty := by
          have h : (upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }) id0 = x.st.parents id0 := upd_ne _ _ _ _ heq
          rw [h]
        rw [hleft, hleftq]
        exact hLe _ hltOld
    · show (({ x.st with parents := upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }, children := upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } } : State).nChildren) = (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).kids.length)
      have hStNC : (({ x.st with parents := upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }, children := upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } } : State).nChildren) = x.st.nChildren := rfl
      have hKidsLen : (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).kids.length) = x.tr.kids.length := by
        show (x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩).length = x.tr.kids.length
        rw [List.length_set]
      rw [hStNC, hKidsLen, hLen]
    · intro j hj
      have hj' : j < x.st.nChildren := by simpa using hj
      by_cases heq : k = j
      · subst heq
        have e1 : (x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩)[k]? = some ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ :=
          List.getElem?_set_self (by omega)
        have e2 : ((upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }) k) = ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ := by
          rw [upd_same]
        have hkk : (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).kids[k]?) = some ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ := e1
        have eS : ((({ x.st with parents := upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }, children := upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } } : State).children k)) = ((upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }) k) := rfl
        simpa [eS, e2] using hkk
      · have hjOld : j < x.st.nChildren := by omega
        have h := hChild j hjOld
        have eOld : (x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩)[j]? = x.tr.kids[j]? :=
          List.getElem?_set_ne heq
        have eCh : ((upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }) j) = x.st.children j := upd_ne _ _ _ _ (Ne.symm heq)
        have hStCh : ((({ x.st with parents := upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }, children := upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } } : State).children j)) = ((upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }) j) := rfl
        have hkk : (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).kids[j]?) = x.tr.kids[j]? := eOld
        simpa [hStCh, eCh, hkk] using h
    · intro j hj
      have hj' : j < x.st.nChildren := by simpa using hj
      by_cases heq : k = j
      · subst heq
        have hkkN : (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).nOrders) = x.tr.nOrders := rfl
        rw [hkkN]
        have ePar : (((( { x.st with parents := upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }, children := upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } } : State).children k)).parent) = (x.st.children k).parent := by
          show (upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } k).parent = _
          rw [upd_same]
        rw [ePar]
        exact hPidLt
      · have hjOld : j < x.st.nChildren := by omega
        have h := hPar j hjOld
        have eCh : (((upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }) j).parent) = (x.st.children j).parent := by
          rw [upd_ne _ _ _ _ (Ne.symm heq)]
        have hkkN : (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).nOrders) = x.tr.nOrders := rfl
        have eS : ((({ x.st with parents := upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) }, children := upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } } : State).children j).parent) = (x.st.children j).parent := by
          show (upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } j).parent = _
          rw [eCh]
        rw [eS, hkkN]
        exact h
    · intro kMem hkMem
      have hkkN : (({ x.tr with kids := x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ } : Truth).nOrders) = x.tr.nOrders := rfl
      rw [hkkN]
      have hkMem' : kMem ∈ x.tr.kids.set k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done)⟩ := hkMem
      rcases List.mem_or_eq_of_mem_set hkMem' with hm | hm
      · exact hMem kMem hm
      · rw [hm]
        exact hPidLt
  · have hr1 := step_fill_fst_of_false b x.st k q hk
    have hr2 := step_fill_snd_of_false b x.st k q hk
    have hlenLe : x.tr.kids.length ≤ k := by omega
    have hnone : x.tr.kids[k]? = none := List.getElem?_eq_none hlenLe
    have hadv : advance step b x (.fill k q) = x := by
      simp [advance, hr1, hr2, Truth.observe, hnone, record_nil]
    rw [hadv]
    exact ⟨hNP, hQty, hSent, hCum, hLe, hLen, hChild, hPar, hMem⟩

theorem inv_run (b : Build) (evs : List Event) : Inv (run step b evs) := by
  refine run_induction step b (fun x => Inv x) inv_start ?_ evs
  intro x e hx
  cases e with
  | parent q f => exact inv_parent b x q f hx
  | route id liq => exact inv_route b x id liq hx
  | ack k => exact inv_ack b x k hx
  | fill k q => exact inv_fill b x k q hx

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> exact ⟨rfl, rfl⟩

theorem req_routes_available : RoutesAvailable step := by
  intro b evs id liq
  have hx := inv_run b evs
  obtain ⟨hNP, hQty, hSent, hCum, hLe, hLen, hChild, hPar, hMem⟩ := hx
  have hstep : step b (run step b evs).st (.route id liq)
      = routeBySent (run step b evs).st id liq := rfl
  rw [hstep]
  by_cases hcondSt : id < (run step b evs).st.nParents ∧ 0 < min liq (((run step b evs).st.parents id).qty - ((run step b evs).st.parents id).sent)
  · have hr2 := routeBySent_snd_of_true _ _ _ hcondSt
    rw [hr2]
    have hid : id < (run step b evs).tr.nOrders := by omega
    have hq : ((run step b evs).st.parents id).qty = (run step b evs).tr.qty id := hQty id
    have hs : ((run step b evs).st.parents id).sent = (run step b evs).tr.sent id := hSent id hid
    have hNP' : (run step b evs).st.nParents = (run step b evs).tr.nOrders := hNP
    have hcondTr : id < (run step b evs).tr.nOrders ∧ 0 < min liq (((run step b evs).tr.qty id) - ((run step b evs).tr.sent id)) := by
      rw [← hNP', ← hq, ← hs]
      exact hcondSt
    show [⟨id, min liq (((run step b evs).st.parents id).qty - ((run step b evs).st.parents id).sent)⟩] = expectedRoute (run step b evs).tr id liq
    unfold expectedRoute
    simp [hcondTr, hq, hs]
  · have hr2 := routeBySent_snd_of_false _ _ _ hcondSt
    rw [hr2]
    have hcondTr : ¬ (id < (run step b evs).tr.nOrders ∧ 0 < min liq (((run step b evs).tr.qty id) - ((run step b evs).tr.sent id))) := by
      intro hcon
      obtain ⟨hlt, hpos⟩ := hcon
      have hidP : id < (run step b evs).st.nParents := by omega
      have hq : ((run step b evs).st.parents id).qty = (run step b evs).tr.qty id := hQty id
      have hs : ((run step b evs).st.parents id).sent = (run step b evs).tr.sent id := hSent id hlt
      apply hcondSt
      refine ⟨hidP, ?_⟩
      rw [hq, hs]
      exact hpos
    show ([] : List Child) = expectedRoute (run step b evs).tr id liq
    unfold expectedRoute
    simp [hcondTr]

theorem req_never_overroute : NeverOverroute step := by
  intro b evs id
  have hx := inv_run b evs
  obtain ⟨hNP, hQty, hSent, hCum, hLe, hLen, hChild, hPar, hMem⟩ := hx
  by_cases hid : id < (run step b evs).tr.nOrders
  · have hsentEq : (run step b evs).tr.sent id = ((run step b evs).st.parents id).sent := (hSent id hid).symm
    have hqtyEq : (run step b evs).tr.qty id = ((run step b evs).st.parents id).qty := (hQty id).symm
    have hle := hLe id hid
    omega
  · have hsent0 : (run step b evs).tr.sent id = 0 := by
      apply sentFor_zero_of_ne
      intro k hk
      have hlt : k.parent < (run step b evs).tr.nOrders := hMem k hk
      omega
    omega

theorem req_fill_accounting : FillAccounting step := by
  intro b evs id hid
  have hx := inv_run b evs
  obtain ⟨hNP, hQty, hSent, hCum, hLe, hLen, hChild, hPar, hMem⟩ := hx
  exact hCum id hid

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  have h1 := exec_le_sent step b evs id
  have h2 := req_never_overroute b evs id
  omega

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e id hexec c hc
  have hx := inv_run b evs
  have hsent_le : (run step b evs).tr.sent id ≤ (run step b evs).tr.qty id :=
    req_never_overroute b evs id
  have hexec_le : (run step b evs).tr.exec id ≤ (run step b evs).tr.sent id :=
    exec_le_sent step b evs id
  have hsentEq : (run step b evs).tr.sent id = (run step b evs).tr.qty id := by
    omega
  cases e with
  | parent q f =>
    have h1 : (step b (run step b evs).st (.parent q f)).2 = [] := rfl
    rw [h1] at hc
    simp at hc
  | route rid liq =>
    have hR := req_routes_available b evs rid liq
    have hstepEq : (step b (run step b evs).st (.route rid liq)).2
        = expectedRoute (run step b evs).tr rid liq := hR
    rw [hstepEq] at hc
    by_cases heq : id = rid
    · subst heq
      have hcondFalse : ¬ (id < (run step b evs).tr.nOrders ∧ 0 < min liq (((run step b evs).tr.qty id) - ((run step b evs).tr.sent id))) := by
        intro hcon
        have hpos := hcon.2
        rw [hsentEq] at hpos
        simp at hpos
      simp [expectedRoute, hcondFalse] at hc
    · have hmem : c.parent = rid := by
        by_cases hcond : rid < (run step b evs).tr.nOrders ∧ 0 < min liq (((run step b evs).tr.qty rid) - ((run step b evs).tr.sent rid))
        · simp [expectedRoute, hcond] at hc
          have heq2 : c = (⟨rid, min liq (((run step b evs).tr.qty rid) - ((run step b evs).tr.sent rid))⟩ : Child) := by
            simpa using hc
          rw [heq2]
        · simp [expectedRoute, hcond] at hc
      rw [hmem]
      exact Ne.symm heq
  | ack k =>
    have h1 : (step b (run step b evs).st (.ack k)).2 = [] := rfl
    rw [h1] at hc
    simp at hc
  | fill k q =>
    have h1 : (step b (run step b evs).st (.fill k q)).2 = [] := by
      by_cases hk : k < (run step b evs).st.nChildren
      · have h2 := step_fill_snd_of_true b (run step b evs).st k q hk
        exact h2
      · have h2 := step_fill_snd_of_false b (run step b evs).st k q hk
        exact h2
    rw [h1] at hc
    simp at hc

end OrderRouter
