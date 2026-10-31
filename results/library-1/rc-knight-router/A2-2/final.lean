import OrderRouter.Spec
import OrderRouter.Lemmas
namespace OrderRouter

def step : Impl := fun b s e =>
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

theorem req_normal_order_routed_aux : True := trivial
#check (NormalOrderRouted step)

theorem foo_test : True := trivial

theorem sentFor_eq_zero_of_ne_aux : ∀ (l : List Kid) (id : Nat), (∀ k ∈ l, k.parent ≠ id) → sentFor l id = 0 := by
  intro l id h
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent ≠ id := h a (by simp)
    have htl : ∀ k ∈ as, k.parent ≠ id := fun k hk => h k (by simp [hk])
    rw [if_neg ha, ih htl, Nat.zero_add]

theorem inv_base_check : (start.st.nParents = start.tr.nOrders) := by rfl

theorem upd_note : ∀ (f : Nat → ParentRec) (k : Nat) (v : ParentRec) (j : Nat), (upd f k v j).sent = (if j = k then v.sent else (f j).sent) := by
  intro f k v j
  simp only [upd]
  split <;> rfl

theorem upd_same_test : ∀ (f : Nat → Nat) (k : Nat) (v : Nat), upd f k v k = v := by
  intro f k v
  simp [upd]

theorem step_route_out_aux : ∀ (b : Build) (s : State) (id liq : Nat),
    (step b s (.route id liq)).2 = (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] else []) := by
  intro b s id liq
  unfold step
  simp only
  split
  · simp_all only
  · simp_all only

theorem sent_record_empty (t : Truth) : (t.record []).kids = t.kids := by simp [Truth.record]

theorem sent_record_nil_sent (t : Truth) (id : Nat) : sentFor (t.record []).kids id = sentFor t.kids id := by simp [Truth.record]

theorem truth_observe_parent_sent (t : Truth) (q : Nat) (f : Bool) (id : Nat) :
    sentFor (t.observe (.parent q f)).kids id = sentFor t.kids id := by
  simp [Truth.observe]

theorem truth_observe_fill_sent (t : Truth) (k q : Nat) (id : Nat) :
    sentFor (t.observe (.fill k q)).kids id = sentFor t.kids id := by
  cases h : t.kids[k]? with
  | none => simp [Truth.observe, h]
  | some c =>
    simp [Truth.observe, h]
    exact sentFor_set_done t.kids k c (c.done + min q (c.qty - c.done)) h id

theorem truth_record_sent (t : Truth) (out : List Child) (id : Nat) :
    sentFor (t.record out).kids id = sentFor t.kids id + sentFor (out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id := by
  simp [Truth.record, sentFor_append]

theorem step_parent_nParents (b : Build) (s : State) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).1.nParents = s.nParents + 1 := by simp [step]

theorem step_parent_out (b : Build) (s : State) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).2 = ([] : List Child) := by simp [step]

theorem step_ack_st (b : Build) (s : State) (k : Nat) :
    (step b s (.ack k)).1 = s := by simp [step]

theorem step_ack_out (b : Build) (s : State) (k : Nat) :
    (step b s (.ack k)).2 = ([] : List Child) := by simp [step]

theorem step_fill_out (b : Build) (s : State) (k q : Nat) :
    (step b s (.fill k q)).2 = ([] : List Child) := by
  simp only [step]
  split <;> rfl

theorem upd_parent_ne2 (f : Nat → ParentRec) (k j : Nat) (v : ParentRec) (h : j ≠ k) : upd f k v j = f j := by simp [upd, h]

theorem my_upd_eq_Parent (f : Nat → ParentRec) (k : Nat) (v : ParentRec) : upd f k v k = v := by simp [upd]

theorem my_upd_ne_Parent (f : Nat → ParentRec) (k j : Nat) (v : ParentRec) (h : j ≠ k) : upd f k v j = f j := by simp [upd, h]

theorem my_upd_eq_Nat (f : Nat → Nat) (k : Nat) (v : Nat) : upd f k v k = v := by simp [upd]

theorem my_upd_ne_Nat (f : Nat → Nat) (k j : Nat) (v : Nat) (h : j ≠ k) : upd f k v j = f j := by simp [upd, h]

theorem expected_mem_parent_aux (t : Truth) (jid liq : Nat) (c : Child) (h : c ∈ expectedRoute t jid liq) : c.parent = jid := by
  unfold expectedRoute at h
  by_cases hcond : (jid < t.nOrders ∧ 0 < min liq (t.qty jid - t.sent jid))
  · rw [if_pos hcond] at h
    simp at h
    rw [h]
  · rw [if_neg hcond] at h
    simp at h

theorem record_nOrders_aux (t : Truth) (out : List Child) : (t.record out).nOrders = t.nOrders := by simp [Truth.record]

theorem record_qty_aux (t : Truth) (out : List Child) (id : Nat) : (t.record out).qty id = t.qty id := by simp [Truth.record]

theorem record_exec_aux (t : Truth) (out : List Child) (id : Nat) : (t.record out).exec id = t.exec id := by
  simp [Truth.exec, Truth.record, execFor_append, execFor_new]

theorem record_sent_aux (t : Truth) (out : List Child) (id : Nat) : (t.record out).sent id = t.sent id + sentFor (out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id := by
  simp [Truth.sent, Truth.record, sentFor_append]

theorem observe_parent_nOrders (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).nOrders = t.nOrders + 1 := by simp [Truth.observe]

theorem observe_parent_qty_eq (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).qty t.nOrders = q := by simp [Truth.observe, upd]

theorem observe_other_nOrders_ack (t : Truth) (k : Nat) : (t.observe (.ack k)).nOrders = t.nOrders := by simp [Truth.observe]

theorem observe_fill_nOrders (t : Truth) (k q : Nat) : (t.observe (.fill k q)).nOrders = t.nOrders := by
  cases h : t.kids[k]? <;> simp [Truth.observe, h]

theorem t1 (b : Build) (s : State) (q : Nat) (f : Bool) (j : Nat) :
    ((step b s (.parent q f)).1.parents j) = (if j = s.nParents then (⟨q, f, 0, 0⟩ : ParentRec) else s.parents j) := by
  simp [step, upd]

theorem inv_nParents_start : start.st.nParents = start.tr.nOrders := rfl

theorem inv_sent_start (id : Nat) : (start.st.parents id).sent = start.tr.sent id := by
  simp [start, init, Truth.empty, Truth.sent, sentFor_nil]

theorem inv_qty_start (id : Nat) : (start.st.parents id).qty = start.tr.qty id := by
  simp [start, init, Truth.empty]

theorem step_route_eq (b : Build) (s : State) (id liq : Nat) :
    step b s (.route id liq) =
    (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
      ({ s with parents := upd s.parents id { (s.parents id) with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) },
                nChildren := s.nChildren + 1,
                children := upd s.children s.nChildren ⟨id, min liq ((s.parents id).qty - (s.parents id).sent), 0⟩ }, [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩])
    else (s, [])) := by
  simp only [step]

def Inv (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ id, (x.st.parents id).sent = sentFor x.tr.kids id) ∧
  (∀ id, (x.st.parents id).cum = execFor x.tr.kids id) ∧
  (∀ id, id < x.tr.nOrders → (x.st.parents id).qty = x.tr.qty id) ∧
  (∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → (x.st.children k).parent = c.parent ∧ (x.st.children k).qty = c.qty ∧ (x.st.children k).done = c.done) ∧
  (∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → c.parent < x.tr.nOrders)

theorem inv_start : Inv start := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro id; simp [start, init, Truth.empty]
  · intro id; simp [start, init, Truth.empty]
  · intro id _; simp [start, init, Truth.empty]
  · intro k c h; simp [start, Truth.empty] at h
  · intro k c h; simp [start, Truth.empty] at h

theorem kids_parent_ne_of_lt2 {l : List Kid} {n id : Nat} (h : ∀ (k : Nat) (c : Kid), l[k]? = some c → c.parent < n) (hle : n ≤ id) (k : Kid) (hk : k ∈ l) : k.parent ≠ id := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
  have hp := h i k hi
  omega

theorem observe_parent_kids (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).kids = t.kids := by simp [Truth.observe]

theorem observe_ack_kids (t : Truth) (k : Nat) : (t.observe (.ack k)).kids = t.kids := by simp [Truth.observe]

theorem observe_route_kids (t : Truth) (id liq : Nat) : (t.observe (.route id liq)).kids = t.kids := by simp [Truth.observe]

theorem observe_parent_nOrders2 (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).nOrders = t.nOrders + 1 := by simp [Truth.observe]

theorem step_parent_st (b : Build) (s : State) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).1 = { s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } := by simp [step]

theorem adv_parent_tr (x : Sys) (q : Nat) (f : Bool) (b : Build) :
    (advance step b x (.parent q f)).tr = (x.tr.observe (.parent q f)).record ([] : List Child) := by
  simp [advance, step_parent_out]

theorem sentFor_zero_of_all_lt3 {l : List Kid} {n id : Nat} (h : ∀ (k : Nat) (c : Kid), l[k]? = some c → c.parent < n) (hle : n ≤ id) : sentFor l id = 0 := by
  apply sentFor_eq_zero_of_ne_aux
  intro k hk
  exact kids_parent_ne_of_lt2 h hle k hk

theorem execFor_zero_aux2 : ∀ (l : List Kid) (id : Nat), (∀ k ∈ l, k.parent ≠ id) → execFor l id = 0 := by
  intro l id h
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent ≠ id := h a (by simp)
    have htl : ∀ k ∈ as, k.parent ≠ id := fun k hk => h k (by simp [hk])
    rw [if_neg ha, ih htl, Nat.zero_add]

theorem execFor_zero_of_all_lt3 {l : List Kid} {n id : Nat} (h : ∀ (k : Nat) (c : Kid), l[k]? = some c → c.parent < n) (hle : n ≤ id) : execFor l id = 0 := by
  apply execFor_zero_aux2
  intro k hk
  exact kids_parent_ne_of_lt2 h hle k hk

theorem inv_holds_test_aux2 : True := trivial

theorem parent_record_simp (t : Truth) : (t.record ([] : List Child)).kids = t.kids := by simp [Truth.record]

theorem parent_record_sent2 (t : Truth) (id : Nat) : sentFor (t.record ([] : List Child)).kids id = sentFor t.kids id := by simp [Truth.record]

theorem parent_upd_cum_eq (f : Nat → ParentRec) (k : Nat) (q : Nat) (fl : Bool) (j : Nat) : (upd f k ⟨q, fl, 0, 0⟩ j).cum = (if j = k then 0 else (f j).cum) := by simp [upd]; split <;> rfl

theorem parent_upd_qty_eq (f : Nat → ParentRec) (k : Nat) (q : Nat) (fl : Bool) (j : Nat) : (upd f k ⟨q, fl, 0, 0⟩ j).qty = (if j = k then q else (f j).qty) := by simp [upd]; split <;> rfl

theorem adv_parent_nPar (x : Sys) (q : Nat) (f : Bool) (b : Build) : (advance step b x (.parent q f)).st.nParents = x.st.nParents + 1 := by simp [advance, step_parent_st]

theorem adv_parent_kids (x : Sys) (q : Nat) (f : Bool) (b : Build) : (advance step b x (.parent q f)).tr.kids = x.tr.kids := by simp [advance, step_parent_out, Truth.record, Truth.observe]

theorem adv_parent_nOrd (x : Sys) (q : Nat) (f : Bool) (b : Build) : (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 := by simp [advance, step_parent_out, Truth.record, Truth.observe]

theorem adv_parent_nCh (x : Sys) (q : Nat) (f : Bool) (b : Build) : (advance step b x (.parent q f)).st.nChildren = x.st.nChildren := by simp [advance, step_parent_st]

def InvRA2 (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  (∀ id, id < x.tr.nOrders → (x.st.parents id).qty = x.tr.qty id) ∧
  (∀ id, (x.st.parents id).sent = sentFor x.tr.kids id)

def InvR (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  (∀ id, id < x.tr.nOrders → (x.st.parents id).qty = x.tr.qty id) ∧
  (∀ id, (x.st.parents id).sent = sentFor x.tr.kids id) ∧
  (∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → c.parent < x.tr.nOrders)

theorem invR_start : InvR start := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro id h; simp [start, Truth.empty] at h
  · intro id; simp [start, init, Truth.empty]
  · intro k c h; simp [start, Truth.empty] at h

theorem adv_parent_parents (x : Sys) (q : Nat) (f : Bool) (b : Build) : (advance step b x (.parent q f)).st.parents = upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ := by simp [advance, step_parent_st]

theorem adv_parent_qty (x : Sys) (q : Nat) (f : Bool) (b : Build) : (advance step b x (.parent q f)).tr.qty = upd x.tr.qty x.tr.nOrders q := by simp [advance, step_parent_out, Truth.record, Truth.observe]












theorem tmp_parent_npar : ∀ (b : Build) (x : Sys) (q : Nat) (f : Bool),
    (advance step b x (.parent q f)).st.nParents = x.st.nParents + 1 := by
  intro b x q f
  unfold advance step
  simp

theorem tmp_parent_trN : ∀ (b : Build) (x : Sys) (q : Nat) (f : Bool),
    (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 := by
  intro b x q f
  unfold advance step Truth.observe Truth.record
  simp

theorem tmp_parent_stpar : ∀ (b : Build) (x : Sys) (q : Nat) (f : Bool) (j : Nat),
    (advance step b x (.parent q f)).st.parents j = upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ j := by
  intro b x q f j
  unfold advance step
  simp [upd]

theorem tmp_parent_trqty : ∀ (b : Build) (x : Sys) (q : Nat) (f : Bool) (j : Nat),
    (advance step b x (.parent q f)).tr.qty j = upd x.tr.qty x.tr.nOrders q j := by
  intro b x q f j
  unfold advance step Truth.observe Truth.record
  simp [upd]

theorem tmp_parent_trkids : ∀ (b : Build) (x : Sys) (q : Nat) (f : Bool),
    (advance step b x (.parent q f)).tr.kids = x.tr.kids := by
  intro b x q f
  unfold advance step Truth.observe Truth.record
  simp

theorem tmp_obs_route : ∀ (t : Truth) (id liq : Nat),
    (t.observe (.route id liq)).kids = t.kids ∧ (t.observe (.route id liq)).nOrders = t.nOrders ∧ (t.observe (.route id liq)).qty = t.qty := by
  intro t id liq; refine ⟨rfl, rfl, rfl⟩

theorem tmp_obs_ack : ∀ (t : Truth) (k : Nat),
    (t.observe (.ack k)).kids = t.kids ∧ (t.observe (.ack k)).nOrders = t.nOrders ∧ (t.observe (.ack k)).qty = t.qty := by
  intro t k; refine ⟨rfl, rfl, rfl⟩

theorem tmp_obs_fill_NO : ∀ (t : Truth) (k q : Nat),
    (t.observe (.fill k q)).nOrders = t.nOrders ∧ (t.observe (.fill k q)).qty = t.qty := by
  intro t k q
  cases h : t.kids[k]? with
  | none => simp [Truth.observe, h]
  | some c => simp [Truth.observe, h]

theorem tmp_rec_NO : ∀ (t : Truth) (out : List Child),
    (t.record out).nOrders = t.nOrders ∧ (t.record out).qty = t.qty := by
  intro t out; simp [Truth.record]

theorem tmp_upd_qty_pos : ∀ (f : Nat → ParentRec) (k : Nat) (q : Nat) (fl : Bool) (j : Nat),
    j = k → (upd f k ⟨q, fl, 0, 0⟩ j).qty = q := by
  intro f k q fl j hj
  simp [upd, hj]

theorem tmp_upd_sent_pos : ∀ (f : Nat → ParentRec) (k : Nat) (q : Nat) (fl : Bool) (j : Nat),
    j = k → (upd f k ⟨q, fl, 0, 0⟩ j).sent = 0 := by
  intro f k q fl j hj
  simp [upd, hj]

theorem tmp_upd_qty_neg : ∀ (f : Nat → ParentRec) (k : Nat) (q : Nat) (fl : Bool) (j : Nat),
    j ≠ k → (upd f k ⟨q, fl, 0, 0⟩ j).qty = (f j).qty := by
  intro f k q fl j hj
  simp [upd, hj]

theorem tmp_upd_sent_neg : ∀ (f : Nat → ParentRec) (k : Nat) (q : Nat) (fl : Bool) (j : Nat),
    j ≠ k → (upd f k ⟨q, fl, 0, 0⟩ j).sent = (f j).sent := by
  intro f k q fl j hj
  simp [upd, hj]

theorem invR_parent5 : ∀ (b : Build) (x : Sys) (q : Nat) (f : Bool), InvR x → InvR (advance step b x (.parent q f)) := by
  intro b x q f hInv
  obtain ⟨hN, hQty, hSent, hPar⟩ := hInv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tmp_parent_npar, tmp_parent_trN, hN]
  · intro id hid
    rw [tmp_parent_stpar, tmp_parent_trqty]
    rw [tmp_parent_trN] at hid
    by_cases heq : id = x.tr.nOrders
    · subst heq
      have hR : (upd x.tr.qty x.tr.nOrders q x.tr.nOrders) = q := by simp [upd]
      rw [hR]
      have hcond : x.tr.nOrders = x.st.nParents := hN.symm
      simp [upd, hcond]
    · have hne : id ≠ x.st.nParents := by
        intro hcon
        apply heq
        omega
      have h1 : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) id) = x.st.parents id := by
        simp [upd, hne]
      have h2 : (upd x.tr.qty x.tr.nOrders q id) = x.tr.qty id := by
        simp [upd, heq]
      rw [h1, h2]
      exact hQty id (by omega)
  · intro id
    rw [tmp_parent_stpar, tmp_parent_trkids]
    by_cases heq : id = x.st.nParents
    · subst heq
      have hL : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) x.st.nParents).sent = 0 := by simp [upd]
      rw [hL]
      have hz : sentFor x.tr.kids x.st.nParents = 0 := by
        have hPar2 : ∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → c.parent < x.st.nParents := by
          rw [hN]; exact hPar
        exact sentFor_zero_of_all_lt3 hPar2 (Nat.le_refl _)
      exact hz.symm
    · have h1 : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) id) = x.st.parents id := by
        simp [upd, heq]
      rw [h1]
      exact hSent id
  · intro k c hk
    rw [tmp_parent_trkids] at hk
    rw [tmp_parent_trN]
    have hlt := hPar k c hk
    omega









theorem plan1_invR_fill : ∀ (b : Build) (x : Sys) (k q : Nat),
    InvR x → InvR (advance step b x (.fill k q)) := by sorry



theorem plan1_sentFor_append_single_aux : ∀ (l : List Kid) (id c j : Nat),
    sentFor (l ++ [⟨id, c, 0⟩]) j = sentFor l j + (if id = j then c else 0) := by
  intro l id c j
  have h : sentFor ([(⟨id, c, 0⟩ : Kid)] ) j = (if id = j then c else 0) := by
    simp
  have h2 := sentFor_append l ([(⟨id, c, 0⟩ : Kid)]) j
  rw [h2, h]

theorem plan1_sentFor_append_single : ∀ (l : List Kid) (id c j : Nat),
    sentFor (l ++ [⟨id, c, 0⟩]) j = sentFor l j + (if id = j then c else 0) := by
  intro l id c j
  have h : sentFor ([(⟨id, c, 0⟩ : Kid)]) j = (if id = j then c else 0) := by rfl
  calc sentFor (l ++ [⟨id, c, 0⟩]) j = sentFor l j + sentFor [⟨id, c, 0⟩] j := sentFor_append l [⟨id, c, 0⟩] j
    _ = sentFor l j + (if id = j then c else 0) := by rw [h]

theorem plan1_invR_route_of_no : ∀ (b : Build) (x : Sys) (id liq : Nat),
    InvR x →
    ¬ (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    InvR (advance step b x (.route id liq)) := by
  intro b x id liq hInv hNo
  obtain ⟨hN, hQty, hSent, hPar⟩ := hInv
  have hStep : step b x.st (.route id liq) = (x.st, ([] : List Child)) := by
    unfold step
    simp [hNo]
  have hObs : x.tr.observe (.route id liq) = x.tr := by
    simp [Truth.observe]
  have hAdvSt : (advance step b x (.route id liq)).st = x.st := by
    simp [advance, hStep]
  have hAdvKids : (advance step b x (.route id liq)).tr.kids = x.tr.kids := by
    simp [advance, hStep, hObs, Truth.record]
  have hAdvN : (advance step b x (.route id liq)).tr.nOrders = x.tr.nOrders := by
    simp [advance, hStep, hObs, Truth.record]
  have hAdvQty : (advance step b x (.route id liq)).tr.qty = x.tr.qty := by
    simp [advance, hStep, hObs, Truth.record]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hAdvSt, hAdvN, hN]
  · intro j hj
    rw [hAdvN] at hj
    have e1 : ((advance step b x (.route id liq)).st.parents j) = (x.st.parents j) := by rw [hAdvSt]
    have e2 : (advance step b x (.route id liq)).tr.qty j = x.tr.qty j := by rw [hAdvQty]
    rw [e1, e2]
    exact hQty j hj
  · intro j
    have e1 : ((advance step b x (.route id liq)).st.parents j).sent = (x.st.parents j).sent := by rw [hAdvSt]
    have e2 : sentFor (advance step b x (.route id liq)).tr.kids j = sentFor x.tr.kids j := by rw [hAdvKids]
    rw [e1, e2]
    exact hSent j
  · intro k c hk
    rw [hAdvKids] at hk
    rw [hAdvN]
    exact hPar k c hk

theorem myRouteYes (b : Build) (x : Sys) (pid liq : Nat)
    (hInv : InvR x)
    (hYes : pid < x.st.nParents ∧ 0 < min liq ((x.st.parents pid).qty - (x.st.parents pid).sent)) :
    InvR (advance step b x (.route pid liq)) := by
  obtain ⟨hN, hQty, hSent, hPar⟩ := hInv
  obtain ⟨hlt, hpos⟩ := hYes
  have hCond : pid < x.st.nParents ∧ 0 < min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) := ⟨hlt, hpos⟩
  have hidOrd : pid < x.tr.nOrders := by omega
  have hStep := step_route_eq b x.st pid liq
  rw [if_pos hCond] at hStep
  have hObs : x.tr.observe (.route pid liq) = x.tr := by simp [Truth.observe]
  have hAdvKids : (advance step b x (.route pid liq)).tr.kids = x.tr.kids ++ [(⟨pid, min liq ((x.st.parents pid).qty - (x.st.parents pid).sent), 0⟩ : Kid)] := by
    simp [advance, hStep, hObs, Truth.record]
  have hAdvN : (advance step b x (.route pid liq)).tr.nOrders = x.tr.nOrders := by
    simp [advance, hStep, hObs, Truth.record]
  have hAdvQty : (advance step b x (.route pid liq)).tr.qty = x.tr.qty := by
    simp [advance, hStep, hObs, Truth.record]
  have hAdvNPar : (advance step b x (.route pid liq)).st.nParents = x.st.nParents := by
    simp [advance, hStep]
  have hParEq : ∀ j, (advance step b x (.route pid liq)).st.parents j =
      (if j = pid then (({ (x.st.parents pid) with sent := (x.st.parents pid).sent + min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) } : ParentRec)) else x.st.parents j) := by
    intro j
    simp [advance, hStep, upd]
  have hSentEq : ∀ j, ((advance step b x (.route pid liq)).st.parents j).sent =
      (if j = pid then (x.st.parents pid).sent + min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) else (x.st.parents j).sent) := by
    intro j
    rw [hParEq j]
    split <;> rfl
  have hQtyEq : ∀ j, ((advance step b x (.route pid liq)).st.parents j).qty =
      (if j = pid then (x.st.parents pid).qty else (x.st.parents j).qty) := by
    intro j
    rw [hParEq j]
    split <;> rfl
  have hKidsSent : ∀ j, sentFor (advance step b x (.route pid liq)).tr.kids j =
      sentFor x.tr.kids j + (if pid = j then min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) else 0) := by
    intro j
    rw [hAdvKids]
    exact plan1_sentFor_append_single x.tr.kids pid (min liq ((x.st.parents pid).qty - (x.st.parents pid).sent)) j
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hAdvNPar, hAdvN, hN]
  · intro j hj
    rw [hAdvN] at hj
    have e1 := hQtyEq j
    have e2 : (advance step b x (.route pid liq)).tr.qty j = x.tr.qty j := by rw [hAdvQty]
    rw [e1, e2]
    by_cases heq : j = pid
    · subst j
      rw [if_pos rfl]
      exact hQty pid hj
    · rw [if_neg heq]
      exact hQty j hj
  · intro j
    rw [hSentEq j, hKidsSent j]
    by_cases heq : j = pid
    · subst j
      rw [if_pos rfl, if_pos rfl, hSent pid]
    · have h1 : (if j = pid then (x.st.parents pid).sent + min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) else (x.st.parents j).sent) = (x.st.parents j).sent := by rw [if_neg heq]
      have h2 : (if pid = j then min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) else 0) = 0 := by rw [if_neg (Ne.symm heq)]
      rw [h1, h2, Nat.add_zero]
      exact hSent j
  · intro k cKid hk
    rw [hAdvN]
    rw [hAdvKids] at hk
    have hmem : cKid ∈ (x.tr.kids ++ [(⟨pid, min liq ((x.st.parents pid).qty - (x.st.parents pid).sent), 0⟩ : Kid)]) := List.mem_of_getElem? hk
    rcases List.mem_append.mp hmem with hOld | hNew
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hOld
      exact hPar i cKid hi
    · simp at hNew
      subst hNew
      simp
      exact hidOrd

theorem myRouteYesApply (b : Build) (x : Sys) (pid liq : Nat) (hInv : InvR x) (hYes : pid < x.st.nParents ∧ 0 < min liq ((x.st.parents pid).qty - (x.st.parents pid).sent)) : InvR (advance step b x (.route pid liq)) := myRouteYes b x pid liq hInv hYes

theorem myRouteYesApply2 (b : Build) (x : Sys) (qq liq : Nat) (hInv : InvR x) (hYes : qq < x.st.nParents ∧ 0 < min liq ((x.st.parents qq).qty - (x.st.parents qq).sent)) : InvR (advance step b x (.route qq liq)) := myRouteYes b x qq liq hInv hYes

theorem plan1_invR_route : ∀ (b : Build) (x : Sys) (id liq : Nat),
    InvR x → InvR (advance step b x (.route id liq)) := by
  intro b x id liq hInv
  by_cases hYes : (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent))
  · exact myRouteYes b x id liq hInv hYes
  · exact plan1_invR_route_of_no b x id liq hInv hYes

theorem fill_st_nParents_aux (b : Build) (s : State) (k q : Nat) :
    (step b s (.fill k q)).1.nParents = s.nParents := by
  simp only [step]
  split
  · simp
  · rfl

theorem fill_st_parents_qty (b : Build) (s : State) (k q j : Nat) :
    ((step b s (.fill k q)).1.parents j).qty = (s.parents j).qty := by
  simp only [step]
  split
  · rename_i h
    simp only
    by_cases heq : j = (s.children k).parent
    · simp [upd, heq]
    · simp [upd, heq]
  · rfl

theorem fill_st_parents_sent (b : Build) (s : State) (k q j : Nat) :
    ((step b s (.fill k q)).1.parents j).sent = (s.parents j).sent := by
  simp only [step]
  split
  · rename_i h
    simp only
    by_cases heq : j = (s.children k).parent
    · simp [upd, heq]
    · simp [upd, heq]
  · rfl

theorem fill_adv_nParents (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).st.nParents = x.st.nParents := by
  simp only [advance]
  exact fill_st_nParents_aux b x.st k q

theorem fill_adv_parents_qty (b : Build) (x : Sys) (k q j : Nat) :
    ((advance step b x (.fill k q)).st.parents j).qty = (x.st.parents j).qty := by
  simp only [advance]
  exact fill_st_parents_qty b x.st k q j

theorem fill_adv_parents_sent (b : Build) (x : Sys) (k q j : Nat) :
    ((advance step b x (.fill k q)).st.parents j).sent = (x.st.parents j).sent := by
  simp only [advance]
  exact fill_st_parents_sent b x.st k q j

theorem fill_obs_sent_eq (t : Truth) (k q id : Nat) :
    sentFor (t.observe (.fill k q)).kids id = sentFor t.kids id := by
  exact truth_observe_fill_sent t k q id

theorem fill_adv_tr_nOrders2 (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders := by
  have hobs : (x.tr.observe (.fill k q)).nOrders = x.tr.nOrders :=
    (tmp_obs_fill_NO x.tr k q).1
  have hrec : ((x.tr.observe (.fill k q)).record ((step b x.st (.fill k q)).2)).nOrders =
      (x.tr.observe (.fill k q)).nOrders :=
    (tmp_rec_NO (x.tr.observe (.fill k q)) ((step b x.st (.fill k q)).2)).1
  have hadv : (advance step b x (.fill k q)).tr =
      (x.tr.observe (.fill k q)).record ((step b x.st (.fill k q)).2) := by
    simp [advance]
  rw [hadv, hrec, hobs]

theorem fill_adv_tr_qty2 (b : Build) (x : Sys) (k q : Nat) (j : Nat) :
    (advance step b x (.fill k q)).tr.qty j = x.tr.qty j := by
  have hobs : (x.tr.observe (.fill k q)).qty = x.tr.qty :=
    (tmp_obs_fill_NO x.tr k q).2
  have hrec : ((x.tr.observe (.fill k q)).record ((step b x.st (.fill k q)).2)).qty =
      (x.tr.observe (.fill k q)).qty :=
    (tmp_rec_NO (x.tr.observe (.fill k q)) ((step b x.st (.fill k q)).2)).2
  have hadv : (advance step b x (.fill k q)).tr =
      (x.tr.observe (.fill k q)).record ((step b x.st (.fill k q)).2) := by
    simp [advance]
  rw [hadv, hrec, hobs]

theorem plan1_invR_ack : ∀ (b : Build) (x : Sys) (k : Nat),
    InvR x → InvR (advance step b x (.ack k)) := by
  intro b x k hInv
  obtain ⟨hN, hQty, hSent, hPar⟩ := hInv
  have hStep1 : (step b x.st (.ack k)).1 = x.st := by simp [step]
  have hStep2 : (step b x.st (.ack k)).2 = ([] : List Child) := by simp [step]
  have hObs : x.tr.observe (.ack k) = x.tr := by simp [Truth.observe]
  have hSt : (advance step b x (.ack k)).st = x.st := by simp [advance, hStep1]
  have hTr : (advance step b x (.ack k)).tr = x.tr := by
    simp [advance, hStep1, hStep2, hObs, Truth.record]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hSt, hTr, hN]
  · intro id hid
    rw [hTr] at hid
    rw [hSt]
    have e2 : (advance step b x (.ack k)).tr.qty id = x.tr.qty id := by rw [hTr]
    rw [e2]
    exact hQty id hid
  · intro id
    have e1 : ((advance step b x (.ack k)).st.parents id).sent = (x.st.parents id).sent := by rw [hSt]
    have e2 : sentFor (advance step b x (.ack k)).tr.kids id = sentFor x.tr.kids id := by rw [hTr]
    rw [e1, e2]
    exact hSent id
  · intro k2 c hk
    rw [hTr] at hk
    have hN2 : (advance step b x (.ack k)).tr.nOrders = x.tr.nOrders := by rw [hTr]
    rw [hN2]
    exact hPar k2 c hk

theorem testPreservedProof : ∀ (b : Build) (x : Sys) (e : Event), InvR x → InvR (advance step b x e) := by
  intro b x e h
  cases e with
  | parent q f => exact invR_parent5 b x q f h
  | route id liq => exact plan1_invR_route b x id liq h
  | ack k => exact plan1_invR_ack b x k h
  | fill k q => exact plan1_invR_fill b x k q h

theorem plan0_invR_preserved : ∀ (b : Build) (x : Sys) (e : Event), InvR x → InvR (advance step b x e) := by
  intro b x e h
  cases e with
  | parent q f => exact invR_parent5 b x q f h
  | route id liq => exact plan1_invR_route b x id liq h
  | ack k => exact plan1_invR_ack b x k h
  | fill k q => exact plan1_invR_fill b x k q h

theorem check_set_lemmas (l : List Kid) (k k2 : Nat) (c0 : Kid) (x : Nat) :
    ((l.set k { c0 with done := c0.done + x })[k2]? = some c0) → True := by
  intro h
  trivial
#check @List.getElem?_set
#check @List.getElem_set

theorem fill_adv_tr_kids_eq2 (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr.kids = (x.tr.observe (.fill k q)).kids := by
  have h1 : (advance step b x (.fill k q)).tr =
      (x.tr.observe (.fill k q)).record ((step b x.st (.fill k q)).2) := by
    simp [advance]
  have h2 : (step b x.st (.fill k q)).2 = ([] : List Child) := step_fill_out b x.st k q
  rw [h1, h2]
  simp [Truth.record]

theorem set_preserves_parent_bound_aux : ∀ (l : List Kid) (k : Nat) (c0 : Kid) (d : Nat),
    l[k]? = some c0 → ∀ (n : Nat),
    (∀ (k2 : Nat) (c : Kid), l[k2]? = some c → c.parent < n) →
    ∀ (k2 : Nat) (c : Kid), (l.set k { c0 with done := d })[k2]? = some c → c.parent < n := by
  intro l
  induction l with
  | nil =>
    intro k c0 d h n hb k2 c hc
    simp at h
  | cons a as ih =>
    intro k c0 d h n hb k2 c hc
    cases k with
    | zero =>
      simp at h
      subst h
      simp only [List.set_cons_zero] at hc
      cases k2 with
      | zero =>
        simp at hc
        subst hc
        simp
        exact hb 0 a rfl
      | succ k2 =>
        simp at hc
        exact hb (k2+1) c hc
    | succ k =>
      simp at h
      simp only [List.set_cons_succ] at hc
      cases k2 with
      | zero =>
        simp at hc
        subst hc
        exact hb 0 a rfl
      | succ k2 =>
        simp at hc
        have hb_tail : ∀ (k3 : Nat) (c3 : Kid), as[k3]? = some c3 → c3.parent < n := by
          intro k3 c3 h3
          exact hb (k3+1) c3 h3
        exact ih k c0 d h n hb_tail k2 c hc

theorem fill_obs_bound_preserved2 (t : Truth) (k q n : Nat)
    (h : ∀ (k2 : Nat) (c : Kid), t.kids[k2]? = some c → c.parent < n) :
    ∀ (k2 : Nat) (c : Kid), (t.observe (.fill k q)).kids[k2]? = some c → c.parent < n := by
  intro k2 c hc
  cases hmem : t.kids[k]? with
  | none =>
    have hEq : (t.observe (.fill k q)).kids = t.kids := by simp [Truth.observe, hmem]
    rw [hEq] at hc
    exact h k2 c hc
  | some c0 =>
    have hEq : (t.observe (.fill k q)).kids = t.kids.set k { c0 with done := c0.done + min q (c0.qty - c0.done) } := by simp [Truth.observe, hmem]
    rw [hEq] at hc
    exact set_preserves_parent_bound_aux t.kids k c0 (c0.done + min q (c0.qty - c0.done)) hmem n h k2 c hc

theorem fill_adv_bound_tmp2 (b : Build) (x : Sys) (k q : Nat)
    (h : ∀ (k2 : Nat) (c : Kid), x.tr.kids[k2]? = some c → c.parent < x.tr.nOrders) :
    ∀ (k2 : Nat) (c : Kid), (advance step b x (.fill k q)).tr.kids[k2]? = some c → c.parent < (advance step b x (.fill k q)).tr.nOrders := by
  have hKids : (advance step b x (.fill k q)).tr.kids = (x.tr.observe (.fill k q)).kids := fill_adv_tr_kids_eq2 b x k q
  have hN : (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders := fill_adv_tr_nOrders2 b x k q
  intro k2 c hc
  rw [hN]
  rw [hKids] at hc
  exact fill_obs_bound_preserved2 x.tr k q x.tr.nOrders h k2 c hc

theorem plan1_invR_fill2 : ∀ (b : Build) (x : Sys) (k q : Nat),
    InvR x → InvR (advance step b x (.fill k q)) := by
  intro b x k q hInv
  obtain ⟨hN, hQty, hSent, hPar⟩ := hInv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fill_adv_nParents, fill_adv_tr_nOrders2, hN]
  · intro id hid
    rw [fill_adv_tr_nOrders2] at hid
    rw [fill_adv_tr_qty2, fill_adv_parents_qty]
    exact hQty id hid
  · intro id
    have h1 : ((advance step b x (.fill k q)).st.parents id).sent = (x.st.parents id).sent := fill_adv_parents_sent b x k q id
    have h2 : sentFor (advance step b x (.fill k q)).tr.kids id = sentFor x.tr.kids id := by
      rw [fill_adv_tr_kids_eq2 b x k q]
      exact truth_observe_fill_sent x.tr k q id
    rw [h1, h2]
    exact hSent id
  · exact fill_adv_bound_tmp2 b x k q hPar

theorem plan0_invR_run : ∀ (b : Build) (evs : List Event), InvR (run step b evs) := by
  intro b evs
  exact run_induction step b InvR invR_start (plan0_invR_preserved b) evs

theorem plan0_step_route_out_helper : ∀ (b : Build) (s : State) (id liq : Nat), (step b s (.route id liq)).2 = (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] else []) := step_route_out_aux

theorem plan0_step_route_out : ∀ (b : Build) (s : State) (id liq : Nat), (step b s (.route id liq)).2 = (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] else []) := step_route_out_aux

theorem plan0_expectedRoute_eq_test : ∀ (t : Truth) (id liq : Nat), expectedRoute t id liq = (if id < t.nOrders ∧ 0 < min liq (t.qty id - t.sent id) then [⟨id, min liq (t.qty id - t.sent id)⟩] else []) := by intro t id liq; rfl

theorem plan0_expectedRoute_eq : ∀ (t : Truth) (id liq : Nat), expectedRoute t id liq = (if id < t.nOrders ∧ 0 < min liq (t.qty id - t.sent id) then [⟨id, min liq (t.qty id - t.sent id)⟩] else []) := by intro t id liq; rfl

theorem plan0_routes_of_invR : ∀ (b : Build) (evs : List Event) (id liq : Nat), InvR (run step b evs) → (step b (run step b evs).st (.route id liq)).2 = expectedRoute (run step b evs).tr id liq := by
  intro b evs id liq hInv
  obtain ⟨hN, hQty, hSent, hPar⟩ := hInv
  rw [plan0_step_route_out, plan0_expectedRoute_eq]
  have hSentEq : ∀ j, ((((run step b evs).st).parents j).sent) = ((((run step b evs).tr).sent j)) := by
    intro j
    have h := hSent j
    simp [Truth.sent] at h ⊢
    exact h
  by_cases hlt : id < (run step b evs).st.nParents
  · have hlt2 : id < (run step b evs).tr.nOrders := by omega
    have hq : (((run step b evs).st).parents id).qty = ((run step b evs).tr).qty id := hQty id hlt2
    have hs : (((run step b evs).st).parents id).sent = ((run step b evs).tr).sent id := hSentEq id
    rw [hq, hs]
    have hN2 : (run step b evs).st.nParents = (run step b evs).tr.nOrders := hN
    rw [hN2]
  · have hlt2 : ¬ id < (run step b evs).tr.nOrders := by omega
    simp [hlt, hlt2]

theorem route_cum_ok2 (s : State) (pid liq : Nat) (b : Build) (j : Nat) :
    ((step b s (.route pid liq)).1.parents j).cum = (s.parents j).cum := by
  simp only [step]
  split
  · rename_i h
    simp only
    by_cases heq : j = pid
    · subst heq
      simp [upd]
    · simp [upd, heq]
  · rfl

theorem probe_fill_step (s : State) (k q : Nat) (b : Build) :
    step b s (.fill k q) =
    (if k < s.nChildren then
      let c := s.children k
      let x := min q (c.qty - c.done)
      let p := s.parents c.parent
      ({ s with parents := upd s.parents c.parent { p with cum := p.cum + x },
                children := upd s.children k { c with done := c.done + x } }, [])
    else (s, [])) := by
  rfl

theorem plan2_observe_fill_exec : ∀ (t : Truth) (k q id : Nat), (t.observe (.fill k q)).exec id = t.exec id + (match t.kids[k]? with | some c => if c.parent = id then min q (c.qty - c.done) else 0 | none => 0) := by
  intro t k q id
  cases h : t.kids[k]? with
  | none => simp [Truth.observe, h, Truth.exec]
  | some c =>
    simp [Truth.observe, h, Truth.exec]
    exact execFor_set_done t.kids k c (min q (c.qty - c.done)) h id












theorem my_fill_exec_test : ∀ (t : Truth) (k q id : Nat), (t.observe (.fill k q)).exec id = t.exec id + (match t.kids[k]? with | some c => if c.parent = id then min q (c.qty - c.done) else 0 | none => 0) := by
  intro t k q id
  cases h : t.kids[k]? with
  | none =>
    simp [Truth.observe, h, Truth.exec]
  | some c =>
    simp [Truth.observe, h, Truth.exec]
    exact execFor_set_done t.kids k c (min q (c.qty - c.done)) h id

theorem plan2_inv_parent : ∀ (b : Build) (x : Sys) (q : Nat) (f : Bool), Inv x → Inv (advance step b x (.parent q f)) := by
  intro b x q f hInv
  obtain ⟨hN, hChLen, hSent, hCum, hQty, hSync, hPar⟩ := hInv
  have hAdvNPar : (advance step b x (.parent q f)).st.nParents = x.st.nParents + 1 :=
    tmp_parent_npar b x q f
  have hAdvNOrd : (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 :=
    tmp_parent_trN b x q f
  have hKids : (advance step b x (.parent q f)).tr.kids = x.tr.kids :=
    tmp_parent_trkids b x q f
  have hStPar : ∀ j, (advance step b x (.parent q f)).st.parents j = upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ j :=
    fun j => tmp_parent_stpar b x q f j
  have hTrQty : ∀ j, (advance step b x (.parent q f)).tr.qty j = upd x.tr.qty x.tr.nOrders q j :=
    fun j => tmp_parent_trqty b x q f j
  have hAdvNCh : (advance step b x (.parent q f)).st.nChildren = x.st.nChildren := by
    simp [advance, step_parent_st]
  have hChFn : (advance step b x (.parent q f)).st.children = x.st.children := by
    simp [advance, step_parent_st]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hAdvNPar, hAdvNOrd, hN]
  · rw [hAdvNCh, hKids, hChLen]
  · intro id
    rw [hStPar id, hKids]
    by_cases heq : id = x.st.nParents
    · subst heq
      have hL : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) x.st.nParents).sent = 0 := by
        simp [upd]
      rw [hL]
      have hPar2 : ∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → c.parent < x.st.nParents := by
        rw [hN]; exact hPar
      exact (sentFor_zero_of_all_lt3 hPar2 (Nat.le_refl _)).symm
    · have h1 : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) id) = x.st.parents id := by
        simp [upd, heq]
      rw [h1]
      exact hSent id
  · intro id
    rw [hStPar id, hKids]
    by_cases heq : id = x.st.nParents
    · subst heq
      have hL : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) x.st.nParents).cum = 0 := by
        simp [upd]
      rw [hL]
      have hPar2 : ∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → c.parent < x.st.nParents := by
        rw [hN]; exact hPar
      exact (execFor_zero_of_all_lt3 hPar2 (Nat.le_refl _)).symm
    · have h1 : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) id) = x.st.parents id := by
        simp [upd, heq]
      rw [h1]
      exact hCum id
  · intro id hid
    rw [hAdvNOrd] at hid
    rw [hStPar id, hTrQty id]
    by_cases heq : id = x.tr.nOrders
    · subst heq
      have hR : (upd x.tr.qty x.tr.nOrders q x.tr.nOrders) = q := by simp [upd]
      rw [hR]
      have hcond : x.tr.nOrders = x.st.nParents := hN.symm
      simp [upd, hcond]
    · have hne : id ≠ x.st.nParents := by intro hcon; apply heq; omega
      have h1 : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) id) = x.st.parents id := by
        simp [upd, hne]
      have h2 : (upd x.tr.qty x.tr.nOrders q id) = x.tr.qty id := by simp [upd, heq]
      rw [h1, h2]
      exact hQty id (by omega)
  · intro k c hk
    rw [hKids] at hk
    have hsync := hSync k c hk
    have e : ((advance step b x (.parent q f)).st.children k) = x.st.children k := by rw [hChFn]
    rw [e]
    exact hsync
  · intro k c hk
    rw [hKids] at hk
    rw [hAdvNOrd]
    have hlt := hPar k c hk
    omega

theorem chkA : True := trivial
#check List.getElem?_append_left

theorem append_get_old_aux (l : List Kid) (y : Kid) (k : Nat) (c : Kid) (hget : (l ++ [y])[k]? = some c) (hlt : k < l.length) : l[k]? = some c := by
  induction l generalizing k with
  | nil => simp at hlt
  | cons a as ih =>
    cases k with
    | zero => simpa using hget
    | succ k =>
      simp at hlt
      simp at hget ⊢
      exact ih k hget hlt

theorem append_get_new2 (l : List Kid) (y : Kid) :
    (l ++ [y])[l.length]? = some y := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.length_cons, List.cons_append, List.getElem?_cons_succ]
    exact ih

theorem append_get_eq_len2 (l : List Kid) (y : Kid) (k : Nat) (c : Kid) (hget : (l ++ [y])[k]? = some c) (heq : k = l.length) : c = y := by
  subst heq
  have h := append_get_new2 l y
  rw [h] at hget
  cases hget
  rfl

theorem execFor_append_single_zero (l : List Kid) (pid c j : Nat) :
    execFor (l ++ [(⟨pid, c, 0⟩ : Kid)]) j = execFor l j := by
  have h : execFor ([(⟨pid, c, 0⟩ : Kid)]) j = 0 := by
    simp
  calc execFor (l ++ [(⟨pid, c, 0⟩ : Kid)]) j
      = execFor l j + execFor [(⟨pid, c, 0⟩ : Kid)] j := execFor_append l [(⟨pid, c, 0⟩ : Kid)] j
    _ = execFor l j := by rw [h, Nat.add_zero]

theorem append_get_old_v2 (l : List Kid) (y : Kid) (k : Nat) (c : Kid) (hget : (l ++ [y])[k]? = some c) (hlt : k < l.length) : l[k]? = some c := append_get_old_aux l y k c hget hlt

theorem route_old_child_ok (x : Sys) (pid liq : Nat) (k : Nat) (c : Kid)
    (hget : (x.tr.kids ++ [(⟨pid, min liq ((x.st.parents pid).qty - (x.st.parents pid).sent), 0⟩ : Kid)])[k]? = some c)
    (hlt : k < x.tr.kids.length) : x.tr.kids[k]? = some c :=
  append_get_old_aux x.tr.kids _ k c hget hlt

theorem chk_upd_child : True := trivial
#check (upd : (Nat → ChildRec) → Nat → ChildRec → Nat → ChildRec)













theorem plan3_route_exec_append_aux_lemma : ∀ (l : List Kid) (pid c j : Nat),
    execFor (l ++ [⟨pid, c, 0⟩]) j = execFor l j := by
  intro l pid c j
  simp [execFor_append]

theorem plan3_route_exec_append : ∀ (l : List Kid) (pid c j : Nat),
    execFor (l ++ [⟨pid, c, 0⟩]) j = execFor l j := by
  intro l pid c j
  simp [execFor_append]

theorem plan3_route_get_cases : ∀ (l : List Kid) (y : Kid) (k : Nat) (c : Kid),
    (l ++ [y])[k]? = some c → l[k]? = some c ∨ (k = l.length ∧ c = y) := by
  intro l
  induction l with
  | nil =>
    intro y k c h
    simp only [List.nil_append] at h
    cases k with
    | zero =>
      simp at h
      subst h
      exact Or.inr ⟨rfl, rfl⟩
    | succ k =>
      simp at h
  | cons a as ih =>
    intro y k c h
    cases k with
    | zero =>
      simp at h
      subst h
      exact Or.inl rfl
    | succ k =>
      simp at h
      simp only [List.getElem?_cons_succ]
      have h2 := ih y k c h
      rcases h2 with h2 | h2
      · exact Or.inl h2
      · obtain ⟨heq1, heq2⟩ := h2
        exact Or.inr ⟨by simp [heq1], heq2⟩

theorem plan3_route_yes_desc_aux_test : True := trivial

theorem route_yes_kids_tmp : ∀ (b : Build) (x : Sys) (id liq : Nat),
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    (advance step b x (.route id liq)).tr.kids =
        x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] := by
  intro b x id liq hYes
  have hPair := step_route_eq b x.st id liq
  rw [if_pos hYes] at hPair
  have hOut : (step b x.st (.route id liq)).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] := by
    rw [hPair]
  have hAdv : (advance step b x (.route id liq)).tr =
      (x.tr.observe (.route id liq)).record ((step b x.st (.route id liq)).2) := by
    rfl
  have hObs : x.tr.observe (.route id liq) = x.tr := by rfl
  rw [hAdv, hObs, hOut]
  rfl

theorem route_yes_nCh_tmp : ∀ (b : Build) (x : Sys) (id liq : Nat),
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    (advance step b x (.route id liq)).st.nChildren = x.st.nChildren + 1 := by
  intro b x id liq hYes
  have hPair := step_route_eq b x.st id liq
  rw [if_pos hYes] at hPair
  have h1 : (advance step b x (.route id liq)).st = (step b x.st (.route id liq)).1 := by rfl
  rw [h1, hPair]

theorem route_yes_children_tmp : ∀ (b : Build) (x : Sys) (id liq : Nat),
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    (advance step b x (.route id liq)).st.children =
        upd x.st.children x.st.nChildren
          ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ := by
  intro b x id liq hYes
  have hPair := step_route_eq b x.st id liq
  rw [if_pos hYes] at hPair
  have h1 : (advance step b x (.route id liq)).st = (step b x.st (.route id liq)).1 := by rfl
  rw [h1, hPair]

theorem route_yes_nOrd_tmp : ∀ (b : Build) (x : Sys) (id liq : Nat),
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    (advance step b x (.route id liq)).tr.nOrders = x.tr.nOrders := by
  intro b x id liq hYes
  have hPair := step_route_eq b x.st id liq
  rw [if_pos hYes] at hPair
  have hAdv : (advance step b x (.route id liq)).tr =
      (x.tr.observe (.route id liq)).record ((step b x.st (.route id liq)).2) := by rfl
  have hObsN : (x.tr.observe (.route id liq)).nOrders = x.tr.nOrders := by rfl
  have hRec : (((x.tr.observe (.route id liq)).record ((step b x.st (.route id liq)).2)).nOrders = (x.tr.observe (.route id liq)).nOrders) := by simp [Truth.record]
  rw [hAdv, hRec, hObsN]

theorem route_yes_nPar_tmp : ∀ (b : Build) (x : Sys) (id liq : Nat),
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    (advance step b x (.route id liq)).st.nParents = x.st.nParents := by
  intro b x id liq hYes
  have hPair := step_route_eq b x.st id liq
  rw [if_pos hYes] at hPair
  have h1 : (advance step b x (.route id liq)).st = (step b x.st (.route id liq)).1 := by rfl
  rw [h1, hPair]

theorem route_yes_qty_tmp : ∀ (b : Build) (x : Sys) (id liq : Nat),
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    (∀ j, ((advance step b x (.route id liq)).st.parents j).qty = (x.st.parents j).qty) := by
  intro b x id liq hYes j
  have hPair := step_route_eq b x.st id liq
  rw [if_pos hYes] at hPair
  have h1 : (advance step b x (.route id liq)).st = (step b x.st (.route id liq)).1 := by rfl
  rw [h1, hPair]
  by_cases heq : j = id
  · subst heq; simp [upd]
  · simp [upd, heq]

theorem route_yes_cum_tmp : ∀ (b : Build) (x : Sys) (id liq : Nat),
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    (∀ j, ((advance step b x (.route id liq)).st.parents j).cum = (x.st.parents j).cum) := by
  intro b x id liq hYes j
  have hPair := step_route_eq b x.st id liq
  rw [if_pos hYes] at hPair
  have h1 : (advance step b x (.route id liq)).st = (step b x.st (.route id liq)).1 := by rfl
  rw [h1, hPair]
  by_cases heq : j = id
  · subst heq; simp [upd]
  · simp [upd, heq]

theorem route_yes_sent_tmp : ∀ (b : Build) (x : Sys) (id liq : Nat),
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    (∀ j, ((advance step b x (.route id liq)).st.parents j).sent =
        if j = id then
          (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent)
        else (x.st.parents j).sent) := by
  intro b x id liq hYes j
  have hPair := step_route_eq b x.st id liq
  rw [if_pos hYes] at hPair
  have h1 : (advance step b x (.route id liq)).st = (step b x.st (.route id liq)).1 := by rfl
  rw [h1, hPair]
  by_cases heq : j = id
  · subst heq; simp [upd]
  · simp [upd, heq]

theorem plan3_route_yes_children_sync : ∀ (b : Build) (x : Sys) (id liq k : Nat) (c : Kid),
    Inv x →
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    (advance step b x (.route id liq)).tr.kids[k]? = some c →
    ((advance step b x (.route id liq)).st.children k).parent = c.parent ∧
    ((advance step b x (.route id liq)).st.children k).qty = c.qty ∧
    ((advance step b x (.route id liq)).st.children k).done = c.done := by
  intro b x id liq k c hInv hYes hget
  obtain ⟨hN, hChLen, hSent, hCum, hQty, hSync, hPar⟩ := hInv
  have hKids : (advance step b x (.route id liq)).tr.kids =
      x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] :=
    route_yes_kids_tmp b x id liq hYes
  have hCh : (advance step b x (.route id liq)).st.children =
      upd x.st.children x.st.nChildren
        ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ :=
    route_yes_children_tmp b x id liq hYes
  have hget2 : (x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩])[k]? = some c := by
    rw [← hKids]; exact hget
  have hcases := plan3_route_get_cases x.tr.kids ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ k c hget2
  have hbound : ∀ (l : List Kid) (kk : Nat) (cc : Kid), l[kk]? = some cc → kk < l.length := by
    intro l kk cc hh
    induction l generalizing kk with
    | nil => simp at hh
    | cons a as ih =>
      cases kk with
      | zero => simp
      | succ kk => simp at hh ⊢; exact ih kk hh
  rcases hcases with hOld | ⟨heq, heqy⟩
  · have hsync := hSync k c hOld
    obtain ⟨hp, hq, hd⟩ := hsync
    have hlt : k < x.tr.kids.length := hbound x.tr.kids k c hOld
    have hne : k ≠ x.st.nChildren := by omega
    have e : ((advance step b x (.route id liq)).st.children k) = x.st.children k := by
      rw [hCh]
      simp [upd, hne]
    rw [e]
    exact ⟨hp, hq, hd⟩
  · subst heqy
    have heqLen : k = x.st.nChildren := by omega
    have e : ((advance step b x (.route id liq)).st.children k) =
        (⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ : ChildRec) := by
      rw [hCh, heqLen]
      simp [upd]
    rw [e]
    simp

theorem plan3_route_no_inv : ∀ (b : Build) (x : Sys) (id liq : Nat),
    Inv x →
    ¬ (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    Inv (advance step b x (.route id liq)) := by
  intro b x id liq hInv hNo
  obtain ⟨hN, hChLen, hSent, hCum, hQty, hSync, hPar⟩ := hInv
  have hStep : step b x.st (.route id liq) = (x.st, ([] : List Child)) := by
    unfold step
    simp [hNo]
  have hObs : x.tr.observe (.route id liq) = x.tr := by
    simp [Truth.observe]
  have hSt : (advance step b x (.route id liq)).st = x.st := by
    simp [advance, hStep]
  have hKids : (advance step b x (.route id liq)).tr.kids = x.tr.kids := by
    simp [advance, hStep, hObs, Truth.record]
  have hNOrd : (advance step b x (.route id liq)).tr.nOrders = x.tr.nOrders := by
    simp [advance, hStep, hObs, Truth.record]
  have hQtyFn : (advance step b x (.route id liq)).tr.qty = x.tr.qty := by
    simp [advance, hStep, hObs, Truth.record]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSt, hNOrd, hN]
  · rw [hSt, hKids, hChLen]
  · intro j
    have e1 : ((advance step b x (.route id liq)).st.parents j).sent = (x.st.parents j).sent := by rw [hSt]
    have e2 : sentFor (advance step b x (.route id liq)).tr.kids j = sentFor x.tr.kids j := by rw [hKids]
    rw [e1, e2]
    exact hSent j
  · intro j
    have e1 : ((advance step b x (.route id liq)).st.parents j).cum = (x.st.parents j).cum := by rw [hSt]
    have e2 : execFor (advance step b x (.route id liq)).tr.kids j = execFor x.tr.kids j := by rw [hKids]
    rw [e1, e2]
    exact hCum j
  · intro j hj
    rw [hNOrd] at hj
    have e1 : ((advance step b x (.route id liq)).st.parents j).qty = (x.st.parents j).qty := by rw [hSt]
    have e2 : (advance step b x (.route id liq)).tr.qty j = x.tr.qty j := by rw [hQtyFn]
    rw [e1, e2]
    exact hQty j hj
  · intro k c hk
    rw [hKids] at hk
    have e : ((advance step b x (.route id liq)).st.children k) = x.st.children k := by rw [hSt]
    rw [e]
    exact hSync k c hk
  · intro k c hk
    rw [hKids] at hk
    rw [hNOrd]
    exact hPar k c hk

theorem plan3_route_yes_inv : ∀ (b : Build) (x : Sys) (pid liq : Nat),
    Inv x →
    (pid < x.st.nParents ∧ 0 < min liq ((x.st.parents pid).qty - (x.st.parents pid).sent)) →
    Inv (advance step b x (.route pid liq)) := by
  intro b x pid liq hInv hYes
  obtain ⟨hN, hChLen, hSent, hCum, hQty, hSync, hPar⟩ := hInv
  have hKids : (advance step b x (.route pid liq)).tr.kids =
      x.tr.kids ++ [⟨pid, min liq ((x.st.parents pid).qty - (x.st.parents pid).sent), 0⟩] :=
    route_yes_kids_tmp b x pid liq hYes
  have hNCh : (advance step b x (.route pid liq)).st.nChildren = x.st.nChildren + 1 :=
    route_yes_nCh_tmp b x pid liq hYes
  have hCh : (advance step b x (.route pid liq)).st.children =
      upd x.st.children x.st.nChildren
        ⟨pid, min liq ((x.st.parents pid).qty - (x.st.parents pid).sent), 0⟩ :=
    route_yes_children_tmp b x pid liq hYes
  have hNOrd : (advance step b x (.route pid liq)).tr.nOrders = x.tr.nOrders :=
    route_yes_nOrd_tmp b x pid liq hYes
  have hNPar : (advance step b x (.route pid liq)).st.nParents = x.st.nParents :=
    route_yes_nPar_tmp b x pid liq hYes
  have hQtyU : ∀ j, ((advance step b x (.route pid liq)).st.parents j).qty = (x.st.parents j).qty :=
    route_yes_qty_tmp b x pid liq hYes
  have hCumU : ∀ j, ((advance step b x (.route pid liq)).st.parents j).cum = (x.st.parents j).cum :=
    route_yes_cum_tmp b x pid liq hYes
  have hSentU : ∀ j, ((advance step b x (.route pid liq)).st.parents j).sent =
        (if j = pid then
          (x.st.parents pid).sent + min liq ((x.st.parents pid).qty - (x.st.parents pid).sent)
        else (x.st.parents j).sent) :=
    route_yes_sent_tmp b x pid liq hYes
  have hQtyFn : (advance step b x (.route pid liq)).tr.qty = x.tr.qty := by
    have hPair := step_route_eq b x.st pid liq
    rw [if_pos hYes] at hPair
    have hAdv : (advance step b x (.route pid liq)).tr =
        (x.tr.observe (.route pid liq)).record ((step b x.st (.route pid liq)).2) := rfl
    have hOut : (step b x.st (.route pid liq)).2 = [⟨pid, min liq ((x.st.parents pid).qty - (x.st.parents pid).sent)⟩] := by rw [hPair]
    have hObs : x.tr.observe (.route pid liq) = x.tr := by rfl
    rw [hAdv, hObs, hOut]
    simp [Truth.record]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hNPar, hNOrd, hN]
  · rw [hNCh, hKids, hChLen]
    simp
  · intro j
    rw [hSentU j, hKids]
    rw [plan1_sentFor_append_single x.tr.kids pid (min liq ((x.st.parents pid).qty - (x.st.parents pid).sent)) j]
    by_cases heq : j = pid
    · subst heq
      simp only [if_true]
      simp [hSent j]
    · have hne : pid ≠ j := Ne.symm heq
      simp [heq, hne, hSent j]
  · intro j
    rw [hCumU j, hKids]
    rw [plan3_route_exec_append x.tr.kids pid (min liq ((x.st.parents pid).qty - (x.st.parents pid).sent)) j]
    exact hCum j
  · intro j hj
    rw [hNOrd] at hj
    have e1 := hQtyU j
    have e2 : (advance step b x (.route pid liq)).tr.qty j = x.tr.qty j := by rw [hQtyFn]
    rw [e1, e2]
    exact hQty j hj
  · intro k c hk
    have hInvFull : Inv x := ⟨hN, hChLen, hSent, hCum, hQty, hSync, hPar⟩
    exact plan3_route_yes_children_sync b x pid liq k c hInvFull hYes hk
  · intro k c hk
    rw [hNOrd]
    rw [hKids] at hk
    have hmem : c ∈ (x.tr.kids ++ [⟨pid, min liq ((x.st.parents pid).qty - (x.st.parents pid).sent), 0⟩]) := List.mem_of_getElem? hk
    rcases List.mem_append.mp hmem with hOld | hNew
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hOld
      exact hPar i c hi
    · simp at hNew
      subst hNew
      simp
      omega

theorem plan2_inv_route : ∀ (b : Build) (x : Sys) (id liq : Nat), Inv x → Inv (advance step b x (.route id liq)) := by
  intro b x id liq hInv
  by_cases hYes : (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent))
  · exact plan3_route_yes_inv b x id liq hInv hYes
  · exact plan3_route_no_inv b x id liq hInv hYes

theorem plan2_inv_ack : ∀ (b : Build) (x : Sys) (k : Nat), Inv x → Inv (advance step b x (.ack k)) := by
  intro b x k hInv
  have hSt : (advance step b x (.ack k)).st = x.st := by
    simp [advance, step_ack_st]
  have hTr : (advance step b x (.ack k)).tr = x.tr := by
    simp [advance, step_ack_st, step_ack_out, Truth.observe, Truth.record]
  obtain ⟨hN, hChLen, hSent, hCum, hQty, hSync, hPar⟩ := hInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSt, hTr, hN]
  · rw [hSt, hTr, hChLen]
  · intro j
    have e1 : ((advance step b x (.ack k)).st.parents j).sent = (x.st.parents j).sent := by rw [hSt]
    have e2 : sentFor (advance step b x (.ack k)).tr.kids j = sentFor x.tr.kids j := by rw [hTr]
    rw [e1, e2]
    exact hSent j
  · intro j
    have e1 : ((advance step b x (.ack k)).st.parents j).cum = (x.st.parents j).cum := by rw [hSt]
    have e2 : execFor (advance step b x (.ack k)).tr.kids j = execFor x.tr.kids j := by rw [hTr]
    rw [e1, e2]
    exact hCum j
  · intro j hj
    rw [hTr] at hj
    have e1 : ((advance step b x (.ack k)).st.parents j).qty = (x.st.parents j).qty := by rw [hSt]
    have e2 : (advance step b x (.ack k)).tr.qty j = x.tr.qty j := by rw [hTr]
    rw [e1, e2]
    exact hQty j hj
  · intro k2 c hk
    rw [hTr] at hk
    have e : ((advance step b x (.ack k)).st.children k2) = x.st.children k2 := by rw [hSt]
    rw [e]
    exact hSync k2 c hk
  · intro k2 c hk
    rw [hTr] at hk
    have hN2 : (advance step b x (.ack k)).tr.nOrders = x.tr.nOrders := by rw [hTr]
    rw [hN2]
    exact hPar k2 c hk

theorem fill_helper_exists_of_lt : ∀ (l : List Kid) (k : Nat), k < l.length → ∃ c, l[k]? = some c := by
  intro l
  induction l with
  | nil => intro k h; simp at h
  | cons a as ih =>
    intro k h
    cases k with
    | zero => exact ⟨a, rfl⟩
    | succ k =>
      simp at h ⊢
      exact ih k h

theorem fill_adv_nCh_aux : ∀ (b : Build) (x : Sys) (k q : Nat),
    (advance step b x (.fill k q)).st.nChildren = x.st.nChildren := by
  intro b x k q
  simp only [advance, step]
  split
  · simp
  · rfl

theorem fill_adv_kids_len_aux : ∀ (b : Build) (x : Sys) (k q : Nat),
    (advance step b x (.fill k q)).tr.kids.length = (x.tr.observe (.fill k q)).kids.length := by
  intro b x k q
  have h1 : (advance step b x (.fill k q)).tr =
      (x.tr.observe (.fill k q)).record ((step b x.st (.fill k q)).2) := by
    simp [advance]
  have h2 : (step b x.st (.fill k q)).2 = ([] : List Child) := step_fill_out b x.st k q
  rw [h1, h2]
  simp [Truth.record]

theorem fill_obs_len_aux : ∀ (t : Truth) (k q : Nat),
    (t.observe (.fill k q)).kids.length = t.kids.length := by
  intro t k q
  cases h : t.kids[k]? with
  | none => simp [Truth.observe, h]
  | some c => simp [Truth.observe, h]

theorem fill_adv_cum_aux : ∀ (b : Build) (s : State) (k q j : Nat),
    ((step b s (.fill k q)).1.parents j).cum =
      if k < s.nChildren then
        (if (s.children k).parent = j then (s.parents ((s.children k).parent)).cum + min q ((s.children k).qty - (s.children k).done) else (s.parents j).cum)
      else (s.parents j).cum := by
  intro b s k q j
  simp only [step]
  split
  · rename_i h
    simp only
    by_cases heq : (s.children k).parent = j
    · subst heq
      simp [upd]
    · simp [upd, heq, Ne.symm heq]
  · rfl

theorem fill_router_parents_cum_aux2 : ∀ (b : Build) (s : State) (k q j : Nat),
    ((step b s (.fill k q)).1.parents j).cum =
      (if k < s.nChildren then
        (if (s.children k).parent = j then (s.parents ((s.children k).parent)).cum + min q ((s.children k).qty - (s.children k).done) else (s.parents j).cum)
      else (s.parents j).cum) := by
  intro b s k q j
  simp only [step]
  split
  · rename_i h
    simp only
    by_cases heq : (s.children k).parent = j
    · subst heq
      simp [upd]
    · have heq2 : ¬ (j = (s.children k).parent) := fun hh => heq hh.symm
      simp [upd, heq, heq2]
  · rfl

theorem fill_adv_exec_aux2 : ∀ (b : Build) (x : Sys) (k q j : Nat),
    (advance step b x (.fill k q)).tr.exec j = (x.tr.observe (.fill k q)).exec j := by
  intro b x k q j
  have h1 : (advance step b x (.fill k q)).tr =
      (x.tr.observe (.fill k q)).record ((step b x.st (.fill k q)).2) := by
    simp [advance]
  have h2 : (step b x.st (.fill k q)).2 = ([] : List Child) := step_fill_out b x.st k q
  rw [h1, h2, record_exec_aux]

theorem fill_router_children_aux2 : ∀ (b : Build) (s : State) (k q j : Nat),
    ((step b s (.fill k q)).1.children j) =
      (if k < s.nChildren then
        (if j = k then ({ (s.children k) with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) } : ChildRec) else s.children j)
      else s.children j) := by
  intro b s k q j
  simp only [step]
  split
  · rename_i h
    simp only
    by_cases heq : j = k
    · subst heq
      simp [upd]
    · simp [upd, heq]
  · rfl

theorem plan4_fill_get_of_lt : ∀ (b : Build) (x : Sys) (k : Nat),
    Inv x → k < x.st.nChildren →
    ∃ c, x.tr.kids[k]? = some c ∧
      (x.st.children k).parent = c.parent ∧
      (x.st.children k).qty = c.qty ∧
      (x.st.children k).done = c.done := by
  intro b x k hInv hlt
  obtain ⟨hN, hChLen, hSent, hCum, hQty, hSync, hPar⟩ := hInv
  have hlen : k < x.tr.kids.length := by omega
  obtain ⟨c, hc⟩ := fill_helper_exists_of_lt x.tr.kids k hlen
  exact ⟨c, hc, (hSync k c hc).1, (hSync k c hc).2.1, (hSync k c hc).2.2⟩












theorem plan4_fill_adv_of_not_lt_aux_test : ∀ (l : List Kid) (k : Nat), ¬ k < l.length → l[k]? = none := by
  intro l
  induction l with
  | nil => intro k _; rfl
  | cons a as ih =>
    intro k h
    cases k with
    | zero => simp at h
    | succ k => simp only [List.getElem?_cons_succ]; exact ih k (by simp at h ⊢; omega)

theorem plan4_notlt_helper_unique1 : ∀ (l : List Kid) (k : Nat), ¬ k < l.length → l[k]? = none := by
  intro l
  induction l with
  | nil => intro k _; rfl
  | cons a as ih =>
    intro k h
    cases k with
    | zero => simp at h
    | succ k => simp only [List.getElem?_cons_succ]; exact ih k (by simp at h ⊢; omega)

theorem plan4_getNone_of_not_lt_aux : ∀ (l : List Kid) (k : Nat), ¬ k < l.length → l[k]? = none := by
  intro l
  induction l with
  | nil =>
    intro k _; rfl
  | cons a as ih =>
    intro k h
    cases k with
    | zero => simp at h
    | succ k =>
      simp only [List.getElem?_cons_succ]
      apply ih
      simp at h ⊢
      omega

theorem plan4_fill_adv_of_not_lt : ∀ (b : Build) (x : Sys) (k q : Nat),
    Inv x → ¬ k < x.st.nChildren →
    advance step b x (.fill k q) = x := by
  intro b x k q hInv hNot
  obtain ⟨hN, hChLen, hSent, hCum, hQty, hSync, hPar⟩ := hInv
  have hSt1 : (step b x.st (.fill k q)).1 = x.st := by
    simp only [step, hNot, ↓reduceIte]
  have hOut : (step b x.st (.fill k q)).2 = ([] : List Child) := by
    simp only [step, hNot, ↓reduceIte]
  have hNotLen : ¬ k < x.tr.kids.length := by omega
  have hNone : x.tr.kids[k]? = none :=
    plan4_getNone_of_not_lt_aux x.tr.kids k hNotLen
  have hObs : x.tr.observe (.fill k q) = x.tr := by
    simp only [Truth.observe, hNone]
  have hEq : advance step b x (.fill k q) = (⟨x.st, x.tr⟩ : Sys) := by
    simp only [advance, hSt1, hOut, hObs]
    congr 1
    simp only [Truth.record, List.map_nil, List.append_nil]
  calc advance step b x (.fill k q) = (⟨x.st, x.tr⟩ : Sys) := hEq
    _ = x := by cases x; rfl

theorem plan4_fill_adv_kids_of_some : ∀ (b : Build) (x : Sys) (k q : Nat) (c : Kid),
    x.tr.kids[k]? = some c →
    (advance step b x (.fill k q)).tr.kids =
      x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) } := by
  intro b x k q c h
  have h2 := fill_adv_tr_kids_eq2 b x k q
  rw [h2]
  simp [Truth.observe, h]

theorem plan4_fill_cum_of_lt : ∀ (b : Build) (x : Sys) (k q : Nat),
    Inv x → k < x.st.nChildren →
    ∀ j, ((advance step b x (.fill k q)).st.parents j).cum =
      execFor (advance step b x (.fill k q)).tr.kids j := by
  intro b x k q hInv hlt j
  obtain ⟨c, hc, hp, hq, hd⟩ := plan4_fill_get_of_lt b x k hInv hlt
  obtain ⟨hN, hChLen, hSent, hCum, hQty, hSync, hPar⟩ := hInv
  have hKidsEq : (advance step b x (.fill k q)).tr.kids =
      x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) } :=
    plan4_fill_adv_kids_of_some b x k q c hc
  have hSt : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := rfl
  have hCumStep := fill_router_parents_cum_aux2 b x.st k q j
  rw [hSt, hCumStep, if_pos hlt, hp]
  rw [hKidsEq, execFor_set_done x.tr.kids k c (min q (c.qty - c.done)) hc j]
  by_cases heq : c.parent = j
  · have hj : j = c.parent := heq.symm
    subst hj
    rw [if_pos rfl, if_pos rfl, hCum c.parent, hq, hd]
  · rw [if_neg heq, if_neg heq, hCum j, Nat.add_zero]

theorem set_get_same_aux : ∀ (l : List Kid) (k : Nat) (a : Kid), k < l.length → (l.set k a)[k]? = some a := by
  intro l
  induction l with
  | nil => intro k a h; simp at h
  | cons hd tl ih =>
    intro k a h
    cases k with
    | zero => simp
    | succ k => simp only [List.set_cons_succ, List.getElem?_cons_succ]; exact ih k a (by simp at h ⊢; omega)

theorem set_get_other_aux : ∀ (l : List Kid) (k : Nat) (a : Kid) (k2 : Nat), k2 ≠ k → (l.set k a)[k2]? = l[k2]? := by
  intro l
  induction l with
  | nil => intro k a k2 _; simp [List.set]
  | cons hd tl ih =>
    intro k a k2 hne
    cases k with
    | zero =>
      cases k2 with
      | zero => simp at hne
      | succ k2 => simp
    | succ k =>
      cases k2 with
      | zero => simp
      | succ k2 =>
        simp only [List.set_cons_succ, List.getElem?_cons_succ]
        exact ih k a k2 (by omega)

theorem plan4_fill_sync_of_lt : ∀ (b : Build) (x : Sys) (k q : Nat),
    Inv x → k < x.st.nChildren →
    ∀ (k2 : Nat) (c2 : Kid),
      (advance step b x (.fill k q)).tr.kids[k2]? = some c2 →
      ((advance step b x (.fill k q)).st.children k2).parent = c2.parent ∧
      ((advance step b x (.fill k q)).st.children k2).qty = c2.qty ∧
      ((advance step b x (.fill k q)).st.children k2).done = c2.done := by
  intro b x k q hInv hlt k2 c2 hget
  obtain ⟨c, hc, hp, hq, hd⟩ := plan4_fill_get_of_lt b x k hInv hlt
  obtain ⟨hN, hChLen, hSent, hCum, hQty, hSync, hPar⟩ := hInv
  have hKidsEq : (advance step b x (.fill k q)).tr.kids =
      x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) } :=
    plan4_fill_adv_kids_of_some b x k q c hc
  have hget2 : (x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) })[k2]? = some c2 := by
    rw [← hKidsEq]; exact hget
  have hChEq := fill_router_children_aux2 b x.st k q k2
  have hAdvCh : ((advance step b x (.fill k q)).st.children k2) = ((step b x.st (.fill k q)).1.children k2) := rfl
  rw [hAdvCh, hChEq, if_pos hlt]
  by_cases heq : k2 = k
  · subst heq
    have hlen : k2 < x.tr.kids.length := by omega
    have hSame : (x.tr.kids.set k2 { c with done := c.done + min q (c.qty - c.done) })[k2]? =
        some { c with done := c.done + min q (c.qty - c.done) } :=
      set_get_same_aux x.tr.kids k2 _ hlen
    have hc2eq : c2 = { c with done := c.done + min q (c.qty - c.done) } := by
      rw [hSame] at hget2
      cases hget2
      rfl
    subst hc2eq
    have hminEq : min q ((x.st.children k2).qty - (x.st.children k2).done) = min q (c.qty - c.done) := by
      rw [hq, hd]
    simp only [if_true]
    refine ⟨?_, ?_, ?_⟩
    · exact hp
    · exact hq
    · rw [hminEq, hd]
  · have hold : x.tr.kids[k2]? = some c2 := by
      have hother : (x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) })[k2]? = x.tr.kids[k2]? :=
        set_get_other_aux x.tr.kids k _ k2 heq
      rw [hother] at hget2
      exact hget2
    have hsync := hSync k2 c2 hold
    obtain ⟨hsp, hsq, hsd⟩ := hsync
    simp only [heq, ↓reduceIte]
    exact ⟨hsp, hsq, hsd⟩

theorem plan4_fill_easy_of_lt : ∀ (b : Build) (x : Sys) (k q : Nat),
    Inv x → k < x.st.nChildren →
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
    (advance step b x (.fill k q)).st.nChildren =
        (advance step b x (.fill k q)).tr.kids.length ∧
    (∀ j, ((advance step b x (.fill k q)).st.parents j).sent =
        sentFor (advance step b x (.fill k q)).tr.kids j) ∧
    (∀ j, j < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents j).qty =
          (advance step b x (.fill k q)).tr.qty j) ∧
    (∀ (k2 : Nat) (c2 : Kid),
      (advance step b x (.fill k q)).tr.kids[k2]? = some c2 →
        c2.parent < (advance step b x (.fill k q)).tr.nOrders) := by
  intro b x k q hInv hlt
  obtain ⟨hN, hChLen, hSent, hCum, hQty, hSync, hPar⟩ := hInv
  have hNP : (advance step b x (.fill k q)).st.nParents = x.st.nParents :=
    fill_adv_nParents b x k q
  have hNO : (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders :=
    fill_adv_tr_nOrders2 b x k q
  have hNC : (advance step b x (.fill k q)).st.nChildren = x.st.nChildren :=
    fill_adv_nCh_aux b x k q
  have hKL1 : (advance step b x (.fill k q)).tr.kids.length =
      (x.tr.observe (.fill k q)).kids.length :=
    fill_adv_kids_len_aux b x k q
  have hKL2 : (x.tr.observe (.fill k q)).kids.length = x.tr.kids.length :=
    fill_obs_len_aux x.tr k q
  have hKL : (advance step b x (.fill k q)).tr.kids.length = x.tr.kids.length := by
    rw [hKL1, hKL2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hNP, hNO, hN]
  · rw [hNC, hKL, hChLen]
  · intro j
    rw [fill_adv_parents_sent b x k q j]
    have hKids : (advance step b x (.fill k q)).tr.kids =
        (x.tr.observe (.fill k q)).kids :=
      fill_adv_tr_kids_eq2 b x k q
    have hS : sentFor (x.tr.observe (.fill k q)).kids j = sentFor x.tr.kids j :=
      truth_observe_fill_sent x.tr k q j
    rw [hKids, hS]
    exact hSent j
  · intro j hj
    rw [hNO] at hj
    rw [fill_adv_parents_qty b x k q j, fill_adv_tr_qty2 b x k q j]
    exact hQty j hj
  · exact fill_adv_bound_tmp2 b x k q hPar

theorem plan2_inv_fill : ∀ (b : Build) (x : Sys) (k q : Nat), Inv x → Inv (advance step b x (.fill k q)) := by
  intro b x k q hInv
  by_cases hlt : k < x.st.nChildren
  · have hEasy := plan4_fill_easy_of_lt b x k q hInv hlt
    obtain ⟨hNP, hNC, hSent, hQty, hPar⟩ := hEasy
    have hCum := plan4_fill_cum_of_lt b x k q hInv hlt
    have hSync := plan4_fill_sync_of_lt b x k q hInv hlt
    exact ⟨hNP, hNC, hSent, hCum, hQty, hSync, hPar⟩
  · have hEq := plan4_fill_adv_of_not_lt b x k q hInv hlt
    rw [hEq]
    exact hInv

theorem plan2_run_inv : ∀ (b : Build) (evs : List Event), Inv (run step b evs) := by
  intro b evs
  apply run_induction step b Inv inv_start _ evs
  intro x e h
  cases e with
  | parent q f => exact plan2_inv_parent b x q f h
  | route id liq => exact plan2_inv_route b x id liq h
  | ack k => exact plan2_inv_ack b x k h
  | fill k q => exact plan2_inv_fill b x k q h

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> constructor <;> rfl

theorem req_routes_available : RoutesAvailable step := by
  have hpres : ∀ (b : Build) (x : Sys) (e : Event), InvR x → InvR (advance step b x e) := by
    intro b x e h
    cases e with
    | parent q f => exact invR_parent5 b x q f h
    | route id liq => exact plan1_invR_route b x id liq h
    | ack k => exact plan1_invR_ack b x k h
    | fill k q => exact plan1_invR_fill2 b x k q h
  have hrun : ∀ (b : Build) (evs : List Event), InvR (run step b evs) := by
    intro b evs
    exact run_induction step b InvR invR_start (hpres b) evs
  intro b evs id liq
  exact plan0_routes_of_invR b evs id liq (hrun b evs)

theorem req_never_overroute : NeverOverroute step := by
  intro b evs id
  let P : Sys → Prop := fun x => InvR x ∧ ∀ j, x.tr.sent j ≤ x.tr.qty j
  have h0 : P start := by
    refine ⟨invR_start, ?_⟩
    intro j
    have hs0 : start.tr.sent j = 0 := by simp [Truth.sent, start, Truth.empty]
    have hq0 : start.tr.qty j = 0 := by simp [start, Truth.empty]
    rw [hs0, hq0]
    exact Nat.zero_le 0
  have hs : ∀ x e, P x → P (advance step b x e) := by
    intro x e hx
    obtain ⟨hInv, hLE⟩ := hx
    refine ⟨?_, ?_⟩
    · cases e with
      | parent q f => exact invR_parent5 b x q f hInv
      | route pid liq => exact plan1_invR_route b x pid liq hInv
      | ack k => exact plan1_invR_ack b x k hInv
      | fill k q => exact plan1_invR_fill2 b x k q hInv
    · cases e with
      | parent q f =>
        intro j
        have hKids : (advance step b x (.parent q f)).tr.kids = x.tr.kids := adv_parent_kids x q f b
        have hSent : (advance step b x (.parent q f)).tr.sent j = x.tr.sent j := by simp [Truth.sent, hKids]
        have hQtyEq : (advance step b x (.parent q f)).tr.qty = upd x.tr.qty x.tr.nOrders q := adv_parent_qty x q f b
        by_cases heq : j = x.tr.nOrders
        · subst j
          rw [hSent]
          have hqnew : (advance step b x (.parent q f)).tr.qty x.tr.nOrders = q := by
            rw [hQtyEq]; simp [upd]
          rw [hqnew]
          obtain ⟨hN, hQty, hSent0, hPar⟩ := hInv
          have hz : x.tr.sent x.tr.nOrders = 0 := by
            have hPar2 : ∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → c.parent < x.tr.nOrders := hPar
            exact sentFor_zero_of_all_lt3 hPar2 (Nat.le_refl _)
          rw [hz]
          exact Nat.zero_le q
        · have hQty : (advance step b x (.parent q f)).tr.qty j = x.tr.qty j := by
            rw [hQtyEq]; simp [upd, heq]
          rw [hSent, hQty]
          exact hLE j
      | route pid liq =>
        intro j
        have hQtyEq : (advance step b x (.route pid liq)).tr.qty j = x.tr.qty j := by
          simp [advance, Truth.observe, Truth.record]
        by_cases hYes : (pid < x.st.nParents ∧ 0 < min liq ((x.st.parents pid).qty - (x.st.parents pid).sent))
        · obtain ⟨hN, hQty, hSent0, hPar⟩ := hInv
          have hidOrd : pid < x.tr.nOrders := by omega
          have hq : (x.st.parents pid).qty = x.tr.qty pid := hQty pid hidOrd
          have hs0 : (x.st.parents pid).sent = x.tr.sent pid := by
            have h := hSent0 pid
            simp [Truth.sent] at h ⊢
            exact h
          have hStep := step_route_eq b x.st pid liq
          rw [if_pos hYes] at hStep
          have hObs : x.tr.observe (.route pid liq) = x.tr := by simp [Truth.observe]
          have hKids : (advance step b x (.route pid liq)).tr.kids = x.tr.kids ++ [(⟨pid, min liq ((x.st.parents pid).qty - (x.st.parents pid).sent), 0⟩ : Kid)] := by
            simp [advance, hStep, hObs, Truth.record]
          have hSentEq : (advance step b x (.route pid liq)).tr.sent j = x.tr.sent j + (if pid = j then min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) else 0) := by
            simp only [Truth.sent, hKids]
            exact plan1_sentFor_append_single x.tr.kids pid (min liq ((x.st.parents pid).qty - (x.st.parents pid).sent)) j
          rw [hSentEq, hQtyEq, hq, hs0]
          by_cases heq : pid = j
          · subst j
            rw [if_pos rfl]
            have hle : x.tr.sent pid ≤ x.tr.qty pid := hLE pid
            have hmin : min liq (x.tr.qty pid - x.tr.sent pid) ≤ x.tr.qty pid - x.tr.sent pid := Nat.min_le_right _ _
            omega
          · rw [if_neg heq]
            simp
            exact hLE j
        · have hStepNo : step b x.st (.route pid liq) = (x.st, ([] : List Child)) := by
            unfold step
            simp [hYes]
          have hObs : x.tr.observe (.route pid liq) = x.tr := by simp [Truth.observe]
          have hKidsNo : (advance step b x (.route pid liq)).tr.kids = x.tr.kids := by
            simp [advance, hStepNo, hObs, Truth.record]
          have hSentEq : (advance step b x (.route pid liq)).tr.sent j = x.tr.sent j := by
            simp [Truth.sent, hKidsNo]
          rw [hSentEq, hQtyEq]
          exact hLE j
      | ack k =>
        intro j
        have hSentEq : (advance step b x (.ack k)).tr.sent j = x.tr.sent j := by
          have hStep2 : (step b x.st (.ack k)).2 = ([] : List Child) := by simp [step]
          have hObs : x.tr.observe (.ack k) = x.tr := by simp [Truth.observe]
          have hKids : (advance step b x (.ack k)).tr.kids = x.tr.kids := by
            simp [advance, hStep2, hObs, Truth.record]
          simp [Truth.sent, hKids]
        have hQtyEq2 : (advance step b x (.ack k)).tr.qty j = x.tr.qty j := by
          simp [advance, Truth.observe, Truth.record]
        rw [hSentEq, hQtyEq2]
        exact hLE j
      | fill k q =>
        intro j
        have hSentEq : (advance step b x (.fill k q)).tr.sent j = x.tr.sent j := by
          have hK := fill_adv_tr_kids_eq2 b x k q
          have hS := truth_observe_fill_sent x.tr k q j
          simp only [Truth.sent] at hS ⊢
          rw [hK]
          exact hS
        have hQtyEq2 : (advance step b x (.fill k q)).tr.qty j = x.tr.qty j := fill_adv_tr_qty2 b x k q j
        rw [hSentEq, hQtyEq2]
        exact hLE j
  have hrun : ∀ l, P (run step b l) := run_induction step b P h0 hs
  have hP := hrun evs
  exact hP.2 id

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e id hexec c hmem hcon
  have hRoutes : ∀ (pid liq : Nat), (step b (run step b evs).st (.route pid liq)).2 = expectedRoute (run step b evs).tr pid liq :=
    fun pid liq => req_routes_available b evs pid liq
  have hSentLE : (run step b evs).tr.sent id ≤ (run step b evs).tr.qty id :=
    req_never_overroute b evs id
  have hExecLE : (run step b evs).tr.exec id ≤ (run step b evs).tr.sent id :=
    exec_le_sent step b evs id
  have hSentEq : (run step b evs).tr.sent id = (run step b evs).tr.qty id := by omega
  cases e with
  | parent q f =>
    have hOut : (step b (run step b evs).st (.parent q f)).2 = ([] : List Child) :=
      step_parent_out b (run step b evs).st q f
    rw [hOut] at hmem
    simp at hmem
  | ack k =>
    have hOut : (step b (run step b evs).st (.ack k)).2 = ([] : List Child) :=
      step_ack_out b (run step b evs).st k
    rw [hOut] at hmem
    simp at hmem
  | fill k q =>
    have hOut : (step b (run step b evs).st (.fill k q)).2 = ([] : List Child) :=
      step_fill_out b (run step b evs).st k q
    rw [hOut] at hmem
    simp at hmem
  | route pid liq =>
    have hOut := hRoutes pid liq
    rw [hOut] at hmem
    have hpar : c.parent = pid := expected_mem_parent_aux (run step b evs).tr pid liq c hmem
    have hpid : pid = id := by omega
    have hSentPid : (run step b evs).tr.sent pid = (run step b evs).tr.qty pid := by
      rw [hpid, hSentEq]
    have hmin : min liq ((run step b evs).tr.qty pid - (run step b evs).tr.sent pid) = 0 := by
      simp [hSentPid]
    have hCondFalse : ¬ (pid < (run step b evs).tr.nOrders ∧ 0 < min liq ((run step b evs).tr.qty pid - (run step b evs).tr.sent pid)) := by
      rw [hmin]
      simp
    have hExp : expectedRoute (run step b evs).tr pid liq = ([] : List Child) := by
      unfold expectedRoute
      rw [if_neg hCondFalse]
    rw [hExp] at hmem
    simp at hmem

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  exact Nat.le_trans (exec_le_sent step b evs id) (req_never_overroute b evs id)

theorem req_fill_accounting : FillAccounting step := by
  intro b evs id _hid
  have h := plan2_run_inv b evs
  obtain ⟨hN, hChLen, hSent, hCum, hQty, hSync, hPar⟩ := h
  have heq := hCum id
  simp only [Truth.exec] at heq ⊢
  exact heq

end OrderRouter
