import OrderRouter.Spec
import OrderRouter.Lemmas

namespace OrderRouter

def step : Impl := fun _ st e => match e with
  | .parent q flag =>
    ({ nParents := st.nParents + 1,
       parents := upd st.parents st.nParents ⟨q, flag, 0, 0⟩,
       nChildren := st.nChildren,
       children := st.children }, [])
  | .route id liq =>
    if _ : id < st.nParents then
      let pr := st.parents id
      let amt := min liq (pr.qty - pr.sent)
      if _ : 0 < amt then
        ({ nParents := st.nParents,
           parents := upd st.parents id { pr with sent := pr.sent + amt },
           nChildren := st.nChildren + 1,
           children := upd st.children st.nChildren ⟨id, amt, 0⟩ }, [⟨id, amt⟩])
        else (st, [])
      else (st, [])
  | .ack _ => (st, [])
  | .fill k q =>
    if _ : k < st.nChildren then
      let cr := st.children k
      let inc := min q (cr.qty - cr.done)
      let cr' : ChildRec := { cr with done := cr.done + inc }
      let pr := st.parents cr.parent
      let pr' : ParentRec := { pr with cum := pr.cum + inc }
      ({ nParents := st.nParents,
         parents := upd st.parents cr.parent pr',
         nChildren := st.nChildren,
         children := upd st.children k cr' }, [])
      else (st, [])

theorem sentFor_eq_zero_of_ne (l : List Kid) (id : Nat) (h : ∀ k ∈ l, k.parent ≠ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent ≠ id := h a (by simp)
    have ih' : sentFor as id = 0 := ih (fun k hk => h k (by simp [hk]))
    simp [ha] at *
    exact ih'

theorem tmp_test1 (x : Sys) (q : Nat) (flag : Bool) (b : Build) :
    (step b x.st (Event.parent q flag)).1.nParents = x.st.nParents + 1 := by
  unfold step
  simp

theorem tmp_parent_simp (x : Sys) (q : Nat) (flag : Bool) (b : Build) :
    (step b x.st (Event.parent q flag)).1.nParents = x.st.nParents + 1 := by
  simp [step]

theorem tmp_route_nPar (x : Sys) (id liq : Nat) (b : Build) :
    (step b x.st (Event.route id liq)).1.nParents = x.st.nParents := by
  simp [step]
  split
  · rename_i h
    split
    · rfl
    · rfl
  · rfl

theorem tmp_obs_parent_nOrders (t : Truth) (q : Nat) (flag : Bool) (out : List Child) :
    ((t.observe (Event.parent q flag)).record out).nOrders = t.nOrders + 1 := by
  simp [Truth.observe, Truth.record]

theorem upd_same {α : Type} (f : Nat → α) (k : Nat) (v : α) : upd f k v k = v := by
  simp [upd]

theorem upd_other {α : Type} (f : Nat → α) (k j : Nat) (v : α) (h : j ≠ k) : upd f k v j = f j := by
  simp [upd, h]

theorem step_parent_out (st : State) (q : Nat) (flag : Bool) (b : Build) :
    (step b st (Event.parent q flag)).2 = [] := by simp [step]

theorem step_parent_st (st : State) (q : Nat) (flag : Bool) (b : Build) :
    (step b st (Event.parent q flag)).1 =
    ({ nParents := st.nParents + 1,
       parents := upd st.parents st.nParents ⟨q, flag, 0, 0⟩,
       nChildren := st.nChildren,
       children := st.children } : State) := by simp [step]

theorem step_route_out_eq (st : State) (id liq : Nat) (b : Build) (h : id < st.nParents)
    (hamt : 0 < min liq ((st.parents id).qty - (st.parents id).sent)) :
    (step b st (Event.route id liq)).2 = [⟨id, min liq ((st.parents id).qty - (st.parents id).sent)⟩] := by
  simp [step, h, hamt]

theorem step_route_st_eq (st : State) (id liq : Nat) (b : Build) (h : id < st.nParents)
    (hamt : 0 < min liq ((st.parents id).qty - (st.parents id).sent)) :
    (step b st (Event.route id liq)).1.nParents = st.nParents ∧
    (step b st (Event.route id liq)).1.nChildren = st.nChildren + 1 := by
  simp [step, h, hamt]

theorem adv_parent_nPar2 (x : Sys) (q : Nat) (flag : Bool) (b : Build) :
    (advance step b x (Event.parent q flag)).st.nParents = x.st.nParents + 1 := by
  simp [advance, step]

theorem obs_parent_qty (t : Truth) (q : Nat) (flag : Bool) (id : Nat) :
    (t.observe (Event.parent q flag)).qty id = upd t.qty t.nOrders q id := by
  simp [Truth.observe]

theorem obs_parent_nOrders2 (t : Truth) (q : Nat) (flag : Bool) :
    (t.observe (Event.parent q flag)).nOrders = t.nOrders + 1 := by
  simp [Truth.observe]

theorem obs_parent_kids (t : Truth) (q : Nat) (flag : Bool) :
    (t.observe (Event.parent q flag)).kids = t.kids := by
  simp [Truth.observe]

theorem rec_qty (t : Truth) (out : List Child) (id : Nat) :
    (t.record out).qty id = t.qty id := by simp [Truth.record]

theorem rec_nOrders (t : Truth) (out : List Child) :
    (t.record out).nOrders = t.nOrders := by simp [Truth.record]

theorem rec_kids (t : Truth) (out : List Child) :
    (t.record out).kids = t.kids ++ out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) := by
  simp [Truth.record]

theorem obs_route_qty (t : Truth) (id liq : Nat) (j : Nat) :
    (t.observe (Event.route id liq)).qty j = t.qty j := by simp [Truth.observe]

theorem obs_route_nOrders2 (t : Truth) (id liq : Nat) :
    (t.observe (Event.route id liq)).nOrders = t.nOrders := by simp [Truth.observe]

theorem obs_route_kids (t : Truth) (id liq : Nat) :
    (t.observe (Event.route id liq)).kids = t.kids := by simp [Truth.observe]

theorem obs_ack_qty (t : Truth) (k : Nat) (j : Nat) :
    (t.observe (Event.ack k)).qty j = t.qty j := by simp [Truth.observe]

theorem obs_ack_nOrders2 (t : Truth) (k : Nat) :
    (t.observe (Event.ack k)).nOrders = t.nOrders := by simp [Truth.observe]

theorem obs_fill_qty (t : Truth) (k q : Nat) (j : Nat) :
    (t.observe (Event.fill k q)).qty j = t.qty j := by
  cases h : (t.kids[k]?) <;> simp [Truth.observe, h]

theorem obs_fill_nOrders2 (t : Truth) (k q : Nat) :
    (t.observe (Event.fill k q)).nOrders = t.nOrders := by
  cases h : (t.kids[k]?) <;> simp [Truth.observe, h]

theorem adv_parent_st_parents (x : Sys) (q : Nat) (flag : Bool) (b : Build) (id : Nat) :
    (advance step b x (Event.parent q flag)).st.parents id =
      upd x.st.parents x.st.nParents ⟨q, flag, 0, 0⟩ id := by
  simp [advance, step]

theorem adv_parent_st_nChild (x : Sys) (q : Nat) (flag : Bool) (b : Build) :
    (advance step b x (Event.parent q flag)).st.nChildren = x.st.nChildren := by
  simp [advance, step]

theorem adv_parent_tr_kids (x : Sys) (q : Nat) (flag : Bool) (b : Build) :
    (advance step b x (Event.parent q flag)).tr.kids = x.tr.kids := by
  simp [advance, step, Truth.observe, Truth.record]

theorem adv_parent_tr_qty (x : Sys) (q : Nat) (flag : Bool) (b : Build) (id : Nat) :
    (advance step b x (Event.parent q flag)).tr.qty id = upd x.tr.qty x.tr.nOrders q id := by
  simp [advance, step, Truth.observe, Truth.record]

theorem step_route_cases (st : State) (id liq : Nat) (b : Build) :
    (step b st (Event.route id liq)).2 = [] ∨
    (∃ amt, amt = min liq ((st.parents id).qty - (st.parents id).sent) ∧ 0 < amt ∧ id < st.nParents ∧
      (step b st (Event.route id liq)).2 = [⟨id, amt⟩]) := by
  simp only [step]
  split
  · rename_i h
    simp only [dite_eq_ite]
    split
    · exact Or.inr ⟨_, rfl, by assumption, h, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem step_parent_out2 (st : State) (q : Nat) (flag : Bool) (b : Build) :
    (step b st (Event.parent q flag)).2 = [] := by simp [step]

theorem step_ack_out2 (st : State) (k : Nat) (b : Build) :
    (step b st (Event.ack k)).2 = [] := by simp [step]

theorem step_fill_out2 (st : State) (k q : Nat) (b : Build) :
    (step b st (Event.fill k q)).2 = [] := by
  simp only [step]
  split
  · rfl
  · rfl

theorem step_ack_nPar (st : State) (k : Nat) (b : Build) :
    (step b st (Event.ack k)).1.nParents = st.nParents := by simp [step]

theorem step_fill_nPar (st : State) (k q : Nat) (b : Build) :
    (step b st (Event.fill k q)).1.nParents = st.nParents := by
  simp only [step]
  split
  · rfl
  · rfl

theorem step_parent_nPar (st : State) (q : Nat) (flag : Bool) (b : Build) :
    (step b st (Event.parent q flag)).1.nParents = st.nParents + 1 := by simp [step]

theorem adv_nPar_parent (x : Sys) (q : Nat) (flag : Bool) (b : Build) :
    (advance step b x (Event.parent q flag)).st.nParents = x.st.nParents + 1 := by
  simp [advance, step_parent_nPar]

theorem adv_nPar_route (x : Sys) (id liq : Nat) (b : Build) :
    (advance step b x (Event.route id liq)).st.nParents = x.st.nParents := by
  simp [advance, step]
  split
  · rename_i h; split <;> rfl
  · rfl

theorem adv_nPar_ack (x : Sys) (k : Nat) (b : Build) :
    (advance step b x (Event.ack k)).st.nParents = x.st.nParents := by
  simp [advance, step]

theorem adv_nPar_fill (x : Sys) (k q : Nat) (b : Build) :
    (advance step b x (Event.fill k q)).st.nParents = x.st.nParents := by
  simp [advance, step_fill_nPar]

theorem invA_nPar_eq_nOrd (b : Build) (evs : List Event) :
    (run step b evs).st.nParents = (run step b evs).tr.nOrders := by
  apply run_induction step b (fun x => x.st.nParents = x.tr.nOrders) rfl _ evs
  intro x e ih
  cases e with
  | parent q flag =>
    simp only [advance, step, Truth.observe, Truth.record] at ih ⊢
    omega
  | route id liq =>
    have h1 : ((x.tr.observe (Event.route id liq)).record (step b x.st (Event.route id liq)).2).nOrders = x.tr.nOrders := by
      simp [Truth.observe, Truth.record]
    have h2 : (step b x.st (Event.route id liq)).1.nParents = x.st.nParents := by
      simp only [step]
      split
      · rename_i h
        split
        · rfl
        · rfl
      · rfl
    simp only [advance, h1, h2, ih]
  | ack k =>
    simp [advance, step, Truth.observe, Truth.record, ih]
  | fill k q =>
    have hout : (step b x.st (Event.fill k q)).2 = [] := step_fill_out2 _ _ _ _
    have h1 : ((x.tr.observe (Event.fill k q)).record (step b x.st (Event.fill k q)).2).nOrders = x.tr.nOrders := by
      rw [hout]
      simp [Truth.record, obs_fill_nOrders2]
    have h2 : (step b x.st (Event.fill k q)).1.nParents = x.st.nParents := step_fill_nPar _ _ _ _
    simp only [advance, h1, h2, ih]

theorem sentFor_singleton (p : Nat) (qq : Nat) (d : Nat) (id : Nat) :
    sentFor [⟨p, qq, d⟩] id = (if p = id then qq else 0) := by simp

theorem execFor_singleton (p : Nat) (qq : Nat) (d : Nat) (id : Nat) :
    execFor [⟨p, qq, d⟩] id = (if p = id then d else 0) := by simp

theorem sentFor_append_singleton (l : List Kid) (p qq : Nat) (id : Nat) :
    sentFor (l ++ [⟨p, qq, 0⟩]) id = sentFor l id + (if p = id then qq else 0) := by
  simp [sentFor_append]

theorem execFor_append_singleton_zero (l : List Kid) (p qq : Nat) (id : Nat) :
    execFor (l ++ [⟨p, qq, 0⟩]) id = execFor l id := by
  simp [execFor_append]

theorem execFor_eq_zero_of_ne (l : List Kid) (id : Nat) (h : ∀ k ∈ l, k.parent ≠ id) : execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent ≠ id := h a (by simp)
    have ih' : execFor as id = 0 := ih (fun k hk => h k (by simp [hk]))
    simp [ha] at *
    exact ih'

theorem sentFor_eq_zero_of_lt (l : List Kid) (N id : Nat)
    (h : ∀ k ∈ l, k.parent < N) (hle : N ≤ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent ≠ id := by
      have hlt := h a (by simp); omega
    have ih' := ih (fun k hk => h k (by simp [hk]))
    simp [ha, ih']

theorem execFor_eq_zero_of_lt (l : List Kid) (N id : Nat)
    (h : ∀ k ∈ l, k.parent < N) (hle : N ≤ id) : execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent ≠ id := by
      have hlt := h a (by simp); omega
    have ih' := ih (fun k hk => h k (by simp [hk]))
    simp [ha, ih']

def Inv2 (x : Sys) : Prop := x.st.nParents = x.tr.nOrders

def InvA (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ id, id < x.st.nParents → (x.st.parents id).qty = x.tr.qty id) ∧
  (∀ id, (x.st.parents id).sent = x.tr.sent id) ∧
  (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
  (∀ k (c : Kid), x.tr.kids[k]? = some c → x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
  (∀ k ∈ x.tr.kids, k.parent < x.st.nParents)

theorem invA_start : InvA start := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro id h
    simp [start, init] at h
  · intro id
    simp [start, init, Truth.empty, Truth.sent]
  · intro id
    simp [start, init, Truth.empty, Truth.exec]
  · intro k c h
    simp [start, init, Truth.empty] at h
  · intro k h
    simp [start, init, Truth.empty] at h

theorem record_nil_kids (t : Truth) : (t.record []).kids = t.kids := by simp [Truth.record]

theorem record_nil_nOrders (t : Truth) : (t.record []).nOrders = t.nOrders := by simp [Truth.record]

theorem record_nil_qty (t : Truth) (id : Nat) : (t.record []).qty id = t.qty id := by simp [Truth.record]

theorem observe_route (t : Truth) (id liq : Nat) : t.observe (Event.route id liq) = t := by simp [Truth.observe]

theorem observe_ack (t : Truth) (k : Nat) : t.observe (Event.ack k) = t := by simp [Truth.observe]

theorem probe_parent_adv (x : Sys) (b : Build) (q : Nat) (flag : Bool) :
    (advance step b x (Event.parent q flag)).st =
    ({ nParents := x.st.nParents + 1,
       parents := upd x.st.parents x.st.nParents ⟨q, flag, 0, 0⟩,
       nChildren := x.st.nChildren,
       children := x.st.children } : State) := by
  simp [advance, step]

theorem probe_route1 (st : State) (id liq : Nat) (b : Build) (h : id < st.nParents)
    (hamt : 0 < min liq ((st.parents id).qty - (st.parents id).sent)) :
    (step b st (Event.route id liq)).2 = [⟨id, min liq ((st.parents id).qty - (st.parents id).sent)⟩] := by
  simp [step, h, hamt]

theorem probe_route2 (st : State) (id liq : Nat) (b : Build) (h : ¬ id < st.nParents) :
    (step b st (Event.route id liq)).2 = ([] : List Child) := by
  simp [step, h]

theorem probe_route3 (st : State) (id liq : Nat) (b : Build) (h : id < st.nParents)
    (hamt : ¬ 0 < min liq ((st.parents id).qty - (st.parents id).sent)) :
    (step b st (Event.route id liq)).2 = ([] : List Child) := by
  simp [step, h, hamt]

def InvR (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  (∀ id, id < x.st.nParents → (x.st.parents id).qty = x.tr.qty id) ∧
  (∀ id, (x.st.parents id).sent = x.tr.sent id) ∧
  (∀ k ∈ x.tr.kids, k.parent < x.st.nParents)

theorem invR_start : InvR start := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro id h; simp [start, init] at h
  · intro id; simp [start, init, Truth.empty, Truth.sent]
  · intro k h; simp [start, Truth.empty] at h

theorem upd_parents_sent_route (st : State) (id : Nat) (amt : Nat) (j : Nat) :
    (upd st.parents id ({ st.parents id with sent := (st.parents id).sent + amt }) j).sent =
    (if j = id then (st.parents id).sent + amt else (st.parents j).sent) := by
  simp only [upd]
  split
  · subst_vars; rfl
  · rfl

theorem upd_parents_qty_route (st : State) (id : Nat) (amt : Nat) (j : Nat) :
    (upd st.parents id ({ st.parents id with sent := (st.parents id).sent + amt }) j).qty =
    (st.parents j).qty := by
  simp only [upd]
  split
  · subst_vars; rfl
  · rfl

theorem upd_parents_sent_fill (st : State) (p : Nat) (inc : Nat) (j : Nat) :
    (upd st.parents p ({ st.parents p with cum := (st.parents p).cum + inc }) j).sent =
    (st.parents j).sent := by
  simp only [upd]
  split
  · subst_vars; rfl
  · rfl

theorem upd_parents_qty_fill (st : State) (p : Nat) (inc : Nat) (j : Nat) :
    (upd st.parents p ({ st.parents p with cum := (st.parents p).cum + inc }) j).qty =
    (st.parents j).qty := by
  simp only [upd]
  split
  · subst_vars; rfl
  · rfl

theorem tr_sent_parent (x : Sys) (q : Nat) (flag : Bool) (b : Build) (id : Nat) :
    (advance step b x (Event.parent q flag)).tr.sent id = x.tr.sent id := by
  simp [advance, step, Truth.observe, Truth.record, Truth.sent]

theorem tr_qty_parent (x : Sys) (q : Nat) (flag : Bool) (b : Build) (id : Nat) :
    (advance step b x (Event.parent q flag)).tr.qty id = upd x.tr.qty x.tr.nOrders q id := by
  simp [advance, step, Truth.observe, Truth.record]

theorem tr_nOrders_parent (x : Sys) (q : Nat) (flag : Bool) (b : Build) :
    (advance step b x (Event.parent q flag)).tr.nOrders = x.tr.nOrders + 1 := by
  simp [advance, step, Truth.observe, Truth.record]

theorem st_sent_parent (x : Sys) (q : Nat) (flag : Bool) (b : Build) (id : Nat) :
    ((advance step b x (Event.parent q flag)).st.parents id).sent =
    (if id = x.st.nParents then 0 else (x.st.parents id).sent) := by
  simp [advance, step, upd]
  split
  · subst_vars; rfl
  · rfl

theorem st_qty_parent (x : Sys) (q : Nat) (flag : Bool) (b : Build) (id : Nat) :
    ((advance step b x (Event.parent q flag)).st.parents id).qty =
    (if id = x.st.nParents then q else (x.st.parents id).qty) := by
  simp [advance, step, upd]
  split
  · subst_vars; rfl
  · rfl

theorem adv_ack_st (x : Sys) (k : Nat) (b : Build) :
    (advance step b x (Event.ack k)).st = x.st := by
  simp [advance, step]

theorem adv_ack_tr (x : Sys) (k : Nat) (b : Build) :
    (advance step b x (Event.ack k)).tr = x.tr := by
  simp [advance, step, Truth.observe, Truth.record]

theorem adv_route_nOrders (x : Sys) (id liq : Nat) (b : Build) :
    (advance step b x (Event.route id liq)).tr.nOrders = x.tr.nOrders := by
  simp [advance, Truth.observe, Truth.record]

theorem adv_route_qty (x : Sys) (id liq : Nat) (b : Build) (j : Nat) :
    (advance step b x (Event.route id liq)).tr.qty j = x.tr.qty j := by
  simp [advance, Truth.observe, Truth.record]

theorem adv_route_trkids (x : Sys) (id liq : Nat) (b : Build) :
    (advance step b x (Event.route id liq)).tr.kids =
    x.tr.kids ++ (step b x.st (Event.route id liq)).2.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) := by
  simp [advance, Truth.observe, Truth.record]

theorem adv_fill_nOrders (x : Sys) (k q : Nat) (b : Build) :
    (advance step b x (Event.fill k q)).tr.nOrders = x.tr.nOrders := by
  simp only [advance]
  have hout : (step b x.st (Event.fill k q)).2 = [] := step_fill_out2 _ _ _ _
  rw [hout]
  simp [Truth.record, obs_fill_nOrders2]

theorem adv_fill_qty (x : Sys) (k q : Nat) (b : Build) (j : Nat) :
    (advance step b x (Event.fill k q)).tr.qty j = x.tr.qty j := by
  simp only [advance]
  have hout : (step b x.st (Event.fill k q)).2 = [] := step_fill_out2 _ _ _ _
  rw [hout]
  simp [Truth.record, obs_fill_qty]

theorem adv_route_st_parents_eq (x : Sys) (id liq : Nat) (b : Build) (j : Nat)
    (h : ¬ id < x.st.nParents) :
    ((advance step b x (Event.route id liq)).st.parents j) = x.st.parents j := by
  have hst : (step b x.st (Event.route id liq)).1 = x.st := by
    simp [step, h]
  simp [advance, hst]

theorem adv_route_st_nPar_eq (x : Sys) (id liq : Nat) (b : Build) (h : ¬ id < x.st.nParents) :
    (advance step b x (Event.route id liq)).st.nParents = x.st.nParents := by
  simp [advance, step, h]

theorem adv_route_sent_eq (x : Sys) (id liq : Nat) (b : Build) (j : Nat)
    (h : ¬ id < x.st.nParents) :
    ((advance step b x (Event.route id liq)).st.parents j).sent = (x.st.parents j).sent := by
  rw [adv_route_st_parents_eq x id liq b j h]

theorem adv_route_st_parents_eq2 (x : Sys) (id liq : Nat) (b : Build) (j : Nat)
    (h : id < x.st.nParents)
    (hamt : ¬ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    ((advance step b x (Event.route id liq)).st.parents j) = x.st.parents j := by
  have hst : (step b x.st (Event.route id liq)).1 = x.st := by
    simp [step, h, hamt]
  simp [advance, hst]

theorem adv_route_st_nPar_eq2 (x : Sys) (id liq : Nat) (b : Build) (h : id < x.st.nParents)
    (hamt : ¬ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (advance step b x (Event.route id liq)).st.nParents = x.st.nParents := by
  simp [advance, step, h, hamt]

theorem adv_route_out_nil (x : Sys) (id liq : Nat) (b : Build) (h : id < x.st.nParents)
    (hamt : ¬ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (step b x.st (Event.route id liq)).2 = [] := by
  simp [step, h, hamt]

theorem adv_route_out_nil2 (x : Sys) (id liq : Nat) (b : Build) (h : ¬ id < x.st.nParents) :
    (step b x.st (Event.route id liq)).2 = [] := by
  simp [step, h]

theorem adv_route_st_parents_succ (x : Sys) (id liq : Nat) (b : Build) (j : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    ((advance step b x (Event.route id liq)).st.parents j) =
    upd x.st.parents id ({ x.st.parents id with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) }) j := by
  simp [advance, step, h, hamt]

theorem adv_route_st_nPar_succ (x : Sys) (id liq : Nat) (b : Build)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (advance step b x (Event.route id liq)).st.nParents = x.st.nParents := by
  simp [advance, step, h, hamt]

theorem adv_route_out_succ (x : Sys) (id liq : Nat) (b : Build)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (step b x.st (Event.route id liq)).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] := by
  simp [step, h, hamt]

theorem sentFor_out_single2 (p amt id : Nat) :
    sentFor ([Child.mk p amt].map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id =
    (if p = id then amt else 0) := by
  simp



theorem plan0_invR_route (b : Build) (x : Sys) (id liq : Nat) :
    InvR x → InvR (advance step b x (Event.route id liq)) := by
  intro h
  obtain ⟨h1, hQty, hSent, hBound⟩ := h
  by_cases hlt : id < x.st.nParents
  · by_cases hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
    · have hnPar : (advance step b x (Event.route id liq)).st.nParents = x.st.nParents :=
        adv_route_st_nPar_succ x id liq b hlt hamt
      have hnOrd : (advance step b x (Event.route id liq)).tr.nOrders = x.tr.nOrders :=
        adv_route_nOrders x id liq b
      have hout : (step b x.st (Event.route id liq)).2 =
          [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] :=
        adv_route_out_succ x id liq b hlt hamt
      have htrk : (advance step b x (Event.route id liq)).tr.kids =
        x.tr.kids ++ (step b x.st (Event.route id liq)).2.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) :=
        adv_route_trkids x id liq b
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hnPar, hnOrd, h1]
      · intro j hj
        have hj0 : j < x.st.nParents := by omega
        have hst : ((advance step b x (Event.route id liq)).st.parents j).qty = (x.st.parents j).qty := by
          rw [adv_route_st_parents_succ x id liq b j hlt hamt]
          exact upd_parents_qty_route x.st id _ j
        have htr : (advance step b x (Event.route id liq)).tr.qty j = x.tr.qty j :=
          adv_route_qty x id liq b j
        rw [hst, htr, hQty j hj0]
      · intro j
        have hst : ((advance step b x (Event.route id liq)).st.parents j).sent =
          (if j = id then (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) else (x.st.parents j).sent) := by
          rw [adv_route_st_parents_succ x id liq b j hlt hamt]
          simp only [upd]
          split
          · subst_vars; rfl
          · rfl
        have hsent : (advance step b x (Event.route id liq)).tr.sent j =
          x.tr.sent j + (if id = j then min liq ((x.st.parents id).qty - (x.st.parents id).sent) else 0) := by
          simp only [Truth.sent]
          rw [htrk, hout]
          simp only [sentFor_append]
          simp
        rw [hst, hsent, hSent id, hSent j]
        by_cases heq : j = id
        · subst heq; simp
        · simp [heq, Ne.symm heq]
      · intro k hk
        rw [hnPar]
        rw [htrk, hout] at hk
        simp only [List.mem_append, List.mem_map] at hk
        rcases hk with hk | hk
        · exact hBound k hk
        · obtain ⟨c, hc, rfl⟩ := hk
          simp at hc
          obtain rfl := hc
          simp
          exact hlt
    · have hnPar : (advance step b x (Event.route id liq)).st.nParents = x.st.nParents :=
        adv_route_st_nPar_eq2 x id liq b hlt hamt
      have hnOrd : (advance step b x (Event.route id liq)).tr.nOrders = x.tr.nOrders :=
        adv_route_nOrders x id liq b
      have hout : (step b x.st (Event.route id liq)).2 = ([] : List Child) :=
        adv_route_out_nil x id liq b hlt hamt
      have htrk : (advance step b x (Event.route id liq)).tr.kids =
        x.tr.kids ++ (step b x.st (Event.route id liq)).2.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) :=
        adv_route_trkids x id liq b
      have hkids : (advance step b x (Event.route id liq)).tr.kids = x.tr.kids := by
        rw [htrk, hout]; simp
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hnPar, hnOrd, h1]
      · intro j hj
        have hj0 : j < x.st.nParents := by omega
        have hst : ((advance step b x (Event.route id liq)).st.parents j) = x.st.parents j :=
          adv_route_st_parents_eq2 x id liq b j hlt hamt
        have htr : (advance step b x (Event.route id liq)).tr.qty j = x.tr.qty j :=
          adv_route_qty x id liq b j
        rw [hst, htr, hQty j hj0]
      · intro j
        have hst : ((advance step b x (Event.route id liq)).st.parents j).sent = (x.st.parents j).sent := by
          rw [adv_route_st_parents_eq2 x id liq b j hlt hamt]
        have htr : (advance step b x (Event.route id liq)).tr.sent j = x.tr.sent j := by
          simp only [Truth.sent]; rw [hkids]
        rw [hst, htr, hSent j]
      · intro k hk
        rw [hnPar]
        rw [hkids] at hk
        exact hBound k hk
  · have hnPar : (advance step b x (Event.route id liq)).st.nParents = x.st.nParents :=
      adv_route_st_nPar_eq x id liq b hlt
    have hnOrd : (advance step b x (Event.route id liq)).tr.nOrders = x.tr.nOrders :=
      adv_route_nOrders x id liq b
    have hout : (step b x.st (Event.route id liq)).2 = ([] : List Child) :=
      adv_route_out_nil2 x id liq b hlt
    have htrk : (advance step b x (Event.route id liq)).tr.kids =
      x.tr.kids ++ (step b x.st (Event.route id liq)).2.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) :=
      adv_route_trkids x id liq b
    have hkids : (advance step b x (Event.route id liq)).tr.kids = x.tr.kids := by
      rw [htrk, hout]; simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hnPar, hnOrd, h1]
    · intro j hj
      have hj0 : j < x.st.nParents := by omega
      have hst : ((advance step b x (Event.route id liq)).st.parents j) = x.st.parents j :=
        adv_route_st_parents_eq x id liq b j hlt
      have htr : (advance step b x (Event.route id liq)).tr.qty j = x.tr.qty j :=
        adv_route_qty x id liq b j
      rw [hst, htr, hQty j hj0]
    · intro j
      have hst : ((advance step b x (Event.route id liq)).st.parents j).sent = (x.st.parents j).sent := by
        rw [adv_route_st_parents_eq x id liq b j hlt]
      have htr : (advance step b x (Event.route id liq)).tr.sent j = x.tr.sent j := by
        simp only [Truth.sent]; rw [hkids]
      rw [hst, htr, hSent j]
    · intro k hk
      rw [hnPar]
      rw [hkids] at hk
      exact hBound k hk










theorem plan0_invR_parent (b : Build) (x : Sys) (q : Nat) (flag : Bool) :
    InvR x → InvR (advance step b x (Event.parent q flag)) := by
  intro h
  obtain ⟨h1, hQty, hSent, hBound⟩ := h
  have hnp : (advance step b x (Event.parent q flag)).st.nParents = x.st.nParents + 1 :=
    adv_nPar_parent _ _ _ _
  have hnt : (advance step b x (Event.parent q flag)).tr.nOrders = x.tr.nOrders + 1 :=
    tr_nOrders_parent _ _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hnp, hnt, h1]
  · intro id hid
    rw [st_qty_parent, tr_qty_parent]
    simp only [upd]
    split
    · rename_i heq
      have heq2 : id = x.tr.nOrders := by omega
      simp [heq2]
    · rename_i hne
      have hne2 : id ≠ x.tr.nOrders := by omega
      simp [hne2]
      have hlt : id < x.st.nParents := by omega
      exact hQty id hlt
  · intro id
    rw [st_sent_parent, tr_sent_parent, hSent id]
    split
    · rename_i heq
      subst heq
      have hzero : sentFor x.tr.kids x.st.nParents = 0 :=
        sentFor_eq_zero_of_lt _ _ _ hBound (by omega)
      simp [Truth.sent, hzero]
    · rfl
  · intro k hk
    rw [adv_parent_tr_kids] at hk
    have hlt := hBound k hk
    omega

theorem plan0_invR_route_frag (x : Sys) (rid liq j : Nat)
    (hSent : ∀ (ide : Nat), (x.st.parents ide).sent = x.tr.sent ide)
    (heq : j = rid) :
    (if j = rid then (x.st.parents rid).sent + min liq ((x.st.parents rid).qty - (x.st.parents rid).sent) else (x.st.parents j).sent) =
    x.tr.sent j + (if rid = j then min liq ((x.st.parents rid).qty - (x.st.parents rid).sent) else 0) := by
  rw [if_pos heq, if_pos heq.symm]
  have e := hSent rid
  have ej : x.tr.sent rid = x.tr.sent j := by rw [heq.symm]
  omega



theorem plan1_adv_route_eq_of_zero_amt (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : ¬ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    advance step b x (Event.route id liq) = x := by
  have h1 : (step b x.st (Event.route id liq)).1 = x.st := by simp [step, h, hamt]
  have h2 : (step b x.st (Event.route id liq)).2 = ([] : List Child) := by simp [step, h, hamt]
  simp only [advance, h1, h2, observe_route]
  congr 1
  simp [Truth.record]


theorem plan1_adv_route_sent_of_succ (b : Build) (x : Sys) (id liq j : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent))
    (hSent : ∀ ide, (x.st.parents ide).sent = x.tr.sent ide) :
    ((advance step b x (Event.route id liq)).st.parents j).sent =
      (advance step b x (Event.route id liq)).tr.sent j := by
  have hst : ((advance step b x (Event.route id liq)).st.parents j).sent =
    (if j = id then (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) else (x.st.parents j).sent) := by
    rw [adv_route_st_parents_succ x id liq b j h hamt]
    simp only [upd]
    split
    · subst_vars; rfl
    · rfl
  have hout : (step b x.st (Event.route id liq)).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] :=
    adv_route_out_succ x id liq b h hamt
  have htr : (advance step b x (Event.route id liq)).tr.kids =
    x.tr.kids ++ (step b x.st (Event.route id liq)).2.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) :=
    adv_route_trkids x id liq b
  have hsent : (advance step b x (Event.route id liq)).tr.sent j =
    x.tr.sent j + (if id = j then min liq ((x.st.parents id).qty - (x.st.parents id).sent) else 0) := by
    simp only [Truth.sent]
    rw [htr, hout]
    simp only [sentFor_append]
    simp
  rw [hst, hsent, hSent id, hSent j]
  by_cases heq : j = id
  · subst heq; simp
  · simp [heq, Ne.symm heq]


theorem plan1_adv_route_core_of_succ (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    InvR x →
      (advance step b x (Event.route id liq)).st.nParents =
          (advance step b x (Event.route id liq)).tr.nOrders ∧
        (∀ j, j < (advance step b x (Event.route id liq)).st.nParents →
          ((advance step b x (Event.route id liq)).st.parents j).qty =
            (advance step b x (Event.route id liq)).tr.qty j) ∧
        (∀ k ∈ (advance step b x (Event.route id liq)).tr.kids,
          k.parent < (advance step b x (Event.route id liq)).st.nParents) := by
  intro hInv
  obtain ⟨h1, hQty, hSent, hBound⟩ := hInv
  have hnPar : (advance step b x (Event.route id liq)).st.nParents = x.st.nParents :=
    adv_route_st_nPar_succ x id liq b h hamt
  have hnOrd : (advance step b x (Event.route id liq)).tr.nOrders = x.tr.nOrders :=
    adv_route_nOrders x id liq b
  have htrkids : (advance step b x (Event.route id liq)).tr.kids =
    x.tr.kids ++ (step b x.st (Event.route id liq)).2.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) :=
    adv_route_trkids x id liq b
  have hout : (step b x.st (Event.route id liq)).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] :=
    adv_route_out_succ x id liq b h hamt
  refine ⟨?_, ?_, ?_⟩
  · rw [hnPar, hnOrd, h1]
  · intro j hj
    have hj0 : j < x.st.nParents := by omega
    have hst : ((advance step b x (Event.route id liq)).st.parents j).qty = (x.st.parents j).qty := by
      rw [adv_route_st_parents_succ x id liq b j h hamt]
      exact upd_parents_qty_route x.st id _ j
    have htr : (advance step b x (Event.route id liq)).tr.qty j = x.tr.qty j :=
      adv_route_qty x id liq b j
    rw [hst, htr, hQty j hj0]
  · intro k hk
    rw [hnPar]
    rw [htrkids, hout] at hk
    simp only [List.mem_append, List.mem_map] at hk
    rcases hk with hk | hk
    · exact hBound k hk
    · obtain ⟨c, hc, rfl⟩ := hk
      simp at hc
      obtain rfl := hc
      simp
      exact h




theorem plan1_adv_route_eq_of_not_lt (b : Build) (x : Sys) (id liq : Nat)
    (h : ¬ id < x.st.nParents) :
    advance step b x (Event.route id liq) = x := by
  have h1 : (step b x.st (Event.route id liq)).1 = x.st := by simp [step, h]
  have h2 : (step b x.st (Event.route id liq)).2 = ([] : List Child) := by simp [step, h]
  simp only [advance, h1, h2, observe_route]
  congr 1
  simp [Truth.record]

theorem plan1_adv_route_eq_of_zero_amt_aux (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : ¬ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    advance step b x (Event.route id liq) = x := by
  have h1 : (step b x.st (Event.route id liq)).1 = x.st := by simp [step, h, hamt]
  have h2 : (step b x.st (Event.route id liq)).2 = ([] : List Child) := by simp [step, h, hamt]
  simp only [advance, h1, h2, observe_route]
  congr 1
  simp [Truth.record]

theorem plan1_adv_route_sent_of_succ_proof (b : Build) (x : Sys) (id liq j : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent))
    (hSent : ∀ ide, (x.st.parents ide).sent = x.tr.sent ide) :
    ((advance step b x (Event.route id liq)).st.parents j).sent =
      (advance step b x (Event.route id liq)).tr.sent j := by
  have hst : ((advance step b x (Event.route id liq)).st.parents j).sent =
    (if j = id then (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) else (x.st.parents j).sent) := by
    rw [adv_route_st_parents_succ x id liq b j h hamt]
    simp only [upd]
    split
    · subst_vars; rfl
    · rfl
  have hout : (step b x.st (Event.route id liq)).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] :=
    adv_route_out_succ x id liq b h hamt
  have htr : (advance step b x (Event.route id liq)).tr.kids =
    x.tr.kids ++ (step b x.st (Event.route id liq)).2.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) :=
    adv_route_trkids x id liq b
  have hsent : (advance step b x (Event.route id liq)).tr.sent j =
    x.tr.sent j + (if id = j then min liq ((x.st.parents id).qty - (x.st.parents id).sent) else 0) := by
    simp only [Truth.sent]
    rw [htr, hout]
    simp only [sentFor_append]
    simp
  rw [hst, hsent, hSent id, hSent j]
  by_cases heq : j = id
  · subst heq; simp
  · simp [heq, Ne.symm heq]

theorem plan1_adv_route_core_of_succ_aux : True := trivial

theorem plan1_adv_route_core_of_succ_proof (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    InvR x →
      (advance step b x (Event.route id liq)).st.nParents =
          (advance step b x (Event.route id liq)).tr.nOrders ∧
        (∀ j, j < (advance step b x (Event.route id liq)).st.nParents →
          ((advance step b x (Event.route id liq)).st.parents j).qty =
            (advance step b x (Event.route id liq)).tr.qty j) ∧
        (∀ k ∈ (advance step b x (Event.route id liq)).tr.kids,
          k.parent < (advance step b x (Event.route id liq)).st.nParents) := by
  intro hInv
  obtain ⟨h1, hQty, hSent, hBound⟩ := hInv
  have hnPar : (advance step b x (Event.route id liq)).st.nParents = x.st.nParents :=
    adv_route_st_nPar_succ x id liq b h hamt
  have hnOrd : (advance step b x (Event.route id liq)).tr.nOrders = x.tr.nOrders :=
    adv_route_nOrders x id liq b
  have htrkids : (advance step b x (Event.route id liq)).tr.kids =
    x.tr.kids ++ (step b x.st (Event.route id liq)).2.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) :=
    adv_route_trkids x id liq b
  have hout : (step b x.st (Event.route id liq)).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] :=
    adv_route_out_succ x id liq b h hamt
  refine ⟨?_, ?_, ?_⟩
  · rw [hnPar, hnOrd, h1]
  · intro j hj
    have hj0 : j < x.st.nParents := by omega
    have hst : ((advance step b x (Event.route id liq)).st.parents j).qty = (x.st.parents j).qty := by
      rw [adv_route_st_parents_succ x id liq b j h hamt]
      exact upd_parents_qty_route x.st id _ j
    have htr : (advance step b x (Event.route id liq)).tr.qty j = x.tr.qty j :=
      adv_route_qty x id liq b j
    rw [hst, htr, hQty j hj0]
  · intro k hk
    rw [hnPar]
    rw [htrkids, hout] at hk
    simp only [List.mem_append, List.mem_map] at hk
    rcases hk with hk | hk
    · exact hBound k hk
    · obtain ⟨c, hc, rfl⟩ := hk
      simp at hc
      obtain rfl := hc
      simp
      exact h

theorem plan1_invR_route_succ_proof2 (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent))
    (hInv : InvR x) : InvR (advance step b x (Event.route id liq)) := by
  have hSent : ∀ ide, (x.st.parents ide).sent = x.tr.sent ide := hInv.2.2.1
  have hCore := plan1_adv_route_core_of_succ_proof b x id liq h hamt hInv
  obtain ⟨c1, c2, c3⟩ := hCore
  refine ⟨c1, c2, ?_, c3⟩
  intro j
  exact plan1_adv_route_sent_of_succ_proof b x id liq j h hamt hSent

theorem plan1_invR_route_succ (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    InvR x → InvR (advance step b x (Event.route id liq)) :=
  fun hInv => plan1_invR_route_succ_proof2 b x id liq h hamt hInv

theorem plan0_invR_route_aux2_gone : True := trivial


theorem plan0_invR_route_dup2 : True := trivial

theorem plan0_invR_ack (b : Build) (x : Sys) (k : Nat) :
    InvR x → InvR (advance step b x (Event.ack k)) := by
  intro h
  have hst : (advance step b x (Event.ack k)).st = x.st := adv_ack_st x k b
  have htr : (advance step b x (Event.ack k)).tr = x.tr := adv_ack_tr x k b
  obtain ⟨h1, hQty, hSent, hBound⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hst, htr, h1]
  · intro id hid
    rw [hst] at hid
    rw [hst, htr]
    exact hQty id hid
  · intro id
    rw [hst, htr]
    exact hSent id
  · intro kk hk
    rw [htr] at hk
    rw [hst]
    exact hBound kk hk

theorem plan0_invR_fill_aux_trkids (x : Sys) (b : Build) (k q : Nat) :
    (advance step b x (Event.fill k q)).tr.kids =
    (x.tr.observe (Event.fill k q)).kids := by
  simp only [advance]
  have hout : (step b x.st (Event.fill k q)).2 = [] := step_fill_out2 _ _ _ _
  rw [hout]
  simp [Truth.record]

theorem plan0_invR_fill_aux_st_nPar (x : Sys) (b : Build) (k q : Nat) :
    (advance step b x (Event.fill k q)).st.nParents = x.st.nParents := by
  simp only [advance, step_fill_nPar]

theorem plan0_invR_fill_aux_qty_st (x : Sys) (b : Build) (k q j : Nat) :
    ((advance step b x (Event.fill k q)).st.parents j).qty = (x.st.parents j).qty := by
  simp only [advance, step]
  split
  · rename_i h
    simp only [upd_parents_qty_fill]
  · rfl

theorem plan0_invR_fill_aux_sent_st (x : Sys) (b : Build) (k q j : Nat) :
    ((advance step b x (Event.fill k q)).st.parents j).sent = (x.st.parents j).sent := by
  simp only [advance, step]
  split
  · rename_i h
    simp only [upd_parents_sent_fill]
  · rfl

theorem plan0_fill_sent_obs (t : Truth) (k q id : Nat) :
    sentFor (t.observe (Event.fill k q)).kids id = sentFor t.kids id := by
  simp only [Truth.observe]
  split
  · rename_i c hc
    exact sentFor_set_done t.kids k c (c.done + min q (c.qty - c.done)) hc id
  · rfl

theorem plan0_fill_tr_sent (x : Sys) (b : Build) (k q j : Nat) :
    (advance step b x (Event.fill k q)).tr.sent j = x.tr.sent j := by
  simp only [Truth.sent]
  rw [plan0_invR_fill_aux_trkids]
  exact plan0_fill_sent_obs x.tr k q j

theorem plan0_fill_bound_aux (t : Truth) (N : Nat) (k q : Nat)
    (hB : ∀ kk ∈ t.kids, kk.parent < N) (kk : Kid)
    (hmem : kk ∈ (t.observe (Event.fill k q)).kids) : kk.parent < N := by
  simp only [Truth.observe] at hmem
  split at hmem
  · rename_i c hc
    rcases List.mem_or_eq_of_mem_set hmem with h | h
    · exact hB kk h
    · subst h
      simp
      exact hB c (List.mem_of_getElem? (by assumption))
  · exact hB kk hmem

theorem plan0_invR_fill (b : Build) (x : Sys) (k q : Nat) :
    InvR x → InvR (advance step b x (Event.fill k q)) := by
  intro h
  obtain ⟨h1, hQty, hSent, hBound⟩ := h
  have hnPar : (advance step b x (Event.fill k q)).st.nParents = x.st.nParents :=
    plan0_invR_fill_aux_st_nPar x b k q
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hnPar, adv_fill_nOrders, h1]
  · intro id hid
    have hj0 : id < x.st.nParents := by omega
    rw [plan0_invR_fill_aux_qty_st, adv_fill_qty]
    exact hQty id hj0
  · intro j
    rw [plan0_invR_fill_aux_sent_st, plan0_fill_tr_sent]
    exact hSent j
  · intro kk hk
    rw [hnPar]
    rw [plan0_invR_fill_aux_trkids] at hk
    exact plan0_fill_bound_aux x.tr x.st.nParents k q hBound kk hk

theorem plan0_invR_run_aux (b : Build) (evs : List Event) :
    InvR (run step b evs) := by
  apply run_induction step b InvR invR_start _ evs
  intro x e hx
  cases e with
  | parent q flag => exact plan0_invR_parent b x q flag hx
  | route id liq => exact plan0_invR_route b x id liq hx
  | ack k => exact plan0_invR_ack b x k hx
  | fill k q => exact plan0_invR_fill b x k q hx

theorem plan0_invR_run (b : Build) (evs : List Event) :
    InvR (run step b evs) := plan0_invR_run_aux b evs

theorem plan0_route_eq_of_invR (b : Build) (x : Sys) (id liq : Nat) :
    InvR x → (step b x.st (Event.route id liq)).2 = expectedRoute x.tr id liq := by
  intro h
  obtain ⟨h1, hQty, hSent, hBound⟩ := h
  have hqy : ∀ j, j < x.st.nParents → (x.st.parents j).qty = x.tr.qty j := hQty
  by_cases hlt : id < x.st.nParents
  · have hlt2 : id < x.tr.nOrders := by omega
    have hqty : (x.st.parents id).qty = x.tr.qty id := hQty id hlt
    have hsent : (x.st.parents id).sent = x.tr.sent id := hSent id
    have e1 : min liq ((x.st.parents id).qty - (x.st.parents id).sent)
        = min liq (x.tr.qty id - x.tr.sent id) := by rw [hqty, hsent]
    unfold step expectedRoute
    simp only [hlt, hlt2, dite_eq_ite, ↓reduceIte]
    rw [e1]
    by_cases hamt : 0 < min liq (x.tr.qty id - x.tr.sent id) <;> simp [hamt]
  · have hltT : ¬ id < x.tr.nOrders := by omega
    unfold step expectedRoute
    simp [hlt, hltT]

theorem sentLE_start_aux2 : ∀ id : Nat, (start.st.parents id).sent ≤ (start.st.parents id).qty := by
  intro id; simp [start, init]

theorem sentLE_route_succ_aux2 (x : Sys) (rid liq j : Nat)
    (hle : (x.st.parents rid).sent ≤ (x.st.parents rid).qty)
    (heq : j = rid) :
    (if j = rid then (x.st.parents rid).sent + min liq ((x.st.parents rid).qty - (x.st.parents rid).sent) else (x.st.parents j).sent) ≤
    (if j = rid then (x.st.parents rid).qty else (x.st.parents j).qty) := by
  rw [if_pos heq, if_pos heq]
  omega

theorem sentLE_route_pres_aux2 (x : Sys) (rid liq : Nat) (b : Build)
    (IH : ∀ j, (x.st.parents j).sent ≤ (x.st.parents j).qty) (j : Nat) :
    ((advance step b x (Event.route rid liq)).st.parents j).sent ≤
      ((advance step b x (Event.route rid liq)).st.parents j).qty := by
  by_cases hlt : rid < x.st.nParents
  · by_cases hamt : 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)
    · have hstS : ((advance step b x (Event.route rid liq)).st.parents j).sent =
        (if j = rid then (x.st.parents rid).sent + min liq ((x.st.parents rid).qty - (x.st.parents rid).sent) else (x.st.parents j).sent) := by
        rw [adv_route_st_parents_succ x rid liq b j hlt hamt]
        simp only [upd]
        split
        · next he => subst he; rfl
        · rfl
      have hstQ : ((advance step b x (Event.route rid liq)).st.parents j).qty =
        (if j = rid then (x.st.parents rid).qty else (x.st.parents j).qty) := by
        rw [adv_route_st_parents_succ x rid liq b j hlt hamt]
        simp only [upd]
        split
        · next he => subst he; rfl
        · rfl
      rw [hstS, hstQ]
      by_cases heq : j = rid
      · rw [if_pos heq, if_pos heq]; have := IH rid; omega
      · rw [if_neg heq, if_neg heq]; exact IH j
    · have heq : ((advance step b x (Event.route rid liq)).st.parents j) = x.st.parents j :=
        adv_route_st_parents_eq2 x rid liq b j hlt hamt
      rw [heq]; exact IH j
  · have heq : ((advance step b x (Event.route rid liq)).st.parents j) = x.st.parents j :=
      adv_route_st_parents_eq x rid liq b j hlt
    rw [heq]; exact IH j

theorem sentLE_run_aux2 (b : Build) (evs : List Event) :
    ∀ id, ((run step b evs).st.parents id).sent ≤ ((run step b evs).st.parents id).qty := by
  apply run_induction step b (fun x => ∀ id, (x.st.parents id).sent ≤ (x.st.parents id).qty) sentLE_start_aux2 _ evs
  intro x e IH
  cases e with
  | parent q flag =>
    intro id
    rw [st_sent_parent, st_qty_parent]
    by_cases heq : id = x.st.nParents
    · simp [heq]
    · simp [heq]; exact IH id
  | route rid liq => exact sentLE_route_pres_aux2 x rid liq b IH
  | ack k =>
    intro id
    rw [adv_ack_st]; exact IH id
  | fill k q =>
    intro id
    rw [plan0_invR_fill_aux_sent_st, plan0_invR_fill_aux_qty_st]; exact IH id

theorem cum_upd_route2 (st : State) (id amt j : Nat) :
    (upd st.parents id ({ st.parents id with sent := (st.parents id).sent + amt }) j).cum =
    (st.parents j).cum := by
  unfold upd
  by_cases h : j = id <;> simp [h]

theorem adv_parent_nChild2 (x : Sys) (q : Nat) (flag : Bool) (b : Build) :
    (advance step b x (Event.parent q flag)).st.nChildren = x.st.nChildren := by
  simp [advance, step]

theorem adv_route_nChild_eq (x : Sys) (id liq : Nat) (b : Build) (h : ¬ id < x.st.nParents) :
    (advance step b x (Event.route id liq)).st.nChildren = x.st.nChildren := by
  simp [advance, step, h]

theorem adv_route_nChild_eq2 (x : Sys) (id liq : Nat) (b : Build) (h : id < x.st.nParents)
    (hamt : ¬ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (advance step b x (Event.route id liq)).st.nChildren = x.st.nChildren := by
  simp [advance, step, h, hamt]

theorem adv_route_nChild_succ (x : Sys) (id liq : Nat) (b : Build) (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (advance step b x (Event.route id liq)).st.nChildren = x.st.nChildren + 1 := by
  simp [advance, step, h, hamt]

theorem adv_ack_nChild (x : Sys) (k : Nat) (b : Build) :
    (advance step b x (Event.ack k)).st.nChildren = x.st.nChildren := by
  simp [advance, step]

theorem adv_fill_nChild (x : Sys) (k q : Nat) (b : Build) :
    (advance step b x (Event.fill k q)).st.nChildren = x.st.nChildren := by
  simp only [advance, step]
  split
  · rfl
  · rfl

theorem adv_fill_trkids3 (x : Sys) (b : Build) (k q : Nat) :
    (advance step b x (Event.fill k q)).tr.kids = (x.tr.observe (Event.fill k q)).kids := by
  exact plan0_invR_fill_aux_trkids x b k q

theorem adv_fill_st_parents_cum3 (x : Sys) (b : Build) (k q j : Nat)
    (h : k < x.st.nChildren) :
    ((advance step b x (Event.fill k q)).st.parents j).cum =
    (if j = (x.st.children k).parent then (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) else (x.st.parents j).cum) := by
  simp only [advance, step, h, dite_eq_ite, ↓reduceIte]
  simp only [upd]
  by_cases heq : j = (x.st.children k).parent <;> simp [heq]

theorem plan2_exec_fill_formula (b : Build) (x : Sys) (k q j : Nat) :
    (advance step b x (Event.fill k q)).tr.exec j =
      x.tr.exec j + (match x.tr.kids[k]? with
        | some c => if c.parent = j then min q (c.qty - c.done) else 0
        | none => 0) := by
  have hout : (step b x.st (Event.fill k q)).2 = [] := step_fill_out2 _ _ _ _
  have htr : (advance step b x (Event.fill k q)).tr.kids = (x.tr.observe (Event.fill k q)).kids := by
    simp [advance, Truth.record, hout]
  have hexec : (advance step b x (Event.fill k q)).tr.exec j =
      execFor (x.tr.observe (Event.fill k q)).kids j := by
    simp [Truth.exec, htr]
  have hx : x.tr.exec j = execFor x.tr.kids j := rfl
  rw [hexec, hx]
  cases h : x.tr.kids[k]? with
  | none =>
    have hobs : (x.tr.observe (Event.fill k q)).kids = x.tr.kids := by
      simp [Truth.observe, h]
    rw [hobs]
    simp
  | some c =>
    have hobs : (x.tr.observe (Event.fill k q)).kids =
        x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) } := by
      simp [Truth.observe, h]
    rw [hobs]
    simp only
    rw [execFor_set_done _ _ _ _ h]


theorem plan2_cum_fill_formula (b : Build) (x : Sys) (k q j : Nat)
    (hlen : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩) :
    ((advance step b x (Event.fill k q)).st.parents j).cum =
      (x.st.parents j).cum + (match x.tr.kids[k]? with
        | some c => if c.parent = j then min q (c.qty - c.done) else 0
        | none => 0) := by
  have hex_aux : ∀ (l : List Kid) (kk : Nat), kk < l.length → ∃ c, l[kk]? = some c := by
    intro l
    induction l with
    | nil => intro kk h; simp at h
    | cons a as ih =>
      intro kk h
      cases kk with
      | zero => exact ⟨a, rfl⟩
      | succ kk =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
        obtain ⟨c, hc⟩ := ih kk h
        exact ⟨c, by simp [hc]⟩
  have hnone_aux : ∀ (l : List Kid) (kk : Nat), l.length ≤ kk → l[kk]? = none := by
    intro l
    induction l with
    | nil => intro kk _; rfl
    | cons a as ih =>
      intro kk h
      cases kk with
      | zero => simp at h
      | succ kk =>
        simp only [List.getElem?_cons_succ]
        apply ih
        simp at h ⊢
        omega
  by_cases hk : k < x.st.nChildren
  · have hlen_lt : k < x.tr.kids.length := by omega
    obtain ⟨c, hc⟩ := hex_aux _ _ hlen_lt
    have hck : x.st.children k = (⟨c.parent, c.qty, c.done⟩ : ChildRec) := hchild k c hc
    have hp : (x.st.children k).parent = c.parent := by rw [hck]
    have hq : (x.st.children k).qty = c.qty := by rw [hck]
    have hd : (x.st.children k).done = c.done := by rw [hck]
    have e := adv_fill_st_parents_cum3 x b k q j hk
    rw [hp, hq, hd] at e
    have hmatch : (match x.tr.kids[k]? with
        | some c' => if c'.parent = j then min q (c'.qty - c'.done) else 0
        | none => 0) = (if c.parent = j then min q (c.qty - c.done) else 0) := by
      rw [hc]
    rw [hmatch]
    by_cases heq : j = c.parent
    · have heq2 : c.parent = j := heq.symm
      rw [if_pos heq] at e
      rw [if_pos heq2]
      have hj : (x.st.parents j).cum = (x.st.parents c.parent).cum := by rw [heq]
      rw [hj]
      exact e
    · have heq2 : ¬ c.parent = j := fun h => heq h.symm
      rw [if_neg heq] at e
      rw [if_neg heq2]
      rw [e, Nat.add_zero]
  · have hle : x.tr.kids.length ≤ k := by omega
    have hnone : x.tr.kids[k]? = none := hnone_aux _ _ hle
    have hst : (advance step b x (Event.fill k q)).st = x.st := by
      simp [advance, step, hk]
    rw [hst, hnone, Nat.add_zero]


theorem plan2_invariant_parent_ack (b : Build) (x : Sys) (q : Nat) (flag : Bool) (k : Nat)
    (h : (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
         x.st.nChildren = x.tr.kids.length ∧
         (∀ idx c, x.tr.kids[idx]? = some c →
           x.st.children idx = ⟨c.parent, c.qty, c.done⟩) ∧
         (∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents)) :
    ((∀ id, ((advance step b x (Event.parent q flag)).st.parents id).cum =
        (advance step b x (Event.parent q flag)).tr.exec id) ∧
     (advance step b x (Event.parent q flag)).st.nChildren =
        (advance step b x (Event.parent q flag)).tr.kids.length ∧
     (∀ idx c, (advance step b x (Event.parent q flag)).tr.kids[idx]? = some c →
       (advance step b x (Event.parent q flag)).st.children idx =
         ⟨c.parent, c.qty, c.done⟩) ∧
     (∀ kid ∈ (advance step b x (Event.parent q flag)).tr.kids,
        kid.parent < (advance step b x (Event.parent q flag)).st.nParents)) ∧
    ((∀ id, ((advance step b x (Event.ack k)).st.parents id).cum =
        (advance step b x (Event.ack k)).tr.exec id) ∧
     (advance step b x (Event.ack k)).st.nChildren =
        (advance step b x (Event.ack k)).tr.kids.length ∧
     (∀ idx c, (advance step b x (Event.ack k)).tr.kids[idx]? = some c →
       (advance step b x (Event.ack k)).st.children idx =
         ⟨c.parent, c.qty, c.done⟩) ∧
     (∀ kid ∈ (advance step b x (Event.ack k)).tr.kids,
        kid.parent < (advance step b x (Event.ack k)).st.nParents)) := by
  obtain ⟨hCum, hLen, hChild, hBound⟩ := h
  have hkids_par : (advance step b x (Event.parent q flag)).tr.kids = x.tr.kids :=
    adv_parent_tr_kids x q flag b
  have hstchild_par : (advance step b x (Event.parent q flag)).st.children = x.st.children := by
    simp [advance, step]
  have hnChild_par : (advance step b x (Event.parent q flag)).st.nChildren = x.st.nChildren :=
    adv_parent_nChild2 x q flag b
  have hnPar_par : (advance step b x (Event.parent q flag)).st.nParents = x.st.nParents + 1 := by
    simp [advance, step]
  have hst_cum : ∀ id, ((advance step b x (Event.parent q flag)).st.parents id).cum =
      (if id = x.st.nParents then 0 else (x.st.parents id).cum) := by
    intro id
    simp [advance, step, upd]
    split
    · subst_vars; rfl
    · rfl
  have htr_exec : ∀ id, (advance step b x (Event.parent q flag)).tr.exec id = x.tr.exec id := by
    intro id
    simp [Truth.exec, hkids_par]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro id
      rw [hst_cum id, htr_exec id, hCum id]
      by_cases heq : id = x.st.nParents
      · subst heq
        have hzero : x.tr.exec x.st.nParents = 0 := by
          simp only [Truth.exec]
          exact execFor_eq_zero_of_lt _ _ _ hBound (Nat.le_refl _)
        rw [if_pos rfl, hzero]
      · rw [if_neg heq]
    · rw [hnChild_par, hkids_par, hLen]
    · intro idx c hc
      rw [hkids_par] at hc
      rw [hstchild_par]
      exact hChild idx c hc
    · intro kid hk
      rw [hkids_par] at hk
      have hlt := hBound kid hk
      omega
  · have hst : (advance step b x (Event.ack k)).st = x.st := adv_ack_st x k b
    have htr : (advance step b x (Event.ack k)).tr = x.tr := adv_ack_tr x k b
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro id
      rw [hst, htr, hCum id]
    · rw [hst, htr, hLen]
    · intro idx c hc
      rw [htr] at hc
      rw [hst]
      exact hChild idx c hc
    · intro kid hk
      rw [htr] at hk
      rw [hst]
      exact hBound kid hk








theorem plan2_exec_fill_formula_test3 (b : Build) (x : Sys) (k q j : Nat) :
    (advance step b x (Event.fill k q)).tr.exec j =
      x.tr.exec j + (match x.tr.kids[k]? with
        | some c => if c.parent = j then min q (c.qty - c.done) else 0
        | none => 0) := by
  have hout : (step b x.st (Event.fill k q)).2 = [] := step_fill_out2 _ _ _ _
  have htr : (advance step b x (Event.fill k q)).tr.kids = (x.tr.observe (Event.fill k q)).kids := by
    simp [advance, Truth.record, hout]
  have hexec : (advance step b x (Event.fill k q)).tr.exec j =
      execFor (x.tr.observe (Event.fill k q)).kids j := by
    simp [Truth.exec, htr]
  have hx : x.tr.exec j = execFor x.tr.kids j := rfl
  rw [hexec, hx]
  cases h : x.tr.kids[k]? with
  | none =>
    have hobs : (x.tr.observe (Event.fill k q)).kids = x.tr.kids := by
      simp [Truth.observe, h]
    rw [hobs]
    simp
  | some c =>
    have hobs : (x.tr.observe (Event.fill k q)).kids =
        x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) } := by
      simp [Truth.observe, h]
    rw [hobs]
    simp only
    rw [execFor_set_done _ _ _ _ h]

theorem aux_some_of_lt (l : List Kid) (k : Nat) (h : k < l.length) : ∃ c, l[k]? = some c := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => exact ⟨a, rfl⟩
    | succ k =>
      simp at h
      have := ih k h
      obtain ⟨c, hc⟩ := this
      exact ⟨c, by simpa using hc⟩

theorem aux_lt_of_some (l : List Kid) (k : Nat) (c : Kid) (h : l[k]? = some c) : k < l.length := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ k => simp at h ⊢; exact ih k h

theorem dbg_cum (b : Build) (x : Sys) (k q : Nat)
    (hk : k < x.st.nChildren) :
    (step b x.st (Event.fill k q)).1.parents =
      upd x.st.parents (x.st.children k).parent
        ({ x.st.parents (x.st.children k).parent with cum :=
          (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) } : ParentRec) := by
  simp only [step, hk, dite_eq_ite, ↓reduceIte]







theorem plan3_fill_adv_st_of_not_lt (b : Build) (x : Sys) (k q : Nat)
    (h : ¬ k < x.st.nChildren) :
    (advance step b x (Event.fill k q)).st = x.st := by
  simp [advance, step, h]


theorem plan3_getElem_ex_of_lt2 (l : List Kid) (k : Nat) (h : k < l.length) :
    ∃ c, l[k]? = some c := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => exact ⟨a, rfl⟩
    | succ k => simp at h; obtain ⟨c, hc⟩ := ih k h; exact ⟨c, by simpa using hc⟩

theorem plan3_getElem_ex_of_lt (l : List Kid) (k : Nat) (h : k < l.length) :
    ∃ c, l[k]? = some c := aux_some_of_lt l k h

theorem plan3_getElem_none_of_length_le (l : List Kid) (k : Nat)
    (h : l.length ≤ k) : l[k]? = none := by
  induction l generalizing k with
  | nil => simp
  | cons a as ih =>
    cases k with
    | zero => simp at h
    | succ k =>
      simp only [List.getElem?_cons_succ]
      apply ih
      simp at h
      omega

theorem helper_fill_cum_test2 (b : Build) (x : Sys) (k q j : Nat) (c : Kid)
    (hk : k < x.st.nChildren)
    (hc : x.tr.kids[k]? = some c)
    (hchild : ∀ idx c', x.tr.kids[idx]? = some c' →
      x.st.children idx = ⟨c'.parent, c'.qty, c'.done⟩) :
    ((advance step b x (Event.fill k q)).st.parents j).cum =
      (x.st.parents j).cum +
        (if c.parent = j then min q (c.qty - c.done) else 0) := by
  have hck : x.st.children k = (⟨c.parent, c.qty, c.done⟩ : ChildRec) := hchild k c hc
  have hp : (x.st.children k).parent = c.parent := by rw [hck]
  have hq : (x.st.children k).qty = c.qty := by rw [hck]
  have hd : (x.st.children k).done = c.done := by rw [hck]
  have e := adv_fill_st_parents_cum3 x b k q j hk
  rw [hp, hq, hd] at e
  by_cases heq : j = c.parent
  · rw [if_pos heq] at e
    have heq2 : c.parent = j := heq.symm
    rw [if_pos heq2]
    rw [e]
    congr 1
    rw [← heq]
  · have heq2 : ¬ c.parent = j := fun h => heq h.symm
    rw [if_neg heq] at e
    rw [if_neg heq2]
    rw [e]
    simp

theorem plan3_fill_cum_of_some_aux (b : Build) (x : Sys) (k q j : Nat) (c : Kid)
    (hk : k < x.st.nChildren)
    (hc : x.tr.kids[k]? = some c)
    (hchild : ∀ idx c', x.tr.kids[idx]? = some c' →
      x.st.children idx = ⟨c'.parent, c'.qty, c'.done⟩) :
    ((advance step b x (Event.fill k q)).st.parents j).cum =
      (x.st.parents j).cum +
        (if c.parent = j then min q (c.qty - c.done) else 0) :=
  helper_fill_cum_test2 b x k q j c hk hc hchild

theorem plan3_fill_cum_of_some (b : Build) (x : Sys) (k q j : Nat) (c : Kid)
    (hk : k < x.st.nChildren)
    (hc : x.tr.kids[k]? = some c)
    (hchild : ∀ idx c', x.tr.kids[idx]? = some c' →
      x.st.children idx = ⟨c'.parent, c'.qty, c'.done⟩) :
    ((advance step b x (Event.fill k q)).st.parents j).cum =
      (x.st.parents j).cum +
        (if c.parent = j then min q (c.qty - c.done) else 0) :=
  helper_fill_cum_test2 b x k q j c hk hc hchild

theorem plan3_fill_adv_st_of_not_lt_proof : ∀ (b : Build) (x : Sys) (k q : Nat),
    (¬ k < x.st.nChildren) →
    (advance step b x (Event.fill k q)).st = x.st := by
  intro b x k q h
  simp [advance, step, h]

theorem plan2_cum_fill_formula_aux (b : Build) (x : Sys) (k q j : Nat)
    (hlen : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩) :
    ((advance step b x (Event.fill k q)).st.parents j).cum =
      (x.st.parents j).cum + (match x.tr.kids[k]? with
        | some c => if c.parent = j then min q (c.qty - c.done) else 0
        | none => 0) := by
  by_cases hk : k < x.st.nChildren
  · have hlen_lt : k < x.tr.kids.length := by omega
    obtain ⟨c, hc⟩ := plan3_getElem_ex_of_lt _ _ hlen_lt
    have hformula := helper_fill_cum_test2 b x k q j c hk hc hchild
    have hmatch : (match x.tr.kids[k]? with
        | some c' => if c'.parent = j then min q (c'.qty - c'.done) else 0
        | none => 0) = (if c.parent = j then min q (c.qty - c.done) else 0) := by
      rw [hc]
    rw [hmatch]
    exact hformula
  · have hle : x.tr.kids.length ≤ k := by omega
    have hnone : x.tr.kids[k]? = none := plan3_getElem_none_of_length_le _ _ hle
    have hst : (advance step b x (Event.fill k q)).st = x.st :=
      plan3_fill_adv_st_of_not_lt b x k q hk
    rw [hst]
    simp [hnone]

theorem plan2_cum_fill_formula_proof (b : Build) (x : Sys) (k q j : Nat)
    (hlen : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩) :
    ((advance step b x (Event.fill k q)).st.parents j).cum =
      (x.st.parents j).cum + (match x.tr.kids[k]? with
        | some c => if c.parent = j then min q (c.qty - c.done) else 0
        | none => 0) :=
  plan2_cum_fill_formula_aux b x k q j hlen hchild

theorem tmp_selfcontained_cum2 (b : Build) (x : Sys) (k q j : Nat)
    (hlen : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩) :
    ((advance step b x (Event.fill k q)).st.parents j).cum =
      (x.st.parents j).cum + (match x.tr.kids[k]? with
        | some c => if c.parent = j then min q (c.qty - c.done) else 0
        | none => 0) := by
  have hex_aux : ∀ (l : List Kid) (kk : Nat), kk < l.length → ∃ c, l[kk]? = some c := by
    intro l
    induction l with
    | nil => intro kk h; simp at h
    | cons a as ih =>
      intro kk h
      cases kk with
      | zero => exact ⟨a, rfl⟩
      | succ kk =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
        obtain ⟨c, hc⟩ := ih kk h
        exact ⟨c, by simp [hc]⟩
  have hnone_aux : ∀ (l : List Kid) (kk : Nat), l.length ≤ kk → l[kk]? = none := by
    intro l
    induction l with
    | nil => intro kk _; rfl
    | cons a as ih =>
      intro kk h
      cases kk with
      | zero => simp at h
      | succ kk =>
        simp only [List.getElem?_cons_succ]
        apply ih
        simp at h ⊢
        omega
  by_cases hk : k < x.st.nChildren
  · have hlen_lt : k < x.tr.kids.length := by omega
    obtain ⟨c, hc⟩ := hex_aux _ _ hlen_lt
    have hck : x.st.children k = (⟨c.parent, c.qty, c.done⟩ : ChildRec) := hchild k c hc
    have hp : (x.st.children k).parent = c.parent := by rw [hck]
    have hq : (x.st.children k).qty = c.qty := by rw [hck]
    have hd : (x.st.children k).done = c.done := by rw [hck]
    have e := adv_fill_st_parents_cum3 x b k q j hk
    rw [hp, hq, hd] at e
    have hmatch : (match x.tr.kids[k]? with
        | some c' => if c'.parent = j then min q (c'.qty - c'.done) else 0
        | none => 0) = (if c.parent = j then min q (c.qty - c.done) else 0) := by
      rw [hc]
    rw [hmatch]
    by_cases heq : j = c.parent
    · have heq2 : c.parent = j := heq.symm
      rw [if_pos heq] at e
      rw [if_pos heq2]
      have hj : (x.st.parents j).cum = (x.st.parents c.parent).cum := by rw [heq]
      rw [hj]
      exact e
    · have heq2 : ¬ c.parent = j := fun h => heq h.symm
      rw [if_neg heq] at e
      rw [if_neg heq2]
      rw [e, Nat.add_zero]
  · have hle : x.tr.kids.length ≤ k := by omega
    have hnone : x.tr.kids[k]? = none := hnone_aux _ _ hle
    have hst : (advance step b x (Event.fill k q)).st = x.st := by
      simp [advance, step, hk]
    rw [hst, hnone, Nat.add_zero]

theorem plan2_invariant_parent_ack_proof (b : Build) (x : Sys) (q : Nat) (flag : Bool) (k : Nat)
    (h : (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
         x.st.nChildren = x.tr.kids.length ∧
         (∀ idx c, x.tr.kids[idx]? = some c →
           x.st.children idx = ⟨c.parent, c.qty, c.done⟩) ∧
         (∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents)) :
    ((∀ id, ((advance step b x (Event.parent q flag)).st.parents id).cum =
        (advance step b x (Event.parent q flag)).tr.exec id) ∧
     (advance step b x (Event.parent q flag)).st.nChildren =
        (advance step b x (Event.parent q flag)).tr.kids.length ∧
     (∀ idx c, (advance step b x (Event.parent q flag)).tr.kids[idx]? = some c →
       (advance step b x (Event.parent q flag)).st.children idx =
         ⟨c.parent, c.qty, c.done⟩) ∧
     (∀ kid ∈ (advance step b x (Event.parent q flag)).tr.kids,
        kid.parent < (advance step b x (Event.parent q flag)).st.nParents)) ∧
    ((∀ id, ((advance step b x (Event.ack k)).st.parents id).cum =
        (advance step b x (Event.ack k)).tr.exec id) ∧
     (advance step b x (Event.ack k)).st.nChildren =
        (advance step b x (Event.ack k)).tr.kids.length ∧
     (∀ idx c, (advance step b x (Event.ack k)).tr.kids[idx]? = some c →
       (advance step b x (Event.ack k)).st.children idx =
         ⟨c.parent, c.qty, c.done⟩) ∧
     (∀ kid ∈ (advance step b x (Event.ack k)).tr.kids,
        kid.parent < (advance step b x (Event.ack k)).st.nParents)) := by
  obtain ⟨hCum, hLen, hChild, hBound⟩ := h
  have hkids_par : (advance step b x (Event.parent q flag)).tr.kids = x.tr.kids :=
    adv_parent_tr_kids x q flag b
  have hstchild_par : (advance step b x (Event.parent q flag)).st.children = x.st.children := by
    simp [advance, step]
  have hnChild_par : (advance step b x (Event.parent q flag)).st.nChildren = x.st.nChildren :=
    adv_parent_nChild2 x q flag b
  have hnPar_par : (advance step b x (Event.parent q flag)).st.nParents = x.st.nParents + 1 := by
    simp [advance, step]
  have hst_cum : ∀ id, ((advance step b x (Event.parent q flag)).st.parents id).cum =
      (if id = x.st.nParents then 0 else (x.st.parents id).cum) := by
    intro id
    simp [advance, step, upd]
    split
    · subst_vars; rfl
    · rfl
  have htr_exec : ∀ id, (advance step b x (Event.parent q flag)).tr.exec id = x.tr.exec id := by
    intro id
    simp [Truth.exec, hkids_par]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro id
      rw [hst_cum id, htr_exec id, hCum id]
      by_cases heq : id = x.st.nParents
      · subst heq
        have hzero : x.tr.exec x.st.nParents = 0 := by
          simp only [Truth.exec]
          exact execFor_eq_zero_of_lt _ _ _ hBound (Nat.le_refl _)
        rw [if_pos rfl, hzero]
      · rw [if_neg heq]
    · rw [hnChild_par, hkids_par, hLen]
    · intro idx c hc
      rw [hkids_par] at hc
      rw [hstchild_par]
      exact hChild idx c hc
    · intro kid hk
      rw [hkids_par] at hk
      have hlt := hBound kid hk
      omega
  · have hst : (advance step b x (Event.ack k)).st = x.st := adv_ack_st x k b
    have htr : (advance step b x (Event.ack k)).tr = x.tr := adv_ack_tr x k b
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro id
      rw [hst, htr, hCum id]
    · rw [hst, htr, hLen]
    · intro idx c hc
      rw [htr] at hc
      rw [hst]
      exact hChild idx c hc
    · intro kid hk
      rw [htr] at hk
      rw [hst]
      exact hBound kid hk

theorem my_route_cum_st (x : Sys) (b : Build) (rid liq j : Nat) :
    ((advance step b x (Event.route rid liq)).st.parents j).cum = (x.st.parents j).cum := by
  simp only [advance, step]
  split
  · rename_i h
    split
    · rename_i h2
      simp only [cum_upd_route2]
    · rfl
  · rfl

theorem my_route_exec_tr (x : Sys) (b : Build) (rid liq j : Nat) :
    (advance step b x (Event.route rid liq)).tr.exec j = x.tr.exec j := by
  have htr := adv_route_trkids x rid liq b
  simp only [Truth.exec]
  rw [htr]
  rw [execFor_append]
  have hz : execFor ((step b x.st (Event.route rid liq)).2.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) j = 0 :=
    execFor_new _ _
  omega

theorem my_route_len_tr (x : Sys) (b : Build) (rid liq : Nat) :
    (advance step b x (Event.route rid liq)).tr.kids.length =
      x.tr.kids.length + (step b x.st (Event.route rid liq)).2.length := by
  have htr := adv_route_trkids x rid liq b
  rw [htr, List.length_append, List.length_map]

theorem my_route_child_st_eq (x : Sys) (b : Build) (rid liq idx : Nat)
    (h : ¬ rid < x.st.nParents) :
    (advance step b x (Event.route rid liq)).st.children idx = x.st.children idx := by
  have hst : (step b x.st (Event.route rid liq)).1 = x.st := by simp [step, h]
  simp [advance, hst]

theorem my_route_child_st_eq2 (x : Sys) (b : Build) (rid liq idx : Nat)
    (h : rid < x.st.nParents)
    (hamt : ¬ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (Event.route rid liq)).st.children idx = x.st.children idx := by
  have hst : (step b x.st (Event.route rid liq)).1 = x.st := by simp [step, h, hamt]
  simp [advance, hst]

theorem my_route_out_len_nil (x : Sys) (b : Build) (rid liq : Nat)
    (h : ¬ rid < x.st.nParents) :
    (step b x.st (Event.route rid liq)).2.length = 0 := by
  rw [adv_route_out_nil2 x rid liq b h]; rfl

theorem my_route_out_len_nil2 (x : Sys) (b : Build) (rid liq : Nat)
    (h : rid < x.st.nParents)
    (hamt : ¬ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (step b x.st (Event.route rid liq)).2.length = 0 := by
  rw [adv_route_out_nil x rid liq b h hamt]; rfl

theorem my_route_out_len_one (x : Sys) (b : Build) (rid liq : Nat)
    (h : rid < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (step b x.st (Event.route rid liq)).2.length = 1 := by
  rw [adv_route_out_succ x rid liq b h hamt]; rfl

theorem my_route_kids_nil (x : Sys) (b : Build) (rid liq : Nat)
    (hout : (step b x.st (Event.route rid liq)).2 = []) :
    (advance step b x (Event.route rid liq)).tr.kids = x.tr.kids := by
  have htr := adv_route_trkids x rid liq b
  rw [hout] at htr
  simp at htr
  exact htr

theorem my_route_st_nil (x : Sys) (b : Build) (rid liq : Nat)
    (hst : (step b x.st (Event.route rid liq)).1 = x.st) :
    (advance step b x (Event.route rid liq)).st = x.st := by
  simp [advance, hst]

theorem my_route_st_eq_of_nil1 (x : Sys) (b : Build) (rid liq : Nat)
    (h : ¬ rid < x.st.nParents) :
    (step b x.st (Event.route rid liq)).1 = x.st := by simp [step, h]

theorem my_route_st_eq_of_nil2 (x : Sys) (b : Build) (rid liq : Nat)
    (h : rid < x.st.nParents)
    (hamt : ¬ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (step b x.st (Event.route rid liq)).1 = x.st := by simp [step, h, hamt]

theorem my_route_children_succ (x : Sys) (b : Build) (rid liq : Nat)
    (h : rid < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (Event.route rid liq)).st.children =
      upd x.st.children x.st.nChildren ⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ := by
  simp [advance, step, h, hamt]

theorem my_route_nPar3 (x : Sys) (b : Build) (rid liq : Nat) :
    (advance step b x (Event.route rid liq)).st.nParents = x.st.nParents := by
  simp only [advance, step]
  split
  · rename_i h
    split
    · rfl
    · rfl
  · rfl

theorem my_upd_other_child (f : Nat → ChildRec) (N idx : Nat) (v : ChildRec) (h : idx ≠ N) :
    upd f N v idx = f idx := by simp [upd, h]

theorem my_upd_same_child (f : Nat → ChildRec) (N : Nat) (v : ChildRec) :
    upd f N v N = v := by simp [upd]

theorem my_route_trkids_succ (x : Sys) (b : Build) (rid liq : Nat)
    (h : rid < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (Event.route rid liq)).tr.kids =
      x.tr.kids ++ [(⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)] := by
  have htr := adv_route_trkids x rid liq b
  have hout := adv_route_out_succ x rid liq b h hamt
  rw [htr, hout]
  rfl

theorem my_route_len_succ_eq (x : Sys) (b : Build) (rid liq : Nat)
    (h : rid < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (Event.route rid liq)).tr.kids.length = x.tr.kids.length + 1 := by
  rw [my_route_trkids_succ x b rid liq h hamt, List.length_append]
  rfl

theorem my_route_nChild_succ2 (x : Sys) (b : Build) (rid liq : Nat)
    (h : rid < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (Event.route rid liq)).st.nChildren = x.st.nChildren + 1 :=
  adv_route_nChild_succ x rid liq b h hamt



theorem plan4_route_succ_desc_aux_done : True := trivial








theorem plan4_adv_route_eq_of_out_nil (b : Build) (x : Sys) (id liq : Nat)
    (hout : (step b x.st (Event.route id liq)).2 = []) :
    advance step b x (Event.route id liq) = x := by
  have hst : (step b x.st (Event.route id liq)).1 = x.st := by
    by_cases hlt : id < x.st.nParents
    · by_cases hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
      · have hout2 : (step b x.st (Event.route id liq)).2 =
            [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] := by
          simp [step, hlt, hamt]
        rw [hout2] at hout
        simp at hout
      · simp [step, hlt, hamt]
    · simp [step, hlt]
  have htr : (x.tr.observe (Event.route id liq)).record (step b x.st (Event.route id liq)).2 = x.tr := by
    rw [hout]
    have hobs : x.tr.observe (Event.route id liq) = x.tr := observe_route _ _ _
    rw [hobs]
    simp [Truth.record]
  have hadv : advance step b x (Event.route id liq) =
      ⟨(step b x.st (Event.route id liq)).1,
       (x.tr.observe (Event.route id liq)).record (step b x.st (Event.route id liq)).2⟩ := rfl
  rw [hadv, hst, htr]

theorem plan4_route_succ_desc_proof (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (advance step b x (Event.route id liq)).tr.kids =
      x.tr.kids ++ [(⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ : Kid)] ∧
    (advance step b x (Event.route id liq)).st.children =
      upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ ∧
    (advance step b x (Event.route id liq)).st.nChildren = x.st.nChildren + 1 ∧
    (advance step b x (Event.route id liq)).st.nParents = x.st.nParents ∧
    (∀ j, ((advance step b x (Event.route id liq)).st.parents j).cum = (x.st.parents j).cum) ∧
    (∀ j, (advance step b x (Event.route id liq)).tr.exec j = x.tr.exec j) := by
  refine ⟨my_route_trkids_succ x b id liq h hamt, my_route_children_succ x b id liq h hamt,
    my_route_nChild_succ2 x b id liq h hamt, my_route_nPar3 x b id liq, ?_, ?_⟩
  · intro j; exact my_route_cum_st x b id liq j
  · intro j; exact my_route_exec_tr x b id liq j

theorem plan4_route_succ_desc_check (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (advance step b x (Event.route id liq)).tr.kids =
      x.tr.kids ++ [(⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ : Kid)] := by
  exact my_route_trkids_succ x b id liq h hamt

theorem plan4_route_succ_desc (b : Build) (x : Sys) (id liq : Nat)
    (h : id < x.st.nParents)
    (hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (advance step b x (Event.route id liq)).tr.kids =
      x.tr.kids ++ [(⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ : Kid)] ∧
    (advance step b x (Event.route id liq)).st.children =
      upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ ∧
    (advance step b x (Event.route id liq)).st.nChildren = x.st.nChildren + 1 ∧
    (advance step b x (Event.route id liq)).st.nParents = x.st.nParents ∧
    (∀ j, ((advance step b x (Event.route id liq)).st.parents j).cum = (x.st.parents j).cum) ∧
    (∀ j, (advance step b x (Event.route id liq)).tr.exec j = x.tr.exec j) :=
  ⟨my_route_trkids_succ x b id liq h hamt, my_route_children_succ x b id liq h hamt,
    my_route_nChild_succ2 x b id liq h hamt, my_route_nPar3 x b id liq,
    fun j => my_route_cum_st x b id liq j,
    fun j => my_route_exec_tr x b id liq j⟩

theorem plan4_getElem_append_singleton (l : List Kid) (kid : Kid) (idx : Nat) (c : Kid)
    (h : (l ++ [kid])[idx]? = some c) :
    (l[idx]? = some c) ∨ (idx = l.length ∧ c = kid) := by
  induction l generalizing idx with
  | nil =>
    cases idx with
    | zero =>
      simp at h
      subst h
      exact Or.inr ⟨rfl, rfl⟩
    | succ n =>
      simp at h
  | cons a as ih =>
    cases idx with
    | zero =>
      have h0 : ((a :: as) ++ [kid])[0]? = some a := by simp
      simp only [List.getElem?_cons_zero] at h ⊢
      -- h : some a = some c, goal l[0]? = some c
      cases h
      exact Or.inl rfl
    | succ n =>
      have heq1 : ((a :: as) ++ [kid])[n+1]? = (as ++ [kid])[n]? := by simp
      have heq2 : (a :: as)[n+1]? = as[n]? := by simp
      rw [heq1] at h
      rw [heq2]
      have h2 := ih n h
      rcases h2 with h2 | ⟨heq, heqc⟩
      · exact Or.inl h2
      · exact Or.inr ⟨by simp [heq], heqc⟩

theorem plan4_route_children (b : Build) (x : Sys) (id liq : Nat)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hChild : ∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩) :
    ∀ idx c, (advance step b x (Event.route id liq)).tr.kids[idx]? = some c →
      (advance step b x (Event.route id liq)).st.children idx =
        ⟨c.parent, c.qty, c.done⟩ := by
  by_cases hlt : id < x.st.nParents
  · by_cases hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
    · have hdesc := plan4_route_succ_desc b x id liq hlt hamt
      obtain ⟨htrk, hstc, hnC, hnP, _, _⟩ := hdesc
      intro idx c hc
      rw [htrk] at hc
      have hdecomp := plan4_getElem_append_singleton x.tr.kids (⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ : Kid) idx c hc
      rw [hstc]
      rcases hdecomp with hOld | ⟨heqIdx, heqC⟩
      · have hltIdx : idx < x.tr.kids.length := aux_lt_of_some x.tr.kids idx c hOld
        have hne : idx ≠ x.st.nChildren := by omega
        rw [my_upd_other_child _ _ _ _ hne]
        exact hChild idx c hOld
      · subst heqIdx
        subst heqC
        have hupd : upd x.st.children x.st.nChildren (⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ : ChildRec) x.tr.kids.length =
            (⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ : ChildRec) := by
          rw [← hLen]
          exact my_upd_same_child _ _ _
        simpa using hupd
    · have hout : (step b x.st (Event.route id liq)).2 = [] :=
        adv_route_out_nil x id liq b hlt hamt
      have heq : advance step b x (Event.route id liq) = x :=
        plan4_adv_route_eq_of_out_nil b x id liq hout
      intro idx c hc
      rw [heq] at hc ⊢
      exact hChild idx c hc
  · have hout : (step b x.st (Event.route id liq)).2 = [] :=
      adv_route_out_nil2 x id liq b hlt
    have heq : advance step b x (Event.route id liq) = x :=
      plan4_adv_route_eq_of_out_nil b x id liq hout
    intro idx c hc
    rw [heq] at hc ⊢
    exact hChild idx c hc

theorem plan4_route_cum_len_bound (b : Build) (x : Sys) (id liq : Nat)
    (hCum : ∀ j, (x.st.parents j).cum = x.tr.exec j)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hBound : ∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents) :
    (∀ j, ((advance step b x (Event.route id liq)).st.parents j).cum =
        (advance step b x (Event.route id liq)).tr.exec j) ∧
    (advance step b x (Event.route id liq)).st.nChildren =
        (advance step b x (Event.route id liq)).tr.kids.length ∧
    (∀ kid ∈ (advance step b x (Event.route id liq)).tr.kids,
       kid.parent < (advance step b x (Event.route id liq)).st.nParents) := by
  have hCum' : ∀ j, ((advance step b x (Event.route id liq)).st.parents j).cum =
      (advance step b x (Event.route id liq)).tr.exec j := by
    intro j
    rw [my_route_cum_st x b id liq j, my_route_exec_tr x b id liq j, hCum j]
  refine ⟨hCum', ?_, ?_⟩
  · by_cases hlt : id < x.st.nParents
    · by_cases hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
      · have hC : (advance step b x (Event.route id liq)).st.nChildren = x.st.nChildren + 1 :=
          my_route_nChild_succ2 x b id liq hlt hamt
        have hT : (advance step b x (Event.route id liq)).tr.kids.length = x.tr.kids.length + 1 :=
          my_route_len_succ_eq x b id liq hlt hamt
        omega
      · have hC : (advance step b x (Event.route id liq)).st.nChildren = x.st.nChildren :=
          adv_route_nChild_eq2 x id liq b hlt hamt
        have hout : (step b x.st (Event.route id liq)).2 = [] :=
          adv_route_out_nil x id liq b hlt hamt
        have hT : (advance step b x (Event.route id liq)).tr.kids = x.tr.kids :=
          my_route_kids_nil x b id liq hout
        rw [hC, hT, hLen]
    · have hC : (advance step b x (Event.route id liq)).st.nChildren = x.st.nChildren :=
        adv_route_nChild_eq x id liq b hlt
      have hout : (step b x.st (Event.route id liq)).2 = [] :=
        adv_route_out_nil2 x id liq b hlt
      have hT : (advance step b x (Event.route id liq)).tr.kids = x.tr.kids :=
        my_route_kids_nil x b id liq hout
      rw [hC, hT, hLen]
  · have hnP : (advance step b x (Event.route id liq)).st.nParents = x.st.nParents :=
      my_route_nPar3 x b id liq
    rw [hnP]
    by_cases hlt : id < x.st.nParents
    · by_cases hamt : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
      · have htrk := my_route_trkids_succ x b id liq hlt hamt
        intro kid hk
        rw [htrk] at hk
        simp only [List.mem_append] at hk
        rcases hk with hk | hk
        · exact hBound kid hk
        · simp at hk
          obtain rfl := hk
          exact hlt
      · have hout : (step b x.st (Event.route id liq)).2 = [] :=
          adv_route_out_nil x id liq b hlt hamt
        have hT : (advance step b x (Event.route id liq)).tr.kids = x.tr.kids :=
          my_route_kids_nil x b id liq hout
        intro kid hk
        rw [hT] at hk
        exact hBound kid hk
    · have hout : (step b x.st (Event.route id liq)).2 = [] :=
        adv_route_out_nil2 x id liq b hlt
      have hT : (advance step b x (Event.route id liq)).tr.kids = x.tr.kids :=
        my_route_kids_nil x b id liq hout
      intro kid hk
      rw [hT] at hk
      exact hBound kid hk

theorem plan2_invariant_route_tmp_check (b : Build) (x : Sys) (id liq : Nat)
    (h : (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
         x.st.nChildren = x.tr.kids.length ∧
         (∀ idx c, x.tr.kids[idx]? = some c →
           x.st.children idx = ⟨c.parent, c.qty, c.done⟩) ∧
         (∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents)) :
    (∀ j, ((advance step b x (Event.route id liq)).st.parents j).cum =
        (advance step b x (Event.route id liq)).tr.exec j) ∧
    (advance step b x (Event.route id liq)).st.nChildren =
        (advance step b x (Event.route id liq)).tr.kids.length ∧
    (∀ idx c, (advance step b x (Event.route id liq)).tr.kids[idx]? = some c →
      (advance step b x (Event.route id liq)).st.children idx =
        ⟨c.parent, c.qty, c.done⟩) ∧
    (∀ kid ∈ (advance step b x (Event.route id liq)).tr.kids,
       kid.parent < (advance step b x (Event.route id liq)).st.nParents) := by
  obtain ⟨hCum, hLen, hChild, hBound⟩ := h
  have hCLB := plan4_route_cum_len_bound b x id liq hCum hLen hBound
  obtain ⟨hCum', hLen', hBound'⟩ := hCLB
  have hCh := plan4_route_children b x id liq hLen hChild
  exact ⟨hCum', hLen', hCh, hBound'⟩

theorem plan2_invariant_route (b : Build) (x : Sys) (id liq : Nat)
    (h : (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
         x.st.nChildren = x.tr.kids.length ∧
         (∀ idx c, x.tr.kids[idx]? = some c →
           x.st.children idx = ⟨c.parent, c.qty, c.done⟩) ∧
         (∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents)) :
    (∀ j, ((advance step b x (Event.route id liq)).st.parents j).cum =
        (advance step b x (Event.route id liq)).tr.exec j) ∧
    (advance step b x (Event.route id liq)).st.nChildren =
        (advance step b x (Event.route id liq)).tr.kids.length ∧
    (∀ idx c, (advance step b x (Event.route id liq)).tr.kids[idx]? = some c →
      (advance step b x (Event.route id liq)).st.children idx =
        ⟨c.parent, c.qty, c.done⟩) ∧
    (∀ kid ∈ (advance step b x (Event.route id liq)).tr.kids,
       kid.parent < (advance step b x (Event.route id liq)).st.nParents) := by
  obtain ⟨hCum, hLen, hChild, hBound⟩ := h
  have hCLB := plan4_route_cum_len_bound b x id liq hCum hLen hBound
  obtain ⟨hCum', hLen', hBound'⟩ := hCLB
  have hCh := plan4_route_children b x id liq hLen hChild
  exact ⟨hCum', hLen', hCh, hBound'⟩

theorem fill_observe_length2 (t : Truth) (k q : Nat) :
    (t.observe (Event.fill k q)).kids.length = t.kids.length := by
  cases h : t.kids[k]? <;> simp [Truth.observe, h]

theorem fill_adv_tr_length2 (x : Sys) (b : Build) (k q : Nat) :
    (advance step b x (Event.fill k q)).tr.kids.length = x.tr.kids.length := by
  have htr : (advance step b x (Event.fill k q)).tr.kids =
    (x.tr.observe (Event.fill k q)).kids := plan0_invR_fill_aux_trkids x b k q
  rw [htr, fill_observe_length2]

theorem fill_st_children_eq_of_lt3 (x : Sys) (b : Build) (k q idx : Nat)
    (hk : k < x.st.nChildren) :
    (advance step b x (Event.fill k q)).st.children idx =
      upd x.st.children k
        ({ (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } : ChildRec) idx := by
  simp [advance, step, hk]

theorem set_get_eq_test (l : List Kid) (k : Nat) (v : Kid) (hk : k < l.length) :
    (l.set k v)[k]? = some v := by
  simp [hk]

theorem probe_set_lemmas (l : List Kid) (k : Nat) (v : Kid) (h : k < l.length) :
    (l.set k v)[k]? = some v := by
  simp [h]











theorem plan5_fill_kids_cases (t : Truth) (k q idx : Nat) (c : Kid)
    (h : ((t.observe (Event.fill k q)).kids)[idx]? = some c) :
    (t.kids[idx]? = some c ∧ idx ≠ k) ∨
      (∃ c0 : Kid, t.kids[k]? = some c0 ∧ idx = k ∧
        c = { c0 with done := c0.done + min q (c0.qty - c0.done) }) := by
  have set_self : ∀ (l : List Kid) (kk : Nat) (v : Kid), kk < l.length → (l.set kk v)[kk]? = some v := by
    intro l
    induction l with
    | nil => intro kk v hh; simp at hh
    | cons a as ih =>
      intro kk v hh
      cases kk with
      | zero => simp
      | succ kk => simp; exact ih kk v (by simpa using hh)
  have set_other : ∀ (l : List Kid) (kk idx2 : Nat) (v : Kid), idx2 ≠ kk → (l.set kk v)[idx2]? = l[idx2]? := by
    intro l
    induction l with
    | nil => intro kk idx2 v hne; simp
    | cons a as ih =>
      intro kk idx2 v hne
      cases kk with
      | zero =>
        cases idx2 with
        | zero => exact absurd rfl hne
        | succ n => simp
      | succ kk =>
        cases idx2 with
        | zero => simp
        | succ n =>
          simp
          exact ih kk n v (fun he => hne (congrArg Nat.succ he))
  revert h
  cases hEq : t.kids[k]? with
  | none =>
    intro h
    have hobs : (t.observe (Event.fill k q)).kids = t.kids := by simp [Truth.observe, hEq]
    rw [hobs] at h
    by_cases heq : idx = k
    · rw [heq, hEq] at h; simp at h
    · exact Or.inl ⟨h, heq⟩
  | some d =>
    intro h
    have hobs : (t.observe (Event.fill k q)).kids =
        t.kids.set k { d with done := d.done + min q (d.qty - d.done) } := by
      simp [Truth.observe, hEq]
    rw [hobs] at h
    by_cases heq : idx = k
    · rw [heq] at h
      have hlen : k < t.kids.length := aux_lt_of_some t.kids k d hEq
      have hset := set_self t.kids k { d with done := d.done + min q (d.qty - d.done) } hlen
      rw [hset] at h
      have hc_eq : c = { d with done := d.done + min q (d.qty - d.done) } := by simpa using h.symm
      exact Or.inr ⟨d, rfl, heq, hc_eq⟩
    · have hget := set_other t.kids k idx { d with done := d.done + min q (d.qty - d.done) } heq
      rw [hget] at h
      exact Or.inl ⟨h, heq⟩

theorem plan5_fill_st_children (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (Event.fill k q)).st.children =
      if k < x.st.nChildren then
        upd x.st.children k
          { x.st.children k with
            done := (x.st.children k).done +
              min q ((x.st.children k).qty - (x.st.children k).done) }
      else x.st.children := by
  simp only [advance, step]
  split
  · rfl
  · rfl

theorem plan5_fill_children_preserved_testC (b : Build) (x : Sys) (k q : Nat)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hChild : ∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩)
    (idx : Nat) (c : Kid)
    (hc : (advance step b x (Event.fill k q)).tr.kids[idx]? = some c) :
      (advance step b x (Event.fill k q)).st.children idx =
        ⟨c.parent, c.qty, c.done⟩ := by
  have htr_eq := plan0_invR_fill_aux_trkids x b k q
  have hc2 : (x.tr.observe (Event.fill k q)).kids[idx]? = some c := by
    rw [← htr_eq]; exact hc
  have hcases := plan5_fill_kids_cases x.tr k q idx c hc2
  by_cases hk : k < x.st.nChildren
  · rcases hcases with ⟨hOld, hne⟩ | ⟨c0, hk0, heqIdx, heqC⟩
    · have hold := hChild idx c hOld
      have h1 := fill_st_children_eq_of_lt3 x b k q idx hk
      rw [h1]
      rw [upd_other _ _ _ _ hne]
      exact hold
    · have h1 := fill_st_children_eq_of_lt3 x b k q idx hk
      rw [h1]
      rw [heqIdx]
      rw [upd_same]
      have hck := hChild k c0 hk0
      rw [hck]
      rw [heqC]
  · have hst : (advance step b x (Event.fill k q)).st = x.st :=
      plan3_fill_adv_st_of_not_lt b x k q hk
    rw [hst]
    rcases hcases with ⟨hOld, hne⟩ | ⟨c0, hk0, heqIdx, heqC⟩
    · exact hChild idx c hOld
    · exfalso
      have hlen_le : x.tr.kids.length ≤ k := by omega
      have hnone : x.tr.kids[k]? = none :=
        plan3_getElem_none_of_length_le x.tr.kids k hlen_le
      rw [hnone] at hk0
      simp at hk0

theorem plan5_fill_children_preserved (b : Build) (x : Sys) (k q : Nat)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hChild : ∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩) :
    ∀ idx c, (advance step b x (Event.fill k q)).tr.kids[idx]? = some c →
      (advance step b x (Event.fill k q)).st.children idx =
        ⟨c.parent, c.qty, c.done⟩ :=
  fun idx c hc => plan5_fill_children_preserved_testC b x k q hLen hChild idx c hc

theorem plan5_fill_cum_preserved (b : Build) (x : Sys) (k q : Nat)
    (hCum : ∀ id, (x.st.parents id).cum = x.tr.exec id)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hChild : ∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩) :
    ∀ j, ((advance step b x (Event.fill k q)).st.parents j).cum =
      (advance step b x (Event.fill k q)).tr.exec j := by
  intro j
  rw [plan2_cum_fill_formula_aux b x k q j hLen hChild, plan2_exec_fill_formula b x k q j, hCum j]

theorem plan5_fill_length_and_bound_aux_test (b : Build) (x : Sys) (k q : Nat)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hBound : ∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents) :
    (advance step b x (Event.fill k q)).st.nChildren =
        (advance step b x (Event.fill k q)).tr.kids.length ∧
      (∀ kid ∈ (advance step b x (Event.fill k q)).tr.kids,
        kid.parent < (advance step b x (Event.fill k q)).st.nParents) := by
  have hnC : (advance step b x (Event.fill k q)).st.nChildren = x.st.nChildren :=
    adv_fill_nChild x k q b
  have hnT : (advance step b x (Event.fill k q)).tr.kids.length = x.tr.kids.length :=
    fill_adv_tr_length2 x b k q
  have hnP : (advance step b x (Event.fill k q)).st.nParents = x.st.nParents :=
    plan0_invR_fill_aux_st_nPar x b k q
  have htrk : (advance step b x (Event.fill k q)).tr.kids = (x.tr.observe (Event.fill k q)).kids :=
    plan0_invR_fill_aux_trkids x b k q
  refine ⟨?_, ?_⟩
  · rw [hnC, hnT, hLen]
  · intro kid hk
    rw [hnP]
    rw [htrk] at hk
    exact plan0_fill_bound_aux x.tr x.st.nParents k q hBound kid hk

theorem plan5_fill_length_and_bound2 (b : Build) (x : Sys) (k q : Nat)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hBound : ∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents) :
    (advance step b x (Event.fill k q)).st.nChildren =
        (advance step b x (Event.fill k q)).tr.kids.length ∧
      (∀ kid ∈ (advance step b x (Event.fill k q)).tr.kids,
        kid.parent < (advance step b x (Event.fill k q)).st.nParents) := by
  have hnC : (advance step b x (Event.fill k q)).st.nChildren = x.st.nChildren :=
    adv_fill_nChild x k q b
  have hnT : (advance step b x (Event.fill k q)).tr.kids.length = x.tr.kids.length :=
    fill_adv_tr_length2 x b k q
  have hnP : (advance step b x (Event.fill k q)).st.nParents = x.st.nParents :=
    plan0_invR_fill_aux_st_nPar x b k q
  have htrk : (advance step b x (Event.fill k q)).tr.kids = (x.tr.observe (Event.fill k q)).kids :=
    plan0_invR_fill_aux_trkids x b k q
  refine ⟨?_, ?_⟩
  · rw [hnC, hnT, hLen]
  · intro kid hk
    rw [hnP]
    rw [htrk] at hk
    exact plan0_fill_bound_aux x.tr x.st.nParents k q hBound kid hk

theorem plan5_fill_length_and_bound (b : Build) (x : Sys) (k q : Nat)
    (hLen : x.st.nChildren = x.tr.kids.length)
    (hBound : ∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents) :
    (advance step b x (Event.fill k q)).st.nChildren =
        (advance step b x (Event.fill k q)).tr.kids.length ∧
      (∀ kid ∈ (advance step b x (Event.fill k q)).tr.kids,
        kid.parent < (advance step b x (Event.fill k q)).st.nParents) := by
  have hnC : (advance step b x (Event.fill k q)).st.nChildren = x.st.nChildren :=
    adv_fill_nChild x k q b
  have hnT : (advance step b x (Event.fill k q)).tr.kids.length = x.tr.kids.length :=
    fill_adv_tr_length2 x b k q
  have hnP : (advance step b x (Event.fill k q)).st.nParents = x.st.nParents :=
    plan0_invR_fill_aux_st_nPar x b k q
  have htrk : (advance step b x (Event.fill k q)).tr.kids = (x.tr.observe (Event.fill k q)).kids :=
    plan0_invR_fill_aux_trkids x b k q
  refine ⟨?_, ?_⟩
  · rw [hnC, hnT, hLen]
  · intro kid hk
    rw [hnP]
    rw [htrk] at hk
    exact plan0_fill_bound_aux x.tr x.st.nParents k q hBound kid hk

theorem plan2_invariant_fill (b : Build) (x : Sys) (k q : Nat)
    (h : (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
         x.st.nChildren = x.tr.kids.length ∧
         (∀ idx c, x.tr.kids[idx]? = some c →
           x.st.children idx = ⟨c.parent, c.qty, c.done⟩) ∧
         (∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents)) :
    (∀ j, ((advance step b x (Event.fill k q)).st.parents j).cum =
        (advance step b x (Event.fill k q)).tr.exec j) ∧
    (advance step b x (Event.fill k q)).st.nChildren =
        (advance step b x (Event.fill k q)).tr.kids.length ∧
    (∀ idx c, (advance step b x (Event.fill k q)).tr.kids[idx]? = some c →
      (advance step b x (Event.fill k q)).st.children idx =
        ⟨c.parent, c.qty, c.done⟩) ∧
    (∀ kid ∈ (advance step b x (Event.fill k q)).tr.kids,
       kid.parent < (advance step b x (Event.fill k q)).st.nParents) := by
  obtain ⟨hCum, hLen, hChild, hBound⟩ := h
  have hCum' := plan5_fill_cum_preserved b x k q hCum hLen hChild
  have hCh := plan5_fill_children_preserved b x k q hLen hChild
  have hLB := plan5_fill_length_and_bound b x k q hLen hBound
  exact ⟨hCum', hLB.1, hCh, hLB.2⟩

theorem plan2_run_invariant_proofcheck (b : Build) (evs : List Event) :
    (∀ id, ((run step b evs).st.parents id).cum = (run step b evs).tr.exec id) ∧
    (run step b evs).st.nChildren = (run step b evs).tr.kids.length ∧
    (∀ idx c, (run step b evs).tr.kids[idx]? = some c →
      (run step b evs).st.children idx = ⟨c.parent, c.qty, c.done⟩) ∧
    (∀ kid ∈ (run step b evs).tr.kids,
       kid.parent < (run step b evs).st.nParents) := by
  apply run_induction step b (fun x =>
    (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
    x.st.nChildren = x.tr.kids.length ∧
    (∀ idx c, x.tr.kids[idx]? = some c →
      x.st.children idx = ⟨c.parent, c.qty, c.done⟩) ∧
    (∀ kid ∈ x.tr.kids, kid.parent < x.st.nParents)) _ _ evs
  · refine ⟨?_, rfl, ?_, ?_⟩
    · intro id
      simp [start, init, Truth.empty, Truth.exec]
    · intro idx c h
      simp [start, init, Truth.empty] at h
    · intro kid h
      simp [start, Truth.empty] at h
  · intro x e hx
    cases e with
    | parent q flag =>
      exact (plan2_invariant_parent_ack b x q flag 0 hx).1
    | route id liq =>
      exact plan2_invariant_route b x id liq hx
    | ack k =>
      exact (plan2_invariant_parent_ack b x 0 false k hx).2
    | fill k q =>
      exact plan2_invariant_fill b x k q hx









theorem plan6_fill_kids_cases (t : Truth) (k q idx : Nat) (c : Kid)
    (h : ((t.observe (Event.fill k q)).kids)[idx]? = some c) :
    (t.kids[idx]? = some c ∧ idx ≠ k) ∨
      (∃ c0 : Kid, t.kids[k]? = some c0 ∧ idx = k ∧
        c = { c0 with done := c0.done + min q (c0.qty - c0.done) }) :=
  plan5_fill_kids_cases t k q idx c h


theorem plan6_getElem_set_of_ne (l : List Kid) (k idx : Nat) (v : Kid)
    (h : idx ≠ k) : (l.set k v)[idx]? = l[idx]? := by
  induction l generalizing k idx with
  | nil =>
    simp
  | cons a as ih =>
    cases k with
    | zero =>
      cases idx with
      | zero => simp at h
      | succ n => simp
    | succ k =>
      cases idx with
      | zero => simp
      | succ n =>
        simp only [List.set_cons_succ, List.getElem?_cons_succ]
        exact ih k n (fun he => h (congrArg Nat.succ he))

theorem plan6_getElem_set_self_aux (l : List Kid) (k : Nat) (v : Kid)
    (h : k < l.length) : (l.set k v)[k]? = some v := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      simp only [List.set_cons_succ, List.getElem?_cons_succ]
      exact ih k h

theorem plan6_getElem_set_self (l : List Kid) (k : Nat) (v : Kid)
    (h : k < l.length) : (l.set k v)[k]? = some v := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      simp only [List.set_cons_succ, List.getElem?_cons_succ]
      exact ih k h

theorem plan6_getElem_append_singleton_cases (l : List Kid) (kid : Kid)
    (idx : Nat) (c : Kid) (h : (l ++ [kid])[idx]? = some c) :
    (l[idx]? = some c) ∨ (idx = l.length ∧ c = kid) :=
  plan4_getElem_append_singleton l kid idx c h

theorem plan6_observe_fill_length (t : Truth) (k q : Nat) :
    (t.observe (Event.fill k q)).kids.length = t.kids.length := by
  cases h : t.kids[k]? <;> simp [Truth.observe, h]

theorem plan6_fill_kids_cases_proof (t : Truth) (k q idx : Nat) (c : Kid)
    (h : ((t.observe (Event.fill k q)).kids)[idx]? = some c) :
    (t.kids[idx]? = some c ∧ idx ≠ k) ∨
      (∃ c0 : Kid, t.kids[k]? = some c0 ∧ idx = k ∧
        c = { c0 with done := c0.done + min q (c0.qty - c0.done) }) :=
  plan5_fill_kids_cases t k q idx c h

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> constructor <;> rfl

theorem req_routes_available : RoutesAvailable step := by
  intro b evs id liq
  exact plan0_route_eq_of_invR b (run step b evs) id liq (plan0_invR_run b evs)

theorem req_never_overroute : NeverOverroute step := by
  intro b evs id
  have hInv := plan0_invR_run b evs
  obtain ⟨h1, hQty, hSent, hBound⟩ := hInv
  have hLE := sentLE_run_aux2 b evs
  by_cases hlt : id < (run step b evs).tr.nOrders
  · have hltS : id < (run step b evs).st.nParents := by omega
    have hsent : ((run step b evs).st.parents id).sent = (run step b evs).tr.sent id := hSent id
    have hqty : ((run step b evs).st.parents id).qty = (run step b evs).tr.qty id := hQty id hltS
    have h := hLE id
    omega
  · have hNle : (run step b evs).st.nParents ≤ id := by omega
    have hzero : (run step b evs).tr.sent id = 0 := by
      simp only [Truth.sent]
      exact sentFor_eq_zero_of_lt _ _ _ hBound hNle
    rw [hzero]
    exact Nat.zero_le _

theorem req_stop_when_filled    : StopWhenFilled step := by
  intro b evs e id hexec c hc
  cases e with
  | parent q flag =>
    have hout : (step b (run step b evs).st (Event.parent q flag)).2 = [] := step_parent_out2 _ _ _ _
    rw [hout] at hc
    simp at hc
  | ack k =>
    have hout : (step b (run step b evs).st (Event.ack k)).2 = [] := step_ack_out2 _ _ _
    rw [hout] at hc
    simp at hc
  | fill k q =>
    have hout : (step b (run step b evs).st (Event.fill k q)).2 = [] := step_fill_out2 _ _ _ _
    rw [hout] at hc
    simp at hc
  | route j liq =>
    have hroute : (step b (run step b evs).st (Event.route j liq)).2 =
        expectedRoute (run step b evs).tr j liq :=
      req_routes_available b evs j liq
    rw [hroute] at hc
    by_cases hcond : (j < (run step b evs).tr.nOrders ∧ 0 < min liq ((run step b evs).tr.qty j - (run step b evs).tr.sent j))
    · have heq : expectedRoute (run step b evs).tr j liq =
          [⟨j, min liq ((run step b evs).tr.qty j - (run step b evs).tr.sent j)⟩] := by
        simp [expectedRoute, hcond]
      rw [heq] at hc
      simp only [List.mem_singleton] at hc
      obtain rfl := hc
      simp only
      intro hcon
      subst hcon
      have hexec_le : (run step b evs).tr.exec j ≤ (run step b evs).tr.sent j :=
        exec_le_sent step b evs j
      have hsent_le : (run step b evs).tr.sent j ≤ (run step b evs).tr.qty j :=
        req_never_overroute b evs j
      have h1 : 0 < min liq ((run step b evs).tr.qty j - (run step b evs).tr.sent j) := hcond.2
      omega
    · have heq : expectedRoute (run step b evs).tr j liq = ([] : List Child) := by
        simp [expectedRoute, hcond]
      rw [heq] at hc
      simp at hc

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  have h1 : (run step b evs).tr.exec id ≤ (run step b evs).tr.sent id :=
    exec_le_sent step b evs id
  have h2 : (run step b evs).tr.sent id ≤ (run step b evs).tr.qty id :=
    req_never_overroute b evs id
  omega

theorem req_fill_accounting : FillAccounting step := fun b evs id _ => (plan2_run_invariant_proofcheck b evs).1 id

end OrderRouter
