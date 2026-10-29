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

theorem inv_test_aux : True := trivial
#check (run_induction step Build.rlp (fun x => x.st.nParents = x.tr.nOrders))

theorem upd_same_test (f : Nat → ParentRec) (k : Nat) (v : ParentRec) : upd f k v k = v := by simp [upd]

theorem upd_diff_test (f : Nat → ParentRec) (k j : Nat) (v : ParentRec) (h : j ≠ k) : upd f k v j = f j := by simp [upd, h]

theorem obs_parent_nOrders (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).nOrders = t.nOrders + 1 := by simp [Truth.observe]
#check Truth.observe
#check Truth.record

theorem sentFor_zero_of_ne (l : List Kid) (id : Nat)
    (h : ∀ k ∈ l, k.parent ≠ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent ≠ id := h a List.mem_cons_self
    simp [ha]
    exact ih (fun k hk => h k (List.mem_cons_of_mem a hk))

theorem sent_eq_helper_test : ∀ (x : Sys), x.st.nParents = x.tr.nOrders → True := fun _ _ => trivial

theorem probe_adv_parent (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    (step b x.st (.parent q f)).1.nParents = x.st.nParents + 1 := by
  simp [step]

theorem nor_qty_parent (t : Truth) (q : Nat) (f : Bool) (id : Nat) :
    (t.observe (.parent q f)).qty id = upd t.qty t.nOrders q id := by
  simp [Truth.observe, upd]

theorem nor_sent_observe_parent (t : Truth) (q : Nat) (f : Bool) (id : Nat) :
    sentFor (t.observe (.parent q f)).kids id = sentFor t.kids id := by
  simp [Truth.observe]

theorem nor_qty_fill (t : Truth) (k q : Nat) (id : Nat) :
    (t.observe (.fill k q)).qty id = t.qty id := by
  cases h : t.kids[k]? <;> simp [Truth.observe, h]

theorem nor_nOrders_fill (t : Truth) (k q : Nat) :
    (t.observe (.fill k q)).nOrders = t.nOrders := by
  cases h : t.kids[k]? <;> simp [Truth.observe, h]

theorem obs_route (t : Truth) (id liq : Nat) : t.observe (.route id liq) = t := by
  simp [Truth.observe]

theorem obs_ack (t : Truth) (k : Nat) : t.observe (.ack k) = t := by
  simp [Truth.observe]

theorem rec_nil (t : Truth) : t.record [] = t := by
  simp [Truth.record]

theorem qty_route (t : Truth) (id liq j : Nat) :
    (t.observe (.route id liq)).qty j = t.qty j := by simp [Truth.observe]

theorem nOrders_route (t : Truth) (id liq : Nat) :
    (t.observe (.route id liq)).nOrders = t.nOrders := by simp [Truth.observe]

theorem step_parent_out (s : State) (b : Build) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).2 = [] := by simp [step]

theorem step_parent_st (s : State) (b : Build) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).1 = { s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } := by simp [step]

theorem step_ack_out (s : State) (b : Build) (k : Nat) :
    (step b s (.ack k)).2 = [] := by simp [step]

theorem step_ack_st (s : State) (b : Build) (k : Nat) :
    (step b s (.ack k)).1 = s := by simp [step]

theorem step_fill_out (s : State) (b : Build) (k q : Nat) :
    (step b s (.fill k q)).2 = [] := by
  simp only [step]
  split <;> rfl

theorem inv_defs_ok_start : True := trivial

-- single-step preservation test: unfold advance for route case

theorem adv_route_tr (b : Build) (x : Sys) (id liq : Nat) :
    (advance step b x (.route id liq)).tr = (x.tr.record (step b x.st (.route id liq)).2) := by
  simp [advance, Truth.observe]

theorem sent_record_eq (t : Truth) (out : List Child) (id : Nat) :
    (t.record out).sent id = t.sent id + sentFor (out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id := by
  simp [Truth.record, Truth.sent, sentFor_append]

theorem sent_observe_fill_eq (t : Truth) (k q : Nat) (id : Nat) :
    (t.observe (.fill k q)).sent id = t.sent id := by
  simp only [Truth.observe]
  split
  · rename_i c hc
    have := sentFor_set_done t.kids k c (c.done + min q (c.qty - c.done)) hc id
    simp [Truth.sent] at this ⊢
    -- the set in observe is {c with done := ...}, need to match
    have h2 : t.kids.set k { c with done := c.done + min q (c.qty - c.done) } = t.kids.set k ({ c with done := c.done + min q (c.qty - c.done) }) := rfl
    rw [h2]; exact this
  · rfl

theorem qty_observe_fill_eq (t : Truth) (k q : Nat) (id : Nat) :
    (t.observe (.fill k q)).qty id = t.qty id := by
  simp only [Truth.observe]
  split
  · rename_i h; simp
  · rfl

theorem inv_nParents_eq3 : ∀ (b : Build) (evs : List Event),
    (run step b evs).st.nParents = (run step b evs).tr.nOrders := by
  intro b evs
  refine run_induction step b (fun x => x.st.nParents = x.tr.nOrders) rfl ?_ evs
  intro x e hx
  cases e with
  | parent q f =>
    show (step b x.st (.parent q f)).1.nParents = ((x.tr.observe (.parent q f)).record (step b x.st (.parent q f)).2).nOrders
    have h1 : (step b x.st (.parent q f)).1.nParents = x.st.nParents + 1 := by simp [step]
    have h2 : (((x.tr.observe (.parent q f)).record (step b x.st (.parent q f)).2).nOrders) = x.tr.nOrders + 1 := by
      have ho : (step b x.st (.parent q f)).2 = [] := by simp [step]
      simp [Truth.observe, Truth.record, ho]
    rw [h1, h2, hx]
  | route id liq =>
    show (step b x.st (.route id liq)).1.nParents = ((x.tr.observe (.route id liq)).record (step b x.st (.route id liq)).2).nOrders
    have h1 : (step b x.st (.route id liq)).1.nParents = x.st.nParents := by simp [step]; split <;> rfl
    have h2 : (((x.tr.observe (.route id liq)).record (step b x.st (.route id liq)).2).nOrders) = x.tr.nOrders := by
      simp [Truth.observe, Truth.record]
    rw [h1, h2, hx]
  | ack k =>
    show (step b x.st (.ack k)).1.nParents = ((x.tr.observe (.ack k)).record (step b x.st (.ack k)).2).nOrders
    have h1 : (step b x.st (.ack k)).1.nParents = x.st.nParents := by simp [step]
    have h2 : (((x.tr.observe (.ack k)).record (step b x.st (.ack k)).2).nOrders) = x.tr.nOrders := by
      simp [Truth.observe, Truth.record]
    rw [h1, h2, hx]
  | fill k q =>
    show (step b x.st (.fill k q)).1.nParents = ((x.tr.observe (.fill k q)).record (step b x.st (.fill k q)).2).nOrders
    have h1 : (step b x.st (.fill k q)).1.nParents = x.st.nParents := by simp [step]; split <;> rfl
    have h2 : (((x.tr.observe (.fill k q)).record (step b x.st (.fill k q)).2).nOrders) = x.tr.nOrders := by
      cases hc : x.tr.kids[k]? <;> simp [Truth.observe, Truth.record, hc]
    rw [h1, h2, hx]

theorem sentFor_ge_zero (l : List Kid) (N id : Nat)
    (h : ∀ k ∈ l, k.parent < N) (hle : N ≤ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent ≠ id := by
      have h1 := h a List.mem_cons_self
      omega
    simp [ha]
    exact ih (fun k hk => h k (List.mem_cons_of_mem a hk))

theorem execFor_ge_zero (l : List Kid) (N id : Nat)
    (h : ∀ k ∈ l, k.parent < N) (hle : N ≤ id) : execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent ≠ id := by
      have h1 := h a List.mem_cons_self
      omega
    simp [ha]
    exact ih (fun k hk => h k (List.mem_cons_of_mem a hk))

theorem kids_mem_record_bound2 (t : Truth) (out : List Child)
    (hb : ∀ k ∈ t.kids, k.parent < (t.record out).nOrders)
    (hout : ∀ c ∈ out, c.parent < (t.record out).nOrders)
    (y : Kid) (hy : y ∈ (t.record out).kids) : y.parent < (t.record out).nOrders := by
  simp only [Truth.record, List.mem_append, List.mem_map] at hy
  rcases hy with h1 | ⟨c, hc, rfl⟩
  · exact hb y h1
  · exact hout c hc

theorem upd_eq_par (f : Nat → ParentRec) (k : Nat) (v : ParentRec) : upd f k v k = v := by simp [upd]

theorem upd_ne_par (f : Nat → ParentRec) (k j : Nat) (v : ParentRec) (h : j ≠ k) : upd f k v j = f j := by simp [upd, h]

theorem step_parent_nChildren (b : Build) (s : State) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).1.nChildren = s.nChildren := by simp [step]

theorem step_parent_nParents (b : Build) (s : State) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).1.nParents = s.nParents + 1 := by simp [step]

theorem step_ack_nChildren (b : Build) (s : State) (k : Nat) :
    (step b s (.ack k)).1.nChildren = s.nChildren := by simp [step]

theorem step_ack_nParents (b : Build) (s : State) (k : Nat) :
    (step b s (.ack k)).1.nParents = s.nParents := by simp [step]

theorem step_nc_plus_outlen (b : Build) (s : State) (e : Event) :
    (step b s e).1.nChildren = s.nChildren + (step b s e).2.length := by
  cases e with
  | parent q f => simp [step]
  | route id liq => simp only [step]; split <;> simp
  | ack k => simp [step]
  | fill k q => simp only [step]; split <;> simp

theorem record_nOrders (t : Truth) (out : List Child) : (t.record out).nOrders = t.nOrders := by simp [Truth.record]

theorem record_qty (t : Truth) (out : List Child) (id : Nat) : (t.record out).qty id = t.qty id := by simp [Truth.record]

theorem record_kids (t : Truth) (out : List Child) : (t.record out).kids = t.kids ++ out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) := by simp [Truth.record]

theorem record_sent (t : Truth) (out : List Child) (id : Nat) :
    (t.record out).sent id = t.sent id + sentFor (out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id := by simp [Truth.record, Truth.sent, sentFor_append]

theorem record_exec (t : Truth) (out : List Child) (id : Nat) :
    (t.record out).exec id = t.exec id := by simp [Truth.record, Truth.exec, execFor_append, execFor_new]

theorem inv_nChildren_len : ∀ (b : Build) (evs : List Event),
    (run step b evs).st.nChildren = (run step b evs).tr.kids.length := by
  intro b evs
  refine run_induction step b (fun x => x.st.nChildren = x.tr.kids.length) rfl ?_ evs
  intro x e hx
  simp only [advance]
  have hstep : (step b x.st e).1.nChildren = x.st.nChildren + (step b x.st e).2.length := step_nc_plus_outlen b x.st e
  have htr : ((x.tr.observe e).record (step b x.st e).2).kids.length = (x.tr.observe e).kids.length + (step b x.st e).2.length := by
    simp [Truth.record]
  have hobs : (x.tr.observe e).kids.length = x.tr.kids.length := by
    cases e with
    | parent q f => simp [Truth.observe]
    | route id liq => simp [Truth.observe]
    | ack k => simp [Truth.observe]
    | fill k q => cases h : x.tr.kids[k]? <;> simp [Truth.observe, h]
  omega

theorem probe_parent_children (s : State) (b : Build) (q : Nat) (f : Bool) (k : Nat) :
    (step b s (.parent q f)).1.children k = s.children k := by simp [step]

theorem probe_route_nParents (s : State) (b : Build) (id liq : Nat) :
    (step b s (.route id liq)).1.nParents = s.nParents := by simp [step]; split <;> rfl

theorem probe_fill_nParents (s : State) (b : Build) (k q : Nat) :
    (step b s (.fill k q)).1.nParents = s.nParents := by simp [step]; split <;> rfl

theorem probe_fill_nChildren (s : State) (b : Build) (k q : Nat) :
    (step b s (.fill k q)).1.nChildren = s.nChildren := by simp [step]; split <;> rfl

theorem probe_observe_fill_kids (t : Truth) (k q : Nat) (h : t.kids[k]? = none) :
    (t.observe (.fill k q)).kids = t.kids := by simp [Truth.observe, h]

theorem obs_parent_kids (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).kids = t.kids := by simp [Truth.observe]

theorem obs_parent_qty (t : Truth) (q : Nat) (f : Bool) (id : Nat) : (t.observe (.parent q f)).qty id = upd t.qty t.nOrders q id := by simp [Truth.observe]

theorem obs_fill_nOrders (t : Truth) (k q : Nat) : (t.observe (.fill k q)).nOrders = t.nOrders := by cases h : t.kids[k]? <;> simp [Truth.observe, h]

theorem obs_fill_qty (t : Truth) (k q : Nat) (id : Nat) : (t.observe (.fill k q)).qty id = t.qty id := by cases h : t.kids[k]? <;> simp [Truth.observe, h]

theorem step_parent_children_eq (s : State) (b : Build) (q : Nat) (f : Bool) (k : Nat) : (step b s (.parent q f)).1.children k = s.children k := by simp [step]

theorem step_parent_parents_eq (s : State) (b : Build) (q : Nat) (f : Bool) (id : Nat) : (step b s (.parent q f)).1.parents id = upd s.parents s.nParents ⟨q, f, 0, 0⟩ id := by simp [step]

theorem step_route_parents (s : State) (b : Build) (id liq : Nat) (j : Nat) :
    (step b s (.route id liq)).1.parents j =
      if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)
      then upd s.parents id { s.parents id with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) } j
      else s.parents j := by simp [step]; split <;> rfl

theorem step_fill_parents (s : State) (b : Build) (k q : Nat) (j : Nat) :
    (step b s (.fill k q)).1.parents j =
      if k < s.nChildren then upd s.parents (s.children k).parent { s.parents (s.children k).parent with cum := (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) } j
      else s.parents j := by simp [step]; split <;> rfl

theorem step_route_out (s : State) (b : Build) (id liq : Nat) :
    (step b s (.route id liq)).2 = if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] else [] := by simp [step]; split <;> rfl

theorem inv_helper_state_parent_qty (s : State) (q : Nat) (f : Bool) (j : Nat) (hj : j < s.nParents) :
    (({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } : State).parents j).qty = (s.parents j).qty := by
  simp [upd_ne_par _ _ _ _ (by omega : j ≠ s.nParents)]

theorem probe_set_mem : ∀ (l : List Kid) (k : Nat) (c : Kid), l[k]? = some c → c ∈ l := by
  intro l k c h
  exact List.mem_of_getElem? h
#check List.mem_of_getElem?
#check List.getElem?_eq_getElem

theorem parents_parent_old (s : State) (q : Nat) (f : Bool) (j : Nat) (h : j ≠ s.nParents) :
    (({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } : State).parents j).qty = (s.parents j).qty := by
  simp only []
  have : upd s.parents s.nParents (⟨q, f, 0, 0⟩ : ParentRec) j = s.parents j := by simp [upd, h]
  simp [this]

theorem parents_parent_old_sent (s : State) (q : Nat) (f : Bool) (j : Nat) (h : j ≠ s.nParents) :
    (({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } : State).parents j).sent = (s.parents j).sent := by
  have : upd s.parents s.nParents (⟨q, f, 0, 0⟩ : ParentRec) j = s.parents j := by simp [upd, h]
  simp [this]

theorem parents_parent_new_qty (s : State) (q : Nat) (f : Bool) :
    (({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } : State).parents s.nParents).qty = q := by
  have : upd s.parents s.nParents (⟨q, f, 0, 0⟩ : ParentRec) s.nParents = (⟨q, f, 0, 0⟩ : ParentRec) := by simp [upd]
  simp [this]

theorem parents_parent_new_sent (s : State) (q : Nat) (f : Bool) :
    (({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } : State).parents s.nParents).sent = 0 := by
  have : upd s.parents s.nParents (⟨q, f, 0, 0⟩ : ParentRec) s.nParents = (⟨q, f, 0, 0⟩ : ParentRec) := by simp [upd]
  simp [this]

theorem state_parent_sent_eq (s : State) (q : Nat) (f : Bool) (j : Nat) (h : j ≠ s.nParents) :
    (({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } : State).parents j).sent = (s.parents j).sent := parents_parent_old_sent s q f j h

theorem truth_parent_sent_eq (t : Truth) (q : Nat) (f : Bool) (out : List Child) (h : out = []) (id : Nat) :
    ((t.observe (.parent q f)).record out).sent id = t.sent id := by
  subst h; simp [Truth.observe, Truth.record, Truth.sent]

theorem truth_parent_qty_eq (t : Truth) (q : Nat) (f : Bool) (out : List Child) (h : out = []) (id : Nat) :
    ((t.observe (.parent q f)).record out).qty id = upd t.qty t.nOrders q id := by
  subst h; simp [Truth.observe, Truth.record]

theorem truth_parent_nOrders_eq (t : Truth) (q : Nat) (f : Bool) (out : List Child) (h : out = []) :
    ((t.observe (.parent q f)).record out).nOrders = t.nOrders + 1 := by
  subst h; simp [Truth.observe, Truth.record]

theorem upd_qry (f : Nat → ParentRec) (k : Nat) (v : ParentRec) (j : Nat) :
    (upd f k v j).qty = (if j = k then v.qty else (f j).qty) := by simp [upd]; split <;> rfl

theorem upd_stt (f : Nat → ParentRec) (k : Nat) (v : ParentRec) (j : Nat) :
    (upd f k v j).sent = (if j = k then v.sent else (f j).sent) := by simp [upd]; split <;> rfl

theorem upd_cm (f : Nat → ParentRec) (k : Nat) (v : ParentRec) (j : Nat) :
    (upd f k v j).cum = (if j = k then v.cum else (f j).cum) := by simp [upd]; split <;> rfl

theorem upd_ch_parent (f : Nat → ChildRec) (k : Nat) (v : ChildRec) (j : Nat) :
    (upd f k v j).parent = (if j = k then v.parent else (f j).parent) := by simp [upd]; split <;> rfl

theorem upd_ch_qty (f : Nat → ChildRec) (k : Nat) (v : ChildRec) (j : Nat) :
    (upd f k v j).qty = (if j = k then v.qty else (f j).qty) := by simp [upd]; split <;> rfl

theorem upd_ch_done (f : Nat → ChildRec) (k : Nat) (v : ChildRec) (j : Nat) :
    (upd f k v j).done = (if j = k then v.done else (f j).done) := by simp [upd]; split <;> rfl

theorem sentFor_map_single2 (pid c j : Nat) :
    sentFor (List.map (fun cc => (⟨cc.parent, cc.qty, 0⟩ : Kid)) ([⟨pid, c⟩] : List Child)) j = (if pid = j then c else 0) := by
  simp

theorem t_route_qty2 (s : State) (b : Build) (id liq j : Nat) :
    ((step b s (.route id liq)).1.parents j).qty = (s.parents j).qty := by
  have h := step_route_parents s b id liq j
  rw [h]
  split
  · rename_i hh
    rw [upd_qry]
    split
    · rename_i heq; subst heq; rfl
    · rfl
  · rfl

theorem t_fill_parents_qty (s : State) (b : Build) (k q j : Nat) :
    ((step b s (.fill k q)).1.parents j).qty = (s.parents j).qty := by
  simp only [step]
  split
  · rename_i hh
    by_cases hj : j = (s.children k).parent
    · subst hj; simp [upd]
    · simp [upd, hj]
  · rfl

theorem t_fill_parents_sent (s : State) (b : Build) (k q j : Nat) :
    ((step b s (.fill k q)).1.parents j).sent = (s.parents j).sent := by
  simp only [step]
  split
  · rename_i hh
    by_cases hj : j = (s.children k).parent
    · subst hj; simp [upd]
    · simp [upd, hj]
  · rfl

theorem t_ack_parents (s : State) (b : Build) (k j : Nat) :
    ((step b s (.ack k)).1.parents j) = (s.parents j) := by
  simp [step]

def InvNever : Sys → Prop := fun x =>
  x.st.nParents = x.tr.nOrders
  ∧ (∀ id, id < x.st.nParents → (x.st.parents id).qty = x.tr.qty id)
  ∧ (∀ id, id < x.st.nParents → (x.st.parents id).sent = x.tr.sent id)
  ∧ (∀ id, id < x.st.nParents → (x.st.parents id).sent ≤ (x.st.parents id).qty)
  ∧ (∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)
  ∧ (∀ id, x.tr.nOrders ≤ id → x.tr.qty id = 0)

theorem invNever_start : InvNever start := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro id h; simp [start, init] at h
  · intro id h; simp [start, init] at h
  · intro id h; simp [start, init] at h
  · intro k h; simp [start, Truth.empty] at h
  · intro id h; simp [start, Truth.empty]

def InvStop : Sys → Prop := fun x =>
  x.st.nParents = x.tr.nOrders
  ∧ (∀ id, id < x.st.nParents → (x.st.parents id).qty = x.tr.qty id)
  ∧ (∀ id, id < x.st.nParents → (x.st.parents id).sent = x.tr.sent id)
  ∧ (∀ id, x.tr.sent id ≤ x.tr.qty id)
  ∧ (∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)
  ∧ (∀ id, x.tr.nOrders ≤ id → x.tr.qty id = 0)

theorem invStop_start : InvStop start := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro id h; simp [start, init] at h
  · intro id h; simp [start, init] at h
  · intro id
    simp [start, Truth.empty, Truth.sent]
  · intro k h; simp [start, Truth.empty] at h
  · intro id h; simp [start, Truth.empty]

theorem invStop_nParents_all : ∀ (b : Build) (evs : List Event), (run step b evs).st.nParents = (run step b evs).tr.nOrders :=
  inv_nParents_eq3

def InvFill : Sys → Prop := fun x =>
  x.st.nParents = x.tr.nOrders
  ∧ x.st.nChildren = x.tr.kids.length
  ∧ (∀ id, id < x.st.nParents → (x.st.parents id).qty = x.tr.qty id)
  ∧ (∀ id, id < x.st.nParents → (x.st.parents id).sent = x.tr.sent id)
  ∧ (∀ id, id < x.st.nParents → (x.st.parents id).cum = x.tr.exec id)
  ∧ (∀ k, k < x.st.nChildren → x.tr.kids[k]? = some ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done⟩)
  ∧ (∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)

theorem invFill_start : InvFill start := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro id h; simp [start, init] at h
  · intro id h; simp [start, init] at h
  · intro id h; simp [start, init] at h
  · intro k h; simp [start, init] at h
  · intro k h; simp [start, Truth.empty] at h

theorem exec_observe_fill_eq2 (t : Truth) (k q id : Nat) :
    (t.observe (.fill k q)).exec id = t.exec id +
      (match t.kids[k]? with | some c => if c.parent = id then min q (c.qty - c.done) else 0 | none => 0) := by
  cases h : t.kids[k]? with
  | none => simp [Truth.observe, h, Truth.exec]
  | some c =>
    have hh := execFor_set_done t.kids k c (min q (c.qty - c.done)) h id
    simp only [Truth.observe, h, Truth.exec] at *
    have hset : t.kids.set k ({ c with done := c.done + min q (c.qty - c.done) } : Kid) = t.kids.set k { c with done := c.done + min q (c.qty - c.done) } := rfl
    rw [hset]; exact hh

theorem t_route_cum2 (s : State) (b : Build) (id liq j : Nat) :
    ((step b s (.route id liq)).1.parents j).cum = (s.parents j).cum := by
  simp only [step]
  split
  · rename_i hh
    simp only [upd_cm]
    split
    · rename_i heq; subst heq; rfl
    · rfl
  · rfl

theorem t_fill_cum2 (s : State) (b : Build) (k q j : Nat) :
    ((step b s (.fill k q)).1.parents j).cum =
      (if j = (s.children k).parent ∧ k < s.nChildren
      then (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done)
      else (s.parents j).cum) := by
  simp only [step]
  split
  · rename_i hh
    by_cases hj : j = (s.children k).parent
    · subst hj; simp [upd, hh]
    · simp [upd, hj]
  · rename_i hh
    by_cases hj : j = (s.children k).parent
    · subst hj; simp [hh]
    · simp [hj]

theorem step_fill_children2 (s : State) (b : Build) (k q j : Nat) :
    (step b s (.fill k q)).1.children j =
      (if j = k ∧ k < s.nChildren
      then { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) }
      else s.children j) := by
  simp only [step]
  split
  · rename_i hh
    by_cases hj : j = k
    · subst hj; simp [upd, hh]
    · simp [upd, hj]
  · rename_i hh
    by_cases hj : j = k
    · subst hj; simp [hh]
    · simp [hj]

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> decide

theorem req_routes_available : RoutesAvailable step := sorry

theorem req_never_overroute : NeverOverroute step := sorry

theorem req_stop_when_filled : StopWhenFilled step := sorry

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  exact Nat.le_trans (exec_le_sent step b evs id) (req_never_overroute b evs id)

theorem req_fill_accounting : FillAccounting step := sorry

end OrderRouter
