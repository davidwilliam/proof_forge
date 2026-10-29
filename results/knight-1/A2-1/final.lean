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

theorem foo_test : True := trivial

theorem sent_zero_of_all_lt (l : List Kid) (n : Nat) (h : ∀ k ∈ l, k.parent < n) (id : Nat) (hid : n ≤ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent < n := h a (by simp)
    have hne : a.parent ≠ id := by omega
    simp [hne]
    exact ih (fun k hk => h k (by simp [hk]))

theorem check_obs_parent (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).nOrders = t.nOrders + 1 := rfl

theorem check_obs_parent_qty (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).qty = upd t.qty t.nOrders q := rfl

theorem check_obs_parent_kids (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).kids = t.kids := rfl

theorem check_rec_kids (t : Truth) (out : List Child) : (t.record out).kids = t.kids ++ out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) := rfl

theorem upd_eq_test (f : Nat → ParentRec) (k : Nat) (v : ParentRec) : upd f k v k = v := by simp [upd]

theorem state_upd_parents_test (s : State) (f : Nat → ParentRec) : ({ s with parents := f } : State).parents = f := rfl

theorem state_upd_nParents_test (s : State) (n : Nat) : ({ s with nParents := n } : State).nParents = n := rfl

theorem check_sent_def (t : Truth) (id : Nat) : t.sent id = sentFor t.kids id := rfl

theorem check_adv_st (st : Impl) (b : Build) (x : Sys) (e : Event) : (advance st b x e).st = (st b x.st e).1 := rfl

theorem check_adv_tr (st : Impl) (b : Build) (x : Sys) (e : Event) : (advance st b x e).tr = (x.tr.observe e).record (st b x.st e).2 := rfl

theorem upd_eq2 (f : Nat → ParentRec) (k : Nat) (v : ParentRec) (j : Nat) (h : j = k) : upd f k v j = v := by simp [upd, h]

theorem upd_neq2 (f : Nat → ParentRec) (k j : Nat) (v : ParentRec) (h : j ≠ k) : upd f k v j = f j := by simp [upd, h]

theorem sentFor_record_nil (l : List Kid) (id : Nat) : sentFor (l ++ ([] : List Child).map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id = sentFor l id := by simp

theorem sentFor_observe_parent (t : Truth) (q : Nat) (f : Bool) (id : Nat) : sentFor (t.observe (.parent q f)).kids id = sentFor t.kids id := by rfl

theorem upd_eq_gen {α : Type} (f : Nat → α) (k : Nat) (v : α) : upd f k v k = v := by simp [upd]

theorem upd_ne_gen {α : Type} (f : Nat → α) (k j : Nat) (v : α) (h : j ≠ k) : upd f k v j = f j := by simp [upd, h]

theorem aux_sent_zero_test (l : List Kid) (n : Nat) (h : ∀ k ∈ l, k.parent < n) (id : Nat) (hid : n ≤ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent < n := h a (by simp)
    have hne : a.parent ≠ id := by omega
    simp [hne]
    exact ih (fun k hk => h k (by simp [hk]))

theorem t1 (t : Truth) (id liq : Nat) : t.observe (.route id liq) = t := by rfl

theorem t2 (t : Truth) (k : Nat) : t.observe (.ack k) = t := by rfl

theorem t3 (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).kids = t.kids := by rfl

theorem zz1 (t : Truth) (id liq : Nat) : (t.observe (.route id liq)).nOrders = t.nOrders := by simp [Truth.observe]

theorem zz2 (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).nOrders = t.nOrders + 1 := by simp [Truth.observe]

theorem zz3 (t : Truth) (k q : Nat) : (t.observe (.fill k q)).nOrders = t.nOrders := by
  simp only [Truth.observe]
  split <;> simp

theorem rr1 (t : Truth) (out : List Child) : (t.record out).nOrders = t.nOrders := by simp [Truth.record]

theorem rr2 (t : Truth) (out : List Child) : (t.record out).qty = t.qty := by simp [Truth.record]

theorem rr3 (t : Truth) (out : List Child) : (t.record out).kids = t.kids ++ out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) := by simp [Truth.record]

theorem zz4 (t : Truth) (k : Nat) : (t.observe (.ack k)).nOrders = t.nOrders := by simp [Truth.observe]

theorem inv_nParents_eq4 (b : Build) (evs : List Event) : (run step b evs).st.nParents = (run step b evs).tr.nOrders := by
  refine run_induction step b (fun x => x.st.nParents = x.tr.nOrders) rfl ?_ evs
  intro x e ih
  unfold advance
  cases e with
  | parent q f =>
    show ((step b x.st (.parent q f)).1).nParents = _
    simp only [step, rr1, zz2]
    simp [ih]
  | route id liq =>
    show ((step b x.st (.route id liq)).1).nParents = _
    simp only [step]
    split
    · simp [ih, zz1, rr1]
    · simp [ih, zz1, rr1]
  | ack c =>
    show ((step b x.st (.ack c)).1).nParents = _
    simp only [step]
    simp [ih, rr1, zz4]
  | fill k q =>
    show ((step b x.st (.fill k q)).1).nParents = _
    simp only [step]
    split
    · simp [ih, zz3, rr1]
    · simp [ih, zz3, rr1]

theorem qq1 (t : Truth) (id liq : Nat) : (t.observe (.route id liq)).qty = t.qty := by simp [Truth.observe]

theorem qq2 (t : Truth) (k : Nat) : (t.observe (.ack k)).qty = t.qty := by simp [Truth.observe]

theorem qq3 (t : Truth) (k q : Nat) : (t.observe (.fill k q)).qty = t.qty := by
  simp only [Truth.observe]
  split <;> simp

theorem qq4 (t : Truth) (q : Nat) (f : Bool) (id : Nat) : id < t.nOrders → (t.observe (.parent q f)).qty id = t.qty id := by
  intro h
  simp only [Truth.observe]
  simp [upd, Nat.ne_of_lt h]

theorem qq5 (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).qty t.nOrders = q := by
  simp only [Truth.observe]
  simp [upd]

theorem kk1 (t : Truth) (id liq : Nat) : (t.observe (.route id liq)).kids = t.kids := by rfl

theorem kk2 (t : Truth) (k : Nat) : (t.observe (.ack k)).kids = t.kids := by rfl

theorem sentZero_of_bound (l : List Kid) (n : Nat) (h : ∀ k ∈ l, k.parent < n) (id : Nat) (hid : n ≤ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent < n := h a (by simp)
    have hne : a.parent ≠ id := by omega
    simp [hne]
    exact ih (fun k hk => h k (by simp [hk]))

theorem tmp_qty_parent (x : Sys) (b : Build) (q : Nat) (f : Bool) (j : Nat) :
    ((((x.tr.observe (.parent q f)).record ((step b x.st (.parent q f)).2)).qty) j) = ((x.tr.observe (.parent q f)).qty j) := by
  simp [Truth.record]

theorem tmp_adv_unfold (x : Sys) (b : Build) (e : Event) :
    advance step b x e = ⟨(step b x.st e).1, (x.tr.observe e).record (step b x.st e).2⟩ := rfl

theorem tmp_parent_out (s : State) (b : Build) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).2 = ([] : List Child) := by simp [step]

theorem tmp_parent_st (s : State) (b : Build) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).1 = ({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } : State) := by simp [step]

theorem execZero_of_bound (l : List Kid) (n : Nat) (h : ∀ k ∈ l, k.parent < n) (id : Nat) (hid : n ≤ id) : execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent < n := h a (by simp)
    have hne : a.parent ≠ id := by omega
    simp [hne]
    exact ih (fun k hk => h k (by simp [hk]))

theorem tmp_route_stuff (x : Sys) (b : Build) (id liq : Nat) (j : Nat) :
    ((step b x.st (.route id liq)).1.parents j).qty =
    (if id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent) then (if j = id then (x.st.parents id).qty else (x.st.parents j).qty) else (x.st.parents j).qty) := by
  simp only [step]
  split
  · simp [upd]
    by_cases heq : j = id <;> simp [heq]
  · rfl

theorem sent_record_singleton (t : Truth) (pid qq : Nat) (id : Nat) :
    sentFor ((t.record [⟨pid, qq⟩]).kids) id = sentFor t.kids id + (if pid = id then qq else 0) := by
  simp [Truth.record, sentFor_append]

theorem step_parent_eq (b : Build) (s : State) (q : Nat) (f : Bool) : step b s (.parent q f) = (({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } : State), []) := by simp [step]

theorem step_ack_eq (b : Build) (s : State) (k : Nat) : step b s (.ack k) = (s, []) := by simp [step]

theorem step_fill_noop (b : Build) (s : State) (k q : Nat) (h : ¬ k < s.nChildren) : step b s (.fill k q) = (s, []) := by simp [step, h]

theorem step_fill_some (b : Build) (s : State) (k q : Nat) (h : k < s.nChildren) : step b s (.fill k q) = (({ s with parents := upd s.parents (s.children k).parent { (s.parents (s.children k).parent) with cum := (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) }, children := upd s.children k { (s.children k) with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) } } : State), []) := by simp [step, h]

theorem obs_route_eq (t : Truth) (id liq : Nat) : t.observe (.route id liq) = t := rfl

theorem obs_ack_eq (t : Truth) (k : Nat) : t.observe (.ack k) = t := rfl

theorem rec_nOrders (t : Truth) (out : List Child) : (t.record out).nOrders = t.nOrders := rfl

theorem rec_qty (t : Truth) (out : List Child) (j : Nat) : (t.record out).qty j = t.qty j := rfl

theorem obs_route_nOrders (t : Truth) (id liq : Nat) : (t.observe (.route id liq)).nOrders = t.nOrders := rfl

theorem obs_ack_nOrders (t : Truth) (k : Nat) : (t.observe (.ack k)).nOrders = t.nOrders := rfl

theorem obs_fill_kids_len (t : Truth) (k q : Nat) : (t.observe (.fill k q)).kids.length = t.kids.length := by
  simp only [Truth.observe]
  split
  · rename_i h
    simp only [List.length_set]
  · rfl

theorem rec_nil_kids_len (t : Truth) : (t.record []).kids.length = t.kids.length := by simp [Truth.record]

theorem rec_single_kids_len (t : Truth) (c : Child) : (t.record [c]).kids.length = t.kids.length + 1 := by simp [Truth.record]

theorem obs_parent_kids_len (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).kids.length = t.kids.length := rfl

theorem sent_after_parent2 (t : Truth) (q : Nat) (f : Bool) (id : Nat) :
    sentFor (t.observe (.parent q f)).kids id = sentFor t.kids id := by
  simp [Truth.observe]

theorem sent_after_record_nil (t : Truth) (id : Nat) :
    sentFor ((t.record ([] : List Child)).kids) id = sentFor t.kids id := by
  simp [Truth.record]

theorem sent_after_parent_record (t : Truth) (q : Nat) (f : Bool) (id : Nat) :
    (((t.observe (.parent q f)).record ([] : List Child)).sent id) = t.sent id := by
  simp [Truth.sent, Truth.record, Truth.observe]

theorem upd_ParentRec_sent (f : Nat → ParentRec) (k : Nat) (v : ParentRec) (j : Nat) :
    (upd f k v j).sent = (if j = k then v.sent else (f j).sent) := by
  simp [upd]
  by_cases h : j = k <;> simp [h]

theorem upd_ParentRec_qty (f : Nat → ParentRec) (k : Nat) (v : ParentRec) (j : Nat) :
    (upd f k v j).qty = (if j = k then v.qty else (f j).qty) := by
  simp [upd]
  by_cases h : j = k <;> simp [h]

theorem obs_parent_sent (t : Truth) (q : Nat) (f : Bool) (id : Nat) :
    ((t.observe (.parent q f)).sent id) = t.sent id := by rfl

theorem rec_sent_eq (t : Truth) (out : List Child) (id : Nat) :
    ((t.record out).sent id) = sentFor t.kids id + sentFor (out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id := by
  simp [Truth.sent, Truth.record, sentFor_append]

theorem obs_route_sent (t : Truth) (id liq idd : Nat) :
    ((t.observe (.route id liq)).sent idd) = t.sent idd := by rfl

theorem obs_ack_sent (t : Truth) (k id : Nat) :
    ((t.observe (.ack k)).sent id) = t.sent id := by rfl

theorem step_route_out2 (b : Build) (s : State) (id liq : Nat) :
    (step b s (.route id liq)).2 =
    (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] else []) := by
  unfold step
  simp only
  split
  · rfl
  · rfl





theorem plan0_run_invariants (b : Build) (evs : List Event) :
    (run step b evs).st.nParents = (run step b evs).tr.nOrders ∧
      (∀ id, id < (run step b evs).tr.nOrders →
        ((run step b evs).st.parents id).qty =
          (run step b evs).tr.qty id ∧
        ((run step b evs).st.parents id).sent =
          (run step b evs).tr.sent id) ∧
      ∀ k ∈ (run step b evs).tr.kids,
        k.parent < (run step b evs).tr.nOrders := by sorry



theorem plan0_step_route_out (b : Build) (s : State) (id liq : Nat) :
    (step b s (.route id liq)).2 =
      if id < s.nParents ∧
          0 < min liq ((s.parents id).qty - (s.parents id).sent) then
        [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩]
      else [] := by
  simp only [step]
  split <;> rfl

theorem plan0_advance_preserves_aux : True := trivial

-- helper: sentFor of record [] is unchanged

theorem sentRecNil_aux (t : Truth) (id : Nat) : (t.record ([] : List Child)).sent id = t.sent id := by
  simp [Truth.sent, Truth.record]

-- helper: observe parent/route/ack preserve sent

theorem sentObsParent_aux (t : Truth) (q : Nat) (f : Bool) (id : Nat) : (t.observe (.parent q f)).sent id = t.sent id := by rfl

theorem sentObsRoute_aux (t : Truth) (id liq idd : Nat) : (t.observe (.route id liq)).sent idd = t.sent idd := by rfl

theorem sentObsAck_aux (t : Truth) (k id : Nat) : (t.observe (.ack k)).sent id = t.sent id := by rfl

theorem sentObsFill_aux2 (t : Truth) (k q : Nat) (id : Nat) :
    (t.observe (.fill k q)).sent id = t.sent id := by
  simp only [Truth.sent]
  cases h : t.kids[k]? with
  | none =>
    have : t.observe (.fill k q) = t := by simp [Truth.observe, h]
    rw [this]
  | some c =>
    have : (t.observe (.fill k q)).kids = t.kids.set k { c with done := c.done + min q (c.qty - c.done) } := by simp [Truth.observe, h]
    rw [this]
    exact sentFor_set_done t.kids k c _ h id

theorem qtyObsFill_aux2 (t : Truth) (k q : Nat) (j : Nat) :
    (t.observe (.fill k q)).qty j = t.qty j := by
  cases h : t.kids[k]? with
  | none =>
    have hh : t.observe (.fill k q) = t := by simp [Truth.observe, h]
    rw [hh]
  | some c =>
    have hh : t.observe (.fill k q) = { t with kids := t.kids.set k { c with done := c.done + min q (c.qty - c.done) } } := by simp [Truth.observe, h]
    rw [hh]

theorem sentRecSingle_aux2 (t : Truth) (pid qq : Nat) (id : Nat) :
    ((t.record [⟨pid, qq⟩]).sent id) = t.sent id + (if pid = id then qq else 0) := by
  simp [Truth.sent, Truth.record, sentFor_append]

theorem qtyRec_aux2 (t : Truth) (out : List Child) (j : Nat) :
    (t.record out).qty j = t.qty j := by simp [Truth.record]

theorem nOrdersRec_aux2 (t : Truth) (out : List Child) :
    (t.record out).nOrders = t.nOrders := by simp [Truth.record]

theorem nOrdersObsFill_aux2 (t : Truth) (k q : Nat) :
    (t.observe (.fill k q)).nOrders = t.nOrders := by
  cases h : t.kids[k]? <;> simp [Truth.observe, h]

theorem parentsUpdQty_aux (f : Nat → ParentRec) (k : Nat) (v : ParentRec) (j : Nat) :
    (upd f k v j).qty = (if j = k then v.qty else (f j).qty) := by
  simp [upd]; split <;> rfl

theorem parentsUpdSent_aux (f : Nat → ParentRec) (k : Nat) (v : ParentRec) (j : Nat) :
    (upd f k v j).sent = (if j = k then v.sent else (f j).sent) := by
  simp [upd]; split <;> rfl

theorem setParent_mem_aux (l : List Kid) (k : Nat) (c : Kid) (d : Nat) (y : Kid)
    (hy : y ∈ l.set k { c with done := d }) : y ∈ l ∨ y = { c with done := d } := by
  exact List.mem_or_eq_of_mem_set hy





theorem plan1_advance_parent_preserves (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.parent q f)).st.nParents =
        (advance step b x (.parent q f)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.parent q f)).tr.nOrders →
        ((advance step b x (.parent q f)).st.parents id).qty =
          (advance step b x (.parent q f)).tr.qty id ∧
        ((advance step b x (.parent q f)).st.parents id).sent =
          (advance step b x (.parent q f)).tr.sent id) ∧
      ∀ k ∈ (advance step b x (.parent q f)).tr.kids,
        k.parent < (advance step b x (.parent q f)).tr.nOrders := by sorry

theorem plan1_advance_route_preserves (b : Build) (x : Sys) (id liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.route id liq)).st.nParents =
        (advance step b x (.route id liq)).tr.nOrders ∧
      (∀ j, j < (advance step b x (.route id liq)).tr.nOrders →
        ((advance step b x (.route id liq)).st.parents j).qty =
          (advance step b x (.route id liq)).tr.qty j ∧
        ((advance step b x (.route id liq)).st.parents j).sent =
          (advance step b x (.route id liq)).tr.sent j) ∧
      ∀ k ∈ (advance step b x (.route id liq)).tr.kids,
        k.parent < (advance step b x (.route id liq)).tr.nOrders := by sorry



theorem plan1_advance_fill_preserves (b : Build) (x : Sys) (k q : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents id).qty =
          (advance step b x (.fill k q)).tr.qty id ∧
        ((advance step b x (.fill k q)).st.parents id).sent =
          (advance step b x (.fill k q)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.fill k q)).tr.kids,
        j.parent < (advance step b x (.fill k q)).tr.nOrders := by sorry

theorem plan1_sentFor_zero_of_all_parent_lt (l : List Kid) (n id : Nat)
    (h : ∀ k ∈ l, k.parent < n) (hid : n ≤ id) :
    sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent < n := h a (by simp)
    have hne : a.parent ≠ id := by omega
    simp [hne, ih (fun k hk => h k (by simp [hk]))]

theorem plan1_kids_bound_record (t : Truth) (out : List Child)
    (h1 : ∀ k ∈ t.kids, k.parent < t.nOrders)
    (h2 : ∀ c ∈ out, c.parent < t.nOrders) :
    ∀ k ∈ (t.record out).kids, k.parent < (t.record out).nOrders := by
  intro k hk
  have hn : (t.record out).nOrders = t.nOrders := by simp [Truth.record]
  rw [hn]
  have hk2 : k ∈ t.kids ++ out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) := by
    have : (t.record out).kids = t.kids ++ out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) := by simp [Truth.record]
    rw [← this]; exact hk
  rcases List.mem_append.mp hk2 with h | h
  · exact h1 k h
  · rcases List.mem_map.mp h with ⟨c, hc, rfl⟩
    simp
    exact h2 c hc

theorem plan1_advance_parent_preserves_proof5 : True := trivial
theorem plan1_parent_full_tmp2 : True := trivial


theorem plan1_parent_full_tmp (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.parent q f)).st.nParents =
        (advance step b x (.parent q f)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.parent q f)).tr.nOrders →
        ((advance step b x (.parent q f)).st.parents id).qty =
          (advance step b x (.parent q f)).tr.qty id ∧
        ((advance step b x (.parent q f)).st.parents id).sent =
          (advance step b x (.parent q f)).tr.sent id) ∧
      ∀ k ∈ (advance step b x (.parent q f)).tr.kids,
        k.parent < (advance step b x (.parent q f)).tr.nOrders := by
  obtain ⟨hn, hqs, hkb⟩ := h
  have hst1 : (step b x.st (.parent q f)).1 = ({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State) := by simp [step]
  have hout2 : (step b x.st (.parent q f)).2 = ([] : List Child) := by simp [step]
  have hN : (advance step b x (.parent q f)).st.nParents = (advance step b x (.parent q f)).tr.nOrders := by
    simp only [advance, hst1, hout2]
    simp only [Truth.record, Truth.observe]
    rw [hn]
  refine ⟨hN, ?_, ?_⟩
  · intro id hid
    have hid2 : id = x.tr.nOrders ∨ id < x.tr.nOrders := by
      have hid' : id < ((x.tr.observe (.parent q f)).record ([] : List Child)).nOrders := by
        have heq : (advance step b x (.parent q f)).tr = (x.tr.observe (.parent q f)).record ([] : List Child) := by
          simp [advance, hout2]
        rw [← heq]; exact hid
      simp [Truth.record, Truth.observe] at hid'
      omega
    have hst_eq : (advance step b x (.parent q f)).st.parents id = (upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id := by
      simp [advance, hst1]
    have htr_qty : (advance step b x (.parent q f)).tr.qty id = (upd x.tr.qty x.tr.nOrders q) id := by
      have heq : (advance step b x (.parent q f)).tr = (x.tr.observe (.parent q f)).record ([] : List Child) := by
        simp [advance, hout2]
      rw [heq]
      simp [Truth.record, Truth.observe]
    have htr_sent : (advance step b x (.parent q f)).tr.sent id = ((x.tr.observe (.parent q f)).record ([] : List Child)).sent id := by
      have heq : (advance step b x (.parent q f)).tr = (x.tr.observe (.parent q f)).record ([] : List Child) := by
        simp [advance, hout2]
      rw [heq]
    rcases hid2 with rfl | hlt
    · have hst_at : (upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) x.tr.nOrders = ⟨q, f, 0, 0⟩ := by
        rw [← hn]; simp [upd]
      have hqty : (upd x.tr.qty x.tr.nOrders q) x.tr.nOrders = q := by simp [upd]
      have hz : sentFor x.tr.kids x.tr.nOrders = 0 :=
        sent_zero_of_all_lt x.tr.kids x.tr.nOrders hkb x.tr.nOrders (Nat.le_refl _)
      have hsent_new : (((x.tr.observe (.parent q f)).record ([] : List Child)).sent x.tr.nOrders) = 0 := by
        simp [Truth.sent, Truth.record, Truth.observe, hz]
      rw [hst_eq, htr_qty, htr_sent, hst_at, hqty, hsent_new]
      constructor <;> rfl
    · have hne : id ≠ x.st.nParents := by omega
      have hne2 : id ≠ x.tr.nOrders := by omega
      have hold := hqs id hlt
      have h1 : (upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ id).qty = (x.st.parents id).qty := by simp [upd, hne]
      have h1' : (upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ id).sent = (x.st.parents id).sent := by simp [upd, hne]
      have h2 : (upd x.tr.qty x.tr.nOrders q) id = x.tr.qty id := by simp [upd, hne2]
      have h3 : (((x.tr.observe (.parent q f)).record ([] : List Child)).sent id) = x.tr.sent id := by
        simp [Truth.sent, Truth.record, Truth.observe]
      rw [hst_eq, htr_qty, htr_sent, h1, h1', h2, h3]
      exact hold
  · intro k hk
    have heq : (advance step b x (.parent q f)).tr = (x.tr.observe (.parent q f)).record ([] : List Child) := by
      simp [advance, hout2]
    have hk' : k ∈ ((x.tr.observe (.parent q f)).record ([] : List Child)).kids := by
      rw [← heq]
      exact hk
    have hk2 : k ∈ x.tr.kids := by simpa [Truth.record, Truth.observe] using hk'
    have hlt := hkb k hk2
    rw [heq]
    simp [Truth.record, Truth.observe]
    omega

theorem tmp_check_route_true (b : Build) (x : Sys) (id liq : Nat)
    (hcond : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (step b x.st (.route id liq)).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] := by
  have h := step_route_out2 b x.st id liq
  simp [hcond] at h
  exact h

theorem tmp_check_route_false (b : Build) (x : Sys) (id liq : Nat)
    (hcond : ¬ id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (step b x.st (.route id liq)).2 = ([] : List Child) := by
  have h := step_route_out2 b x.st id liq
  simp [hcond] at h
  exact h

theorem tmp_route_nPar (b : Build) (s : State) (id liq : Nat) :
    (step b s (.route id liq)).1.nParents = s.nParents := by
  unfold step
  simp only
  split <;> rfl

theorem tmp_route_qty (b : Build) (s : State) (id liq j : Nat) :
    ((step b s (.route id liq)).1.parents j).qty =
    (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
      (if j = id then (s.parents id).qty else (s.parents j).qty)
     else (s.parents j).qty) := by
  unfold step
  simp only
  split
  · simp [upd]
    by_cases heq : j = id <;> simp [heq]
  · rfl

theorem tmp_route_sent (b : Build) (s : State) (id liq j : Nat) :
    ((step b s (.route id liq)).1.parents j).sent =
    (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
      (if j = id then (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) else (s.parents j).sent)
     else (s.parents j).sent) := by
  unfold step
  simp only
  split
  · simp [upd]
    by_cases heq : j = id <;> simp [heq]
  · rfl

theorem plan1_advance_ack_preserves (b : Build) (x : Sys) (k : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.ack k)).st.nParents =
        (advance step b x (.ack k)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.ack k)).tr.nOrders →
        ((advance step b x (.ack k)).st.parents id).qty =
          (advance step b x (.ack k)).tr.qty id ∧
        ((advance step b x (.ack k)).st.parents id).sent =
          (advance step b x (.ack k)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.ack k)).tr.kids,
        j.parent < (advance step b x (.ack k)).tr.nOrders := by
  obtain ⟨hn, hqs, hkb⟩ := h
  have hstep : step b x.st (.ack k) = (x.st, []) := step_ack_eq b x.st k
  have hobs : x.tr.observe (.ack k) = x.tr := obs_ack_eq x.tr k
  have hadv_st : (advance step b x (.ack k)).st = x.st := by
    simp [advance, hstep]
  have hadv_tr : (advance step b x (.ack k)).tr = x.tr := by
    simp [advance, hstep, hobs, Truth.record]
  rw [hadv_st, hadv_tr]
  exact ⟨hn, hqs, hkb⟩

theorem fill_qty_aux (s : State) (kk : Nat) (x1 idd : Nat) :
    ((upd s.parents (s.children kk).parent { (s.parents (s.children kk).parent) with cum := (s.parents (s.children kk).parent).cum + x1 }) idd).qty = (s.parents idd).qty := by
  rw [parentsUpdQty_aux]
  by_cases heq : idd = (s.children kk).parent
  · simp [heq]
  · simp [heq]

theorem fill_sent_aux (s : State) (kk : Nat) (x1 idd : Nat) :
    ((upd s.parents (s.children kk).parent { (s.parents (s.children kk).parent) with cum := (s.parents (s.children kk).parent).cum + x1 }) idd).sent = (s.parents idd).sent := by
  rw [parentsUpdSent_aux]
  by_cases heq : idd = (s.children kk).parent
  · simp [heq]
  · simp [heq]

theorem fill_hstQty_tmp (b : Build) (x : Sys) (k q : Nat) (hk : k < x.st.nChildren) (idd : Nat) :
    ((step b x.st (.fill k q)).1.parents idd).qty = (x.st.parents idd).qty := by
  have hstep := step_fill_some b x.st k q hk
  rw [hstep]
  exact fill_qty_aux x.st k (min q ((x.st.children k).qty - (x.st.children k).done)) idd

theorem fill_hstSent_tmp (b : Build) (x : Sys) (k q : Nat) (hk : k < x.st.nChildren) (idd : Nat) :
    ((step b x.st (.fill k q)).1.parents idd).sent = (x.st.parents idd).sent := by
  have hstep := step_fill_some b x.st k q hk
  rw [hstep]
  exact fill_sent_aux x.st k (min q ((x.st.children k).qty - (x.st.children k).done)) idd

theorem fill_hout_some_tmp (b : Build) (x : Sys) (k q : Nat) (hk : k < x.st.nChildren) :
    (step b x.st (.fill k q)).2 = ([] : List Child) := by
  rw [step_fill_some b x.st k q hk]

theorem fill_hstN_some_tmp2 (b : Build) (x : Sys) (k q : Nat) (hk : k < x.st.nChildren) :
    (step b x.st (.fill k q)).1.nParents = x.st.nParents := by
  have hstep := step_fill_some b x.st k q hk
  rw [hstep]

theorem plan0_advance_preserves_proof : ∀ (b : Build) (x : Sys) (e : Event),
    (x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) →
    (advance step b x e).st.nParents = (advance step b x e).tr.nOrders ∧
      (∀ id, id < (advance step b x e).tr.nOrders →
        ((advance step b x e).st.parents id).qty =
          (advance step b x e).tr.qty id ∧
        ((advance step b x e).st.parents id).sent =
          (advance step b x e).tr.sent id) ∧
      ∀ k ∈ (advance step b x e).tr.kids,
        k.parent < (advance step b x e).tr.nOrders := by
  intro b x e h
  cases e with
  | parent q f => exact plan1_advance_parent_preserves b x q f h
  | route id liq => exact plan1_advance_route_preserves b x id liq h
  | ack k => exact plan1_advance_ack_preserves b x k h
  | fill k q => exact plan1_advance_fill_preserves b x k q h

theorem plan1_route_full_proof (b : Build) (x : Sys) (id liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.route id liq)).st.nParents =
        (advance step b x (.route id liq)).tr.nOrders ∧
      (∀ j, j < (advance step b x (.route id liq)).tr.nOrders →
        ((advance step b x (.route id liq)).st.parents j).qty =
          (advance step b x (.route id liq)).tr.qty j ∧
        ((advance step b x (.route id liq)).st.parents j).sent =
          (advance step b x (.route id liq)).tr.sent j) ∧
      ∀ k ∈ (advance step b x (.route id liq)).tr.kids,
        k.parent < (advance step b x (.route id liq)).tr.nOrders := by
  obtain ⟨hn, hqs, hkb⟩ := h
  by_cases hcond : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · have hout : (step b x.st (.route id liq)).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] := tmp_check_route_true b x id liq hcond
    have hnS : (step b x.st (.route id liq)).1.nParents = x.st.nParents := tmp_route_nPar b x.st id liq
    have hqtyS : ∀ j, ((step b x.st (.route id liq)).1.parents j).qty = (x.st.parents j).qty := by
      intro j
      have htmp := tmp_route_qty b x.st id liq j
      rw [if_pos hcond] at htmp
      rw [htmp]
      by_cases heq : j = id <;> simp [heq]
    have hsentS : ∀ j, ((step b x.st (.route id liq)).1.parents j).sent =
        (if j = id then (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) else (x.st.parents j).sent) := by
      intro j
      have htmp := tmp_route_sent b x.st id liq j
      rw [if_pos hcond] at htmp
      exact htmp
    have hadvSt : (advance step b x (.route id liq)).st = (step b x.st (.route id liq)).1 := by simp [advance]
    have hadvTr : (advance step b x (.route id liq)).tr = (x.tr.record [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩]) := by
      simp [advance, obs_route_eq, hout]
    have hidLt : id < x.tr.nOrders := by omega
    have hqsId := hqs id hidLt
    have hN : (advance step b x (.route id liq)).st.nParents = (advance step b x (.route id liq)).tr.nOrders := by
      rw [hadvSt, hadvTr, hnS, nOrdersRec_aux2, hn]
    refine ⟨hN, ?_, ?_⟩
    · intro j hj
      rw [hadvTr] at hj
      rw [nOrdersRec_aux2] at hj
      have hjOld : j < x.tr.nOrders := hj
      have hold := hqs j hjOld
      have eQty : ((advance step b x (.route id liq)).st.parents j).qty = (advance step b x (.route id liq)).tr.qty j := by
        rw [hadvSt, hadvTr, hqtyS j, qtyRec_aux2]
        exact hold.1
      have eSent : ((advance step b x (.route id liq)).st.parents j).sent = (advance step b x (.route id liq)).tr.sent j := by
        rw [hadvSt, hadvTr, hsentS j]
        rw [sentRecSingle_aux2]
        rw [hold.2, hqsId.1, hqsId.2]
        by_cases heq : id = j
        · subst heq; simp
        · simp [heq, Ne.symm heq]
      exact ⟨eQty, eSent⟩
    · intro k hk
      rw [hadvTr] at hk ⊢
      rw [nOrdersRec_aux2]
      apply plan1_kids_bound_record x.tr [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] hkb _ k hk
      intro c hc
      simp at hc; subst hc; exact hidLt
  · have hout : (step b x.st (.route id liq)).2 = ([] : List Child) := by
      have h := step_route_out2 b x.st id liq
      rw [if_neg hcond] at h
      exact h
    have hnS : (step b x.st (.route id liq)).1.nParents = x.st.nParents := tmp_route_nPar b x.st id liq
    have hadvSt : (advance step b x (.route id liq)).st = (step b x.st (.route id liq)).1 := by simp [advance]
    have hadvTr : (advance step b x (.route id liq)).tr = x.tr := by
      simp [advance, obs_route_eq, hout, Truth.record]
    have hN : (advance step b x (.route id liq)).st.nParents = (advance step b x (.route id liq)).tr.nOrders := by
      rw [hadvSt, hadvTr, hnS, hn]
    refine ⟨hN, ?_, ?_⟩
    · intro j hj
      rw [hadvTr] at hj
      have hq : ((step b x.st (.route id liq)).1.parents j).qty = (x.st.parents j).qty := by
        have htmp := tmp_route_qty b x.st id liq j
        rw [if_neg hcond] at htmp
        exact htmp
      have hs : ((step b x.st (.route id liq)).1.parents j).sent = (x.st.parents j).sent := by
        have htmp := tmp_route_sent b x.st id liq j
        rw [if_neg hcond] at htmp
        exact htmp
      have e1 : ((advance step b x (.route id liq)).st.parents j).qty = (x.st.parents j).qty := by
        rw [hadvSt]; exact hq
      have e2 : ((advance step b x (.route id liq)).st.parents j).sent = (x.st.parents j).sent := by
        rw [hadvSt]; exact hs
      have e3 : (advance step b x (.route id liq)).tr.qty j = x.tr.qty j := by rw [hadvTr]
      have e4 : (advance step b x (.route id liq)).tr.sent j = x.tr.sent j := by rw [hadvTr]
      rw [e1, e3, e2, e4]
      exact hqs j hj
    · intro k hk
      rw [hadvTr] at hk ⊢
      exact hkb k hk

theorem plan1_fill_full_proof (b : Build) (x : Sys) (k q : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents id).qty =
          (advance step b x (.fill k q)).tr.qty id ∧
        ((advance step b x (.fill k q)).st.parents id).sent =
          (advance step b x (.fill k q)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.fill k q)).tr.kids,
        j.parent < (advance step b x (.fill k q)).tr.nOrders := by
  obtain ⟨hn, hqs, hkb⟩ := h
  by_cases hk : k < x.st.nChildren
  · have hstep := step_fill_some b x.st k q hk
    have hout : (step b x.st (.fill k q)).2 = ([] : List Child) := by rw [hstep]
    have hstN : (step b x.st (.fill k q)).1.nParents = x.st.nParents := by rw [hstep]
    have hstQ : ∀ j, ((step b x.st (.fill k q)).1.parents j).qty = (x.st.parents j).qty :=
      fun j => fill_hstQty_tmp b x k q hk j
    have hstS : ∀ j, ((step b x.st (.fill k q)).1.parents j).sent = (x.st.parents j).sent :=
      fun j => fill_hstSent_tmp b x k q hk j
    have hadvSt : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := by simp [advance]
    have hadvTr : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record ([] : List Child) := by
      simp [advance, hout]
    have hN : (advance step b x (.fill k q)).st.nParents = (advance step b x (.fill k q)).tr.nOrders := by
      rw [hadvSt, hadvTr, hstN, nOrdersRec_aux2, nOrdersObsFill_aux2, hn]
    refine ⟨hN, ?_, ?_⟩
    · intro id hid
      rw [hadvTr, nOrdersRec_aux2, nOrdersObsFill_aux2] at hid
      have hold := hqs id hid
      have e1 : ((advance step b x (.fill k q)).st.parents id).qty = (x.st.parents id).qty := by
        rw [hadvSt]; exact hstQ id
      have e2 : ((advance step b x (.fill k q)).st.parents id).sent = (x.st.parents id).sent := by
        rw [hadvSt]; exact hstS id
      have e3 : (advance step b x (.fill k q)).tr.qty id = x.tr.qty id := by
        rw [hadvTr, qtyRec_aux2, qtyObsFill_aux2]
      have e4 : (advance step b x (.fill k q)).tr.sent id = x.tr.sent id := by
        rw [hadvTr, sentRecNil_aux, sentObsFill_aux2]
      rw [e1, e3, e2, e4]
      exact hold
    · intro j hj
      rw [hadvTr] at hj ⊢
      rw [nOrdersRec_aux2, nOrdersObsFill_aux2]
      have hj2 : j ∈ (x.tr.observe (.fill k q)).kids := by
        have : ((x.tr.observe (.fill k q)).record ([] : List Child)).kids = (x.tr.observe (.fill k q)).kids := by
          simp [Truth.record]
        rw [this] at hj
        exact hj
      cases hh : x.tr.kids[k]? with
      | none =>
        have hobs : x.tr.observe (.fill k q) = x.tr := by simp [Truth.observe, hh]
        rw [hobs] at hj2
        exact hkb j hj2
      | some c =>
        have hobsKids : (x.tr.observe (.fill k q)).kids = x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) } := by
          simp [Truth.observe, hh]
        rw [hobsKids] at hj2
        rcases setParent_mem_aux x.tr.kids k c (c.done + min q (c.qty - c.done)) j hj2 with hjOld | rfl
        · exact hkb j hjOld
        · have hcMem : c ∈ x.tr.kids := List.mem_of_getElem? hh
          have := hkb c hcMem
          simpa using this
  · have hstep := step_fill_noop b x.st k q hk
    have hout : (step b x.st (.fill k q)).2 = ([] : List Child) := by rw [hstep]
    have hadvSt : (advance step b x (.fill k q)).st = x.st := by simp [advance, hstep]
    have hadvTr : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record ([] : List Child) := by
      simp [advance, hout]
    have hN : (advance step b x (.fill k q)).st.nParents = (advance step b x (.fill k q)).tr.nOrders := by
      rw [hadvSt, hadvTr, nOrdersRec_aux2, nOrdersObsFill_aux2, hn]
    refine ⟨hN, ?_, ?_⟩
    · intro id hid
      rw [hadvTr, nOrdersRec_aux2, nOrdersObsFill_aux2] at hid
      have hold := hqs id hid
      have e1 : ((advance step b x (.fill k q)).st.parents id).qty = (x.st.parents id).qty := by rw [hadvSt]
      have e2 : ((advance step b x (.fill k q)).st.parents id).sent = (x.st.parents id).sent := by rw [hadvSt]
      have e3 : (advance step b x (.fill k q)).tr.qty id = x.tr.qty id := by
        rw [hadvTr, qtyRec_aux2, qtyObsFill_aux2]
      have e4 : (advance step b x (.fill k q)).tr.sent id = x.tr.sent id := by
        rw [hadvTr, sentRecNil_aux, sentObsFill_aux2]
      rw [e1, e3, e2, e4]
      exact hold
    · intro j hj
      rw [hadvTr] at hj ⊢
      rw [nOrdersRec_aux2, nOrdersObsFill_aux2]
      have hj2 : j ∈ (x.tr.observe (.fill k q)).kids := by
        have : ((x.tr.observe (.fill k q)).record ([] : List Child)).kids = (x.tr.observe (.fill k q)).kids := by
          simp [Truth.record]
        rw [this] at hj
        exact hj
      cases hh : x.tr.kids[k]? with
      | none =>
        have hobs : x.tr.observe (.fill k q) = x.tr := by simp [Truth.observe, hh]
        rw [hobs] at hj2
        exact hkb j hj2
      | some c =>
        have hobsKids : (x.tr.observe (.fill k q)).kids = x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) } := by
          simp [Truth.observe, hh]
        rw [hobsKids] at hj2
        rcases setParent_mem_aux x.tr.kids k c (c.done + min q (c.qty - c.done)) j hj2 with hjOld | rfl
        · exact hkb j hjOld
        · have hcMem : c ∈ x.tr.kids := List.mem_of_getElem? hh
          have := hkb c hcMem
          simpa using this

theorem plan0_advance_preserves (b : Build) (x : Sys) (e : Event)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x e).st.nParents = (advance step b x e).tr.nOrders ∧
      (∀ id, id < (advance step b x e).tr.nOrders →
        ((advance step b x e).st.parents id).qty =
          (advance step b x e).tr.qty id ∧
        ((advance step b x e).st.parents id).sent =
          (advance step b x e).tr.sent id) ∧
      ∀ k ∈ (advance step b x e).tr.kids,
        k.parent < (advance step b x e).tr.nOrders := by
  cases e with
  | parent q f => exact plan1_parent_full_tmp b x q f h
  | route id liq => exact plan1_advance_route_preserves b x id liq h
  | ack k => exact plan1_advance_ack_preserves b x k h
  | fill k q => exact plan1_advance_fill_preserves b x k q h

theorem plan1_advance_route_preserves2 (b : Build) (x : Sys) (id liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.route id liq)).st.nParents =
        (advance step b x (.route id liq)).tr.nOrders ∧
      (∀ j, j < (advance step b x (.route id liq)).tr.nOrders →
        ((advance step b x (.route id liq)).st.parents j).qty =
          (advance step b x (.route id liq)).tr.qty j ∧
        ((advance step b x (.route id liq)).st.parents j).sent =
          (advance step b x (.route id liq)).tr.sent j) ∧
      ∀ k ∈ (advance step b x (.route id liq)).tr.kids,
        k.parent < (advance step b x (.route id liq)).tr.nOrders :=
  plan1_route_full_proof b x id liq h

theorem tmp_test_route_simp (b : Build) (s : State) (id liq : Nat)
    (hcond : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) :
    (step b s (.route id liq)).2 = [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] := by
  simp only [step] at *
  simp [hcond]

theorem foo_test2 : True := trivial

theorem advance_preserves_new (b : Build) (x : Sys) (e : Event)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x e).st.nParents = (advance step b x e).tr.nOrders ∧
      (∀ id, id < (advance step b x e).tr.nOrders →
        ((advance step b x e).st.parents id).qty =
          (advance step b x e).tr.qty id ∧
        ((advance step b x e).st.parents id).sent =
          (advance step b x e).tr.sent id) ∧
      ∀ k ∈ (advance step b x e).tr.kids,
        k.parent < (advance step b x e).tr.nOrders := by
  cases e with
  | parent q f => exact plan1_parent_full_tmp b x q f h
  | route id liq => exact plan1_advance_route_preserves2 b x id liq h
  | ack k => exact plan1_advance_ack_preserves b x k h
  | fill k q => exact plan1_fill_full_proof b x k q h

theorem test_npar_early (b : Build) (s : State) (id liq : Nat) :
    (step b s (.route id liq)).1.nParents = s.nParents := by
  simp only [step]
  split <;> rfl

theorem plan1_advance_fill_preserves2 (b : Build) (x : Sys) (k q : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents id).qty =
          (advance step b x (.fill k q)).tr.qty id ∧
        ((advance step b x (.fill k q)).st.parents id).sent =
          (advance step b x (.fill k q)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.fill k q)).tr.kids,
        j.parent < (advance step b x (.fill k q)).tr.nOrders :=
  plan1_fill_full_proof b x k q h

theorem myFillSelf : True := trivial

theorem fillEarlyProof : True := trivial

theorem fillProofInline (b : Build) (x : Sys) (k q : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents id).qty =
          (advance step b x (.fill k q)).tr.qty id ∧
        ((advance step b x (.fill k q)).st.parents id).sent =
          (advance step b x (.fill k q)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.fill k q)).tr.kids,
        j.parent < (advance step b x (.fill k q)).tr.nOrders := by
  obtain ⟨hn, hqs, hkb⟩ := h
  by_cases hk : k < x.st.nChildren
  · have hstep := step_fill_some b x.st k q hk
    have hout : (step b x.st (.fill k q)).2 = ([] : List Child) := by rw [hstep]
    have hstN : (step b x.st (.fill k q)).1.nParents = x.st.nParents := by rw [hstep]
    have hstQ : ∀ j, ((step b x.st (.fill k q)).1.parents j).qty = (x.st.parents j).qty := by
      intro j
      rw [hstep]
      simp only []
      rw [parentsUpdQty_aux]
      by_cases heq : j = (x.st.children k).parent
      · simp [heq]
      · simp [heq]
    have hstS : ∀ j, ((step b x.st (.fill k q)).1.parents j).sent = (x.st.parents j).sent := by
      intro j
      rw [hstep]
      simp only []
      rw [parentsUpdSent_aux]
      by_cases heq : j = (x.st.children k).parent
      · simp [heq]
      · simp [heq]
    have hadvSt : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := by simp [advance]
    have hadvTr : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record ([] : List Child) := by
      simp [advance, hout]
    have hN : (advance step b x (.fill k q)).st.nParents = (advance step b x (.fill k q)).tr.nOrders := by
      rw [hadvSt, hadvTr, hstN, nOrdersRec_aux2, nOrdersObsFill_aux2, hn]
    refine ⟨hN, ?_, ?_⟩
    · intro id hid
      rw [hadvTr, nOrdersRec_aux2, nOrdersObsFill_aux2] at hid
      have hold := hqs id hid
      have e1 : ((advance step b x (.fill k q)).st.parents id).qty = (x.st.parents id).qty := by
        rw [hadvSt]; exact hstQ id
      have e2 : ((advance step b x (.fill k q)).st.parents id).sent = (x.st.parents id).sent := by
        rw [hadvSt]; exact hstS id
      have e3 : (advance step b x (.fill k q)).tr.qty id = x.tr.qty id := by
        rw [hadvTr, qtyRec_aux2, qtyObsFill_aux2]
      have e4 : (advance step b x (.fill k q)).tr.sent id = x.tr.sent id := by
        rw [hadvTr, sentRecNil_aux, sentObsFill_aux2]
      rw [e1, e3, e2, e4]
      exact hold
    · intro j hj
      rw [hadvTr] at hj ⊢
      rw [nOrdersRec_aux2, nOrdersObsFill_aux2]
      have hj2 : j ∈ (x.tr.observe (.fill k q)).kids := by
        have : ((x.tr.observe (.fill k q)).record ([] : List Child)).kids = (x.tr.observe (.fill k q)).kids := by
          simp [Truth.record]
        rw [this] at hj
        exact hj
      cases hh : x.tr.kids[k]? with
      | none =>
        have hobs : x.tr.observe (.fill k q) = x.tr := by simp [Truth.observe, hh]
        rw [hobs] at hj2
        exact hkb j hj2
      | some c =>
        have hobsKids : (x.tr.observe (.fill k q)).kids = x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) } := by
          simp [Truth.observe, hh]
        rw [hobsKids] at hj2
        rcases setParent_mem_aux x.tr.kids k c (c.done + min q (c.qty - c.done)) j hj2 with hjOld | rfl
        · exact hkb j hjOld
        · have hcMem : c ∈ x.tr.kids := List.mem_of_getElem? hh
          have := hkb c hcMem
          simpa using this
  · have hstep := step_fill_noop b x.st k q hk
    have hout : (step b x.st (.fill k q)).2 = ([] : List Child) := by rw [hstep]
    have hadvSt : (advance step b x (.fill k q)).st = x.st := by simp [advance, hstep]
    have hadvTr : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record ([] : List Child) := by
      simp [advance, hout]
    have hN : (advance step b x (.fill k q)).st.nParents = (advance step b x (.fill k q)).tr.nOrders := by
      rw [hadvSt, hadvTr, nOrdersRec_aux2, nOrdersObsFill_aux2, hn]
    refine ⟨hN, ?_, ?_⟩
    · intro id hid
      rw [hadvTr, nOrdersRec_aux2, nOrdersObsFill_aux2] at hid
      have hold := hqs id hid
      have e1 : ((advance step b x (.fill k q)).st.parents id).qty = (x.st.parents id).qty := by rw [hadvSt]
      have e2 : ((advance step b x (.fill k q)).st.parents id).sent = (x.st.parents id).sent := by rw [hadvSt]
      have e3 : (advance step b x (.fill k q)).tr.qty id = x.tr.qty id := by
        rw [hadvTr, qtyRec_aux2, qtyObsFill_aux2]
      have e4 : (advance step b x (.fill k q)).tr.sent id = x.tr.sent id := by
        rw [hadvTr, sentRecNil_aux, sentObsFill_aux2]
      rw [e1, e3, e2, e4]
      exact hold
    · intro j hj
      rw [hadvTr] at hj ⊢
      rw [nOrdersRec_aux2, nOrdersObsFill_aux2]
      have hj2 : j ∈ (x.tr.observe (.fill k q)).kids := by
        have : ((x.tr.observe (.fill k q)).record ([] : List Child)).kids = (x.tr.observe (.fill k q)).kids := by
          simp [Truth.record]
        rw [this] at hj
        exact hj
      cases hh : x.tr.kids[k]? with
      | none =>
        have hobs : x.tr.observe (.fill k q) = x.tr := by simp [Truth.observe, hh]
        rw [hobs] at hj2
        exact hkb j hj2
      | some c =>
        have hobsKids : (x.tr.observe (.fill k q)).kids = x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) } := by
          simp [Truth.observe, hh]
        rw [hobsKids] at hj2
        rcases setParent_mem_aux x.tr.kids k c (c.done + min q (c.qty - c.done)) j hj2 with hjOld | rfl
        · exact hkb j hjOld
        · have hcMem : c ∈ x.tr.kids := List.mem_of_getElem? hh
          have := hkb c hcMem
          simpa using this

theorem plan0_run_invariants_proof : ∀ (b : Build) (evs : List Event),
    (run step b evs).st.nParents = (run step b evs).tr.nOrders ∧
      (∀ id, id < (run step b evs).tr.nOrders →
        ((run step b evs).st.parents id).qty =
          (run step b evs).tr.qty id ∧
        ((run step b evs).st.parents id).sent =
          (run step b evs).tr.sent id) ∧
      ∀ k ∈ (run step b evs).tr.kids,
        k.parent < (run step b evs).tr.nOrders := by
  intro b evs
  refine run_induction step b (fun x => x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) ?h0 ?hs evs
  · refine ⟨rfl, ?_, ?_⟩
    · intro id hid
      simp [start, Truth.empty] at hid
    · intro k hk
      simp [start, Truth.empty] at hk
  · intro x e hx
    exact advance_preserves_new b x e hx

theorem plan0_run_invariants_aux_wrap : True := trivial

theorem check_can_use_early (b : Build) (s : State) (id liq : Nat) :
    (step b s (.route id liq)).2 =
    (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] else []) :=
  step_route_out2 b s id liq

theorem check_fill_early (b : Build) (s : State) (k q : Nat) (h : k < s.nChildren) :
    (step b s (.fill k q)).2 = ([] : List Child) := by
  rw [step_fill_some b s k q h]

theorem plan0_run_invariants_dup_test (b : Build) (evs : List Event) :
    (run step b evs).st.nParents = (run step b evs).tr.nOrders :=
  (plan0_run_invariants b evs).1

theorem plan0_run_invariants_newproof_aliascheck : True := trivial


theorem plan2_parent_preserves (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.parent q f)).st.nParents =
        (advance step b x (.parent q f)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.parent q f)).tr.nOrders →
        ((advance step b x (.parent q f)).st.parents id).qty =
          (advance step b x (.parent q f)).tr.qty id ∧
        ((advance step b x (.parent q f)).st.parents id).sent =
          (advance step b x (.parent q f)).tr.sent id) ∧
      ∀ k ∈ (advance step b x (.parent q f)).tr.kids,
        k.parent < (advance step b x (.parent q f)).tr.nOrders :=
  plan1_parent_full_tmp b x q f h


theorem plan2_route_preserves (b : Build) (x : Sys) (id liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ j, j < x.tr.nOrders →
        (x.st.parents j).qty = x.tr.qty j ∧
        (x.st.parents j).sent = x.tr.sent j) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.route id liq)).st.nParents =
        (advance step b x (.route id liq)).tr.nOrders ∧
      (∀ j, j < (advance step b x (.route id liq)).tr.nOrders →
        ((advance step b x (.route id liq)).st.parents j).qty =
          (advance step b x (.route id liq)).tr.qty j ∧
        ((advance step b x (.route id liq)).st.parents j).sent =
          (advance step b x (.route id liq)).tr.sent j) ∧
      ∀ k ∈ (advance step b x (.route id liq)).tr.kids,
        k.parent < (advance step b x (.route id liq)).tr.nOrders :=
  plan1_route_full_proof b x id liq h


theorem plan2_ack_preserves (b : Build) (x : Sys) (k : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ j ∈ x.tr.kids, j.parent < x.tr.nOrders) :
    (advance step b x (.ack k)).st.nParents =
        (advance step b x (.ack k)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.ack k)).tr.nOrders →
        ((advance step b x (.ack k)).st.parents id).qty =
          (advance step b x (.ack k)).tr.qty id ∧
        ((advance step b x (.ack k)).st.parents id).sent =
          (advance step b x (.ack k)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.ack k)).tr.kids,
        j.parent < (advance step b x (.ack k)).tr.nOrders :=
  plan1_advance_ack_preserves b x k h




theorem plan2_advance_preserves (b : Build) (x : Sys) (e : Event)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x e).st.nParents = (advance step b x e).tr.nOrders ∧
      (∀ id, id < (advance step b x e).tr.nOrders →
        ((advance step b x e).st.parents id).qty =
          (advance step b x e).tr.qty id ∧
        ((advance step b x e).st.parents id).sent =
          (advance step b x e).tr.sent id) ∧
      ∀ k ∈ (advance step b x e).tr.kids,
        k.parent < (advance step b x e).tr.nOrders := by
  cases e with
  | parent q f => exact plan2_parent_preserves b x q f h
  | route id liq => exact plan2_route_preserves b x id liq h
  | ack k => exact plan2_ack_preserves b x k h
  | fill k q => exact fillProofInline b x k q h


theorem plan2_parent_preserves_aux_wrap : plan2_parent_preserves = plan2_parent_preserves := rfl

theorem plan2_parent_helper_proof (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.parent q f)).st.nParents =
        (advance step b x (.parent q f)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.parent q f)).tr.nOrders →
        ((advance step b x (.parent q f)).st.parents id).qty =
          (advance step b x (.parent q f)).tr.qty id ∧
        ((advance step b x (.parent q f)).st.parents id).sent =
          (advance step b x (.parent q f)).tr.sent id) ∧
      ∀ k ∈ (advance step b x (.parent q f)).tr.kids,
        k.parent < (advance step b x (.parent q f)).tr.nOrders :=
  plan1_parent_full_tmp b x q f h

theorem plan2_route_preserves_proof_aux (b : Build) (x : Sys) (id liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ j, j < x.tr.nOrders →
        (x.st.parents j).qty = x.tr.qty j ∧
        (x.st.parents j).sent = x.tr.sent j) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.route id liq)).st.nParents =
        (advance step b x (.route id liq)).tr.nOrders ∧
      (∀ j, j < (advance step b x (.route id liq)).tr.nOrders →
        ((advance step b x (.route id liq)).st.parents j).qty =
          (advance step b x (.route id liq)).tr.qty j ∧
        ((advance step b x (.route id liq)).st.parents j).sent =
          (advance step b x (.route id liq)).tr.sent j) ∧
      ∀ k ∈ (advance step b x (.route id liq)).tr.kids,
        k.parent < (advance step b x (.route id liq)).tr.nOrders :=
  plan1_route_full_proof b x id liq h

theorem plan2_ack_preserves_proved (b : Build) (x : Sys) (k : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ j ∈ x.tr.kids, j.parent < x.tr.nOrders) :
    (advance step b x (.ack k)).st.nParents =
        (advance step b x (.ack k)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.ack k)).tr.nOrders →
        ((advance step b x (.ack k)).st.parents id).qty =
          (advance step b x (.ack k)).tr.qty id ∧
        ((advance step b x (.ack k)).st.parents id).sent =
          (advance step b x (.ack k)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.ack k)).tr.kids,
        j.parent < (advance step b x (.ack k)).tr.nOrders :=
  plan1_advance_ack_preserves b x k h

theorem plan2_fill_preserves_aux_delegate (b : Build) (x : Sys) (k q : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ j ∈ x.tr.kids, j.parent < x.tr.nOrders) :
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents id).qty =
          (advance step b x (.fill k q)).tr.qty id ∧
        ((advance step b x (.fill k q)).st.parents id).sent =
          (advance step b x (.fill k q)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.fill k q)).tr.kids,
        j.parent < (advance step b x (.fill k q)).tr.nOrders :=
  fillProofInline b x k q h

theorem plan2_fill_preserves (b : Build) (x : Sys) (k q : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ j ∈ x.tr.kids, j.parent < x.tr.nOrders) :
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
      (∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents id).qty =
          (advance step b x (.fill k q)).tr.qty id ∧
        ((advance step b x (.fill k q)).st.parents id).sent =
          (advance step b x (.fill k q)).tr.sent id) ∧
      ∀ j ∈ (advance step b x (.fill k q)).tr.kids,
        j.parent < (advance step b x (.fill k q)).tr.nOrders :=
  fillProofInline b x k q h

theorem plan2_advance_preserves_aux_proof (b : Build) (x : Sys) (e : Event)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x e).st.nParents = (advance step b x e).tr.nOrders ∧
      (∀ id, id < (advance step b x e).tr.nOrders →
        ((advance step b x e).st.parents id).qty =
          (advance step b x e).tr.qty id ∧
        ((advance step b x e).st.parents id).sent =
          (advance step b x e).tr.sent id) ∧
      ∀ k ∈ (advance step b x e).tr.kids,
        k.parent < (advance step b x e).tr.nOrders := by
  cases e with
  | parent q f => exact plan2_parent_preserves b x q f h
  | route id liq => exact plan2_route_preserves b x id liq h
  | ack k => exact plan2_ack_preserves b x k h
  | fill k q => exact plan2_fill_preserves b x k q h

theorem plan2_advance_preserves_fix : True := trivial

theorem plan2_advance_preserves_check (b : Build) (x : Sys) (e : Event)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x e).st.nParents = (advance step b x e).tr.nOrders ∧
      (∀ id, id < (advance step b x e).tr.nOrders →
        ((advance step b x e).st.parents id).qty =
          (advance step b x e).tr.qty id ∧
        ((advance step b x e).st.parents id).sent =
          (advance step b x e).tr.sent id) ∧
      ∀ k ∈ (advance step b x e).tr.kids,
        k.parent < (advance step b x e).tr.nOrders := by
  cases e with
  | parent q f => exact plan2_parent_preserves b x q f h
  | route id liq => exact plan2_route_preserves b x id liq h
  | ack k => exact plan2_ack_preserves b x k h
  | fill k q => exact plan2_fill_preserves b x k q h

theorem plan2_advance_preserves_inline_test (b : Build) (x : Sys) (e : Event)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x e).st.nParents = (advance step b x e).tr.nOrders ∧
      (∀ id, id < (advance step b x e).tr.nOrders →
        ((advance step b x e).st.parents id).qty =
          (advance step b x e).tr.qty id ∧
        ((advance step b x e).st.parents id).sent =
          (advance step b x e).tr.sent id) ∧
      ∀ k ∈ (advance step b x e).tr.kids,
        k.parent < (advance step b x e).tr.nOrders := by
  cases e with
  | parent q f => exact plan2_parent_preserves b x q f h
  | route id liq => exact plan2_route_preserves b x id liq h
  | ack k => exact plan2_ack_preserves b x k h
  | fill k q => exact fillProofInline b x k q h

theorem dummy_unique_zzz : True := trivial

theorem myAdvancePreserves_unique123 (b : Build) (x : Sys) (e : Event)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x e).st.nParents = (advance step b x e).tr.nOrders ∧
      (∀ id, id < (advance step b x e).tr.nOrders →
        ((advance step b x e).st.parents id).qty =
          (advance step b x e).tr.qty id ∧
        ((advance step b x e).st.parents id).sent =
          (advance step b x e).tr.sent id) ∧
      ∀ k ∈ (advance step b x e).tr.kids,
        k.parent < (advance step b x e).tr.nOrders := by
  cases e with
  | parent q f => exact plan1_parent_full_tmp b x q f h
  | route id liq => exact plan1_route_full_proof b x id liq h
  | ack k => exact plan1_advance_ack_preserves b x k h
  | fill k q => exact fillProofInline b x k q h

theorem myRunInv_unique123 (b : Build) (evs : List Event) :
    (run step b evs).st.nParents = (run step b evs).tr.nOrders ∧
      (∀ id, id < (run step b evs).tr.nOrders →
        ((run step b evs).st.parents id).qty =
          (run step b evs).tr.qty id ∧
        ((run step b evs).st.parents id).sent =
          (run step b evs).tr.sent id) ∧
      ∀ k ∈ (run step b evs).tr.kids,
        k.parent < (run step b evs).tr.nOrders := by
  refine run_induction step b (fun x => x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) ?h0 ?hs evs
  · refine ⟨rfl, ?_, ?_⟩
    · intro id hid
      simp [start, Truth.empty] at hid
    · intro k hk
      simp [start, Truth.empty] at hk
  · intro x e hx
    exact myAdvancePreserves_unique123 b x e hx

theorem routeNegQty_uniqueC (b : Build) (s : State) (id liq j : Nat)
    (hcond : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    ((step b s (.route id liq)).1.parents j).qty = (s.parents j).qty := by
  unfold step
  simp [hcond]

theorem routeNegSent_uniqueC (b : Build) (s : State) (id liq j : Nat)
    (hcond : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    ((step b s (.route id liq)).1.parents j).sent = (s.parents j).sent := by
  unfold step
  simp [hcond]

theorem routeNegNPar_uniqueC (b : Build) (s : State) (id liq : Nat)
    (hcond : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    (step b s (.route id liq)).1.nParents = s.nParents := by
  unfold step
  simp [hcond]

theorem routeNegOut_uniqueC (b : Build) (s : State) (id liq : Nat)
    (hcond : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    (step b s (.route id liq)).2 = ([] : List Child) := by
  unfold step
  simp [hcond]

theorem checkUnfoldRouteNeg_uniqueD (b : Build) (s : State) (id liq j : Nat)
    (hcond : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    ((step b s (.route id liq)).1.parents j).qty = (s.parents j).qty := by
  unfold step
  simp [hcond]

theorem invViaDelegate_uniqueZZ (b : Build) (evs : List Event) :
    (run step b evs).st.nParents = (run step b evs).tr.nOrders ∧
      (∀ id, id < (run step b evs).tr.nOrders →
        ((run step b evs).st.parents id).qty =
          (run step b evs).tr.qty id ∧
        ((run step b evs).st.parents id).sent =
          (run step b evs).tr.sent id) ∧
      ∀ k ∈ (run step b evs).tr.kids,
        k.parent < (run step b evs).tr.nOrders :=
  plan0_run_invariants_proof b evs

theorem plan0_route_eq_expected_of_invariants (b : Build) (x : Sys)
    (id liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      (∀ id, id < x.tr.nOrders →
        (x.st.parents id).qty = x.tr.qty id ∧
        (x.st.parents id).sent = x.tr.sent id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (step b x.st (.route id liq)).2 = expectedRoute x.tr id liq := by
  obtain ⟨hn, hqs, hkb⟩ := h
  rw [plan0_step_route_out]
  unfold expectedRoute
  by_cases hid : id < x.tr.nOrders
  · obtain ⟨hq, hs⟩ := hqs id hid
    rw [hn, hq, hs]
  · have hst : ¬ id < x.st.nParents := by rw [hn]; exact hid
    simp [hst, hid]

theorem tmpRepro123 (b : Build) (evs : List Event) :
    ∀ id, id < (run step b evs).st.nParents → True := by
  refine run_induction step b (fun x => ∀ id, id < x.st.nParents → True) ?h0 ?hs evs
  · intro id hid
    trivial
  · intro x e ih id hid
    cases e with
    | parent q f =>
      trivial
    | route rid liq =>
      have hstN : (step b x.st (.route rid liq)).1.nParents = x.st.nParents := tmp_route_nPar b x.st rid liq
      trivial
    | ack k => trivial
    | fill k q => trivial

theorem tmpRepro124 (b : Build) (evs : List Event) :
    ∀ id, id < (run step b evs).st.nParents → True := by
  refine run_induction step b (fun x => ∀ id, id < x.st.nParents → True) ?h0 ?hs evs
  · intro id hid
    trivial
  · intro x e ih id hid
    cases e with
    | parent q f =>
      trivial
    | route rr ll =>
      by_cases hcond : rr < x.st.nParents ∧ 0 < min ll ((x.st.parents rr).qty - (x.st.parents rr).sent)
      · have hstN : (step b x.st (.route rr ll)).1.nParents = x.st.nParents := tmp_route_nPar b x.st rr ll
        trivial
      · trivial
    | ack kk => trivial
    | fill kk qq => trivial

theorem tmpRepro126 (b : Build) (evs : List Event) :
    ∀ id, id < (run step b evs).st.nParents → True := by
  refine run_induction step b (fun x => ∀ id, id < x.st.nParents → True) ?h0 ?hs evs
  · intro id hid
    trivial
  · intro x e ih id hid
    cases e with
    | parent q f =>
      trivial
    | route rr ll =>
      have hadvSt : (advance step b x (.route rr ll)).st = (step b x.st (.route rr ll)).1 := by simp [advance]
      rw [hadvSt] at hid
      by_cases hcond : rr < x.st.nParents ∧ 0 < min ll ((x.st.parents rr).qty - (x.st.parents rr).sent)
      · have hstN : (step b x.st (.route rr ll)).1.nParents = x.st.nParents := tmp_route_nPar b x.st rr ll
        trivial
      · trivial
    | ack kk => trivial
    | fill kk qq => trivial

theorem tmpRepro128 (x : Sys) (b : Build) (id rr ll : Nat)
    (hcond : rr < x.st.nParents ∧ 0 < min ll ((x.st.parents rr).qty - (x.st.parents rr).sent)) :
    ((step b x.st (.route rr ll)).1.parents id).qty = (x.st.parents id).qty := by
  have htmp := tmp_route_qty b x.st rr ll id
  rw [if_pos hcond] at htmp
  rw [htmp]
  by_cases heq : id = rr <;> simp [heq]







theorem plan3_tr_sent_eq_zero_of_ge (b : Build) (evs : List Event) (id : Nat)
    (hid : (run step b evs).tr.nOrders ≤ id) :
    (run step b evs).tr.sent id = 0 := by
  have hinv := plan0_run_invariants_proof b evs
  have hkb : ∀ k ∈ (run step b evs).tr.kids, k.parent < (run step b evs).tr.nOrders := hinv.2.2
  have h0 : sentFor (run step b evs).tr.kids id = 0 :=
    plan1_sentFor_zero_of_all_parent_lt _ _ _ hkb hid
  simp [Truth.sent, h0]




theorem probe_parent2_tmp (b : Build) (x : Sys) (q : Nat) (f : Bool) (id : Nat)
    (h : ∀ id, id < x.st.nParents → (x.st.parents id).sent ≤ (x.st.parents id).qty)
    (hid : id < (advance step b x (.parent q f)).st.nParents) :
    ((advance step b x (.parent q f)).st.parents id).sent ≤
    ((advance step b x (.parent q f)).st.parents id).qty := by
  have hst : (advance step b x (.parent q f)).st = ({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State) := by simp [advance, step]
  rw [hst] at hid ⊢
  simp only at hid ⊢
  by_cases heq : id = x.st.nParents
  · subst heq; simp [upd]
  · have hlt : id < x.st.nParents := by omega
    have hle := h id hlt
    simp [upd, heq]
    exact hle

theorem probe_if2_tmp (x : Sys) (a b : Nat) (heq : a = b)
    (hle : (x.st.parents a).sent ≤ (x.st.parents a).qty) :
    (if a = b then (x.st.parents a).sent + min 5 ((x.st.parents a).qty - (x.st.parents a).sent) else (x.st.parents a).sent) ≤
    (if a = b then (x.st.parents a).qty else (x.st.parents a).qty) := by
  simp only [if_pos heq]
  have hmin : min 5 ((x.st.parents a).qty - (x.st.parents a).sent) ≤ (x.st.parents a).qty - (x.st.parents a).sent := Nat.min_le_right _ _
  omega





theorem plan4_route_sent_le_qty (b : Build) (x : Sys) (rid liq : Nat)
    (h : ∀ id, id < x.st.nParents →
      (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ id, id < (advance step b x (.route rid liq)).st.nParents →
      ((advance step b x (.route rid liq)).st.parents id).sent ≤
        ((advance step b x (.route rid liq)).st.parents id).qty := by sorry





theorem plan4_sent_add_min_le (sent qty liq : Nat) (h : sent ≤ qty) :
    sent + min liq (qty - sent) ≤ qty := by
  have hm : min liq (qty - sent) ≤ qty - sent := Nat.min_le_right _ _
  omega

theorem plan4_parent_sent_le_qty_proof : True := trivial

theorem plan4_parent_sent_le_qty (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : ∀ id, id < x.st.nParents →
      (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ id, id < (advance step b x (.parent q f)).st.nParents →
      ((advance step b x (.parent q f)).st.parents id).sent ≤
        ((advance step b x (.parent q f)).st.parents id).qty := by
  intro id hid
  have hst : (advance step b x (.parent q f)).st = ({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State) := by simp [advance, step]
  rw [hst] at hid ⊢
  simp only at hid ⊢
  by_cases heq : id = x.st.nParents
  · subst heq; simp [upd]
  · have hlt : id < x.st.nParents := by omega
    have hle := h id hlt
    simp [upd, heq]
    exact hle

theorem plan4_ack_sent_le_qty_proof_tmp2 (b : Build) (x : Sys) (k : Nat)
    (h : ∀ id, id < x.st.nParents →
      (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ id, id < (advance step b x (.ack k)).st.nParents →
      ((advance step b x (.ack k)).st.parents id).sent ≤
        ((advance step b x (.ack k)).st.parents id).qty := by
  intro id hid
  have hst : (advance step b x (.ack k)).st = x.st := by simp [advance, step_ack_eq b x.st k]
  rw [hst] at hid ⊢
  exact h id hid

theorem plan4_ack_sent_le_qty (b : Build) (x : Sys) (k : Nat)
    (h : ∀ id, id < x.st.nParents →
      (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ id, id < (advance step b x (.ack k)).st.nParents →
      ((advance step b x (.ack k)).st.parents id).sent ≤
        ((advance step b x (.ack k)).st.parents id).qty := by
  intro id hid
  have hst : (advance step b x (.ack k)).st = x.st := by simp [advance, step_ack_eq b x.st k]
  rw [hst] at hid ⊢
  exact h id hid

theorem plan4_fill_sent_le_qty (b : Build) (x : Sys) (k q : Nat)
    (h : ∀ id, id < x.st.nParents →
      (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ id, id < (advance step b x (.fill k q)).st.nParents →
      ((advance step b x (.fill k q)).st.parents id).sent ≤
        ((advance step b x (.fill k q)).st.parents id).qty := by
  intro id hid
  by_cases hk : k < x.st.nChildren
  · have hstN : (step b x.st (.fill k q)).1.nParents = x.st.nParents := fill_hstN_some_tmp2 b x k q hk
    have hadvSt : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := by simp [advance]
    rw [hadvSt, hstN] at hid
    have hQ : ((advance step b x (.fill k q)).st.parents id).qty = (x.st.parents id).qty := by
      rw [hadvSt]; exact fill_hstQty_tmp b x k q hk id
    have hS : ((advance step b x (.fill k q)).st.parents id).sent = (x.st.parents id).sent := by
      rw [hadvSt]; exact fill_hstSent_tmp b x k q hk id
    rw [hQ, hS]
    exact h id hid
  · have hstep := step_fill_noop b x.st k q hk
    have hadvSt : (advance step b x (.fill k q)).st = x.st := by simp [advance, hstep]
    rw [hadvSt] at hid ⊢
    exact h id hid

theorem plan3_advance_sent_le_qty_auxD (b : Build) (x : Sys) (rid liq id : Nat)
    (h : ∀ id, id < x.st.nParents → (x.st.parents id).sent ≤ (x.st.parents id).qty)
    (hid : id < (advance step b x (.route rid liq)).st.nParents) :
    ((advance step b x (.route rid liq)).st.parents id).sent ≤
      ((advance step b x (.route rid liq)).st.parents id).qty := by
  have hadvSt : (advance step b x (.route rid liq)).st = (step b x.st (.route rid liq)).1 := by simp [advance]
  have hnS : (step b x.st (.route rid liq)).1.nParents = x.st.nParents := tmp_route_nPar b x.st rid liq
  rw [hadvSt, hnS] at hid
  have hle : (x.st.parents id).sent ≤ (x.st.parents id).qty := h id hid
  by_cases hcond : rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)
  · have hrid : (x.st.parents rid).sent ≤ (x.st.parents rid).qty := h rid hcond.1
    by_cases heq : id = rid
    · subst heq
      have hQ : ((advance step b x (.route id liq)).st.parents id).qty = (x.st.parents id).qty := by
        have htmp := tmp_route_qty b x.st id liq id
        have hadv : (advance step b x (.route id liq)).st.parents id = (step b x.st (.route id liq)).1.parents id := by simp [advance]
        rw [hadv, htmp, if_pos hcond, if_pos rfl]
      have hS : ((advance step b x (.route id liq)).st.parents id).sent = (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) := by
        have htmp := tmp_route_sent b x.st id liq id
        have hadv : (advance step b x (.route id liq)).st.parents id = (step b x.st (.route id liq)).1.parents id := by simp [advance]
        rw [hadv, htmp, if_pos hcond, if_pos rfl]
      rw [hQ, hS]
      exact plan4_sent_add_min_le _ _ _ hrid
    · have hQ : ((advance step b x (.route rid liq)).st.parents id).qty = (x.st.parents id).qty := by
        have htmp := tmp_route_qty b x.st rid liq id
        have hadv : (advance step b x (.route rid liq)).st.parents id = (step b x.st (.route rid liq)).1.parents id := by simp [advance]
        rw [hadv, htmp, if_pos hcond, if_neg heq]
      have hS : ((advance step b x (.route rid liq)).st.parents id).sent = (x.st.parents id).sent := by
        have htmp := tmp_route_sent b x.st rid liq id
        have hadv : (advance step b x (.route rid liq)).st.parents id = (step b x.st (.route rid liq)).1.parents id := by simp [advance]
        rw [hadv, htmp, if_pos hcond, if_neg heq]
      rw [hQ, hS]
      exact hle
  · have hQ : ((advance step b x (.route rid liq)).st.parents id).qty = (x.st.parents id).qty := by
      have htmp := tmp_route_qty b x.st rid liq id
      have hadv : (advance step b x (.route rid liq)).st.parents id = (step b x.st (.route rid liq)).1.parents id := by simp [advance]
      rw [hadv, htmp, if_neg hcond]
    have hS : ((advance step b x (.route rid liq)).st.parents id).sent = (x.st.parents id).sent := by
      have htmp := tmp_route_sent b x.st rid liq id
      have hadv : (advance step b x (.route rid liq)).st.parents id = (step b x.st (.route rid liq)).1.parents id := by simp [advance]
      rw [hadv, htmp, if_neg hcond]
    rw [hQ, hS]
    exact hle

theorem plan3_advance_sent_le_qty (b : Build) (x : Sys) (e : Event)
    (h : ∀ id, id < x.st.nParents →
      (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ id, id < (advance step b x e).st.nParents →
      ((advance step b x e).st.parents id).sent ≤
        ((advance step b x e).st.parents id).qty := by
  intro id hid
  cases e with
  | parent q f => exact plan4_parent_sent_le_qty b x q f h id hid
  | route rid liq => exact plan3_advance_sent_le_qty_auxD b x rid liq id h hid
  | ack k => exact plan4_ack_sent_le_qty b x k h id hid
  | fill k q => exact plan4_fill_sent_le_qty b x k q h id hid

theorem plan3_run_sent_le_qty (b : Build) (evs : List Event) (id : Nat)
    (hid : id < (run step b evs).st.nParents) :
    ((run step b evs).st.parents id).sent ≤
      ((run step b evs).st.parents id).qty := by
  have hall : ∀ id, id < (run step b evs).st.nParents →
      ((run step b evs).st.parents id).sent ≤
        ((run step b evs).st.parents id).qty := by
    refine run_induction step b (fun x => ∀ id, id < x.st.nParents → (x.st.parents id).sent ≤ (x.st.parents id).qty) ?h0 ?hs evs
    · intro id hid
      simp [start, init] at hid
    · intro x e ih
      exact plan3_advance_sent_le_qty b x e ih
  exact hall id hid

theorem plan3_tr_sent_le_qty_of_lt (b : Build) (evs : List Event) (id : Nat)
    (hid : id < (run step b evs).tr.nOrders) :
    (run step b evs).tr.sent id ≤ (run step b evs).tr.qty id := by
  have hinv := plan0_run_invariants_proof b evs
  have hn : (run step b evs).st.nParents = (run step b evs).tr.nOrders := hinv.1
  have hqs := hinv.2.1
  obtain ⟨hq, hs⟩ := hqs id hid
  have hidSt : id < (run step b evs).st.nParents := by rw [hn]; exact hid
  have hle := plan3_run_sent_le_qty b evs id hidSt
  omega

theorem plan3_tr_sent_eq_zero_of_ge_proof : ∀ (b : Build) (evs : List Event) (id : Nat),
    (run step b evs).tr.nOrders ≤ id →
    (run step b evs).tr.sent id = 0 := by
  intro b evs id hid
  have hinv := plan0_run_invariants_proof b evs
  have hkb : ∀ k ∈ (run step b evs).tr.kids, k.parent < (run step b evs).tr.nOrders := hinv.2.2
  have h0 : sentFor (run step b evs).tr.kids id = 0 :=
    plan1_sentFor_zero_of_all_parent_lt _ _ _ hkb hid
  simp [Truth.sent, h0]

theorem plan3_tr_sent_eq_zero_of_ge_auxwrap : ∀ (b : Build) (evs : List Event) (id : Nat),
    (run step b evs).tr.nOrders ≤ id →
    (run step b evs).tr.sent id = 0 :=
  fun b evs id hid => plan3_tr_sent_eq_zero_of_ge_proof b evs id hid

theorem plan3_tr_sent_eq_zero_of_ge_NEW (b : Build) (evs : List Event) (id : Nat)
    (hid : (run step b evs).tr.nOrders ≤ id) :
    (run step b evs).tr.sent id = 0 := by
  have hinv := plan0_run_invariants_proof b evs
  have hkb : ∀ k ∈ (run step b evs).tr.kids, k.parent < (run step b evs).tr.nOrders := hinv.2.2
  have h0 : sentFor (run step b evs).tr.kids id = 0 :=
    plan1_sentFor_zero_of_all_parent_lt _ _ _ hkb hid
  simp [Truth.sent, h0]

theorem checkNewExists (b : Build) (evs : List Event) (id : Nat)
    (hid : (run step b evs).tr.nOrders ≤ id) :
    (run step b evs).tr.sent id = 0 :=
  plan3_tr_sent_eq_zero_of_ge_NEW b evs id hid

theorem plan3_never_overroute_all_proof : NeverOverroute step := by
  intro b evs id
  by_cases h : id < (run step b evs).tr.nOrders
  · exact plan3_tr_sent_le_qty_of_lt b evs id h
  · have hle : (run step b evs).tr.nOrders ≤ id := Nat.le_of_not_gt h
    have hz := plan3_tr_sent_eq_zero_of_ge_proof b evs id hle
    omega

theorem plan3_never_overroute_all : NeverOverroute step := by
  intro b evs id
  by_cases h : id < (run step b evs).tr.nOrders
  · exact plan3_tr_sent_le_qty_of_lt b evs id h
  · have hle : (run step b evs).tr.nOrders ≤ id := Nat.le_of_not_gt h
    have hz := plan3_tr_sent_eq_zero_of_ge_proof b evs id hle
    omega

theorem req_never_overroute_aux_proof : NeverOverroute step :=
  plan3_never_overroute_all

theorem stop_fill_route_auxA (b : Build) (evs : List Event) (rid liq id : Nat)
    (hSentEq : (run step b evs).tr.sent id = (run step b evs).tr.qty id)
    (hn : (run step b evs).st.nParents = (run step b evs).tr.nOrders)
    (hqs : ∀ id_1, id_1 < (run step b evs).tr.nOrders →
      ((run step b evs).st.parents id_1).qty = (run step b evs).tr.qty id_1 ∧
      ((run step b evs).st.parents id_1).sent = (run step b evs).tr.sent id_1)
    (c : Child)
    (hc : c ∈ (step b (run step b evs).st (Event.route rid liq)).2) :
    c.parent ≠ id := by
  have hout := plan0_step_route_out b (run step b evs).st rid liq
  by_cases hcond : rid < (run step b evs).st.nParents ∧ 0 < min liq (((run step b evs).st.parents rid).qty - ((run step b evs).st.parents rid).sent)
  · rw [if_pos hcond] at hout
    rw [hout] at hc
    simp at hc
    obtain rfl := hc
    simp only
    intro hcontra
    subst hcontra
    have hlt : rid < (run step b evs).tr.nOrders := by omega
    obtain ⟨hq, hs⟩ := hqs rid hlt
    have hzero : ((run step b evs).st.parents rid).qty - ((run step b evs).st.parents rid).sent = 0 := by
      rw [hq, hs, hSentEq, Nat.sub_self]
    rw [hzero] at hcond
    simp at hcond
  · rw [if_neg hcond] at hout
    rw [hout] at hc
    simp at hc

theorem execObsParent_aux (t : Truth) (q : Nat) (f : Bool) (id : Nat) : (t.observe (.parent q f)).exec id = t.exec id := by rfl

theorem execObsRoute_aux (t : Truth) (id liq idd : Nat) : (t.observe (.route id liq)).exec idd = t.exec idd := by rfl

theorem execObsAck_aux (t : Truth) (k id : Nat) : (t.observe (.ack k)).exec id = t.exec id := by rfl

theorem execRecNil_aux (t : Truth) (id : Nat) : ((t.record ([] : List Child)).exec id) = t.exec id := by simp [Truth.exec, Truth.record]

theorem execRecSingle_aux (t : Truth) (pid qq id : Nat) : (((t.record [⟨pid, qq⟩]).exec id)) = t.exec id := by simp [Truth.exec, Truth.record]

theorem qtyRecNil_aux (t : Truth) (j : Nat) : ((t.record ([] : List Child)).qty j) = t.qty j := by simp [Truth.record]

theorem nOrdersObsRoute_aux (t : Truth) (id liq : Nat) : (t.observe (.route id liq)).nOrders = t.nOrders := by rfl

theorem kidsObsRoute_aux (t : Truth) (id liq : Nat) : (t.observe (.route id liq)).kids = t.kids := by rfl

theorem nChildParent_aux (s : State) (b : Build) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).1.nChildren = s.nChildren := by simp [step]

theorem childParent_aux (s : State) (b : Build) (q : Nat) (f : Bool) (k : Nat) :
    (step b s (.parent q f)).1.children k = s.children k := by simp [step]

theorem cumParentOld_aux (s : State) (b : Build) (q : Nat) (f : Bool) (j : Nat) (h : j ≠ s.nParents) :
    ((step b s (.parent q f)).1.parents j).cum = (s.parents j).cum := by
  simp [step, upd, h]

theorem cumParentNew_aux (s : State) (b : Build) (q : Nat) (f : Bool) :
    ((step b s (.parent q f)).1.parents s.nParents).cum = 0 := by simp [step, upd]

theorem outParent_aux (s : State) (b : Build) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).2 = ([] : List Child) := by simp [step]

theorem trParentKids_aux (t : Truth) (q : Nat) (f : Bool) :
    (t.observe (.parent q f)).kids = t.kids := by rfl

theorem trParentExec_aux (t : Truth) (q : Nat) (f : Bool) (id : Nat) :
    (t.observe (.parent q f)).exec id = t.exec id := by rfl

theorem trParentNOrd_aux (t : Truth) (q : Nat) (f : Bool) :
    (t.observe (.parent q f)).nOrders = t.nOrders + 1 := by simp [Truth.observe]

theorem nChildRoute_aux (s : State) (b : Build) (id liq : Nat) :
    (step b s (.route id liq)).1.nChildren =
    (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then s.nChildren + 1 else s.nChildren) := by
  simp only [step]; split <;> rfl

theorem nChildFillSome_aux (s : State) (b : Build) (k q : Nat) (hk : k < s.nChildren) :
    (step b s (.fill k q)).1.nChildren = s.nChildren := by rw [step_fill_some b s k q hk]

theorem nChildFillNone_aux (s : State) (b : Build) (k q : Nat) (hk : ¬ k < s.nChildren) :
    (step b s (.fill k q)).1.nChildren = s.nChildren := by rw [step_fill_noop b s k q hk]

theorem nChildAck_aux (s : State) (b : Build) (k : Nat) :
    (step b s (.ack k)).1.nChildren = s.nChildren := by simp [step_ack_eq b s k]

theorem kidsLenParent_aux (t : Truth) (q : Nat) (f : Bool) (out : List Child) :
    (((t.observe (.parent q f)).record out).kids.length) = t.kids.length + out.length := by simp [Truth.observe, Truth.record]

theorem kidsLenRoute_aux (t : Truth) (id liq : Nat) (out : List Child) :
    (((t.observe (.route id liq)).record out).kids.length) = t.kids.length + out.length := by simp [Truth.observe, Truth.record]

theorem kidsLenAck_aux (t : Truth) (k : Nat) (out : List Child) :
    (((t.observe (.ack k)).record out).kids.length) = t.kids.length + out.length := by simp [Truth.observe, Truth.record]

theorem kidsLenFillNil_aux (t : Truth) (k q : Nat) :
    (((t.observe (.fill k q)).record ([] : List Child)).kids.length) = t.kids.length := by
  simp [Truth.record, obs_fill_kids_len]

theorem getAppLeft_aux (l : List Kid) (l₂ : List Kid) (k : Nat) (h : k < l.length) :
    (l ++ l₂)[k]? = l[k]? := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ k => simp at h ⊢; exact ih k h

theorem cumRouteTrue_aux (s : State) (id liq j : Nat)
    (hcond : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) :
    ((step arbitrary s (.route id liq)).1.parents j).cum = (s.parents j).cum := by
  simp only [step]
  simp [hcond]
  by_cases heq : j = id <;> simp [heq, upd]

theorem cumRouteFalse_aux (s : State) (id liq j : Nat)
    (hcond : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    ((step arbitrary s (.route id liq)).1.parents j).cum = (s.parents j).cum := by
  simp only [step]
  simp [hcond]

theorem childRouteTrueOld_aux (s : State) (b : Build) (rid liq k : Nat)
    (hcond : rid < s.nParents ∧ 0 < min liq ((s.parents rid).qty - (s.parents rid).sent))
    (hne : k ≠ s.nChildren) :
    (step b s (.route rid liq)).1.children k = s.children k := by
  simp only [step]
  simp [hcond, upd, hne]

theorem childRouteTrueNew_aux (s : State) (b : Build) (rid liq : Nat)
    (hcond : rid < s.nParents ∧ 0 < min liq ((s.parents rid).qty - (s.parents rid).sent)) :
    (step b s (.route rid liq)).1.children s.nChildren = ⟨rid, min liq ((s.parents rid).qty - (s.parents rid).sent), 0⟩ := by
  simp only [step]
  simp [hcond, upd]

theorem childRouteFalse_aux (s : State) (b : Build) (rid liq k : Nat)
    (hcond : ¬ (rid < s.nParents ∧ 0 < min liq ((s.parents rid).qty - (s.parents rid).sent))) :
    (step b s (.route rid liq)).1.children k = s.children k := by
  simp only [step]
  simp [hcond]



theorem plan5_advance_parent_key (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.parent q f)).st.nParents =
        (advance step b x (.parent q f)).tr.nOrders ∧
      (advance step b x (.parent q f)).st.nChildren =
        (advance step b x (.parent q f)).tr.kids.length ∧
      (∀ k, k < (advance step b x (.parent q f)).tr.kids.length →
        ∃ c, (advance step b x (.parent q f)).tr.kids[k]? = some c ∧
          (advance step b x (.parent q f)).st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.parent q f)).tr.nOrders →
        ((advance step b x (.parent q f)).st.parents id).cum =
          (advance step b x (.parent q f)).tr.exec id) ∧
      ∀ k ∈ (advance step b x (.parent q f)).tr.kids,
        k.parent < (advance step b x (.parent q f)).tr.nOrders := by
  obtain ⟨hnP, hnC, hchild, hcum, hkb⟩ := h
  have hst1 : (step b x.st (.parent q f)).1 = ({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State) := by simp [step]
  have hout : (step b x.st (.parent q f)).2 = ([] : List Child) := outParent_aux x.st b q f
  have hadvSt : (advance step b x (.parent q f)).st = (step b x.st (.parent q f)).1 := by simp [advance]
  have hadvTr : (advance step b x (.parent q f)).tr = (x.tr.observe (.parent q f)).record ([] : List Child) := by simp [advance, hout]
  have hNOrd : ((x.tr.observe (.parent q f)).record ([] : List Child)).nOrders = x.tr.nOrders + 1 := by simp [Truth.record, Truth.observe]
  have hKidsEq : ((x.tr.observe (.parent q f)).record ([] : List Child)).kids = x.tr.kids := by simp [Truth.record, Truth.observe]
  have hN : (advance step b x (.parent q f)).st.nParents = (advance step b x (.parent q f)).tr.nOrders := by rw [hadvSt, hadvTr, hst1, hNOrd, hnP]
  refine ⟨hN, ?_, ?_, ?_, ?_⟩
  · have hC1 : (advance step b x (.parent q f)).st.nChildren = x.st.nChildren := by rw [hadvSt, hst1]
    have hC2 : (advance step b x (.parent q f)).tr.kids.length = x.tr.kids.length := by rw [hadvTr, hKidsEq]
    rw [hC1, hC2, hnC]
  · intro k hk
    rw [hadvTr, hKidsEq] at hk
    obtain ⟨c, hcGet, hcSt⟩ := hchild k hk
    refine ⟨c, ?_, ?_⟩
    · rw [hadvTr, hKidsEq]; exact hcGet
    · have hch : (advance step b x (.parent q f)).st.children k = x.st.children k := by rw [hadvSt, hst1]
      rw [hch]; exact hcSt
  · intro id hid
    rw [hadvTr, hNOrd] at hid
    have hExecTr : (advance step b x (.parent q f)).tr.exec id = x.tr.exec id := by
      rw [hadvTr]
      have e1 : (((x.tr.observe (.parent q f)).record ([] : List Child)).exec id) = ((x.tr.observe (.parent q f)).exec id) := execRecNil_aux _ _
      have e2 : ((x.tr.observe (.parent q f)).exec id) = x.tr.exec id := trParentExec_aux _ _ _ _
      rw [e1, e2]
    rw [hExecTr]
    have hStCum : ((advance step b x (.parent q f)).st.parents id).cum = (if id = x.st.nParents then 0 else (x.st.parents id).cum) := by
      have : ((advance step b x (.parent q f)).st.parents id) = ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id) := by rw [hadvSt, hst1]
      rw [this]
      by_cases heq : id = x.st.nParents <;> simp [upd, heq]
    by_cases heq : id = x.st.nParents
    · rw [hStCum, if_pos heq]
      have hidEq : id = x.tr.nOrders := by omega
      subst hidEq
      have hz : execFor x.tr.kids x.tr.nOrders = 0 := execZero_of_bound x.tr.kids x.tr.nOrders hkb _ (Nat.le_refl _)
      simp only [Truth.exec, hz]
    · rw [hStCum, if_neg heq]
      have hlt : id < x.tr.nOrders := by omega
      exact hcum id hlt
  · intro k hk
    rw [hadvTr, hKidsEq] at hk
    rw [hadvTr, hNOrd]
    have := hkb k hk
    omega










theorem plan5_exec_observe_fill (t : Truth) (k q : Nat) (c : Kid)
    (hc : t.kids[k]? = some c) (id : Nat) :
    (t.observe (.fill k q)).exec id =
      t.exec id + (if c.parent = id then min q (c.qty - c.done) else 0) := by
  simp only [Truth.observe, hc, Truth.exec]
  exact execFor_set_done t.kids k c (min q (c.qty - c.done)) hc id

theorem plan5_advance_parent_key_proof (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.parent q f)).st.nParents =
        (advance step b x (.parent q f)).tr.nOrders ∧
      (advance step b x (.parent q f)).st.nChildren =
        (advance step b x (.parent q f)).tr.kids.length ∧
      (∀ k, k < (advance step b x (.parent q f)).tr.kids.length →
        ∃ c, (advance step b x (.parent q f)).tr.kids[k]? = some c ∧
          (advance step b x (.parent q f)).st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.parent q f)).tr.nOrders →
        ((advance step b x (.parent q f)).st.parents id).cum =
          (advance step b x (.parent q f)).tr.exec id) ∧
      ∀ k ∈ (advance step b x (.parent q f)).tr.kids,
        k.parent < (advance step b x (.parent q f)).tr.nOrders := by
  obtain ⟨hnP, hnC, hchild, hcum, hkb⟩ := h
  have hst1 : (step b x.st (.parent q f)).1 = ({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State) := by simp [step]
  have hout : (step b x.st (.parent q f)).2 = ([] : List Child) := outParent_aux x.st b q f
  have hadvSt : (advance step b x (.parent q f)).st = (step b x.st (.parent q f)).1 := by simp [advance]
  have hadvTr : (advance step b x (.parent q f)).tr = (x.tr.observe (.parent q f)).record ([] : List Child) := by simp [advance, hout]
  have hNOrd : ((x.tr.observe (.parent q f)).record ([] : List Child)).nOrders = x.tr.nOrders + 1 := by simp [Truth.record, Truth.observe]
  have hKidsEq : ((x.tr.observe (.parent q f)).record ([] : List Child)).kids = x.tr.kids := by simp [Truth.record, Truth.observe]
  have hN : (advance step b x (.parent q f)).st.nParents = (advance step b x (.parent q f)).tr.nOrders := by
    rw [hadvSt, hadvTr, hst1, hNOrd, hnP]
  refine ⟨hN, ?_, ?_, ?_, ?_⟩
  · have hC1 : (advance step b x (.parent q f)).st.nChildren = x.st.nChildren := by rw [hadvSt, hst1]
    have hC2 : (advance step b x (.parent q f)).tr.kids.length = x.tr.kids.length := by rw [hadvTr, hKidsEq]
    rw [hC1, hC2, hnC]
  · intro k hk
    rw [hadvTr, hKidsEq] at hk
    obtain ⟨c, hcGet, hcSt⟩ := hchild k hk
    refine ⟨c, ?_, ?_⟩
    · rw [hadvTr, hKidsEq]; exact hcGet
    · have hch : (advance step b x (.parent q f)).st.children k = x.st.children k := by
        rw [hadvSt, hst1]
      rw [hch]; exact hcSt
  · intro id hid
    rw [hadvTr, hNOrd] at hid
    have hExecTr : (advance step b x (.parent q f)).tr.exec id = x.tr.exec id := by
      rw [hadvTr]
      have e1 : (((x.tr.observe (.parent q f)).record ([] : List Child)).exec id) = ((x.tr.observe (.parent q f)).exec id) := execRecNil_aux _ _
      have e2 : ((x.tr.observe (.parent q f)).exec id) = x.tr.exec id := trParentExec_aux _ _ _ _
      rw [e1, e2]
    rw [hExecTr]
    have hStCum : ((advance step b x (.parent q f)).st.parents id).cum = (if id = x.st.nParents then 0 else (x.st.parents id).cum) := by
      have : ((advance step b x (.parent q f)).st.parents id) = ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id) := by rw [hadvSt, hst1]
      rw [this]
      by_cases heq : id = x.st.nParents <;> simp [upd, heq]
    by_cases heq : id = x.st.nParents
    · rw [hStCum, if_pos heq]
      have hidEq : id = x.tr.nOrders := by omega
      subst hidEq
      have hz : execFor x.tr.kids x.tr.nOrders = 0 :=
        execZero_of_bound x.tr.kids x.tr.nOrders hkb _ (Nat.le_refl _)
      simp only [Truth.exec, hz]
    · rw [hStCum, if_neg heq]
      have hlt : id < x.tr.nOrders := by omega
      exact hcum id hlt
  · intro k hk
    rw [hadvTr, hKidsEq] at hk
    rw [hadvTr, hNOrd]
    have := hkb k hk
    omega

theorem plan5_advance_parent_key_dup : True := trivial

theorem negBranchInline (b : Build) (x : Sys) (rid liq : Nat)
    (hnP : x.st.nParents = x.tr.nOrders)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩)
    (hcum : ∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id)
    (hkb : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)
    (hcond : ¬(rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent))) :
    (advance step b x (.route rid liq)).st.nParents =
        (advance step b x (.route rid liq)).tr.nOrders ∧
      (advance step b x (.route rid liq)).st.nChildren =
        (advance step b x (.route rid liq)).tr.kids.length ∧
      (∀ k, k < (advance step b x (.route rid liq)).tr.kids.length →
        ∃ c, (advance step b x (.route rid liq)).tr.kids[k]? = some c ∧
          (advance step b x (.route rid liq)).st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.route rid liq)).tr.nOrders →
        ((advance step b x (.route rid liq)).st.parents id).cum =
          (advance step b x (.route rid liq)).tr.exec id) ∧
      ∀ k ∈ (advance step b x (.route rid liq)).tr.kids,
        k.parent < (advance step b x (.route rid liq)).tr.nOrders := by
  have h1 : (step b x.st (.route rid liq)).1 = x.st := by
    unfold step
    simp [hcond]
  have h2 : (step b x.st (.route rid liq)).2 = ([] : List Child) := by
    unfold step
    simp [hcond]
  have hSt : (advance step b x (.route rid liq)).st = x.st := by simp [advance, h1]
  have hTr : (advance step b x (.route rid liq)).tr = x.tr := by
    simp [advance, h2, obs_route_eq, Truth.record]
  rw [hSt, hTr]
  exact ⟨hnP, hnC, hchild, hcum, hkb⟩

theorem negBranchUse (b : Build) (x : Sys) (rid liq : Nat)
    (hnP : x.st.nParents = x.tr.nOrders)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩)
    (hcum : ∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id)
    (hkb : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)
    (hcond : ¬(rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent))) :
    (advance step b x (.route rid liq)).st.nParents =
        (advance step b x (.route rid liq)).tr.nOrders ∧
      (advance step b x (.route rid liq)).st.nChildren =
        (advance step b x (.route rid liq)).tr.kids.length ∧
      (∀ k, k < (advance step b x (.route rid liq)).tr.kids.length →
        ∃ c, (advance step b x (.route rid liq)).tr.kids[k]? = some c ∧
          (advance step b x (.route rid liq)).st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.route rid liq)).tr.nOrders →
        ((advance step b x (.route rid liq)).st.parents id).cum =
          (advance step b x (.route rid liq)).tr.exec id) ∧
      ∀ k ∈ (advance step b x (.route rid liq)).tr.kids,
        k.parent < (advance step b x (.route rid liq)).tr.nOrders :=
  negBranchInline b x rid liq hnP hnC hchild hcum hkb hcond

theorem cumPosCheck (b : Build) (x : Sys) (rid liq : Nat)
    (hcum : ∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id)
    (hcond : rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent))
    (hadvSt : (advance step b x (.route rid liq)).st = (step b x.st (.route rid liq)).1)
    (hadvTr : (advance step b x (.route rid liq)).tr = (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]))
    (hTrN : (advance step b x (.route rid liq)).tr.nOrders = x.tr.nOrders) :
    ∀ id, id < (advance step b x (.route rid liq)).tr.nOrders →
      ((advance step b x (.route rid liq)).st.parents id).cum =
        (advance step b x (.route rid liq)).tr.exec id := by
  intro id hid
  rw [hTrN] at hid
  have hStCum : ((advance step b x (.route rid liq)).st.parents id).cum = (x.st.parents id).cum := by
    rw [hadvSt]
    exact cumRouteTrue_aux x.st rid liq id hcond
  have hTrExec : (advance step b x (.route rid liq)).tr.exec id = x.tr.exec id := by
    rw [hadvTr]
    exact execRecSingle_aux x.tr rid _ id
  rw [hStCum, hTrExec]
  exact hcum id hid











theorem plan6_route_neg_advance_eq (b : Build) (x : Sys) (rid liq : Nat)
    (hcond : ¬ (rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent))) :
    advance step b x (.route rid liq) = x := by
  obtain ⟨st, tr⟩ := x
  have hstep : step b st (.route rid liq) = (st, []) := by
    simp [step, hcond]
  have hobs : tr.observe (.route rid liq) = tr := obs_route_eq _ _ _
  have hrec : (tr.record ([] : List Child)) = tr := by
    cases tr with
    | mk nO q ks => simp [Truth.record]
  simp [advance, hstep, hobs, hrec]

theorem tmp_pos_adv : ∀ (b : Build) (x : Sys) (rid liq : Nat),
    (rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) →
    (advance step b x (.route rid liq)).st = (step b x.st (.route rid liq)).1 ∧
      (advance step b x (.route rid liq)).tr =
        x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩] := by
  intro b x rid liq hcond
  have hout : (step b x.st (.route rid liq)).2 = [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩] := by
    simp [step, hcond]
  constructor
  · rfl
  · show (x.tr.observe (.route rid liq)).record ((step b x.st (.route rid liq)).2) = _
    rw [obs_route_eq, hout]

theorem plan6_route_pos_advance_eq (b : Build) (x : Sys) (rid liq : Nat)
    (hcond : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st =
        (step b x.st (.route rid liq)).1 ∧
      (advance step b x (.route rid liq)).tr =
        x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩] :=
  tmp_pos_adv b x rid liq hcond

theorem plan6_route_pos_children_helperA : True := trivial

theorem plan6_route_pos_children (b : Build) (x : Sys) (rid liq : Nat)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ k, k < x.tr.kids.length →
      ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩)
    (hcond : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    ∀ k, k < x.tr.kids.length + 1 →
      ∃ c, ((x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids)[k]? = some c ∧
        (step b x.st (.route rid liq)).1.children k = ⟨c.parent, c.qty, c.done⟩ := by
  intro k hk
  have hKidsEq : ((x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids) = x.tr.kids ++ [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩] := by
    simp [Truth.record]
  by_cases hlt : k < x.tr.kids.length
  · obtain ⟨c, hcGet, hcSt⟩ := hchild k hlt
    refine ⟨c, ?_, ?_⟩
    · have hmap : ((x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids)[k]? = x.tr.kids[k]? := by
        rw [hKidsEq]
        exact getAppLeft_aux x.tr.kids [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩] k hlt
      rw [hmap, hcGet]
    · have hne : k ≠ x.st.nChildren := by omega
      have hch : (step b x.st (.route rid liq)).1.children k = x.st.children k :=
        childRouteTrueOld_aux x.st b rid liq k hcond hne
      rw [hch, hcSt]
  · have hkeq : k = x.tr.kids.length := by omega
    subst hkeq
    refine ⟨⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩, ?_, ?_⟩
    · rw [hKidsEq]
      simp
    · have hchNew : (step b x.st (.route rid liq)).1.children x.st.nChildren =
        (⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec) := childRouteTrueNew_aux x.st b rid liq hcond
      have hkeq2 : x.tr.kids.length = x.st.nChildren := hnC.symm
      rw [hkeq2]
      exact hchNew

theorem plan6_route_pos_lengths_bounds_proof_tmp (b : Build) (x : Sys) (rid liq : Nat)
    (hnP : x.st.nParents = x.tr.nOrders)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hkb : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)
    (hcond : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nParents =
        (advance step b x (.route rid liq)).tr.nOrders ∧
      (advance step b x (.route rid liq)).st.nChildren =
        (advance step b x (.route rid liq)).tr.kids.length ∧
      ∀ k ∈ (advance step b x (.route rid liq)).tr.kids,
        k.parent < (advance step b x (.route rid liq)).tr.nOrders := by
  obtain ⟨hadvStEq, hadvTrEq⟩ := tmp_pos_adv b x rid liq hcond
  have hridLt : rid < x.tr.nOrders := by omega
  have hnS : (step b x.st (.route rid liq)).1.nParents = x.st.nParents :=
    tmp_route_nPar b x.st rid liq
  have hnCpos : (step b x.st (.route rid liq)).1.nChildren = x.st.nChildren + 1 := by
    have h := nChildRoute_aux x.st b rid liq
    rw [if_pos hcond] at h
    exact h
  have hTrN : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).nOrders = x.tr.nOrders := by
    exact nOrdersRec_aux2 _ _
  have hTrLen : ((x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids.length) = x.tr.kids.length + 1 := by
    exact rec_single_kids_len _ _
  have h1 : (advance step b x (.route rid liq)).st.nParents = (advance step b x (.route rid liq)).tr.nOrders := by
    rw [hadvStEq, hadvTrEq, hnS, hTrN, hnP]
  have h2 : (advance step b x (.route rid liq)).st.nChildren = (advance step b x (.route rid liq)).tr.kids.length := by
    rw [hadvStEq, hadvTrEq, hnCpos, hTrLen, hnC]
  refine ⟨h1, h2, ?_⟩
  rw [hadvTrEq]
  have hbound := plan1_kids_bound_record x.tr [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩] hkb ?_ 
  · exact hbound
  · intro c hc
    simp at hc
    subst hc
    exact hridLt

theorem plan6_route_pos_lengths_bounds (b : Build) (x : Sys) (rid liq : Nat)
    (hnP : x.st.nParents = x.tr.nOrders)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hkb : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)
    (hcond : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nParents =
        (advance step b x (.route rid liq)).tr.nOrders ∧
      (advance step b x (.route rid liq)).st.nChildren =
        (advance step b x (.route rid liq)).tr.kids.length ∧
      ∀ k ∈ (advance step b x (.route rid liq)).tr.kids,
        k.parent < (advance step b x (.route rid liq)).tr.nOrders := by
  obtain ⟨hadvStEq, hadvTrEq⟩ := tmp_pos_adv b x rid liq hcond
  have hridLt : rid < x.tr.nOrders := by omega
  have hnS : (step b x.st (.route rid liq)).1.nParents = x.st.nParents :=
    tmp_route_nPar b x.st rid liq
  have hnCpos : (step b x.st (.route rid liq)).1.nChildren = x.st.nChildren + 1 := by
    have h := nChildRoute_aux x.st b rid liq
    rw [if_pos hcond] at h
    exact h
  have hTrN : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).nOrders = x.tr.nOrders := by
    exact nOrdersRec_aux2 _ _
  have hTrLen : ((x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids.length) = x.tr.kids.length + 1 := by
    exact rec_single_kids_len _ _
  have h1 : (advance step b x (.route rid liq)).st.nParents = (advance step b x (.route rid liq)).tr.nOrders := by
    rw [hadvStEq, hadvTrEq, hnS, hTrN, hnP]
  have h2 : (advance step b x (.route rid liq)).st.nChildren = (advance step b x (.route rid liq)).tr.kids.length := by
    rw [hadvStEq, hadvTrEq, hnCpos, hTrLen, hnC]
  refine ⟨h1, h2, ?_⟩
  rw [hadvTrEq]
  exact plan1_kids_bound_record x.tr [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩] hkb (by intro c hc; simp at hc; subst hc; exact hridLt)

theorem plan6_route_pos_cum_proof_tmp (b : Build) (x : Sys) (rid liq : Nat)
    (hcum : ∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id)
    (hcond : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    ∀ id, id < (advance step b x (.route rid liq)).tr.nOrders →
      ((advance step b x (.route rid liq)).st.parents id).cum =
        (advance step b x (.route rid liq)).tr.exec id := by
  intro id hid
  obtain ⟨hadvStEq, hadvTrEq⟩ := tmp_pos_adv b x rid liq hcond
  have hTrN : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).nOrders = x.tr.nOrders :=
    nOrdersRec_aux2 _ _
  have hidOld : id < x.tr.nOrders := by
    have : id < (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).nOrders := by
      rw [← hadvTrEq]; exact hid
    rw [hTrN] at this
    exact this
  have hStCum : ((advance step b x (.route rid liq)).st.parents id).cum = (x.st.parents id).cum := by
    rw [hadvStEq]
    exact cumRouteTrue_aux x.st rid liq id hcond
  have hTrExec : (advance step b x (.route rid liq)).tr.exec id = x.tr.exec id := by
    rw [hadvTrEq]
    exact execRecSingle_aux x.tr rid _ id
  rw [hStCum, hTrExec]
  exact hcum id hidOld

theorem plan6_route_pos_cum (b : Build) (x : Sys) (rid liq : Nat)
    (hcum : ∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id)
    (hcond : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    ∀ id, id < (advance step b x (.route rid liq)).tr.nOrders →
      ((advance step b x (.route rid liq)).st.parents id).cum =
        (advance step b x (.route rid liq)).tr.exec id :=
  plan6_route_pos_cum_proof_tmp b x rid liq hcum hcond

theorem plan5_advance_route_key_proof_tmp2 (b : Build) (x : Sys) (rid liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.route rid liq)).st.nParents =
        (advance step b x (.route rid liq)).tr.nOrders ∧
      (advance step b x (.route rid liq)).st.nChildren =
        (advance step b x (.route rid liq)).tr.kids.length ∧
      (∀ k, k < (advance step b x (.route rid liq)).tr.kids.length →
        ∃ c, (advance step b x (.route rid liq)).tr.kids[k]? = some c ∧
          (advance step b x (.route rid liq)).st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.route rid liq)).tr.nOrders →
        ((advance step b x (.route rid liq)).st.parents id).cum =
          (advance step b x (.route rid liq)).tr.exec id) ∧
      ∀ k ∈ (advance step b x (.route rid liq)).tr.kids,
        k.parent < (advance step b x (.route rid liq)).tr.nOrders := by
  obtain ⟨hnP, hnC, hchild, hcum, hkb⟩ := h
  by_cases hcond : rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)
  · obtain ⟨hadvStEq, hadvTrEq⟩ := tmp_pos_adv b x rid liq hcond
    have hLens := plan6_route_pos_lengths_bounds b x rid liq hnP hnC hkb hcond
    obtain ⟨hN, hC, hkb'⟩ := hLens
    have hch := plan6_route_pos_children b x rid liq hnC hchild hcond
    have hcum' := plan6_route_pos_cum b x rid liq hcum hcond
    refine ⟨hN, hC, ?_, hcum', hkb'⟩
    intro k hk
    have hk2 : k < x.tr.kids.length + 1 := by
      have : k < ((x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids.length) := by
        rw [← hadvTrEq]; exact hk
      rw [rec_single_kids_len] at this
      exact this
    obtain ⟨c, hcGet, hcSt⟩ := hch k hk2
    refine ⟨c, ?_, ?_⟩
    · rw [← hadvTrEq] at hcGet
      exact hcGet
    · rw [← hadvStEq] at hcSt
      exact hcSt
  · exact negBranchInline b x rid liq hnP hnC hchild hcum hkb hcond

theorem plan5_advance_route_key_check_tmp (b : Build) (x : Sys) (rid liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.route rid liq)).st.nParents =
        (advance step b x (.route rid liq)).tr.nOrders ∧
      (advance step b x (.route rid liq)).st.nChildren =
        (advance step b x (.route rid liq)).tr.kids.length ∧
      (∀ k, k < (advance step b x (.route rid liq)).tr.kids.length →
        ∃ c, (advance step b x (.route rid liq)).tr.kids[k]? = some c ∧
          (advance step b x (.route rid liq)).st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.route rid liq)).tr.nOrders →
        ((advance step b x (.route rid liq)).st.parents id).cum =
          (advance step b x (.route rid liq)).tr.exec id) ∧
      ∀ k ∈ (advance step b x (.route rid liq)).tr.kids,
        k.parent < (advance step b x (.route rid liq)).tr.nOrders := by
  obtain ⟨hnP, hnC, hchild, hcum, hkb⟩ := h
  by_cases hcond : rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)
  · obtain ⟨hadvStEq, hadvTrEq⟩ := tmp_pos_adv b x rid liq hcond
    have hLens := plan6_route_pos_lengths_bounds b x rid liq hnP hnC hkb hcond
    obtain ⟨hN, hC, hkb'⟩ := hLens
    have hch := plan6_route_pos_children b x rid liq hnC hchild hcond
    have hcum' := plan6_route_pos_cum b x rid liq hcum hcond
    refine ⟨hN, hC, ?_, hcum', hkb'⟩
    intro k hk
    have hk2 : k < x.tr.kids.length + 1 := by
      have : k < ((x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids.length) := by
        rw [← hadvTrEq]; exact hk
      rw [rec_single_kids_len] at this
      exact this
    obtain ⟨c, hcGet, hcSt⟩ := hch k hk2
    refine ⟨c, ?_, ?_⟩
    · rw [← hadvTrEq] at hcGet
      exact hcGet
    · rw [← hadvStEq] at hcSt
      exact hcSt
  · exact negBranchInline b x rid liq hnP hnC hchild hcum hkb hcond

theorem plan5_advance_route_key (b : Build) (x : Sys) (rid liq : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.route rid liq)).st.nParents =
        (advance step b x (.route rid liq)).tr.nOrders ∧
      (advance step b x (.route rid liq)).st.nChildren =
        (advance step b x (.route rid liq)).tr.kids.length ∧
      (∀ k, k < (advance step b x (.route rid liq)).tr.kids.length →
        ∃ c, (advance step b x (.route rid liq)).tr.kids[k]? = some c ∧
          (advance step b x (.route rid liq)).st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.route rid liq)).tr.nOrders →
        ((advance step b x (.route rid liq)).st.parents id).cum =
          (advance step b x (.route rid liq)).tr.exec id) ∧
      ∀ k ∈ (advance step b x (.route rid liq)).tr.kids,
        k.parent < (advance step b x (.route rid liq)).tr.nOrders :=
  plan5_advance_route_key_proof_tmp2 b x rid liq h

theorem ack_key_tmp_proof (b : Build) (x : Sys) (k : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.ack k)).st.nParents =
        (advance step b x (.ack k)).tr.nOrders ∧
      (advance step b x (.ack k)).st.nChildren =
        (advance step b x (.ack k)).tr.kids.length ∧
      (∀ j, j < (advance step b x (.ack k)).tr.kids.length →
        ∃ c, (advance step b x (.ack k)).tr.kids[j]? = some c ∧
          (advance step b x (.ack k)).st.children j = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.ack k)).tr.nOrders →
        ((advance step b x (.ack k)).st.parents id).cum =
          (advance step b x (.ack k)).tr.exec id) ∧
      ∀ j ∈ (advance step b x (.ack k)).tr.kids,
        j.parent < (advance step b x (.ack k)).tr.nOrders := by
  have hstep : step b x.st (.ack k) = (x.st, []) := step_ack_eq b x.st k
  have hobs : x.tr.observe (.ack k) = x.tr := obs_ack_eq x.tr k
  have hadvSt : (advance step b x (.ack k)).st = x.st := by simp [advance, hstep]
  have hadvTr : (advance step b x (.ack k)).tr = x.tr := by
    simp only [advance, hstep, hobs]
    cases x with
    | mk st tr =>
      simp [Truth.record]
  rw [hadvSt, hadvTr]
  exact h

theorem plan5_advance_ack_key (b : Build) (x : Sys) (k : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.ack k)).st.nParents =
        (advance step b x (.ack k)).tr.nOrders ∧
      (advance step b x (.ack k)).st.nChildren =
        (advance step b x (.ack k)).tr.kids.length ∧
      (∀ j, j < (advance step b x (.ack k)).tr.kids.length →
        ∃ c, (advance step b x (.ack k)).tr.kids[j]? = some c ∧
          (advance step b x (.ack k)).st.children j = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.ack k)).tr.nOrders →
        ((advance step b x (.ack k)).st.parents id).cum =
          (advance step b x (.ack k)).tr.exec id) ∧
      ∀ j ∈ (advance step b x (.ack k)).tr.kids,
        j.parent < (advance step b x (.ack k)).tr.nOrders :=
  ack_key_tmp_proof b x k h

theorem probe_cum_simp (s : State) (k q id : Nat) :
    (({ s with parents := upd s.parents (s.children k).parent { (s.parents (s.children k).parent) with cum := (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) } } : State).parents id).cum =
    (if id = (s.children k).parent then (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) else (s.parents id).cum) := by
  simp only [upd]
  by_cases heq : id = (s.children k).parent <;> simp [heq]

theorem probe_cum_full (b : Build) (s : State) (k q id : Nat) (hk : k < s.nChildren) :
    (((step b s (.fill k q)).fst.parents id).cum =
    (if id = (s.children k).parent then (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) else (s.parents id).cum)) := by
  rw [step_fill_some b s k q hk]
  by_cases heq : id = (s.children k).parent <;> simp [heq, upd]

theorem tmp_getset_test (l : List Kid) (kk j : Nat) (c0 c : Kid) (hcGet : l[j]? = some c) (hne : kk ≠ j) :
    ((l.set kk c0)[j]? = some c) := by
  rw [List.getElem?_set, if_neg hne, hcGet]

theorem plan7_fill_step_children (b : Build) (s : State) (k q j : Nat)
    (hk : k < s.nChildren) :
    (step b s (.fill k q)).1.children j =
      (if j = k then
        { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) }
       else s.children j) := by
  have hstep := step_fill_some b s k q hk
  have h1 : (step b s (.fill k q)).1.children j = (upd s.children k { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) }) j := by
    rw [hstep]
  rw [h1]
  unfold upd
  split <;> rfl




theorem plan7_fill_children_after (b : Build) (x : Sys) (k q : Nat)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ j, j < x.tr.kids.length →
      ∃ c, x.tr.kids[j]? = some c ∧ x.st.children j = ⟨c.parent, c.qty, c.done⟩)
    (hk : k < x.st.nChildren) :
    ∀ j, j < (advance step b x (.fill k q)).tr.kids.length →
      ∃ c, (advance step b x (.fill k q)).tr.kids[j]? = some c ∧
        (advance step b x (.fill k q)).st.children j = ⟨c.parent, c.qty, c.done⟩ := by
  have set_get : ∀ (l : List Kid) (kk jj : Nat) (d : Kid), kk < l.length →
      (l.set kk d)[jj]? = (if jj = kk then some d else l[jj]?) := by
    intro l kk jj d hkk
    induction l generalizing kk jj with
    | nil => simp at hkk
    | cons a as ih =>
      cases kk with
      | zero =>
        cases jj with
        | zero => simp
        | succ jj => simp
      | succ kk =>
        cases jj with
        | zero => simp
        | succ jj =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hkk
          simp only [List.set_cons_succ, List.getElem?_cons_succ, Nat.succ_inj]
          rw [ih _ _ hkk]
  have child_eq : ∀ jj, (step b x.st (.fill k q)).1.children jj =
      (if jj = k then { x.st.children k with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } else x.st.children jj) := by
    intro jj
    have hstep := step_fill_some b x.st k q hk
    have h1 : (step b x.st (.fill k q)).1.children jj = (upd x.st.children k { x.st.children k with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }) jj := by
      rw [hstep]
    rw [h1]
    unfold upd
    split <;> rfl
  intro j hj
  have hk_len : k < x.tr.kids.length := by omega
  obtain ⟨c0, hc0Get, hc0St⟩ := hchild k hk_len
  have hout : (step b x.st (.fill k q)).2 = ([] : List Child) := by
    rw [step_fill_some b x.st k q hk]
  have hadvSt : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := by simp [advance]
  have hadvTrKids : (advance step b x (.fill k q)).tr.kids = (x.tr.observe (.fill k q)).kids := by
    simp [advance, hout, Truth.record]
  have hobsKids : (x.tr.observe (.fill k q)).kids = x.tr.kids.set k { c0 with done := c0.done + min q (c0.qty - c0.done) } := by
    simp [Truth.observe, hc0Get]
  have hlen : (advance step b x (.fill k q)).tr.kids.length = x.tr.kids.length := by
    rw [hadvTrKids, hobsKids, List.length_set]
  have hj_old : j < x.tr.kids.length := by omega
  by_cases heq : j = k
  · refine ⟨{ c0 with done := c0.done + min q (c0.qty - c0.done) }, ?_, ?_⟩
    · rw [hadvTrKids, hobsKids, heq, set_get x.tr.kids k k _ hk_len, if_pos rfl]
    · rw [hadvSt, heq, child_eq k, if_pos rfl, hc0St]
  · obtain ⟨cj, hcjGet, hcjSt⟩ := hchild j hj_old
    refine ⟨cj, ?_, ?_⟩
    · rw [hadvTrKids, hobsKids, set_get x.tr.kids k j _ hk_len, if_neg heq, hcjGet]
    · rw [hadvSt, child_eq j, if_neg heq, hcjSt]


theorem plan7_fill_cum_after (b : Build) (x : Sys) (k q : Nat)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ j, j < x.tr.kids.length →
      ∃ c, x.tr.kids[j]? = some c ∧ x.st.children j = ⟨c.parent, c.qty, c.done⟩)
    (hcum : ∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id)
    (hk : k < x.st.nChildren) :
    ∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
      ((advance step b x (.fill k q)).st.parents id).cum =
        (advance step b x (.fill k q)).tr.exec id := by sorry



theorem plan7_fill_step_children_fixed2 (b : Build) (s : State) (k q j : Nat)
    (hk : k < s.nChildren) :
    (step b s (.fill k q)).1.children j =
      (if j = k then
        { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) }
       else s.children j) := by
  have hstep := step_fill_some b s k q hk
  have h1 : (step b s (.fill k q)).1.children j = (upd s.children k { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) }) j := by
    rw [hstep]
  rw [h1]
  unfold upd
  split <;> rfl

theorem plan7_fill_step_children_aux_check (b : Build) (s : State) (k q j : Nat)
    (hk : k < s.nChildren) :
    (step b s (.fill k q)).1.children j =
      (if j = k then
        { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) }
       else s.children j) := plan7_fill_step_children_fixed2 b s k q j hk

theorem plan7_probe_a (l : List Kid) (k : Nat) (d : Kid) (hk : k < l.length) :
    (l.set k d)[k]? = some d := by
  simp [hk]

theorem plan7_induct_test (l : List Kid) (k j : Nat) (d : Kid)
    (hk : k < l.length) :
    (l.set k d)[j]? = (if j = k then some d else l[j]?) := by
  induction l generalizing k j with
  | nil => simp at hk
  | cons a as ih =>
    cases k with
    | zero =>
      cases j with
      | zero => simp
      | succ j => simp
    | succ k =>
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
        simp only [List.set_cons_succ, List.getElem?_cons_succ, Nat.succ_inj]
        rw [ih _ _ hk]

theorem plan7_set_get_of_lt (l : List Kid) (k j : Nat) (d : Kid)
    (hk : k < l.length) :
    (l.set k d)[j]? = (if j = k then some d else l[j]?) :=
  plan7_induct_test l k j d hk

theorem plan7_fill_children_after_aux_check4_triv : True := trivial

theorem plan7_fill_children_after_direct (b : Build) (x : Sys) (k q : Nat)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ j, j < x.tr.kids.length →
      ∃ c, x.tr.kids[j]? = some c ∧ x.st.children j = ⟨c.parent, c.qty, c.done⟩)
    (hk : k < x.st.nChildren) :
    ∀ j, j < (advance step b x (.fill k q)).tr.kids.length →
      ∃ c, (advance step b x (.fill k q)).tr.kids[j]? = some c ∧
        (advance step b x (.fill k q)).st.children j = ⟨c.parent, c.qty, c.done⟩ := by
  intro j hj
  have hk_len : k < x.tr.kids.length := by omega
  obtain ⟨c0, hc0Get, hc0St⟩ := hchild k hk_len
  have hout : (step b x.st (.fill k q)).2 = ([] : List Child) := by
    rw [step_fill_some b x.st k q hk]
  have hadvSt : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := by simp [advance]
  have hadvTrKids : (advance step b x (.fill k q)).tr.kids = (x.tr.observe (.fill k q)).kids := by
    simp [advance, hout, Truth.record]
  have hobsKids : (x.tr.observe (.fill k q)).kids = x.tr.kids.set k { c0 with done := c0.done + min q (c0.qty - c0.done) } := by
    simp [Truth.observe, hc0Get]
  have hlen : (advance step b x (.fill k q)).tr.kids.length = x.tr.kids.length := by
    rw [hadvTrKids, hobsKids, List.length_set]
  have hj_old : j < x.tr.kids.length := by omega
  by_cases heq : j = k
  · refine ⟨{ c0 with done := c0.done + min q (c0.qty - c0.done) }, ?_, ?_⟩
    · rw [hadvTrKids, hobsKids, heq, plan7_set_get_of_lt x.tr.kids k k _ hk_len, if_pos rfl]
    · rw [hadvSt, heq, plan7_fill_step_children_fixed2 b x.st k q k hk, if_pos rfl, hc0St]
  · obtain ⟨cj, hcjGet, hcjSt⟩ := hchild j hj_old
    refine ⟨cj, ?_, ?_⟩
    · rw [hadvTrKids, hobsKids, plan7_set_get_of_lt x.tr.kids k j _ hk_len, if_neg heq, hcjGet]
    · rw [hadvSt, plan7_fill_step_children_fixed2 b x.st k q j hk, if_neg heq, hcjSt]

theorem plan7_set_get_inline_check (l : List Kid) (k j : Nat) (d : Kid) (hk : k < l.length) :
    (l.set k d)[j]? = (if j = k then some d else l[j]?) := by
  induction l generalizing k j with
  | nil => simp at hk
  | cons a as ih =>
    cases k with
    | zero =>
      cases j with
      | zero => simp
      | succ j => simp
    | succ k =>
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
        simp only [List.set_cons_succ, List.getElem?_cons_succ, Nat.succ_inj]
        rw [ih _ _ hk]

theorem check_set_lookup_sig (l : List Kid) (k j : Nat) (d : Kid) : (l.set k d)[j]? = (l.set k d)[j]? := rfl
#check @List.getElem?_set

theorem plan7_fill_children_after_selfcontained (b : Build) (x : Sys) (k q : Nat)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hchild : ∀ j, j < x.tr.kids.length →
      ∃ c, x.tr.kids[j]? = some c ∧ x.st.children j = ⟨c.parent, c.qty, c.done⟩)
    (hk : k < x.st.nChildren) :
    ∀ j, j < (advance step b x (.fill k q)).tr.kids.length →
      ∃ c, (advance step b x (.fill k q)).tr.kids[j]? = some c ∧
        (advance step b x (.fill k q)).st.children j = ⟨c.parent, c.qty, c.done⟩ := by
  have set_get : ∀ (l : List Kid) (kk jj : Nat) (d : Kid), kk < l.length →
      (l.set kk d)[jj]? = (if jj = kk then some d else l[jj]?) := by
    intro l kk jj d hkk
    induction l generalizing kk jj with
    | nil => simp at hkk
    | cons a as ih =>
      cases kk with
      | zero =>
        cases jj with
        | zero => simp
        | succ jj => simp
      | succ kk =>
        cases jj with
        | zero => simp
        | succ jj =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hkk
          simp only [List.set_cons_succ, List.getElem?_cons_succ, Nat.succ_inj]
          rw [ih _ _ hkk]
  have child_eq : ∀ jj, (step b x.st (.fill k q)).1.children jj =
      (if jj = k then { x.st.children k with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } else x.st.children jj) := by
    intro jj
    have hstep := step_fill_some b x.st k q hk
    have h1 : (step b x.st (.fill k q)).1.children jj = (upd x.st.children k { x.st.children k with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }) jj := by
      rw [hstep]
    rw [h1]
    unfold upd
    split <;> rfl
  intro j hj
  have hk_len : k < x.tr.kids.length := by omega
  obtain ⟨c0, hc0Get, hc0St⟩ := hchild k hk_len
  have hout : (step b x.st (.fill k q)).2 = ([] : List Child) := by
    rw [step_fill_some b x.st k q hk]
  have hadvSt : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := by simp [advance]
  have hadvTrKids : (advance step b x (.fill k q)).tr.kids = (x.tr.observe (.fill k q)).kids := by
    simp [advance, hout, Truth.record]
  have hobsKids : (x.tr.observe (.fill k q)).kids = x.tr.kids.set k { c0 with done := c0.done + min q (c0.qty - c0.done) } := by
    simp [Truth.observe, hc0Get]
  have hlen : (advance step b x (.fill k q)).tr.kids.length = x.tr.kids.length := by
    rw [hadvTrKids, hobsKids, List.length_set]
  have hj_old : j < x.tr.kids.length := by omega
  by_cases heq : j = k
  · refine ⟨{ c0 with done := c0.done + min q (c0.qty - c0.done) }, ?_, ?_⟩
    · rw [hadvTrKids, hobsKids, heq, set_get x.tr.kids k k _ hk_len, if_pos rfl]
    · rw [hadvSt, heq, child_eq k, if_pos rfl, hc0St]
  · obtain ⟨cj, hcjGet, hcjSt⟩ := hchild j hj_old
    refine ⟨cj, ?_, ?_⟩
    · rw [hadvTrKids, hobsKids, set_get x.tr.kids k j _ hk_len, if_neg heq, hcjGet]
    · rw [hadvSt, child_eq j, if_neg heq, hcjSt]

theorem getSome_lt_length_aux170 (l : List Kid) (k : Nat) (c : Kid) (h : l[k]? = some c) : k < l.length := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ k => simp at h ⊢; exact ih k h

theorem plan7_fill_advance_eq_of_not_lt (b : Build) (x : Sys) (k q : Nat)
    (hnC : x.st.nChildren = x.tr.kids.length)
    (hk : ¬ k < x.st.nChildren) :
    advance step b x (.fill k q) = x := by
  have hstep : step b x.st (.fill k q) = (x.st, []) := step_fill_noop b x.st k q hk
  have hkLen : ¬ k < x.tr.kids.length := by omega
  have hget : x.tr.kids[k]? = none := by
    cases hh : x.tr.kids[k]? with
    | none => rfl
    | some c =>
      have hlt := getSome_lt_length_aux170 x.tr.kids k c hh
      exact absurd hlt hkLen
  have hobs : x.tr.observe (.fill k q) = x.tr := by simp [Truth.observe, hget]
  obtain ⟨st, tr⟩ := x
  simp [advance, hstep, hobs, Truth.record]

theorem plan5_advance_fill_key (b : Build) (x : Sys) (k q : Nat)
    (h : x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
      (advance step b x (.fill k q)).st.nChildren =
        (advance step b x (.fill k q)).tr.kids.length ∧
      (∀ j, j < (advance step b x (.fill k q)).tr.kids.length →
        ∃ c, (advance step b x (.fill k q)).tr.kids[j]? = some c ∧
          (advance step b x (.fill k q)).st.children j = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents id).cum =
          (advance step b x (.fill k q)).tr.exec id) ∧
      ∀ j ∈ (advance step b x (.fill k q)).tr.kids,
        j.parent < (advance step b x (.fill k q)).tr.nOrders := by
  obtain ⟨hnP, hnC, hchild, hcum, hkb⟩ := h
  by_cases hk : k < x.st.nChildren
  · have hout : (step b x.st (.fill k q)).2 = ([] : List Child) := by
      rw [step_fill_some b x.st k q hk]
    have hadvSt : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := by simp [advance]
    have hadvTr : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record ([] : List Child) := by
      simp [advance, hout]
    have hstN : (step b x.st (.fill k q)).1.nParents = x.st.nChildren ∨ (step b x.st (.fill k q)).1.nParents = x.st.nParents := by
      right; rw [step_fill_some b x.st k q hk]
    have hNst : (step b x.st (.fill k q)).1.nParents = x.st.nParents := by rw [step_fill_some b x.st k q hk]
    have hCst : (step b x.st (.fill k q)).1.nChildren = x.st.nChildren := by rw [step_fill_some b x.st k q hk]
    have hN : (advance step b x (.fill k q)).st.nParents = (advance step b x (.fill k q)).tr.nOrders := by
      rw [hadvSt, hadvTr, hNst, nOrdersRec_aux2, nOrdersObsFill_aux2, hnP]
    have hKlen : (advance step b x (.fill k q)).tr.kids.length = x.tr.kids.length := by
      rw [hadvTr]
      have : (((x.tr.observe (.fill k q)).record ([] : List Child)).kids.length) = x.tr.kids.length := kidsLenFillNil_aux _ _ _
      exact this
    have hC : (advance step b x (.fill k q)).st.nChildren = (advance step b x (.fill k q)).tr.kids.length := by
      rw [hadvSt, hadvTr, hCst, hnC]
      have : (((x.tr.observe (.fill k q)).record ([] : List Child)).kids.length) = x.tr.kids.length := kidsLenFillNil_aux _ _ _
      rw [this]
    have hch := plan7_fill_children_after_selfcontained b x k q hnC hchild hk
    have hch2 : (∀ j, j < (advance step b x (.fill k q)).tr.kids.length →
        ∃ c, (advance step b x (.fill k q)).tr.kids[j]? = some c ∧
          (advance step b x (.fill k q)).st.children j = ⟨c.parent, c.qty, c.done⟩) := by
      rw [hKlen] at hch ⊢
      exact hch
    -- adapt cum lemma (its tr.nOrders rewritten)
    have hcum0 := plan7_fill_cum_after b x k q hnC hchild hcum hk
    have hcum2 : (∀ id, id < (advance step b x (.fill k q)).tr.nOrders →
        ((advance step b x (.fill k q)).st.parents id).cum =
          (advance step b x (.fill k q)).tr.exec id) := by
      have hTrN : (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders := by
        rw [hadvTr, nOrdersRec_aux2, nOrdersObsFill_aux2]
      rw [hTrN] at hcum0 ⊢
      exact hcum0
    -- bounds
    have hk_len : k < x.tr.kids.length := by omega
    obtain ⟨c0, hc0Get, hc0St⟩ := hchild k hk_len
    have hobsKids : (x.tr.observe (.fill k q)).kids = x.tr.kids.set k { c0 with done := c0.done + min q (c0.qty - c0.done) } := by
      simp [Truth.observe, hc0Get]
    have hadvKids : (advance step b x (.fill k q)).tr.kids = (x.tr.observe (.fill k q)).kids := by
      simp [advance, hout, Truth.record]
    have hTrN2 : (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders := by
      rw [hadvTr, nOrdersRec_aux2, nOrdersObsFill_aux2]
    have hbd : ∀ j ∈ (advance step b x (.fill k q)).tr.kids, j.parent < (advance step b x (.fill k q)).tr.nOrders := by
      rw [hadvKids, hobsKids, hTrN2]
      intro j hj
      rcases setParent_mem_aux x.tr.kids k c0 (c0.done + min q (c0.qty - c0.done)) j hj with hjOld | rfl
      · exact hkb j hjOld
      · have hcMem : c0 ∈ x.tr.kids := List.mem_of_getElem? hc0Get
        have := hkb c0 hcMem
        simpa using this
    exact ⟨hN, hC, hch2, hcum2, hbd⟩
  · have heq : advance step b x (.fill k q) = x := plan7_fill_advance_eq_of_not_lt b x k q hnC hk
    rw [heq]
    exact ⟨hnP, hnC, hchild, hcum, hkb⟩

theorem plan5_run_key (b : Build) (evs : List Event) :
    (run step b evs).st.nParents = (run step b evs).tr.nOrders ∧
      (run step b evs).st.nChildren = (run step b evs).tr.kids.length ∧
      (∀ k, k < (run step b evs).tr.kids.length →
        ∃ c, (run step b evs).tr.kids[k]? = some c ∧
          (run step b evs).st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < (run step b evs).tr.nOrders →
        ((run step b evs).st.parents id).cum = (run step b evs).tr.exec id) ∧
      ∀ k ∈ (run step b evs).tr.kids, k.parent < (run step b evs).tr.nOrders := by
  refine run_induction step b (fun x => x.st.nParents = x.tr.nOrders ∧
      x.st.nChildren = x.tr.kids.length ∧
      (∀ k, k < x.tr.kids.length →
        ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
      (∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id) ∧
      ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) ?h0 ?hs evs
  · refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · intro k hk
      simp [start, Truth.empty] at hk
    · intro id hid
      simp [start, Truth.empty] at hid
    · intro k hk
      simp [start, Truth.empty] at hk
  · intro x e hx
    cases e with
    | parent q f => exact plan5_advance_parent_key_proof b x q f hx
    | route rid liq => exact plan5_advance_route_key b x rid liq hx
    | ack k => exact plan5_advance_ack_key b x k hx
    | fill k q => exact plan5_advance_fill_key b x k q hx

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> constructor <;> rfl

theorem req_routes_available : RoutesAvailable step := by
  intro b evs id liq
  exact plan0_route_eq_expected_of_invariants b (run step b evs) id liq (plan0_run_invariants_proof b evs)

theorem req_never_overroute : NeverOverroute step :=
  plan3_never_overroute_all

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e id hExec c hc
  have hinv := plan0_run_invariants_proof b evs
  obtain ⟨hn, hqs, hkb⟩ := hinv
  have hSentLe : (run step b evs).tr.sent id ≤ (run step b evs).tr.qty id :=
    req_never_overroute b evs id
  have hExecLe : (run step b evs).tr.exec id ≤ (run step b evs).tr.sent id :=
    exec_le_sent step b evs id
  have hSentEq : (run step b evs).tr.sent id = (run step b evs).tr.qty id := by omega
  cases e with
  | parent q f =>
    have hout : (step b (run step b evs).st (Event.parent q f)).2 = ([] : List Child) := by
      simp [step]
    rw [hout] at hc
    simp at hc
  | route rid liq =>
    exact stop_fill_route_auxA b evs rid liq id hSentEq hn hqs c hc
  | ack k =>
    have hout : (step b (run step b evs).st (Event.ack k)).2 = ([] : List Child) := by
      simp [step]
    rw [hout] at hc
    simp at hc
  | fill k q =>
    by_cases hk : k < (run step b evs).st.nChildren
    · have hout : (step b (run step b evs).st (Event.fill k q)).2 = ([] : List Child) := by
        simp [step, hk]
      rw [hout] at hc
      simp at hc
    · have hout : (step b (run step b evs).st (Event.fill k q)).2 = ([] : List Child) := by
        simp [step, hk]
      rw [hout] at hc
      simp at hc

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  have h1 := exec_le_sent step b evs id
  have h2 : (run step b evs).tr.sent id ≤ (run step b evs).tr.qty id := req_never_overroute b evs id
  omega

theorem req_fill_accounting     : FillAccounting step := sorry

end OrderRouter
