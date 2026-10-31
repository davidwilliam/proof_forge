import OrderRouter.Spec
import OrderRouter.Lemmas
import ProofForgeFin.Trading.RouterModel
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

def step : Impl := fun b s e =>
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
      let p' := ({ p with cum := p.cum + x } : ParentRec)
      ({ s with parents := upd s.parents c.parent p',
                children := upd s.children k { c with done := c.done + x } }, [])
    else (s, [])

theorem foo_test : True := by trivial

theorem upd_test (f : Nat → Nat) (k v : Nat) : upd f k v k = v := by simp [upd]

theorem upd_rw_test2 (f : Nat → Nat) (k : Nat) : (upd f k 5) k = 5 := by simp [upd]

theorem sentFor_all_lt_zero (l : List Kid) (n : Nat) (h : ∀ k ∈ l, k.parent < n) (id : Nat) (hid : n ≤ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent < n := h a (by simp)
    have ih' := ih (fun k hk => h k (by simp [hk]))
    have hne : a.parent ≠ id := by omega
    simp [hne, ih']

theorem upd_eq' {α : Type} (f : Nat → α) (k : Nat) (v : α) : upd f k v k = v := by simp [upd]

theorem upd_ne' {α : Type} (f : Nat → α) (k j : Nat) (v : α) (h : j ≠ k) : upd f k v j = f j := by simp [upd, h]

theorem tr_sent_observe2 (t : Truth) (e : Event) (id : Nat) : (t.observe e).sent id = t.sent id := by
  cases e with
  | parent q f => rfl
  | route id' liq => rfl
  | ack k => rfl
  | fill k q =>
    simp only [Truth.observe]
    split
    · rename_i c hc
      simp only [Truth.sent]
      exact sentFor_set_done t.kids k c (c.done + min q (c.qty - c.done)) hc id
    · rfl

theorem tr_nOrders_parent (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).nOrders = t.nOrders + 1 := rfl

theorem tr_nOrders_route (t : Truth) (id liq : Nat) : (t.observe (.route id liq)).nOrders = t.nOrders := rfl

theorem tr_nOrders_ack (t : Truth) (k : Nat) : (t.observe (.ack k)).nOrders = t.nOrders := rfl

theorem tr_nOrders_fill (t : Truth) (k q : Nat) : (t.observe (.fill k q)).nOrders = t.nOrders := by
  simp only [Truth.observe]; split <;> rfl

theorem tr_qty_observe_parent2 (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).qty = upd t.qty t.nOrders q := rfl

theorem tr_sent_record2 (t : Truth) (out : List Child) (id : Nat) :
    (t.record out).sent id = t.sent id + sentFor (out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id := by
  simp [Truth.record, Truth.sent, sentFor_append]

theorem tr_qty_record2 (t : Truth) (out : List Child) (id : Nat) : (t.record out).qty id = t.qty id := rfl

theorem tr_nOrders_record2 (t : Truth) (out : List Child) : (t.record out).nOrders = t.nOrders := rfl

theorem tr_qty_observe_route (t : Truth) (id liq : Nat) (j : Nat) : (t.observe (.route id liq)).qty j = t.qty j := rfl

theorem tr_qty_observe_ack (t : Truth) (k : Nat) (j : Nat) : (t.observe (.ack k)).qty j = t.qty j := rfl

theorem tr_qty_observe_fill (t : Truth) (k q : Nat) (j : Nat) : (t.observe (.fill k q)).qty j = t.qty j := by
  simp only [Truth.observe]; split <;> rfl

theorem tr_qty_observe_parent_eq (t : Truth) (q : Nat) (f : Bool) (j : Nat) :
    (t.observe (.parent q f)).qty j = (if j = t.nOrders then q else t.qty j) := by
  simp [Truth.observe, upd]

theorem tr_kids_observe_parent (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).kids = t.kids := rfl

theorem tr_kids_observe_route (t : Truth) (id liq : Nat) : (t.observe (.route id liq)).kids = t.kids := rfl

theorem tr_kids_observe_ack (t : Truth) (k : Nat) : (t.observe (.ack k)).kids = t.kids := rfl

theorem execFor_all_lt_zero (l : List Kid) (n : Nat) (h : ∀ k ∈ l, k.parent < n) (id : Nat) (hid : n ≤ id) : execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent < n := h a (by simp)
    have ih' := ih (fun k hk => h k (by simp [hk]))
    have hne : a.parent ≠ id := by omega
    simp [hne, ih']

theorem step_parent_fst (b : Build) (s : State) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).1 = { s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } := rfl

theorem step_parent_snd (b : Build) (s : State) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).2 = ([] : List Child) := rfl

theorem step_ack (b : Build) (s : State) (k : Nat) :
    (step b s (.ack k)) = (s, []) := rfl

theorem start_nParents : start.st.nParents = start.tr.nOrders := rfl

theorem start_qty (id : Nat) : (start.st.parents id).qty = start.tr.qty id := rfl

theorem start_sent (id : Nat) : (start.st.parents id).sent = start.tr.sent id := by
  simp [start, init, Truth.empty, Truth.sent, sentFor_nil]

theorem routeBySent_snd2 (s : State) (id liq : Nat) (h : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) :
    (routeBySent s id liq).2 = [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] := by
  unfold routeBySent
  simp [h]

theorem routeBySent_snd_nil (s : State) (id liq : Nat)
    (h : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    (routeBySent s id liq).2 = ([] : List Child) := by
  unfold routeBySent
  simp [h]

theorem route_mem_parent (s : State) (id liq : Nat) (c : Child)
    (h : c ∈ (routeBySent s id liq).2) : c.parent = id := by
  by_cases hc : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)
  · have h2 : (routeBySent s id liq).2 = [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] := routeBySent_snd2 s id liq hc
    rw [h2] at h
    simp at h
    rw [h]
  · have h2 : (routeBySent s id liq).2 = ([] : List Child) := routeBySent_snd_nil s id liq hc
    rw [h2] at h
    simp at h

theorem step_fill_snd2 (b : Build) (s : State) (k q : Nat) :
    (step b s (.fill k q)).2 = ([] : List Child) := by
  simp only [step]
  split <;> rfl

def Inv (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders
  ∧ (∀ id, (x.st.parents id).qty = x.tr.qty id)
  ∧ (∀ id, (x.st.parents id).sent = x.tr.sent id)
  ∧ x.st.nChildren = x.tr.kids.length
  ∧ (∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)
  ∧ (∀ id, (x.st.parents id).sent ≤ (x.st.parents id).qty)

theorem inv_start_thm : Inv start := by
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩
  · intro id; rfl
  · intro id
    simp [start, init, Truth.empty, Truth.sent, sentFor_nil]
  · simp [start, Truth.empty]
  · intro id; simp [start, init]

theorem state_parent_qty (s : State) (q : Nat) (f : Bool) (j : Nat) :
    (({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } : State).parents j).qty
    = if j = s.nParents then q else (s.parents j).qty := by
  by_cases h : j = s.nParents <;> simp [upd, h]

theorem state_parent_sent (s : State) (q : Nat) (f : Bool) (j : Nat) :
    ((({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ } : State)).parents j).sent
    = if j = s.nParents then 0 else (s.parents j).sent := by
  by_cases h : j = s.nParents <;> simp [upd, h]

theorem truth_parent_sent (t : Truth) (q : Nat) (f : Bool) (j : Nat) :
    (t.observe (.parent q f)).sent j = t.sent j := rfl

theorem truth_parent_qty (t : Truth) (q : Nat) (f : Bool) (j : Nat) :
    (t.observe (.parent q f)).qty j = (if j = t.nOrders then q else t.qty j) := by
  simp [Truth.observe, upd]

theorem route_unfold_test (s : State) (id liq : Nat) :
    routeBySent s id liq =
    (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
      ({ s with parents := upd s.parents id { (s.parents id) with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) },
                nChildren := s.nChildren + 1,
                children := upd s.children s.nChildren ⟨id, min liq ((s.parents id).qty - (s.parents id).sent), 0⟩ }, [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩])
    else (s, [])) := by
  simp only [routeBySent]

theorem route_fst_np (s : State) (id liq : Nat) :
    (routeBySent s id liq).1.nParents = s.nParents := by
  rw [route_unfold_test]
  by_cases h : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)
  · simp [h]
  · simp [h]

theorem route_snd_eq (s : State) (id liq : Nat) :
    (routeBySent s id liq).2 =
    (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
      [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] else []) := by
  rw [route_unfold_test]
  by_cases h : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)
  · simp [h]
  · simp [h]

theorem adv_parent_tr_sent2 (x : Sys) (q : Nat) (f : Bool) (b : Build) (j : Nat) :
    (advance step b x (.parent q f)).tr.sent j = x.tr.sent j := by
  simp [advance, Truth.sent, Truth.record, Truth.observe, step]

theorem adv_parent_kids_len2 (x : Sys) (q : Nat) (f : Bool) (b : Build) :
    (advance step b x (.parent q f)).tr.kids.length = x.tr.kids.length := by
  simp [advance, Truth.record, Truth.observe, step]

def InvFull (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders
  ∧ (∀ id, (x.st.parents id).qty = x.tr.qty id)
  ∧ (∀ id, (x.st.parents id).sent = x.tr.sent id)
  ∧ (∀ id, (x.st.parents id).cum = x.tr.exec id)
  ∧ x.st.nChildren = x.tr.kids.length
  ∧ (∀ k c, x.tr.kids[k]? = some c → x.st.children k = (⟨c.parent, c.qty, c.done⟩ : ChildRec))
  ∧ (∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)

theorem invFull_start : InvFull start := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro id; rfl
  · intro id; simp [start, init, Truth.empty, Truth.sent, sentFor_nil]
  · intro id; simp [start, init, Truth.empty, Truth.exec, execFor_nil]
  · intro k c h; simp [start, Truth.empty] at h
  · simp [start, Truth.empty]

theorem tr_exec_observe_parent (t : Truth) (q : Nat) (f : Bool) (id : Nat) :
    (t.observe (.parent q f)).exec id = t.exec id := rfl

theorem tr_exec_observe_route (t : Truth) (id liq j : Nat) :
    (t.observe (.route id liq)).exec j = t.exec j := rfl

theorem tr_exec_observe_ack (t : Truth) (k j : Nat) :
    (t.observe (.ack k)).exec j = t.exec j := rfl

theorem tr_exec_observe_fill_eq (t : Truth) (k q : Nat) (c : Kid) (h : t.kids[k]? = some c) (id : Nat) :
    (t.observe (.fill k q)).exec id = t.exec id + (if c.parent = id then min q (c.qty - c.done) else 0) := by
  simp only [Truth.observe, h]
  simp only [Truth.exec, execFor_set_done t.kids k c (min q (c.qty - c.done)) h id]

theorem tr_exec_observe_fill_none (t : Truth) (k q : Nat) (h : t.kids[k]? = none) (id : Nat) :
    (t.observe (.fill k q)).exec id = t.exec id := by
  simp only [Truth.observe, h]

theorem tr_exec_record (t : Truth) (out : List Child) (id : Nat) :
    (t.record out).exec id = t.exec id := by
  simp [Truth.record, Truth.exec, execFor_append, execFor_new]

theorem tr_sent_observe_fill_eq (t : Truth) (k q : Nat) (c : Kid) (h : t.kids[k]? = some c) (id : Nat) :
    (t.observe (.fill k q)).sent id = t.sent id := by
  simp only [Truth.observe, h]
  simp only [Truth.sent]
  exact sentFor_set_done t.kids k c (c.done + min q (c.qty - c.done)) h id

theorem tr_sent_observe_fill_none (t : Truth) (k q : Nat) (h : t.kids[k]? = none) (id : Nat) :
    (t.observe (.fill k q)).sent id = t.sent id := by
  simp only [Truth.observe, h]

theorem kids_append_lt (l : List Kid) (c : Kid) (k : Nat) (h : k < l.length) :
    (l ++ [c])[k]? = l[k]? := by simp [List.getElem?_append, h]

theorem fill_state_qty (s : State) (k q j : Nat) :
    ((step Build.rlp s (.fill k q)).1.parents j).qty = (s.parents j).qty := by
  simp only [step]
  by_cases h : k < s.nChildren
  · simp [h]
    by_cases hj : j = (s.children k).parent
    · subst hj; simp [upd]
    · simp [upd, hj]
  · simp [h]

theorem fill_state_sent (s : State) (k q j : Nat) :
    ((step Build.rlp s (.fill k q)).1.parents j).sent = (s.parents j).sent := by
  simp only [step]
  by_cases h : k < s.nChildren
  · simp [h]
    by_cases hj : j = (s.children k).parent
    · subst hj; simp [upd]
    · simp [upd, hj]
  · simp [h]

theorem fill_state_np (s : State) (k q : Nat) :
    (step Build.rlp s (.fill k q)).1.nParents = s.nParents := by
  simp only [step]
  by_cases h : k < s.nChildren <;> simp [h]

theorem fill_state_nch (s : State) (k q : Nat) :
    (step Build.rlp s (.fill k q)).1.nChildren = s.nChildren := by
  simp only [step]
  by_cases h : k < s.nChildren <;> simp [h]

theorem fill_state_np_all (b : Build) (s : State) (k q : Nat) :
    (step b s (.fill k q)).1.nParents = s.nParents := by
  simp only [step]
  by_cases h : k < s.nChildren <;> simp [h]

theorem fill_state_nch_all (b : Build) (s : State) (k q : Nat) :
    (step b s (.fill k q)).1.nChildren = s.nChildren := by
  simp only [step]
  by_cases h : k < s.nChildren <;> simp [h]

theorem fill_state_qty_all (b : Build) (s : State) (k q j : Nat) :
    ((step b s (.fill k q)).1.parents j).qty = (s.parents j).qty := by
  simp only [step]
  by_cases h : k < s.nChildren
  · simp [h]
    by_cases hj : j = (s.children k).parent
    · subst hj; simp [upd]
    · simp [upd, hj]
  · simp [h]

theorem fill_state_sent_all (b : Build) (s : State) (k q j : Nat) :
    ((step b s (.fill k q)).1.parents j).sent = (s.parents j).sent := by
  simp only [step]
  by_cases h : k < s.nChildren
  · simp [h]
    by_cases hj : j = (s.children k).parent
    · subst hj; simp [upd]
    · simp [upd, hj]
  · simp [h]

theorem adv_parent_st_sent (x : Sys) (b : Build) (q : Nat) (f : Bool) (j : Nat) :
    ((advance step b x (.parent q f)).st.parents j).sent
    = if j = x.st.nParents then 0 else (x.st.parents j).sent := by
  simp only [advance, step]
  by_cases h : j = x.st.nParents <;> simp [upd, h]

theorem plan0_inv_advance_parent (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hx : Inv x) : Inv (advance step b x (.parent q f)) := by
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have hstNp : (advance step b x (.parent q f)).st.nParents = x.st.nParents + 1 := by
    simp only [advance, step]
  have htrNp : (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 := by
    simp only [advance, step, Truth.observe, Truth.record]
  have hstNc : (advance step b x (.parent q f)).st.nChildren = x.st.nChildren := by
    simp only [advance, step]
  have htrKids : (advance step b x (.parent q f)).tr.kids = x.tr.kids := by
    simp only [advance, step, Truth.observe, Truth.record, List.map_nil, List.append_nil]
  have hstQty : ∀ j, ((advance step b x (.parent q f)).st.parents j).qty
      = (if j = x.st.nParents then q else (x.st.parents j).qty) := by
    intro j
    simp only [advance, step]
    by_cases h : j = x.st.nParents <;> simp [upd, h]
  have htrQty : ∀ j, (advance step b x (.parent q f)).tr.qty j
      = (if j = x.tr.nOrders then q else x.tr.qty j) := by
    intro j
    simp only [advance, step, Truth.observe, Truth.record, upd]
  have hstSent : ∀ j, ((advance step b x (.parent q f)).st.parents j).sent
      = (if j = x.st.nParents then 0 else (x.st.parents j).sent) := by
    intro j
    simp only [advance, step]
    by_cases h : j = x.st.nParents <;> simp [upd, h]
  have htrSent : ∀ j, (advance step b x (.parent q f)).tr.sent j = x.tr.sent j := by
    intro j
    simp only [advance, step, Truth.observe, Truth.record, Truth.sent, List.map_nil, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstNp, htrNp, hNp]
  · intro j; rw [hstQty j, htrQty j, hNp, hQty j]
  · intro j; rw [hstSent j, htrSent j]
    by_cases h : j = x.st.nParents
    · simp only [h, if_true]
      have hz : x.tr.sent x.st.nParents = 0 := by
        simp only [Truth.sent]
        rw [← hNp] at hPar
        exact sentFor_all_lt_zero x.tr.kids x.st.nParents hPar x.st.nParents (by omega)
      rw [hz]
    · simp only [h, if_false]; exact hSent j
  · rw [hstNc, htrKids, hNch]
  · intro k hk; rw [htrKids] at hk; rw [htrNp]
    have h := hPar k hk; omega
  · intro j; rw [hstQty j, hstSent j]
    by_cases h : j = x.st.nParents
    · simp [h]
    · simp [h, hLe j]


theorem plan0_inv_advance_route (b : Build) (x : Sys) (id liq : Nat)
    (hx : Inv x) : Inv (advance step b x (.route id liq)) := by
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have hst_eq : (advance step b x (.route id liq)).st = (routeBySent x.st id liq).1 := rfl
  have htr_eq : (advance step b x (.route id liq)).tr = x.tr.record (routeBySent x.st id liq).2 := rfl
  have hsnd_eq : (routeBySent x.st id liq).2 =
    (if id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent) then
      [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] else []) :=
    route_snd_eq x.st id liq
  by_cases h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · have hsnd : (routeBySent x.st id liq).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] := by
      rw [hsnd_eq]
      simp [h]
    have hpair1 : (routeBySent x.st id liq).1.nParents = x.st.nParents := route_fst_np x.st id liq
    have hst_np : (advance step b x (.route id liq)).st.nParents = x.st.nParents := by
      rw [hst_eq, hpair1]
    have htr_nord : (advance step b x (.route id liq)).tr.nOrders = x.tr.nOrders := by
      rw [htr_eq, hsnd]
      rfl
    have hst_nch : (advance step b x (.route id liq)).st.nChildren = x.st.nChildren + 1 := by
      rw [hst_eq]
      unfold routeBySent
      simp [h]
    have htr_len : (advance step b x (.route id liq)).tr.kids.length = x.tr.kids.length + 1 := by
      rw [htr_eq, hsnd]
      simp [Truth.record]
    have hfst_par : (routeBySent x.st id liq).1.parents =
        upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } := by
      unfold routeBySent
      simp [h]
    have hqty : ∀ j, ((advance step b x (.route id liq)).st.parents j).qty = (advance step b x (.route id liq)).tr.qty j := by
      intro j
      rw [hst_eq, htr_eq, hsnd, hfst_par, tr_qty_record2]
      rw [← hQty j]
      by_cases hj : j = id
      · rw [hj]
        simp [upd]
      · have heq : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } j) = x.st.parents j := by
          simp [upd, hj]
        rw [heq]
    have hsent : ∀ j, ((advance step b x (.route id liq)).st.parents j).sent = (advance step b x (.route id liq)).tr.sent j := by
      intro j
      rw [hst_eq, htr_eq, hsnd, hfst_par]
      have hrec : (x.tr.record [{ parent := id, qty := min liq ((x.st.parents id).qty - (x.st.parents id).sent) }]).sent j
          = x.tr.sent j + (if id = j then min liq ((x.st.parents id).qty - (x.st.parents id).sent) else 0) := by
        simp [Truth.record, Truth.sent, sentFor_append]
      rw [hrec]
      by_cases hj : j = id
      · rw [hj]
        simp only [upd_eq']
        simp only [if_true]
        have he := hSent id
        omega
      · have heq : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } j).sent = (x.st.parents j).sent := by
          have hbase : upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } j = x.st.parents j := by
            simp [upd, hj]
          rw [hbase]
        rw [heq, hSent j]
        have hif : (if id = j then min liq ((x.st.parents id).qty - (x.st.parents id).sent) else 0) = 0 := by
          simp [Ne.symm hj]
        rw [hif, Nat.add_zero]
    have hkids : ∀ k ∈ (advance step b x (.route id liq)).tr.kids, k.parent < (advance step b x (.route id liq)).tr.nOrders := by
      intro k hk
      rw [htr_eq, hsnd] at hk
      rw [htr_nord]
      simp only [Truth.record] at hk
      simp only [List.mem_append, List.mem_map] at hk
      rcases hk with hk | ⟨cc, hcc, rfl⟩
      · exact hPar k hk
      · simp at hcc
        obtain ⟨rfl, rfl⟩ := hcc
        simp only
        omega
    have hle : ∀ j, ((advance step b x (.route id liq)).st.parents j).sent ≤ ((advance step b x (.route id liq)).st.parents j).qty := by
      intro j
      rw [hst_eq, hfst_par]
      by_cases hj : j = id
      · rw [hj]
        simp only [upd_eq']
        have hle0 := hLe id
        have hmin : min liq ((x.st.parents id).qty - (x.st.parents id).sent) ≤ (x.st.parents id).qty - (x.st.parents id).sent := Nat.min_le_right _ _
        omega
      · have heq : upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } j = x.st.parents j := by
          simp [upd, hj]
        rw [heq]
        exact hLe j
    refine ⟨?_, hqty, hsent, ?_, hkids, hle⟩
    · rw [hst_np, htr_nord, hNp]
    · omega
  · have hsnd : (routeBySent x.st id liq).2 = ([] : List Child) := by
      rw [hsnd_eq]
      simp [h]
    have hfst : (routeBySent x.st id liq).1 = x.st := by
      unfold routeBySent
      simp [h]
    have hst2 : (advance step b x (.route id liq)).st = x.st := by
      rw [hst_eq, hfst]
    have htr2 : (advance step b x (.route id liq)).tr = x.tr := by
      rw [htr_eq, hsnd]
      simp [Truth.record]
    unfold Inv
    simp only [hst2, htr2]
    exact ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩


theorem plan0_inv_advance_ack (b : Build) (x : Sys) (k : Nat)
    (hx : Inv x) : Inv (advance step b x (.ack k)) := by
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have hst : (advance step b x (.ack k)).st = x.st := by
    simp only [advance, step_ack]
  have htr : (advance step b x (.ack k)).tr = x.tr := by
    simp only [advance, step_ack, Truth.observe, Truth.record, List.map_nil, List.append_nil]
  unfold Inv
  simp only [hst, htr]
  exact ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩


theorem plan0_inv_advance_fill (b : Build) (x : Sys) (k q : Nat)
    (hx : Inv x) : Inv (advance step b x (.fill k q)) := by
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have hsnd : (step b x.st (.fill k q)).2 = ([] : List Child) := step_fill_snd2 b x.st k q
  have hAdvTr : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record ([] : List Child) := by
    simp only [advance, hsnd]
  have hstNp : (advance step b x (.fill k q)).st.nParents = x.st.nParents := by
    simp only [advance]
    rw [fill_state_np_all]
  have htrNp : (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders := by
    rw [hAdvTr]
    rw [tr_nOrders_record2]
    exact tr_nOrders_fill x.tr k q
  have hstNch : (advance step b x (.fill k q)).st.nChildren = x.st.nChildren := by
    simp only [advance]
    rw [fill_state_nch_all]
  have hstQty : ∀ j, ((advance step b x (.fill k q)).st.parents j).qty = (x.st.parents j).qty := by
    intro j
    simp only [advance]
    exact fill_state_qty_all b x.st k q j
  have hstSent : ∀ j, ((advance step b x (.fill k q)).st.parents j).sent = (x.st.parents j).sent := by
    intro j
    simp only [advance]
    exact fill_state_sent_all b x.st k q j
  have htrQty : ∀ j, (advance step b x (.fill k q)).tr.qty j = x.tr.qty j := by
    intro j
    rw [hAdvTr, tr_qty_record2]
    exact tr_qty_observe_fill x.tr k q j
  have htrSent : ∀ j, (advance step b x (.fill k q)).tr.sent j = x.tr.sent j := by
    intro j
    rw [hAdvTr, tr_sent_record2]
    simp only [List.map_nil, sentFor_nil, Nat.add_zero]
    cases h : x.tr.kids[k]? with
    | none =>
      have := tr_sent_observe_fill_none x.tr k q h j
      simpa [Truth.sent] using this
    | some c =>
      have := tr_sent_observe_fill_eq x.tr k q c h j
      simpa [Truth.sent] using this
  have hKidsEq : (advance step b x (.fill k q)).tr.kids = (x.tr.observe (.fill k q)).kids := by
    rw [hAdvTr]
    simp [Truth.record]
  have hObsKids : (x.tr.observe (.fill k q)).kids =
      match x.tr.kids[k]? with
      | some c => x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) }
      | none => x.tr.kids := by
    simp only [Truth.observe]
    cases h : x.tr.kids[k]? <;> simp [h]
  have hlen : (advance step b x (.fill k q)).tr.kids.length = x.tr.kids.length := by
    rw [hKidsEq, hObsKids]
    cases h : x.tr.kids[k]? with
    | none => rfl
    | some c => simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstNp, htrNp, hNp]
  · intro j; rw [hstQty j, htrQty j, hQty j]
  · intro j; rw [hstSent j, htrSent j, hSent j]
  · rw [hstNch, hlen, hNch]
  · intro y hy
    rw [htrNp]
    rw [hKidsEq, hObsKids] at hy
    cases h : x.tr.kids[k]? with
    | none =>
      simp [h] at hy
      exact hPar y hy
    | some c =>
      simp [h] at hy
      rcases List.mem_or_eq_of_mem_set hy with hy2 | hy2
      · exact hPar y hy2
      · subst hy2
        have hmem : c ∈ x.tr.kids := List.mem_of_getElem? h
        have hlt := hPar c hmem
        simp at hlt ⊢
        omega
  · intro j; rw [hstQty j, hstSent j]; exact hLe j


theorem plan0_inv_run (b : Build) (evs : List Event) :
    Inv (run step b evs) := by
  have hpres : ∀ (x : Sys) (e : Event), Inv x → Inv (advance step b x e) := by
    intro x e hx
    cases e with
    | parent q f => exact plan0_inv_advance_parent b x q f hx
    | route id liq => exact plan0_inv_advance_route b x id liq hx
    | ack k => exact plan0_inv_advance_ack b x k hx
    | fill k q => exact plan0_inv_advance_fill b x k q hx
  exact run_induction step b Inv inv_start_thm hpres evs


theorem plan0_route_output_of_inv (b : Build) (x : Sys) (id liq : Nat)
    (hx : Inv x) :
    (step b x.st (.route id liq)).2 = expectedRoute x.tr id liq := by
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have hstep : (step b x.st (.route id liq)).2 = (routeBySent x.st id liq).2 := rfl
  rw [hstep, route_snd_eq]
  have hqty : (x.st.parents id).qty = x.tr.qty id := hQty id
  have hsent : (x.st.parents id).sent = x.tr.sent id := hSent id
  have hnp : x.st.nParents = x.tr.nOrders := hNp
  simp only [expectedRoute]
  rw [hnp, hqty, hsent]


theorem parent_aux1 (b : Build) (x : Sys) (q : Nat) (f : Bool) (hx : Inv x) :
  (advance step b x (.parent q f)).st.nParents = (advance step b x (.parent q f)).tr.nOrders := by
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  simp only [advance, step, Truth.observe, Truth.record]
  omega

theorem parent_probe1 (b : Build) (x : Sys) (q : Nat) (f : Bool) :
  (advance step b x (.parent q f)).st.nParents = x.st.nParents + 1 := by
  simp only [advance, step]

theorem parent_probe2 (b : Build) (x : Sys) (q : Nat) (f : Bool) :
  (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 := by
  simp only [advance, step, Truth.observe, Truth.record]

theorem parent_probe3 (b : Build) (x : Sys) (q : Nat) (f : Bool) (j : Nat) :
  ((advance step b x (.parent q f)).st.parents j).qty = (if j = x.st.nParents then q else (x.st.parents j).qty) := by
  simp only [advance, step]
  by_cases h : j = x.st.nParents <;> simp [upd, h]

theorem parent_probe4 (b : Build) (x : Sys) (q : Nat) (f : Bool) (j : Nat) :
  (advance step b x (.parent q f)).tr.qty j = (if j = x.tr.nOrders then q else x.tr.qty j) := by
  simp only [advance, step, Truth.observe, Truth.record, upd]

theorem parent_probe5 (b : Build) (x : Sys) (q : Nat) (f : Bool) (j : Nat) :
  ((advance step b x (.parent q f)).st.parents j).sent = (if j = x.st.nParents then 0 else (x.st.parents j).sent) := by
  simp only [advance, step]
  by_cases h : j = x.st.nParents <;> simp [upd, h]

theorem parent_probe6 (b : Build) (x : Sys) (q : Nat) (f : Bool) (j : Nat) :
  (advance step b x (.parent q f)).tr.sent j = x.tr.sent j := by
  have h : (step b x.st (.parent q f)).2 = ([] : List Child) := rfl
  simp only [advance, h, Truth.record, Truth.observe, Truth.sent, List.map_nil, List.append_nil]

theorem parent_probe7 (b : Build) (x : Sys) (q : Nat) (f : Bool) :
  (advance step b x (.parent q f)).st.nChildren = x.st.nChildren := by
  simp only [advance, step]

theorem parent_probe8 (b : Build) (x : Sys) (q : Nat) (f : Bool) :
  (advance step b x (.parent q f)).tr.kids = x.tr.kids := by
  have h : (step b x.st (.parent q f)).2 = ([] : List Child) := rfl
  simp only [advance, h, Truth.record, Truth.observe, List.map_nil, List.append_nil]











theorem plan1_parent_counts (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hNp : x.st.nParents = x.tr.nOrders)
    (hNc : x.st.nChildren = x.tr.kids.length) :
    (advance step b x (.parent q f)).st.nParents = (advance step b x (.parent q f)).tr.nOrders
      ∧ (advance step b x (.parent q f)).st.nChildren = (advance step b x (.parent q f)).tr.kids.length := by
  constructor
  · rw [parent_probe1, parent_probe2, hNp]
  · rw [parent_probe7, parent_probe8, hNc]

theorem plan1_parent_qty (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hNp : x.st.nParents = x.tr.nOrders)
    (hQty : ∀ id, (x.st.parents id).qty = x.tr.qty id) :
    ∀ j, ((advance step b x (.parent q f)).st.parents j).qty = (advance step b x (.parent q f)).tr.qty j := by
  intro j
  rw [parent_probe3, parent_probe4, hNp, hQty j]

theorem plan1_parent_sent (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hNp : x.st.nParents = x.tr.nOrders)
    (hSent : ∀ id, (x.st.parents id).sent = x.tr.sent id)
    (hKids : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    ∀ j, ((advance step b x (.parent q f)).st.parents j).sent = (advance step b x (.parent q f)).tr.sent j := by
  intro j
  rw [parent_probe5, parent_probe6]
  by_cases h : j = x.st.nParents
  · subst h
    simp only [if_true]
    rw [← hNp] at hKids
    have hz : x.tr.sent (x.st.nParents) = 0 := by
      simp only [Truth.sent]
      exact sentFor_all_lt_zero x.tr.kids x.st.nParents hKids (x.st.nParents) (by omega)
    rw [hz]
  · simp only [h, if_false]
    exact hSent j

theorem plan1_parent_kids_lt (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hKids : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    ∀ k ∈ (advance step b x (.parent q f)).tr.kids, k.parent < (advance step b x (.parent q f)).tr.nOrders := by
  intro k hk
  rw [parent_probe8] at hk
  rw [parent_probe2]
  have h := hKids k hk
  omega

theorem plan1_parent_sent_le_qty_aux : True := by trivial

theorem plan1_parent_sent_le_qty_proof (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hLe : ∀ id, (x.st.parents id).sent ≤ (x.st.parents id).qty) (j : Nat) :
    ((advance step b x (.parent q f)).st.parents j).sent ≤ ((advance step b x (.parent q f)).st.parents j).qty := by
  rw [parent_probe5 b x q f j, parent_probe3 b x q f j]
  by_cases h : j = x.st.nParents
  · simp [h]
  · simp [h, hLe j]

theorem plan1_parent_sent_le_qty (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hLe : ∀ id, (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ j, ((advance step b x (.parent q f)).st.parents j).sent ≤ ((advance step b x (.parent q f)).st.parents j).qty := by
  intro j
  rw [parent_probe5 b x q f j, parent_probe3 b x q f j]
  by_cases h : j = x.st.nParents
  · simp [h]
  · simp [h, hLe j]

theorem plan0_inv_advance_parent_proof : ∀ (b : Build) (x : Sys) (q : Nat) (f : Bool),
    Inv x → Inv (advance step b x (.parent q f)) := by
  intro b x q f hx
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have hc := plan1_parent_counts b x q f hNp hNch
  have hq := plan1_parent_qty b x q f hNp hQty
  have hs := plan1_parent_sent b x q f hNp hSent hPar
  have hk := plan1_parent_kids_lt b x q f hPar
  have hle := plan1_parent_sent_le_qty b x q f hLe
  refine ⟨hc.1, hq, hs, hc.2, hk, hle⟩

theorem plan0_parent_selfcontained (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hx : Inv x) : Inv (advance step b x (.parent q f)) := by
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have hstNp : (advance step b x (.parent q f)).st.nParents = x.st.nParents + 1 := by
    simp only [advance, step]
  have htrNp : (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 := by
    simp only [advance, step, Truth.observe, Truth.record]
  have hstNc : (advance step b x (.parent q f)).st.nChildren = x.st.nChildren := by
    simp only [advance, step]
  have htrKids : (advance step b x (.parent q f)).tr.kids = x.tr.kids := by
    simp only [advance, step, Truth.observe, Truth.record, List.map_nil, List.append_nil]
  have hstQty : ∀ j, ((advance step b x (.parent q f)).st.parents j).qty
      = (if j = x.st.nParents then q else (x.st.parents j).qty) := by
    intro j
    simp only [advance, step]
    by_cases h : j = x.st.nParents <;> simp [upd, h]
  have htrQty : ∀ j, (advance step b x (.parent q f)).tr.qty j
      = (if j = x.tr.nOrders then q else x.tr.qty j) := by
    intro j
    simp only [advance, step, Truth.observe, Truth.record, upd]
  have hstSent : ∀ j, ((advance step b x (.parent q f)).st.parents j).sent
      = (if j = x.st.nParents then 0 else (x.st.parents j).sent) := by
    intro j
    simp only [advance, step]
    by_cases h : j = x.st.nParents <;> simp [upd, h]
  have htrSent : ∀ j, (advance step b x (.parent q f)).tr.sent j = x.tr.sent j := by
    intro j
    simp only [advance, step, Truth.observe, Truth.record, Truth.sent, List.map_nil, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstNp, htrNp, hNp]
  · intro j; rw [hstQty j, htrQty j, hNp, hQty j]
  · intro j; rw [hstSent j, htrSent j]
    by_cases h : j = x.st.nParents
    · simp only [h, if_true]
      have hz : x.tr.sent x.st.nParents = 0 := by
        simp only [Truth.sent]
        rw [← hNp] at hPar
        exact sentFor_all_lt_zero x.tr.kids x.st.nParents hPar x.st.nParents (by omega)
      rw [hz]
    · simp only [h, if_false]; exact hSent j
  · rw [hstNc, htrKids, hNch]
  · intro k hk; rw [htrKids] at hk; rw [htrNp]
    have h := hPar k hk; omega
  · intro j; rw [hstQty j, hstSent j]
    by_cases h : j = x.st.nParents
    · simp [h]
    · simp [h, hLe j]

theorem route_fst_nil_aux (s : State) (id liq : Nat)
    (h : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    (routeBySent s id liq).1 = s := by
  unfold routeBySent
  simp [h]

theorem route_fst_cons_aux (s : State) (id liq : Nat)
    (h : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) :
    (routeBySent s id liq).1.parents =
      upd s.parents id { (s.parents id) with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) } := by
  unfold routeBySent
  simp [h]

theorem probe_obs_route (t : Truth) (id liq : Nat) : t.observe (.route id liq) = t := by rfl

theorem route_adv_st_rfl (b : Build) (x : Sys) (id liq : Nat) :
    (advance step b x (.route id liq)).st = (routeBySent x.st id liq).1 := rfl

theorem route_adv_tr_rfl (b : Build) (x : Sys) (id liq : Nat) :
    (advance step b x (.route id liq)).tr = (x.tr.record (routeBySent x.st id liq).2) := by
  simp only [advance, probe_obs_route, step]

theorem route_nil_tr (x : Sys) (b : Build) (id liq : Nat)
    (h : ¬ (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent))) :
    (advance step b x (.route id liq)).tr = x.tr := by
  have h2 : (routeBySent x.st id liq).2 = ([] : List Child) := routeBySent_snd_nil x.st id liq h
  rw [route_adv_tr_rfl b x id liq, h2]
  simp [Truth.record]

theorem route_nil_st (x : Sys) (b : Build) (id liq : Nat)
    (h : ¬ (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent))) :
    (advance step b x (.route id liq)).st = x.st := by
  rw [route_adv_st_rfl b x id liq]
  exact route_fst_nil_aux x.st id liq h

theorem route_cons_nch (s : State) (id liq : Nat)
    (h : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) :
    (routeBySent s id liq).1.nChildren = s.nChildren + 1 := by
  unfold routeBySent
  simp [h]

theorem route_rec_kids_single (t : Truth) (pid : Nat) (qc : Nat) :
    (t.record [{ parent := pid, qty := qc }]).kids = t.kids ++ [{ parent := pid, qty := qc, done := 0 }] := by
  simp [Truth.record]

theorem route_rec_sent_single (t : Truth) (pid : Nat) (qc : Nat) (j : Nat) :
    (t.record [{ parent := pid, qty := qc }]).sent j = t.sent j + (if pid = j then qc else 0) := by
  simp [Truth.record, Truth.sent, sentFor_append]

theorem route_rec_norders_single (t : Truth) (pid : Nat) (qc : Nat) :
    (t.record [{ parent := pid, qty := qc }]).nOrders = t.nOrders := by
  simp [Truth.record]

theorem route_rec_qty_single (t : Truth) (pid : Nat) (qc : Nat) (j : Nat) :
    (t.record [{ parent := pid, qty := qc }]).qty j = t.qty j := by
  simp [Truth.record]

theorem route_rec_len_single (t : Truth) (pid : Nat) (qc : Nat) :
    (t.record [{ parent := pid, qty := qc }]).kids.length = t.kids.length + 1 := by
  simp [Truth.record]

theorem route_adv_len_cons (x : Sys) (b : Build) (id liq : Nat)
    (h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (advance step b x (.route id liq)).tr.kids.length = x.tr.kids.length + 1 := by
  have h2 : (routeBySent x.st id liq).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] :=
    routeBySent_snd2 x.st id liq h
  rw [route_adv_tr_rfl b x id liq, h2]
  simp [Truth.record]

theorem route_proof_test : True := by trivial

theorem route_cons_tr_kids (x : Sys) (b : Build) (id liq : Nat)
    (h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :
    (advance step b x (.route id liq)).tr.kids =
      x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] := by
  have h2 : (routeBySent x.st id liq).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] :=
    routeBySent_snd2 x.st id liq h
  rw [route_adv_tr_rfl b x id liq, h2]
  simp [Truth.record]







theorem plan2_route_kids_lt (b : Build) (x : Sys) (id liq : Nat)
    (hNp : x.st.nParents = x.tr.nOrders)
    (hKids : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    ∀ k ∈ (advance step b x (.route id liq)).tr.kids,
      k.parent < (advance step b x (.route id liq)).tr.nOrders := by
  by_cases h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · have hkids : (advance step b x (.route id liq)).tr.kids =
      x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] :=
      route_cons_tr_kids x b id liq h
    have hnord : (advance step b x (.route id liq)).tr.nOrders = x.tr.nOrders := by
      rw [route_adv_tr_rfl b x id liq]
      exact tr_nOrders_record2 _ _
    intro k hk
    rw [hkids] at hk
    rw [hnord]
    simp only [List.mem_append] at hk
    rcases hk with hk | hk
    · exact hKids k hk
    · simp at hk
      subst hk
      simp only
      omega
  · have htr : (advance step b x (.route id liq)).tr = x.tr := route_nil_tr x b id liq h
    intro k hk
    rw [htr] at hk ⊢
    exact hKids k hk




theorem plan2_route_counts (b : Build) (x : Sys) (id liq : Nat)
    (hNp : x.st.nParents = x.tr.nOrders)
    (hNc : x.st.nChildren = x.tr.kids.length) :
    (advance step b x (.route id liq)).st.nParents = (advance step b x (.route id liq)).tr.nOrders
      ∧ (advance step b x (.route id liq)).st.nChildren = (advance step b x (.route id liq)).tr.kids.length := by
  by_cases h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · constructor
    · have hst : (advance step b x (.route id liq)).st.nParents = x.st.nParents := by
        rw [route_adv_st_rfl]
        exact route_fst_np x.st id liq
      have htr : (advance step b x (.route id liq)).tr.nOrders = x.tr.nOrders := by
        rw [route_adv_tr_rfl]
        exact tr_nOrders_record2 _ _
      rw [hst, htr, hNp]
    · have hst : (advance step b x (.route id liq)).st.nChildren = x.st.nChildren + 1 := by
        rw [route_adv_st_rfl]
        exact route_cons_nch x.st id liq h
      have htr := route_adv_len_cons x b id liq h
      omega
  · have hst : (advance step b x (.route id liq)).st = x.st := route_nil_st x b id liq h
    have htr : (advance step b x (.route id liq)).tr = x.tr := route_nil_tr x b id liq h
    constructor
    · rw [hst, htr, hNp]
    · rw [hst, htr, hNc]

theorem plan2_route_qty (b : Build) (x : Sys) (id liq : Nat)
    (hQty : ∀ j, (x.st.parents j).qty = x.tr.qty j) :
    ∀ j, ((advance step b x (.route id liq)).st.parents j).qty
      = (advance step b x (.route id liq)).tr.qty j := by
  have hst : (advance step b x (.route id liq)).st = (routeBySent x.st id liq).1 := rfl
  have htr : (advance step b x (.route id liq)).tr = (x.tr.record (routeBySent x.st id liq).2) := by
    simp only [advance, probe_obs_route, step]
  intro j
  rw [hst, htr, tr_qty_record2 _ _ _, ← hQty j]
  by_cases h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · rw [route_fst_cons_aux x.st id liq h]
    by_cases hj : j = id
    · subst hj; simp [upd]
    · simp [upd, hj]
  · rw [route_fst_nil_aux x.st id liq h]

theorem plan2_route_sent (b : Build) (x : Sys) (id liq : Nat)
    (hSent : ∀ j, (x.st.parents j).sent = x.tr.sent j) :
    ∀ j, ((advance step b x (.route id liq)).st.parents j).sent
      = (advance step b x (.route id liq)).tr.sent j := by
  intro j
  by_cases h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · have hst : (advance step b x (.route id liq)).st = (routeBySent x.st id liq).1 :=
      route_adv_st_rfl b x id liq
    have htr : (advance step b x (.route id liq)).tr = (x.tr.record (routeBySent x.st id liq).2) := by
      simp only [advance, probe_obs_route, step]
    have hpar : (routeBySent x.st id liq).1.parents =
        upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } :=
      route_fst_cons_aux x.st id liq h
    have hout : (routeBySent x.st id liq).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] :=
      routeBySent_snd2 x.st id liq h
    rw [hst, htr, hout, hpar]
    have hrec : (x.tr.record [{ parent := id, qty := min liq ((x.st.parents id).qty - (x.st.parents id).sent) }]).sent j
        = x.tr.sent j + (if id = j then min liq ((x.st.parents id).qty - (x.st.parents id).sent) else 0) :=
      route_rec_sent_single x.tr id (min liq ((x.st.parents id).qty - (x.st.parents id).sent)) j
    rw [hrec]
    by_cases hj : j = id
    · subst j
      have hupd : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } id).sent
          = (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) := by
        simp [upd]
      rw [hupd, hSent id]
      simp
    · have hupd : (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } j).sent = (x.st.parents j).sent := by
        have hbase : upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } j = x.st.parents j := by
          simp [upd, hj]
        rw [hbase]
      rw [hupd, hSent j]
      have hif : (if id = j then min liq ((x.st.parents id).qty - (x.st.parents id).sent) else 0) = 0 := by
        simp [Ne.symm hj]
      rw [hif, Nat.add_zero]
  · have hst : (advance step b x (.route id liq)).st = x.st := route_nil_st x b id liq h
    have htr : (advance step b x (.route id liq)).tr = x.tr := route_nil_tr x b id liq h
    rw [hst, htr, hSent j]

theorem plan2_route_kids_lt_aux_test : True := by trivial

theorem plan2_route_kids_lt_proof (b : Build) (x : Sys) (id liq : Nat)
    (hNp : x.st.nParents = x.tr.nOrders)
    (hKids : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) :
    ∀ k ∈ (advance step b x (.route id liq)).tr.kids,
      k.parent < (advance step b x (.route id liq)).tr.nOrders := by
  by_cases h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · have hkids : (advance step b x (.route id liq)).tr.kids =
      x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] :=
      route_cons_tr_kids x b id liq h
    have hnord : (advance step b x (.route id liq)).tr.nOrders = x.tr.nOrders := by
      rw [route_adv_tr_rfl b x id liq]
      exact tr_nOrders_record2 _ _
    intro k hk
    rw [hkids] at hk
    rw [hnord]
    simp only [List.mem_append] at hk
    rcases hk with hk | hk
    · exact hKids k hk
    · simp at hk
      subst hk
      simp only
      omega
  · have htr : (advance step b x (.route id liq)).tr = x.tr := route_nil_tr x b id liq h
    intro k hk
    rw [htr] at hk ⊢
    exact hKids k hk

theorem plan2_route_sent_le_qty (b : Build) (x : Sys) (id liq : Nat)
    (hLe : ∀ j, (x.st.parents j).sent ≤ (x.st.parents j).qty) :
    ∀ j, ((advance step b x (.route id liq)).st.parents j).sent
      ≤ ((advance step b x (.route id liq)).st.parents j).qty := by
  intro j
  by_cases h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · have hst : (advance step b x (.route id liq)).st = (routeBySent x.st id liq).1 :=
      route_adv_st_rfl b x id liq
    have hpar : (routeBySent x.st id liq).1.parents =
        upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } :=
      route_fst_cons_aux x.st id liq h
    have hsent : ((advance step b x (.route id liq)).st.parents j).sent =
        (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } j).sent := by
      rw [hst, hpar]
    have hqty : ((advance step b x (.route id liq)).st.parents j).qty =
        (upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } j).qty := by
      rw [hst, hpar]
    rw [hsent, hqty]
    by_cases hj : j = id
    · rw [hj]
      simp only [upd_eq']
      have hle := hLe id
      have hmin : min liq ((x.st.parents id).qty - (x.st.parents id).sent) ≤ (x.st.parents id).qty - (x.st.parents id).sent := Nat.min_le_right _ _
      omega
    · have hupd : upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) } j = x.st.parents j := by
        simp [upd, hj]
      rw [hupd]
      exact hLe j
  · have hst : (advance step b x (.route id liq)).st = x.st := route_nil_st x b id liq h
    rw [hst]
    exact hLe j

theorem plan0_inv_advance_route_proofhelper : True := by trivial

theorem plan0_inv_advance_route_newproof (b : Build) (x : Sys) (id liq : Nat)
    (hx : Inv x) : Inv (advance step b x (.route id liq)) := by
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have hc := plan2_route_counts b x id liq hNp hNch
  have hq := plan2_route_qty b x id liq hQty
  have hs := plan2_route_sent b x id liq hSent
  have hk := plan2_route_kids_lt b x id liq hNp hPar
  have hle := plan2_route_sent_le_qty b x id liq hLe
  exact ⟨hc.1, hq, hs, hc.2, hk, hle⟩

theorem route_tmp5 (b : Build) (x : Sys) (pid liq : Nat)
    (hx : Inv x) : Inv (advance step b x (.route pid liq)) := by
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have hst_eq : (advance step b x (.route pid liq)).st = (routeBySent x.st pid liq).1 := rfl
  have htr_eq : (advance step b x (.route pid liq)).tr = x.tr.record (routeBySent x.st pid liq).2 := rfl
  have hsnd_eq : (routeBySent x.st pid liq).2 =
    (if pid < x.st.nParents ∧ 0 < min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) then
      [⟨pid, min liq ((x.st.parents pid).qty - (x.st.parents pid).sent)⟩] else []) :=
    route_snd_eq x.st pid liq
  by_cases h : pid < x.st.nParents ∧ 0 < min liq ((x.st.parents pid).qty - (x.st.parents pid).sent)
  · have hsnd : (routeBySent x.st pid liq).2 = [⟨pid, min liq ((x.st.parents pid).qty - (x.st.parents pid).sent)⟩] := by
      rw [hsnd_eq]
      simp [h]
    have hpair1 : (routeBySent x.st pid liq).1.nParents = x.st.nParents := route_fst_np x.st pid liq
    have hst_np : (advance step b x (.route pid liq)).st.nParents = x.st.nParents := by
      rw [hst_eq, hpair1]
    have htr_nord : (advance step b x (.route pid liq)).tr.nOrders = x.tr.nOrders := by
      rw [htr_eq, hsnd]
      rfl
    have hst_nch : (advance step b x (.route pid liq)).st.nChildren = x.st.nChildren + 1 := by
      rw [hst_eq]
      unfold routeBySent
      simp [h]
    have htr_len : (advance step b x (.route pid liq)).tr.kids.length = x.tr.kids.length + 1 := by
      rw [htr_eq, hsnd]
      simp [Truth.record]
    have hfst_par : (routeBySent x.st pid liq).1.parents =
        upd x.st.parents pid { (x.st.parents pid) with sent := (x.st.parents pid).sent + min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) } := by
      unfold routeBySent
      simp [h]
    have hqty : ∀ j, ((advance step b x (.route pid liq)).st.parents j).qty = (advance step b x (.route pid liq)).tr.qty j := by
      intro j
      rw [hst_eq, htr_eq, hsnd, hfst_par, tr_qty_record2]
      rw [← hQty j]
      by_cases hj : j = pid
      · rw [hj]
        simp [upd]
      · have heq : (upd x.st.parents pid { (x.st.parents pid) with sent := (x.st.parents pid).sent + min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) } j) = x.st.parents j := by
          simp [upd, hj]
        rw [heq]
    have hsent : ∀ j, ((advance step b x (.route pid liq)).st.parents j).sent = (advance step b x (.route pid liq)).tr.sent j := by
      intro j
      rw [hst_eq, htr_eq, hsnd, hfst_par]
      have hrec : (x.tr.record [{ parent := pid, qty := min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) }]).sent j
          = x.tr.sent j + (if pid = j then min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) else 0) := by
        simp [Truth.record, Truth.sent, sentFor_append]
      rw [hrec]
      by_cases hj : j = pid
      · rw [hj]
        simp only [upd_eq']
        simp only [if_true]
        have he := hSent pid
        omega
      · have heq : (upd x.st.parents pid { (x.st.parents pid) with sent := (x.st.parents pid).sent + min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) } j).sent = (x.st.parents j).sent := by
          have hbase : upd x.st.parents pid { (x.st.parents pid) with sent := (x.st.parents pid).sent + min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) } j = x.st.parents j := by
            simp [upd, hj]
          rw [hbase]
        rw [heq, hSent j]
        have hif : (if pid = j then min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) else 0) = 0 := by
          simp [Ne.symm hj]
        rw [hif, Nat.add_zero]
    have hkids : ∀ k ∈ (advance step b x (.route pid liq)).tr.kids, k.parent < (advance step b x (.route pid liq)).tr.nOrders := by
      intro k hk
      rw [htr_eq, hsnd] at hk
      rw [htr_nord]
      simp only [Truth.record] at hk
      simp only [List.mem_append, List.mem_map] at hk
      rcases hk with hk | ⟨cc, hcc, rfl⟩
      · exact hPar k hk
      · simp at hcc
        obtain ⟨rfl, rfl⟩ := hcc
        simp only
        omega
    have hle : ∀ j, ((advance step b x (.route pid liq)).st.parents j).sent ≤ ((advance step b x (.route pid liq)).st.parents j).qty := by
      intro j
      rw [hst_eq, hfst_par]
      by_cases hj : j = pid
      · rw [hj]
        simp only [upd_eq']
        have hle0 := hLe pid
        have hmin : min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) ≤ (x.st.parents pid).qty - (x.st.parents pid).sent := Nat.min_le_right _ _
        omega
      · have heq : upd x.st.parents pid { (x.st.parents pid) with sent := (x.st.parents pid).sent + min liq ((x.st.parents pid).qty - (x.st.parents pid).sent) } j = x.st.parents j := by
          simp [upd, hj]
        rw [heq]
        exact hLe j
    refine ⟨?_, hqty, hsent, ?_, hkids, hle⟩
    · rw [hst_np, htr_nord, hNp]
    · omega
  · have hsnd : (routeBySent x.st pid liq).2 = ([] : List Child) := by
      rw [hsnd_eq]
      simp [h]
    have hfst : (routeBySent x.st pid liq).1 = x.st := by
      unfold routeBySent
      simp [h]
    have hst2 : (advance step b x (.route pid liq)).st = x.st := by
      rw [hst_eq, hfst]
    have htr2 : (advance step b x (.route pid liq)).tr = x.tr := by
      rw [htr_eq, hsnd]
      simp [Truth.record]
    unfold Inv
    simp only [hst2, htr2]
    exact ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩

theorem plan0_inv_advance_ack_proof (b : Build) (x : Sys) (k : Nat)
    (hx : Inv x) : Inv (advance step b x (.ack k)) := by
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have hst : (advance step b x (.ack k)).st = x.st := by
    simp only [advance, step_ack]
  have htr : (advance step b x (.ack k)).tr = x.tr := by
    simp only [advance, step_ack, Truth.observe, Truth.record, List.map_nil, List.append_nil]
  unfold Inv
  simp only [hst, htr]
  exact ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩

theorem plan0_inv_run_helper2 (b : Build) (evs : List Event) :
    Inv (run step b evs) := by
  have hpres : ∀ (x : Sys) (e : Event), Inv x → Inv (advance step b x e) := by
    intro x e hx
    cases e with
    | parent q f => exact plan0_inv_advance_parent b x q f hx
    | route id liq => exact plan0_inv_advance_route b x id liq hx
    | ack k => exact plan0_inv_advance_ack b x k hx
    | fill k q => exact plan0_inv_advance_fill b x k q hx
  exact run_induction step b Inv inv_start_thm hpres evs

theorem plan0_inv_run_direct_test (b : Build) (evs : List Event) :
    Inv (run step b evs) := by
  have hpres : ∀ (x : Sys) (e : Event), Inv x → Inv (advance step b x e) := by
    intro x e hx
    cases e with
    | parent q f => exact plan0_inv_advance_parent b x q f hx
    | route id liq => exact plan0_inv_advance_route b x id liq hx
    | ack k => exact plan0_inv_advance_ack b x k hx
    | fill k q => exact plan0_inv_advance_fill b x k q hx
  exact run_induction step b Inv inv_start_thm hpres evs

theorem plan0_route_output_of_inv_proof (b : Build) (x : Sys) (id liq : Nat)
    (hx : Inv x) :
    (step b x.st (.route id liq)).2 = expectedRoute x.tr id liq := by
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have hstep : (step b x.st (.route id liq)).2 = (routeBySent x.st id liq).2 := rfl
  rw [hstep, route_snd_eq]
  have hqty : (x.st.parents id).qty = x.tr.qty id := hQty id
  have hsent : (x.st.parents id).sent = x.tr.sent id := hSent id
  have hnp : x.st.nParents = x.tr.nOrders := hNp
  simp only [expectedRoute]
  rw [hnp, hqty, hsent]

theorem req_routes_available_aux_proof : RoutesAvailable step := by
  intro b evs id liq
  exact plan0_route_output_of_inv_proof b (run step b evs) id liq (plan0_inv_run_helper2 b evs)

theorem req_stop_when_filled_aux2 : StopWhenFilled step := by
  intro b evs e pid hexec c hmem hcon
  have hInv := plan0_inv_run_helper2 b evs
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hInv
  have hexec_le_sent : (run step b evs).tr.exec pid ≤ (run step b evs).tr.sent pid :=
    exec_le_sent step b evs pid
  have hsent_eq : ((run step b evs).st.parents pid).sent = (run step b evs).tr.sent pid := hSent pid
  have hqty_eq : ((run step b evs).st.parents pid).qty = (run step b evs).tr.qty pid := hQty pid
  have hle : ((run step b evs).st.parents pid).sent ≤ ((run step b evs).st.parents pid).qty := hLe pid
  have hsent_eq_qty : ((run step b evs).st.parents pid).sent = ((run step b evs).st.parents pid).qty := by
    omega
  cases e with
  | parent q f =>
    have hout : (step b (run step b evs).st (.parent q f)).2 = ([] : List Child) := rfl
    rw [hout] at hmem
    simp at hmem
  | ack k =>
    have hout : (step b (run step b evs).st (.ack k)).2 = ([] : List Child) := rfl
    rw [hout] at hmem
    simp at hmem
  | fill k q =>
    have hout : (step b (run step b evs).st (.fill k q)).2 = ([] : List Child) := step_fill_snd2 b _ k q
    rw [hout] at hmem
    simp at hmem
  | route rid liq =>
    have hstep2 : (step b (run step b evs).st (.route rid liq)).2 = (routeBySent (run step b evs).st rid liq).2 := rfl
    rw [hstep2] at hmem
    have hpar : c.parent = rid := route_mem_parent _ rid liq c hmem
    have hrid : rid = pid := by omega
    have hsent_rid : ((run step b evs).st.parents rid).sent = ((run step b evs).st.parents rid).qty := by
      rw [hrid]; exact hsent_eq_qty
    have hmin_zero : min liq (((run step b evs).st.parents rid).qty - ((run step b evs).st.parents rid).sent) = 0 := by
      rw [← hsent_rid, Nat.sub_self]
      simp
    have hcond : ¬ (rid < (run step b evs).st.nParents ∧ 0 < min liq (((run step b evs).st.parents rid).qty - ((run step b evs).st.parents rid).sent)) := by
      simp [hmin_zero]
    have hout_nil : (routeBySent (run step b evs).st rid liq).2 = ([] : List Child) :=
      routeBySent_snd_nil _ rid liq hcond
    rw [hout_nil] at hmem
    simp at hmem

theorem adv_parent_cum_probe (b : Build) (x : Sys) (q : Nat) (f : Bool) (j : Nat) :
  ((advance step b x (.parent q f)).st.parents j).cum = (if j = x.st.nParents then 0 else (x.st.parents j).cum) := by
  simp only [advance, step]
  by_cases h : j = x.st.nParents <;> simp [upd, h]

theorem adv_parent_exec_probe (b : Build) (x : Sys) (q : Nat) (f : Bool) (j : Nat) :
  (advance step b x (.parent q f)).tr.exec j = x.tr.exec j := by
  have hout : (step b x.st (.parent q f)).2 = ([] : List Child) := rfl
  simp only [advance, hout, tr_exec_record, tr_exec_observe_parent]

theorem invFull_parent4 (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hx : InvFull x) : InvFull (advance step b x (.parent q f)) := by
  obtain ⟨hNp, hQty, hSent, hCum, hNch, hChild, hPar⟩ := hx
  have hstNp : (advance step b x (.parent q f)).st.nParents = x.st.nParents + 1 := by simp only [advance, step]
  have htrNp : (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 := by simp only [advance, step, Truth.observe, Truth.record]
  have hstNch : (advance step b x (.parent q f)).st.nChildren = x.st.nChildren := by simp only [advance, step]
  have htrKids : (advance step b x (.parent q f)).tr.kids = x.tr.kids := by simp only [advance, step, Truth.observe, Truth.record, List.map_nil, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstNp, htrNp, hNp]
  · intro j
    rw [parent_probe3 b x q f j, parent_probe4 b x q f j, hNp, hQty j]
  · intro j
    rw [parent_probe5 b x q f j, parent_probe6 b x q f j]
    by_cases h : j = x.st.nParents
    · subst h
      simp only [if_true]
      have hz : x.tr.sent x.st.nParents = 0 := by
        simp only [Truth.sent]
        rw [← hNp] at hPar
        exact sentFor_all_lt_zero x.tr.kids x.st.nParents hPar x.st.nParents (by omega)
      rw [hz]
    · simp only [h, if_false]; exact hSent j
  · intro j
    rw [adv_parent_cum_probe b x q f j, adv_parent_exec_probe b x q f j]
    by_cases h : j = x.st.nParents
    · subst h
      simp only [if_true]
      have hz : x.tr.exec x.st.nParents = 0 := by
        simp only [Truth.exec]
        rw [← hNp] at hPar
        exact execFor_all_lt_zero x.tr.kids x.st.nParents hPar x.st.nParents (by omega)
      exact hz.symm
    · simp only [h, if_false]; exact hCum j
  · rw [hstNch, htrKids, hNch]
  · intro k c hk
    rw [htrKids] at hk
    have hst : (advance step b x (.parent q f)).st.children = x.st.children := by simp only [advance, step]
    rw [hst]; exact hChild k c hk
  · intro k hk; rw [htrKids] at hk; rw [htrNp]; have h := hPar k hk; omega

theorem invFull_ack6 (b : Build) (x : Sys) (k : Nat)
    (hx : InvFull x) : InvFull (advance step b x (.ack k)) := by
  obtain ⟨hNp, hQty, hSent, hCum, hNch, hChild, hPar⟩ := hx
  have hst : (advance step b x (.ack k)).st = x.st := by simp only [advance, step_ack]
  have htr : (advance step b x (.ack k)).tr = x.tr := by simp only [advance, step_ack, Truth.observe, Truth.record, List.map_nil, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst, htr, hNp]
  · intro j; rw [hst, htr]; exact hQty j
  · intro j; rw [hst, htr]; exact hSent j
  · intro j; rw [hst, htr]; exact hCum j
  · rw [hst, htr, hNch]
  · intro k2 c hc
    have hc2 : x.tr.kids[k2]? = some c := by rw [← htr]; exact hc
    have hcc := hChild k2 c hc2
    have hst2 : (advance step b x (.ack k)).st.children k2 = x.st.children k2 := by rw [hst]
    rw [hst2]; exact hcc
  · intro kk hk
    rw [htr] at hk ⊢
    exact hPar kk hk

theorem adv_route_st_parents_cum5 (b : Build) (x : Sys) (id liq : Nat) (j : Nat) :
  ((advance step b x (.route id liq)).st.parents j).cum = (x.st.parents j).cum := by
  rw [route_adv_st_rfl b x id liq]
  unfold routeBySent
  by_cases h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent) <;> simp [h]
  by_cases hj : j = id
  · subst hj; simp [upd]
  · simp [upd, hj]

theorem adv_route_exec_eq (b : Build) (x : Sys) (id liq : Nat) (j : Nat) :
  (advance step b x (.route id liq)).tr.exec j = x.tr.exec j := by
  rw [route_adv_tr_rfl b x id liq]
  exact tr_exec_record _ _ _













theorem plan3_invFull_advance_route_aux1 (b : Build) (x : Sys) (id liq : Nat)
    (hx : InvFull x) : (advance step b x (.route id liq)).st.nParents = (advance step b x (.route id liq)).tr.nOrders := by
  obtain ⟨hNp, hQty, hSent, hCum, hNch, hChild, hPar⟩ := hx
  have hst : (advance step b x (.route id liq)).st.nParents = x.st.nParents := by
    rw [route_adv_st_rfl]; exact route_fst_np x.st id liq
  have htr : (advance step b x (.route id liq)).tr.nOrders = x.tr.nOrders := by
    rw [route_adv_tr_rfl]; exact tr_nOrders_record2 _ _
  rw [hst, htr, hNp]

theorem plan3_invFull_advance_route_aux2 (b : Build) (x : Sys) (id liq : Nat)
    (hx : InvFull x) : ∀ j, ((advance step b x (.route id liq)).st.parents j).cum = (advance step b x (.route id liq)).tr.exec j := by
  obtain ⟨hNp, hQty, hSent, hCum, hNch, hChild, hPar⟩ := hx
  intro j
  rw [adv_route_st_parents_cum5 b x id liq j, adv_route_exec_eq b x id liq j, hCum j]

theorem plan3_route_child_nil (b : Build) (x : Sys) (id liq : Nat)
    (hChild : ∀ k c, x.tr.kids[k]? = some c → x.st.children k = (⟨c.parent, c.qty, c.done⟩ : ChildRec))
    (h : ¬ (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)))
    (idx : Nat) (c : Kid) (hk : (advance step b x (.route id liq)).tr.kids[idx]? = some c) :
    (advance step b x (.route id liq)).st.children idx = (⟨c.parent, c.qty, c.done⟩ : ChildRec) := by
  have hst : (advance step b x (.route id liq)).st = x.st := route_nil_st x b id liq h
  have htr : (advance step b x (.route id liq)).tr = x.tr := route_nil_tr x b id liq h
  rw [hst]
  have hk2 : x.tr.kids[idx]? = some c := by rw [← htr]; exact hk
  exact hChild idx c hk2

theorem plan3_route_child_cons_old (b : Build) (x : Sys) (id liq : Nat)
    (hNch : x.st.nChildren = x.tr.kids.length)
    (hChild : ∀ k c, x.tr.kids[k]? = some c → x.st.children k = (⟨c.parent, c.qty, c.done⟩ : ChildRec))
    (h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent))
    (idx : Nat) (c : Kid) (hlt : idx < x.tr.kids.length) (hk : (advance step b x (.route id liq)).tr.kids[idx]? = some c) :
    (advance step b x (.route id liq)).st.children idx = (⟨c.parent, c.qty, c.done⟩ : ChildRec) := by
  have htrKids : (advance step b x (.route id liq)).tr.kids =
      x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] :=
    route_cons_tr_kids x b id liq h
  have hk2 : x.tr.kids[idx]? = some c := by
    rw [htrKids] at hk
    have := kids_append_lt x.tr.kids ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ idx hlt
    rw [this] at hk
    exact hk
  have hstChild : (advance step b x (.route id liq)).st.children =
      upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ := by
    rw [route_adv_st_rfl b x id liq]
    unfold routeBySent
    simp [h]
  have hne : idx ≠ x.st.nChildren := by omega
  rw [hstChild]
  simp only [upd, hne, if_false]
  exact hChild idx c hk2

theorem plan3_route_child_cons_new2 (b : Build) (x : Sys) (id liq : Nat)
    (hNch : x.st.nChildren = x.tr.kids.length)
    (h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent))
    (idx : Nat) (c : Kid) (heq : idx = x.tr.kids.length) (hk : (advance step b x (.route id liq)).tr.kids[idx]? = some c) :
    (advance step b x (.route id liq)).st.children idx = (⟨c.parent, c.qty, c.done⟩ : ChildRec) := by
  have htrKids : (advance step b x (.route id liq)).tr.kids =
      x.tr.kids ++ [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩] :=
    route_cons_tr_kids x b id liq h
  have hc : c = ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ := by
    rw [htrKids, heq] at hk
    simp at hk
    exact hk.symm
  have hstChild : (advance step b x (.route id liq)).st.children =
      upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ := by
    rw [route_adv_st_rfl b x id liq]
    unfold routeBySent
    simp [h]
  subst hc
  rw [hstChild, heq, ← hNch]
  simp [upd]

theorem plan3_idx_lt (l : List Kid) (idx : Nat) (c : Kid) (hk : l[idx]? = some c) : idx < l.length := by
  induction l generalizing idx with
  | nil => simp at hk
  | cons a as ih =>
    cases idx with
    | zero => simp
    | succ n =>
      simp at hk
      have h := ih n hk
      simp
      omega

theorem plan3_invFull_advance_route (b : Build) (x : Sys) (id liq : Nat)
    (hx : InvFull x) : InvFull (advance step b x (.route id liq)) := by
  obtain ⟨hNp, hQty, hSent, hCum, hNch, hChild, hPar⟩ := hx
  have hc := plan2_route_counts b x id liq hNp hNch
  have hq := plan2_route_qty b x id liq hQty
  have hs := plan2_route_sent b x id liq hSent
  have hcum : ∀ j, ((advance step b x (.route id liq)).st.parents j).cum = (advance step b x (.route id liq)).tr.exec j := by
    intro j
    rw [adv_route_st_parents_cum5 b x id liq j, adv_route_exec_eq b x id liq j, hCum j]
  have hklt := plan2_route_kids_lt b x id liq hNp hPar
  refine ⟨hc.1, hq, hs, hcum, hc.2, ?_, hklt⟩
  intro idx c hk
  by_cases h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · have hlen : (advance step b x (.route id liq)).tr.kids.length = x.tr.kids.length + 1 :=
      route_adv_len_cons x b id liq h
    have hlt_adv : idx < x.tr.kids.length + 1 := by
      rw [← hlen]
      exact plan3_idx_lt _ idx c hk
    by_cases hlt : idx < x.tr.kids.length
    · exact plan3_route_child_cons_old b x id liq hNch hChild h idx c hlt hk
    · have heq : idx = x.tr.kids.length := by omega
      exact plan3_route_child_cons_new2 b x id liq hNch h idx c heq hk
  · exact plan3_route_child_nil b x id liq hChild h idx c hk

theorem probe_set_ne2 (l : List Kid) (k idx : Nat) (v : Kid) (h : idx ≠ k) :
    (l.set k v)[idx]? = l[idx]? := by
  exact List.getElem?_set_ne h.symm

theorem my_some_lt_len (l : List Kid) (k : Nat) (c : Kid) (h : l[k]? = some c) : k < l.length := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ k => simp at h; have := ih k h; simp; omega







theorem plan4_getElem_set_ne_idx (l : List Kid) (k idx : Nat) (v : Kid)
    (h : idx ≠ k) :
    (l.set k v)[idx]? = l[idx]? :=
  probe_set_ne2 l k idx v h




theorem plan4_fill_tr_kids_match2 (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr.kids =
      match x.tr.kids[k]? with
      | some c => x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) }
      | none => x.tr.kids := by
  have h2 : (step b x.st (.fill k q)).2 = ([] : List Child) := step_fill_snd2 b x.st k q
  have hAdv : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record (step b x.st (.fill k q)).2 := rfl
  rw [hAdv, h2]
  have hrec : ∀ (t : Truth), (t.record ([] : List Child)).kids = t.kids := fun t => by simp [Truth.record]
  rw [hrec]
  cases h : x.tr.kids[k]? <;> simp [Truth.observe, h]

theorem plan4_fill_tr_kids_match (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr.kids =
      match x.tr.kids[k]? with
      | some c => x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) }
      | none => x.tr.kids := by
  have h2 : (step b x.st (.fill k q)).2 = ([] : List Child) := step_fill_snd2 b x.st k q
  have hAdv : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record (step b x.st (.fill k q)).2 := rfl
  rw [hAdv, h2]
  have hrec : ∀ (t : Truth), (t.record ([] : List Child)).kids = t.kids := fun t => by simp [Truth.record]
  rw [hrec]
  cases h : x.tr.kids[k]? <;> simp [Truth.observe, h]

theorem plan4_same_aux_test (l : List Kid) (k : Nat) (old : Kid) (d : Nat)
    (h : l[k]? = some old) :
    (l.set k { old with done := d })[k]? = some { old with done := d } := by
  induction l generalizing k with
  | nil => simp_all
  | cons a as ih =>
    cases k with
    | zero => simp_all
    | succ n => simp_all

theorem plan4_getElem_set_same (l : List Kid) (k : Nat) (old : Kid) (d : Nat)
    (h : l[k]? = some old) :
    (l.set k { old with done := d })[k]? = some { old with done := d } := by
  induction l generalizing k with
  | nil => simp_all
  | cons a as ih =>
    cases k with
    | zero => simp_all
    | succ n => simp_all

theorem plan4_getElem_set_ne_idx_proof : True := by trivial

theorem plan4_getElem_set_ne_idx_aux (l : List Kid) (k idx : Nat) (v : Kid) (h : idx ≠ k) : (l.set k v)[idx]? = l[idx]? := by
  induction l generalizing k idx with
  | nil =>
    cases k with
    | zero => cases idx with | zero => simp at h | succ n => rfl
    | succ k => cases idx with | zero => rfl | succ n => rfl
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
        simp only [List.set_cons_succ]
        have h2 : n ≠ k := by omega
        exact ih k n h2

theorem plan4_ne_tmp (l : List Kid) (k idx : Nat) (v : Kid) (h : idx ≠ k) : (l.set k v)[idx]? = l[idx]? := by
  induction l generalizing k idx with
  | nil =>
    cases k with
    | zero => cases idx with | zero => simp at h | succ n => rfl
    | succ k => cases idx with | zero => rfl | succ n => rfl
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
        simp only [List.set_cons_succ]
        have h2 : n ≠ k := by omega
        exact ih k n h2

theorem plan4_ne_inline_check (l : List Kid) (k idx : Nat) (v : Kid) (h : idx ≠ k) : (l.set k v)[idx]? = l[idx]? := by
  exact probe_set_ne2 l k idx v h

theorem plan4_fill_children_core_test (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).st.children =
      if k < x.st.nChildren then
        upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }
      else x.st.children := by
  simp only [advance, step]
  split <;> simp_all

theorem plan4_fill_st_children_eq (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).st.children =
      if k < x.st.nChildren then
        upd x.st.children k { (x.st.children k) with
          done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }
      else x.st.children := by
  simp only [advance, step]
  by_cases h : k < x.st.nChildren <;> simp [h]

theorem plan4_exists_of_lt (l : List Kid) (k : Nat) (h : k < l.length) : ∃ c, l[k]? = some c := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => exact ⟨a, rfl⟩
    | succ k =>
      simp at h
      obtain ⟨c, hc⟩ := ih k h
      exact ⟨c, by simp [hc]⟩

theorem plan4_none_not_lt (l : List Kid) (k : Nat) (h : l[k]? = none) : ¬ k < l.length := by
  intro hlt
  obtain ⟨c, hc⟩ := plan4_exists_of_lt l k hlt
  rw [hc] at h
  simp at h

theorem plan4_upd_ne_check (f : Nat → ChildRec) (kk idx : Nat) (v : ChildRec) (h : idx ≠ kk) :
    upd f kk v idx = f idx := upd_ne' f kk idx v h

theorem plan4_tmp_a (x : Sys) (k q : Nat) (old : Kid) (idx : Nat) :
    (x.tr.kids.set k ⟨old.parent, old.qty, old.done + min q (old.qty - old.done)⟩)[idx]? = x.tr.kids[idx]? ∨ True := by
  by_cases heq : idx = k
  · simp [heq]
  · have h := probe_set_ne2 x.tr.kids k idx ⟨old.parent, old.qty, old.done + min q (old.qty - old.done)⟩ heq
    exact Or.inl h

theorem plan4_subst_check (x : Sys) (k idx : Nat) (heq : idx = k) (c : Kid)
    (hk : x.tr.kids[idx]? = some c) : x.tr.kids[k]? = some c := by
  rw [← heq]
  exact hk

theorem plan4_fill_children_core (b : Build) (x : Sys) (k q : Nat)
    (hNch : x.st.nChildren = x.tr.kids.length)
    (hChild : ∀ i cc, x.tr.kids[i]? = some cc → x.st.children i = (⟨cc.parent, cc.qty, cc.done⟩ : ChildRec)) :
    ∀ (idx : Nat) (c : Kid), (advance step b x (.fill k q)).tr.kids[idx]? = some c →
      (advance step b x (.fill k q)).st.children idx = (⟨c.parent, c.qty, c.done⟩ : ChildRec) := by
  intro idx c hk
  have hTrEq := plan4_fill_tr_kids_match b x k q
  have hStEq := plan4_fill_st_children_eq b x k q
  cases hOld : x.tr.kids[k]? with
  | none =>
    have hTr2 : (advance step b x (.fill k q)).tr.kids = x.tr.kids := by
      rw [hTrEq, hOld]
    have hNotLt : ¬ k < x.tr.kids.length := plan4_none_not_lt x.tr.kids k hOld
    have hNotLtS : ¬ k < x.st.nChildren := by rw [hNch]; exact hNotLt
    have hk2 : x.tr.kids[idx]? = some c := by rw [← hTr2]; exact hk
    have hSt2 : (advance step b x (.fill k q)).st.children idx = x.st.children idx := by
      rw [hStEq, if_neg hNotLtS]
    rw [hSt2]
    exact hChild idx c hk2
  | some old =>
    have hLt : k < x.tr.kids.length := my_some_lt_len x.tr.kids k old hOld
    have hLtS : k < x.st.nChildren := by rw [hNch]; exact hLt
    have hTr2 : (advance step b x (.fill k q)).tr.kids =
        x.tr.kids.set k { old with done := old.done + min q (old.qty - old.done) } := by
      rw [hTrEq, hOld]
    have hSt2 : (advance step b x (.fill k q)).st.children =
        upd x.st.children k { (x.st.children k) with
          done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } := by
      rw [hStEq, if_pos hLtS]
    by_cases heq : idx = k
    · rw [heq] at hk
      have hSetK := plan4_getElem_set_same x.tr.kids k old (old.done + min q (old.qty - old.done)) hOld
      rw [hTr2] at hk
      rw [hSetK] at hk
      simp at hk
      subst hk
      rw [heq, hSt2]
      have hCK : x.st.children k = (⟨old.parent, old.qty, old.done⟩ : ChildRec) := hChild k old hOld
      rw [hCK]
      simp [upd]
    · have hSetNe : (x.tr.kids.set k { old with done := old.done + min q (old.qty - old.done) })[idx]? = x.tr.kids[idx]? :=
        probe_set_ne2 x.tr.kids k idx { old with done := old.done + min q (old.qty - old.done) } heq
      rw [hTr2, hSetNe] at hk
      have hCKidx : x.st.children idx = (⟨c.parent, c.qty, c.done⟩ : ChildRec) := hChild idx c hk
      rw [hSt2]
      have h2 : upd x.st.children k { (x.st.children k) with
          done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } idx = x.st.children idx :=
        upd_ne' x.st.children k idx _ heq
      rw [h2, hCKidx]

theorem plan3_fill_children_step (b : Build) (x : Sys) (k q : Nat)
    (hx : InvFull x) :
    ∀ (idx : Nat) (c : Kid), (advance step b x (.fill k q)).tr.kids[idx]? = some c →
      (advance step b x (.fill k q)).st.children idx = (⟨c.parent, c.qty, c.done⟩ : ChildRec) := by
  obtain ⟨hNp, hQty, hSent, hCum, hNch, hChild, hPar⟩ := hx
  exact plan4_fill_children_core b x k q hNch hChild

theorem plan3_fill_st_cum_probe (b : Build) (x : Sys) (k q j : Nat)
    (hLtS : k < x.st.nChildren) :
    ((advance step b x (.fill k q)).st.parents j).cum =
      (if j = (x.st.children k).parent then (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) else (x.st.parents j).cum) := by
  simp only [advance, step]
  simp only [hLtS, ↓reduceIte]
  by_cases hj : j = (x.st.children k).parent
  · simp [upd, hj]
  · simp [upd, hj]

theorem plan3_fill_cum_step (b : Build) (x : Sys) (k q : Nat)
    (hx : InvFull x) :
    ∀ j : Nat, ((advance step b x (.fill k q)).st.parents j).cum
      = (advance step b x (.fill k q)).tr.exec j := by
  obtain ⟨hNp, hQty, hSent, hCum, hNch, hChild, hPar⟩ := hx
  intro j
  have hSnd : (step b x.st (.fill k q)).2 = ([] : List Child) := step_fill_snd2 b x.st k q
  have hTrAdv : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record ([] : List Child) := by
    simp only [advance, hSnd]
  have hTrExec : ∀ jj, (advance step b x (.fill k q)).tr.exec jj = (x.tr.observe (.fill k q)).exec jj := by
    intro jj; rw [hTrAdv]; exact tr_exec_record _ _ _
  cases hOld : x.tr.kids[k]? with
  | none =>
    have hTrEq : (advance step b x (.fill k q)).tr.exec j = x.tr.exec j := by
      rw [hTrExec j, tr_exec_observe_fill_none x.tr k q hOld j]
    have hNotLt : ¬ k < x.tr.kids.length := plan4_none_not_lt x.tr.kids k hOld
    have hNotLtS : ¬ k < x.st.nChildren := by rw [hNch]; exact hNotLt
    have hSt : ((advance step b x (.fill k q)).st.parents j).cum = (x.st.parents j).cum := by
      simp only [advance, step]
      simp [hNotLtS]
    rw [hTrEq, hSt, hCum j]
  | some old =>
    have hLt : k < x.tr.kids.length := my_some_lt_len x.tr.kids k old hOld
    have hLtS : k < x.st.nChildren := by rw [hNch]; exact hLt
    have hCK : x.st.children k = (⟨old.parent, old.qty, old.done⟩ : ChildRec) := hChild k old hOld
    have hTrEq : (advance step b x (.fill k q)).tr.exec j = x.tr.exec j + (if old.parent = j then min q (old.qty - old.done) else 0) := by
      rw [hTrExec j, tr_exec_observe_fill_eq x.tr k q old hOld j]
    have hSt := plan3_fill_st_cum_probe b x k q j hLtS
    rw [hCK] at hSt
    simp only at hSt
    rw [hSt, hTrEq]
    by_cases hj : j = old.parent
    · subst hj
      rw [if_pos rfl, if_pos rfl, hCum]
    · rw [if_neg hj, if_neg (Ne.symm hj), Nat.add_zero, hCum j]

theorem plan3_fill_nOrders_tmp (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders := by
  have hsnd : (step b x.st (.fill k q)).2 = ([] : List Child) := step_fill_snd2 b x.st k q
  have hAdv : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record ([] : List Child) := by
    simp only [advance, hsnd]
  rw [hAdv, tr_nOrders_record2]
  exact tr_nOrders_fill x.tr k q

theorem plan3_fill_stNp_tmp (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).st.nParents = x.st.nParents := by
  simp only [advance]
  exact fill_state_np_all b x.st k q

theorem plan3_fill_stNch_tmp (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).st.nChildren = x.st.nChildren := by
  simp only [advance]
  exact fill_state_nch_all b x.st k q

theorem plan3_fill_trQty_tmp (b : Build) (x : Sys) (k q j : Nat) :
    (advance step b x (.fill k q)).tr.qty j = x.tr.qty j := by
  have hsnd : (step b x.st (.fill k q)).2 = ([] : List Child) := step_fill_snd2 b x.st k q
  have hAdv : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record ([] : List Child) := by
    simp only [advance, hsnd]
  rw [hAdv, tr_qty_record2]
  exact tr_qty_observe_fill x.tr k q j

theorem plan3_fill_stQty_tmp (b : Build) (x : Sys) (k q j : Nat) :
    ((advance step b x (.fill k q)).st.parents j).qty = (x.st.parents j).qty := by
  simp only [advance]
  exact fill_state_qty_all b x.st k q j

theorem plan3_fill_stSent_tmp (b : Build) (x : Sys) (k q j : Nat) :
    ((advance step b x (.fill k q)).st.parents j).sent = (x.st.parents j).sent := by
  simp only [advance]
  exact fill_state_sent_all b x.st k q j

theorem plan3_fill_trSent_tmp (b : Build) (x : Sys) (k q j : Nat) :
    (advance step b x (.fill k q)).tr.sent j = x.tr.sent j := by
  have hsnd : (step b x.st (.fill k q)).2 = ([] : List Child) := step_fill_snd2 b x.st k q
  have hAdv : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record ([] : List Child) := by
    simp only [advance, hsnd]
  rw [hAdv, tr_sent_record2]
  simp only [List.map_nil, sentFor_nil, Nat.add_zero]
  cases h : x.tr.kids[k]? with
  | none =>
    have h2 := tr_sent_observe_fill_none x.tr k q h j
    simpa [Truth.sent] using h2
  | some c =>
    have h2 := tr_sent_observe_fill_eq x.tr k q c h j
    simpa [Truth.sent] using h2

theorem plan3_fill_kidsLen_tmp (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr.kids.length = x.tr.kids.length := by
  have hTrEq := plan4_fill_tr_kids_match b x k q
  rw [hTrEq]
  cases h : x.tr.kids[k]? with
  | none => rfl
  | some c => simp

theorem plan3_fill_kidsPar_tmp (b : Build) (x : Sys) (k q : Nat)
    (hPar : ∀ k_1 ∈ x.tr.kids, k_1.parent < x.tr.nOrders) :
    ∀ kk ∈ (advance step b x (.fill k q)).tr.kids, kk.parent < (advance step b x (.fill k q)).tr.nOrders := by
  have hTrEq := plan4_fill_tr_kids_match b x k q
  have hN := plan3_fill_nOrders_tmp b x k q
  intro y hy
  rw [hN]
  rw [hTrEq] at hy
  cases h : x.tr.kids[k]? with
  | none =>
    simp [h] at hy
    exact hPar y hy
  | some c =>
    simp [h] at hy
    rcases List.mem_or_eq_of_mem_set hy with hy2 | hy2
    · exact hPar y hy2
    · subst hy2
      have hmem : c ∈ x.tr.kids := List.mem_of_getElem? h
      have hlt := hPar c hmem
      simp at hlt ⊢
      omega

theorem plan3_invFull_advance_fill_proof (b : Build) (x : Sys) (k q : Nat)
    (hx : InvFull x) : InvFull (advance step b x (.fill k q)) := by
  obtain ⟨hNp, hQty, hSent, hCum, hNch, hChild, hPar⟩ := hx
  have h1 : (advance step b x (.fill k q)).st.nParents = (advance step b x (.fill k q)).tr.nOrders := by
    rw [plan3_fill_stNp_tmp b x k q, plan3_fill_nOrders_tmp b x k q, hNp]
  have h2 : ∀ id, ((advance step b x (.fill k q)).st.parents id).qty = (advance step b x (.fill k q)).tr.qty id := by
    intro j
    rw [plan3_fill_stQty_tmp b x k q j, plan3_fill_trQty_tmp b x k q j, hQty j]
  have h3 : ∀ id, ((advance step b x (.fill k q)).st.parents id).sent = (advance step b x (.fill k q)).tr.sent id := by
    intro j
    rw [plan3_fill_stSent_tmp b x k q j, plan3_fill_trSent_tmp b x k q j, hSent j]
  have h4 : ∀ id, ((advance step b x (.fill k q)).st.parents id).cum = (advance step b x (.fill k q)).tr.exec id :=
    plan3_fill_cum_step b x k q ⟨hNp, hQty, hSent, hCum, hNch, hChild, hPar⟩
  have h5 : (advance step b x (.fill k q)).st.nChildren = (advance step b x (.fill k q)).tr.kids.length := by
    rw [plan3_fill_stNch_tmp b x k q, plan3_fill_kidsLen_tmp b x k q, hNch]
  have h6 : ∀ kk c, (advance step b x (.fill k q)).tr.kids[kk]? = some c →
      (advance step b x (.fill k q)).st.children kk = (⟨c.parent, c.qty, c.done⟩ : ChildRec) :=
    plan3_fill_children_step b x k q ⟨hNp, hQty, hSent, hCum, hNch, hChild, hPar⟩
  have h7 : ∀ kk ∈ (advance step b x (.fill k q)).tr.kids, kk.parent < (advance step b x (.fill k q)).tr.nOrders :=
    plan3_fill_kidsPar_tmp b x k q hPar
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem plan3_fill_inline_nOrders (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders := by
  have hsnd : (step b x.st (.fill k q)).2 = ([] : List Child) := step_fill_snd2 b x.st k q
  have hAdv : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record ([] : List Child) := by
    simp only [advance, hsnd]
  rw [hAdv, tr_nOrders_record2]
  exact tr_nOrders_fill x.tr k q

theorem plan3_fill_inline_check2 : True := by trivial

theorem plan3_invFull_advance_fill_dup_test : True := by trivial







theorem plan5_fill_cum (b : Build) (x : Sys) (k q : Nat) (hx : InvFull x) :
    ∀ j, ((advance step b x (.fill k q)).st.parents j).cum
      = (advance step b x (.fill k q)).tr.exec j :=
  plan3_fill_cum_step b x k q hx




theorem plan5_fill_children (b : Build) (x : Sys) (k q : Nat) (hx : InvFull x) :
    ∀ (idx : Nat) (c : Kid), (advance step b x (.fill k q)).tr.kids[idx]? = some c →
      (advance step b x (.fill k q)).st.children idx = (⟨c.parent, c.qty, c.done⟩ : ChildRec) :=
  plan3_fill_children_step b x k q hx


theorem plan5_fill_easy_parts (b : Build) (x : Sys) (k q : Nat) (hx : InvFull x) :
    (advance step b x (.fill k q)).st.nParents = (advance step b x (.fill k q)).tr.nOrders
    ∧ (advance step b x (.fill k q)).st.nChildren = (advance step b x (.fill k q)).tr.kids.length
    ∧ (∀ j, ((advance step b x (.fill k q)).st.parents j).qty = (advance step b x (.fill k q)).tr.qty j)
    ∧ (∀ j, ((advance step b x (.fill k q)).st.parents j).sent = (advance step b x (.fill k q)).tr.sent j)
    ∧ (∀ kk ∈ (advance step b x (.fill k q)).tr.kids, kk.parent < (advance step b x (.fill k q)).tr.nOrders) := by
  obtain ⟨hNp, hQty, hSent, hCum, hNch, hChild, hPar⟩ := hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [plan3_fill_stNp_tmp b x k q, plan3_fill_nOrders_tmp b x k q, hNp]
  · rw [plan3_fill_stNch_tmp b x k q, plan3_fill_kidsLen_tmp b x k q, hNch]
  · intro j
    rw [plan3_fill_stQty_tmp b x k q j, plan3_fill_trQty_tmp b x k q j, hQty j]
  · intro j
    rw [plan3_fill_stSent_tmp b x k q j, plan3_fill_trSent_tmp b x k q j, hSent j]
  · exact plan3_fill_kidsPar_tmp b x k q hPar

theorem plan5_fill_tr_exec_match (b : Build) (x : Sys) (k q : Nat) (j : Nat) :
    (advance step b x (.fill k q)).tr.exec j =
      match x.tr.kids[k]? with
      | some c => x.tr.exec j + (if c.parent = j then min q (c.qty - c.done) else 0)
      | none => x.tr.exec j := by
  have hsnd : (step b x.st (.fill k q)).2 = ([] : List Child) := step_fill_snd2 b x.st k q
  have hAdv2 : (advance step b x (.fill k q)).tr = (x.tr.observe (.fill k q)).record ([] : List Child) := by
    simp only [advance, hsnd]
  have hExec : (advance step b x (.fill k q)).tr.exec j = (x.tr.observe (.fill k q)).exec j := by
    rw [hAdv2]
    exact tr_exec_record _ _ _
  rw [hExec]
  cases h : x.tr.kids[k]? with
  | none => exact tr_exec_observe_fill_none x.tr k q h j
  | some c => exact tr_exec_observe_fill_eq x.tr k q c h j

theorem plan5_fill_st_cum_match (b : Build) (x : Sys) (k q : Nat) (j : Nat) :
    ((advance step b x (.fill k q)).st.parents j).cum =
      if k < x.st.nChildren then
        (if j = (x.st.children k).parent
         then (x.st.parents j).cum + min q ((x.st.children k).qty - (x.st.children k).done)
         else (x.st.parents j).cum)
      else (x.st.parents j).cum := by
  simp only [advance, step]
  by_cases h : k < x.st.nChildren
  · simp only [h, ↓reduceIte]
    by_cases hj : j = (x.st.children k).parent
    · subst hj
      simp [upd]
    · simp [upd, hj]
  · simp [h]

theorem plan5_fill_cum_proof : True := by trivial

theorem plan5_fill_cum_aux (b : Build) (x : Sys) (k q : Nat) (hx : InvFull x) :
    ∀ j, ((advance step b x (.fill k q)).st.parents j).cum
      = (advance step b x (.fill k q)).tr.exec j :=
  plan3_fill_cum_step b x k q hx

theorem plan5_fill_kids_children_raw (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr.kids =
      (match x.tr.kids[k]? with
       | some c => x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) }
       | none => x.tr.kids)
    ∧ (advance step b x (.fill k q)).st.children =
      (if k < x.st.nChildren then
         upd x.st.children k { (x.st.children k) with
           done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }
       else x.st.children) :=
  ⟨plan4_fill_tr_kids_match b x k q, plan4_fill_st_children_eq b x k q⟩

theorem plan5_fill_children_pf (b : Build) (x : Sys) (k q : Nat) (hx : InvFull x) :
    ∀ (idx : Nat) (c : Kid), (advance step b x (.fill k q)).tr.kids[idx]? = some c →
      (advance step b x (.fill k q)).st.children idx = (⟨c.parent, c.qty, c.done⟩ : ChildRec) :=
  plan3_fill_children_step b x k q hx

theorem plan3_invFull_advance_fill (b : Build) (x : Sys) (k q : Nat)
    (hx : InvFull x) : InvFull (advance step b x (.fill k q)) :=
  plan3_invFull_advance_fill_proof b x k q hx

theorem plan3_invFull_run_aux : InvFull start := invFull_start

theorem plan3_invFull_run (b : Build) (evs : List Event) :
    InvFull (run step b evs) := by
  have hpres : ∀ (x : Sys) (e : Event), InvFull x → InvFull (advance step b x e) := by
    intro x e hx
    cases e with
    | parent q f => exact invFull_parent4 b x q f hx
    | route id liq => exact plan3_invFull_advance_route b x id liq hx
    | ack k => exact invFull_ack6 b x k hx
    | fill k q => exact plan3_invFull_advance_fill_proof b x k q hx
  exact run_induction step b InvFull invFull_start hpres evs

theorem plan3_req_fill_accounting : FillAccounting step := by
  intro b evs id _
  have hI := plan3_invFull_run b evs
  exact hI.2.2.2.1 id

theorem req_fill_accounting_pf : FillAccounting step := plan3_req_fill_accounting

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> constructor <;> rfl

theorem req_routes_available : RoutesAvailable step := by
  intro b evs id liq
  exact plan0_route_output_of_inv_proof b (run step b evs) id liq (plan0_inv_run_helper2 b evs)

theorem req_never_overroute     : NeverOverroute step := by
  intro b evs id
  have hx := plan0_inv_run_helper2 b evs
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have h1 : ((run step b evs).st.parents id).sent = (run step b evs).tr.sent id := hSent id
  have h2 : ((run step b evs).st.parents id).qty = (run step b evs).tr.qty id := hQty id
  have h3 : ((run step b evs).st.parents id).sent ≤ ((run step b evs).st.parents id).qty := hLe id
  omega

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e pid hexec c hmem hcon
  have hInv := plan0_inv_run_helper2 b evs
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hInv
  have hexec_le_sent : (run step b evs).tr.exec pid ≤ (run step b evs).tr.sent pid :=
    exec_le_sent step b evs pid
  have hsent_eq : ((run step b evs).st.parents pid).sent = (run step b evs).tr.sent pid := hSent pid
  have hqty_eq : ((run step b evs).st.parents pid).qty = (run step b evs).tr.qty pid := hQty pid
  have hle : ((run step b evs).st.parents pid).sent ≤ ((run step b evs).st.parents pid).qty := hLe pid
  have hsent_eq_qty : ((run step b evs).st.parents pid).sent = ((run step b evs).st.parents pid).qty := by
    omega
  cases e with
  | parent q f =>
    have hout : (step b (run step b evs).st (.parent q f)).2 = ([] : List Child) := rfl
    rw [hout] at hmem
    simp at hmem
  | ack k =>
    have hout : (step b (run step b evs).st (.ack k)).2 = ([] : List Child) := rfl
    rw [hout] at hmem
    simp at hmem
  | fill k q =>
    have hout : (step b (run step b evs).st (.fill k q)).2 = ([] : List Child) := step_fill_snd2 b _ k q
    rw [hout] at hmem
    simp at hmem
  | route rid liq =>
    have hstep2 : (step b (run step b evs).st (.route rid liq)).2 = (routeBySent (run step b evs).st rid liq).2 := rfl
    rw [hstep2] at hmem
    have hpar : c.parent = rid := route_mem_parent _ rid liq c hmem
    have hrid : rid = pid := by omega
    have hsent_rid : ((run step b evs).st.parents rid).sent = ((run step b evs).st.parents rid).qty := by
      rw [hrid]; exact hsent_eq_qty
    have hmin_zero : min liq (((run step b evs).st.parents rid).qty - ((run step b evs).st.parents rid).sent) = 0 := by
      rw [← hsent_rid, Nat.sub_self]
      simp
    have hcond : ¬ (rid < (run step b evs).st.nParents ∧ 0 < min liq (((run step b evs).st.parents rid).qty - ((run step b evs).st.parents rid).sent)) := by
      simp [hmin_zero]
    have hout_nil : (routeBySent (run step b evs).st rid liq).2 = ([] : List Child) :=
      routeBySent_snd_nil _ rid liq hcond
    rw [hout_nil] at hmem
    simp at hmem

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  have hx := plan0_inv_run_helper2 b evs
  obtain ⟨hNp, hQty, hSent, hNch, hPar, hLe⟩ := hx
  have h1 : (run step b evs).tr.exec id ≤ (run step b evs).tr.sent id :=
    exec_le_sent step b evs id
  have h2 : ((run step b evs).st.parents id).sent = (run step b evs).tr.sent id := hSent id
  have h3 : ((run step b evs).st.parents id).qty = (run step b evs).tr.qty id := hQty id
  have h4 : ((run step b evs).st.parents id).sent ≤ ((run step b evs).st.parents id).qty := hLe id
  omega

theorem req_fill_accounting : FillAccounting step := plan3_req_fill_accounting

end OrderRouter
