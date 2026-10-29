import OrderRouter.Spec
import OrderRouter.Lemmas
namespace OrderRouter

def routeBySent (s : State) (id liq : Nat) : State × List Child :=
  let p := s.parents id
  let c := min liq (p.qty - p.sent)
  if id < s.nParents ∧ 0 < c then
    ({ s with parents := upd s.parents id { p with sent := p.sent + c },
              nChildren := s.nChildren + 1,
              children := upd s.children s.nChildren ⟨id, c, 0⟩ }, [⟨id, c⟩])
  else (s, [])

def powerPegPath (b : Build) (p : ParentRec) : Bool := false

def routePowerPeg (s : State) (id liq : Nat) : State × List Child :=
  routeBySent s id liq

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
      ({ s with parents := upd s.parents c.parent { p with cum := p.cum + x },
                children := upd s.children k { c with done := c.done + x } }, [])
    else (s, [])

theorem tmp_test : True := by trivial

theorem tmp_test2 : 1 = 1 := rfl

theorem myhelper1 : True := trivial

theorem mytest_hello : True := trivial

theorem mytest_lemma_check : 2 = 2 := rfl

theorem myroute_unfold (s : State) (id liq : Nat) :
    routeBySent s id liq =
    let p := s.parents id
    let c := min liq (p.qty - p.sent)
    if id < s.nParents ∧ 0 < c then
      ({ s with parents := upd s.parents id { p with sent := p.sent + c },
                nChildren := s.nChildren + 1,
                children := upd s.children s.nChildren ⟨id, c, 0⟩ }, [⟨id, c⟩])
    else (s, []) := by rfl

theorem myupd_same (f : Nat → Nat) (k v : Nat) : upd f k v k = v := by simp [upd]

theorem myadvance_route (b : Build) (x : Sys) (id liq : Nat) :
    (step b x.st (.route id liq)).2 = (routeBySent x.st id liq).2 := by
  simp [step]

theorem my_sent_zero_helper (l : List Kid) (id : Nat) (h : ∀ k ∈ l, k.parent ≠ id) : sentFor l id = 0 := by induction l with | nil => rfl | cons a as ih => simp only [sentFor_cons]; have ha : a.parent ≠ id := h a (by simp); have ht : ∀ k ∈ as, k.parent ≠ id := fun k hk => h k (by simp [hk]); simp [ha, ih ht]

theorem mytest_inv_def : True := trivial

theorem my_rec_sent (t : Truth) (out : List Child) (id : Nat) :
    (t.record out).sent id = t.sent id + sentFor (out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id := by
  simp [Truth.record, Truth.sent, sentFor_append]

theorem my_rec_exec (t : Truth) (out : List Child) (id : Nat) :
    (t.record out).exec id = t.exec id := by
  simp [Truth.record, Truth.exec, execFor_append, execFor_new]

theorem my_rec_nOrders (t : Truth) (out : List Child) : (t.record out).nOrders = t.nOrders := by
  simp [Truth.record]

theorem my_rec_qty (t : Truth) (out : List Child) : (t.record out).qty = t.qty := by
  simp [Truth.record]

theorem my_obs_parent_sent (t : Truth) (q : Nat) (f : Bool) (id : Nat) :
    (t.observe (.parent q f)).sent id = t.sent id := by
  simp [Truth.observe, Truth.sent]

theorem my_obs_parent_exec (t : Truth) (q : Nat) (f : Bool) (id : Nat) :
    (t.observe (.parent q f)).exec id = t.exec id := by
  simp [Truth.observe, Truth.exec]

theorem my_route_cases (s : State) (id liq : Nat) :
    (routeBySent s id liq).2 = [] ∨
    (routeBySent s id liq).2 = [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] := by
  unfold routeBySent
  simp only
  split
  · simp
  · simp

theorem my_obs_route_eq (t : Truth) (id liq : Nat) :
    t.observe (.route id liq) = t := by simp [Truth.observe]

theorem my_obs_ack_eq (t : Truth) (k : Nat) :
    t.observe (.ack k) = t := by simp [Truth.observe]

theorem my_obs_parent_eq (t : Truth) (q : Nat) (f : Bool) :
    (t.observe (.parent q f)).kids = t.kids ∧ (t.observe (.parent q f)).nOrders = t.nOrders + 1 := by
  constructor <;> simp [Truth.observe]

theorem my_step_parent_out (b : Build) (s : State) (q : Nat) (f : Bool) :
    (step b s (.parent q f)).2 = [] := by simp [step]

theorem my_step_ack_out (b : Build) (s : State) (k : Nat) :
    (step b s (.ack k)).2 = [] := by simp [step]

theorem my_step_fill_out (b : Build) (s : State) (k q : Nat) :
    (step b s (.fill k q)).2 = [] := by simp [step]; split <;> rfl

theorem my_step_route_eq (b : Build) (s : State) (id liq : Nat) :
    step b s (.route id liq) = routeBySent s id liq := by simp [step]

def InvStop (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  (∀ id, (x.st.parents id).sent = x.tr.sent id) ∧
  (∀ id, id < x.tr.nOrders → (x.st.parents id).qty = x.tr.qty id) ∧
  (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ k, k < x.st.nChildren → ((x.st.children k).parent < x.st.nParents)) ∧
  (∀ id, (x.st.parents id).sent ≤ (x.st.parents id).qty)

theorem invStop_base : InvStop start := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro id; rfl
  · intro id h; simp [start, Truth.empty] at h
  · intro id; rfl
  · intro k h; simp [start, init] at h
  · intro id; simp [start, init]

theorem upd_eq {α : Type} (f : Nat → α) (k : Nat) (v : α) : upd f k v k = v := by simp [upd]

theorem upd_neq {α : Type} (f : Nat → α) (k j : Nat) (v : α) (h : j ≠ k) : upd f k v j = f j := by simp [upd, h]

theorem upd_eq' {α : Type} (f : Nat → α) (k : Nat) (v : α) (j : Nat) (h : j = k) : upd f k v j = v := by simp [upd, h]

def InvAll (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  (∀ id, (x.st.parents id).sent = x.tr.sent id) ∧
  (∀ id, id < x.tr.nOrders → (x.st.parents id).qty = x.tr.qty id) ∧
  (∀ id, (x.st.parents id).cum = x.tr.exec id) ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
  (∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → c.parent < x.tr.nOrders) ∧
  (∀ id, (x.st.parents id).sent ≤ (x.st.parents id).qty)

theorem invAll_base : InvAll start := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro id; rfl
  · intro id h; simp [start, Truth.empty] at h
  · intro id; rfl
  · intro k c h; simp [start, Truth.empty] at h
  · intro k c h; simp [start, Truth.empty] at h
  · intro id; simp [start, init]

theorem my_exec_zero_helper (l : List Kid) (id : Nat) (h : ∀ k ∈ l, k.parent ≠ id) : execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent ≠ id := h a (by simp)
    have ht : ∀ k ∈ as, k.parent ≠ id := fun k hk => h k (by simp [hk])
    simp [ha, ih ht]

theorem my_record_kids (t : Truth) (out : List Child) :
    (t.record out).kids = t.kids ++ out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) := by rfl

theorem my_record_nOrders2 (t : Truth) (out : List Child) : (t.record out).nOrders = t.nOrders := by simp [Truth.record]

theorem my_record_qty2 (t : Truth) (out : List Child) (id : Nat) : (t.record out).qty id = t.qty id := by simp [Truth.record]

theorem my_record_len (t : Truth) (out : List Child) : (t.record out).kids.length = t.kids.length + out.length := by simp [Truth.record]

theorem my_record_sent2 (t : Truth) (out : List Child) (id : Nat) :
    (t.record out).sent id = t.sent id + sentFor (out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id := by simp [Truth.record, Truth.sent, sentFor_append]

theorem my_record_exec2 (t : Truth) (out : List Child) (id : Nat) :
    (t.record out).exec id = t.exec id := by simp [Truth.record, Truth.exec, execFor_append, execFor_new]

theorem my_obs_parent_kids (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).kids = t.kids := by simp [Truth.observe]

theorem my_obs_parent_nOrders (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).nOrders = t.nOrders + 1 := by simp [Truth.observe]

theorem my_obs_parent_qty_eq (t : Truth) (q : Nat) (f : Bool) (id : Nat) :
    (t.observe (.parent q f)).qty id = (upd t.qty t.nOrders q) id := by simp [Truth.observe]

theorem my_obs_fill_nOrders (t : Truth) (k q : Nat) : (t.observe (.fill k q)).nOrders = t.nOrders := by
  cases h : t.kids[k]? <;> simp [Truth.observe, h]

theorem my_obs_fill_qty (t : Truth) (k q : Nat) (id : Nat) : (t.observe (.fill k q)).qty id = t.qty id := by
  cases h : t.kids[k]? <;> simp [Truth.observe, h]

theorem my_obs_route_nOrders (t : Truth) (id liq : Nat) : (t.observe (.route id liq)).nOrders = t.nOrders := by simp [Truth.observe]

theorem my_obs_route_qty (t : Truth) (id liq : Nat) (j : Nat) : (t.observe (.route id liq)).qty j = t.qty j := by simp [Truth.observe]

theorem my_obs_route_kids (t : Truth) (id liq : Nat) : (t.observe (.route id liq)).kids = t.kids := by simp [Truth.observe]

theorem my_obs_ack_nOrders (t : Truth) (k : Nat) : (t.observe (.ack k)).nOrders = t.nOrders := by simp [Truth.observe]

theorem my_obs_ack_qty (t : Truth) (k : Nat) (j : Nat) : (t.observe (.ack k)).qty j = t.qty j := by simp [Truth.observe]

theorem my_obs_ack_kids (t : Truth) (k : Nat) : (t.observe (.ack k)).kids = t.kids := by simp [Truth.observe]

theorem my_step_fill_st2 (b : Build) (s : State) (k q : Nat) (h : k < s.nChildren) :
    (step b s (.fill k q)).1 =
      let c := s.children k
      let x := min q (c.qty - c.done)
      let p := s.parents c.parent
      ({ s with parents := upd s.parents c.parent { p with cum := p.cum + x },
                children := upd s.children k { c with done := c.done + x } }) := by
  simp [step, h]

theorem my_step_fill_st3 (b : Build) (s : State) (k q : Nat) (h : ¬ k < s.nChildren) :
    (step b s (.fill k q)).1 = s := by
  simp [step, h]

theorem my_obs_fill_sent (t : Truth) (k q : Nat) (id : Nat) :
    (t.observe (.fill k q)).sent id = t.sent id := by
  simp only [Truth.observe]
  split
  · rename_i c hc
    simp only [Truth.sent]
    have h : sentFor (t.kids.set k { c with done := c.done + min q (c.qty - c.done) }) id = sentFor t.kids id := by
      have h2 : ({ c with done := c.done + min q (c.qty - c.done) } : Kid) = { c with done := (c.done + min q (c.qty - c.done)) } := rfl
      exact sentFor_set_done t.kids k c (c.done + min q (c.qty - c.done)) hc id
    exact h
  · rfl

theorem my_obs_fill_exec (t : Truth) (k q : Nat) (id : Nat) :
    (t.observe (.fill k q)).exec id = t.exec id + (match t.kids[k]? with | some c => if c.parent = id then min q (c.qty - c.done) else 0 | none => 0) := by
  simp only [Truth.observe]
  split
  · rename_i c hc
    simp only [Truth.exec]
    have h := execFor_set_done t.kids k c (min q (c.qty - c.done)) hc id
    simp [hc, h]
  · simp [*]

def InvWeak2 (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  (∀ id, (x.st.parents id).sent = x.tr.sent id) ∧
  (∀ id, id < x.tr.nOrders → (x.st.parents id).qty = x.tr.qty id) ∧
  (∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) ∧
  (∀ id, (x.st.parents id).sent ≤ (x.st.parents id).qty)

theorem myInvWeak2_base : InvWeak2 start := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro id; rfl
  · intro id h; simp [start, Truth.empty] at h
  · intro k hk; simp [start, Truth.empty] at hk
  · intro id; simp [start, init]

theorem myAdv_parent_st (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    (advance step b x (.parent q f)).st =
    { x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } := by
  simp [advance, step]

theorem myAdv_parent_tr (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    (advance step b x (.parent q f)).tr = x.tr.observe (.parent q f) := by
  simp [advance, step, Truth.record]

theorem my_sentFor_ge (l : List Kid) (n id : Nat) (h : ∀ k ∈ l, k.parent < n) (hle : n ≤ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent ≠ id := by
      have hlt := h a (by simp)
      omega
    have ht : ∀ k ∈ as, k.parent < n := fun k hk => h k (by simp [hk])
    simp [ha, ih ht]

theorem my_execFor_ge (l : List Kid) (n id : Nat) (h : ∀ k ∈ l, k.parent < n) (hle : n ≤ id) : execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent ≠ id := by
      have hlt := h a (by simp)
      omega
    have ht : ∀ k ∈ as, k.parent < n := fun k hk => h k (by simp [hk])
    simp [ha, ih ht]

def InvFillAcc (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
  (∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) ∧
  (∀ id, (x.st.parents id).cum = x.tr.exec id)

theorem invFillAcc_base : InvFillAcc start := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro k c h; simp [start, Truth.empty] at h
  · intro k hk; simp [start, Truth.empty] at hk
  · intro id; rfl

theorem my_route_expand (s : State) (id liq : Nat) (p : ParentRec) (c : Nat)
    (hp : s.parents id = p) (hc : c = min liq (p.qty - p.sent)) :
    routeBySent s id liq =
    (if id < s.nParents ∧ 0 < c then
      ({ s with parents := upd s.parents id { p with sent := p.sent + c },
                nChildren := s.nChildren + 1,
                children := upd s.children s.nChildren ⟨id, c, 0⟩ }, [⟨id, c⟩])
    else (s, [])) := by
  simp [routeBySent, hp, ← hc]

theorem my_route_nParents2 (s : State) (id liq : Nat) : (routeBySent s id liq).1.nParents = s.nParents := by
  simp [routeBySent]
  split
  · rfl
  · rfl

theorem my_route_out_len (s : State) (id liq : Nat) : (routeBySent s id liq).2.length = 0 ∨ (routeBySent s id liq).2.length = 1 := by
  have h := my_route_cases s id liq
  rcases h with h | h <;> simp [h]

theorem my_adv_parent_unfold (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    advance step b x (.parent q f) =
    ⟨{ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ },
     (x.tr.observe (.parent q f)).record []⟩ := by
  simp [advance, step]

theorem my_upd_parent_cum_old (x : Sys) (q : Nat) (f : Bool) (id : Nat) (h : id ≠ x.st.nParents) :
    ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) id).cum = (x.st.parents id).cum := by
  simp [upd, h]

theorem my_upd_parent_cum_new (x : Sys) (q : Nat) (f : Bool) :
    ((upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩) x.st.nParents).cum = 0 := by
  simp [upd]

theorem my_route_cum_old2 (s : State) (id liq j : Nat) : ((routeBySent s id liq).1.parents j).cum = (s.parents j).cum := by
  simp only [routeBySent]
  split
  · rename_i h
    simp only
    by_cases hj : j = id
    · subst hj; simp [upd_eq]
    · simp [upd_neq _ _ _ _ hj]
  · rfl

theorem mySt_parent_sent (x : Sys) (q : Nat) (f : Bool) (id : Nat) :
    (({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State).parents id).sent =
    (if id = x.st.nParents then 0 else (x.st.parents id).sent) := by
  simp only [upd]
  split
  · subst_vars; rfl
  · rfl

theorem mySt_parent_qty (x : Sys) (q : Nat) (f : Bool) (id : Nat) :
    (({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State).parents id).qty =
    (if id = x.st.nParents then q else (x.st.parents id).qty) := by
  simp only [upd]
  split
  · subst_vars; rfl
  · rfl

theorem plan0_parent_kids_eq (x : Sys) (q : Nat) (f : Bool) :
    (x.tr.observe (.parent q f)).kids = x.tr.kids := by simp [Truth.observe]

theorem plan0_inv_weak2_parent (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    InvWeak2 x → InvWeak2 (advance step b x (.parent q f)) := by
  intro hx
  obtain ⟨hNP, hSent, hQty, hKids, hLe⟩ := hx
  have hst : (advance step b x (.parent q f)).st =
    ({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State) :=
    myAdv_parent_st b x q f
  have htr : (advance step b x (.parent q f)).tr = x.tr.observe (.parent q f) :=
    myAdv_parent_tr b x q f
  have hnO : (x.tr.observe (.parent q f)).nOrders = x.tr.nOrders + 1 :=
    my_obs_parent_nOrders x.tr q f
  have hkids : (x.tr.observe (.parent q f)).kids = x.tr.kids :=
    my_obs_parent_kids x.tr q f
  have eN : (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 := by
    rw [htr, hnO]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hst, htr, hnO, hNP]
  · intro id
    have e1 : ((advance step b x (.parent q f)).st.parents id).sent =
      (if id = x.st.nParents then 0 else (x.st.parents id).sent) := by
      rw [hst]; exact mySt_parent_sent x q f id
    have e2 : ((advance step b x (.parent q f)).tr.sent id) = x.tr.sent id := by
      rw [htr]; exact my_obs_parent_sent x.tr q f id
    rw [e1, e2, hSent id]
    by_cases h : id = x.st.nParents
    · simp only [h, ↓reduceIte]
      symm
      simp only [Truth.sent]
      have hle : x.tr.nOrders ≤ x.st.nParents := by omega
      exact my_sentFor_ge x.tr.kids x.tr.nOrders x.st.nParents hKids hle
    · simp only [h, ↓reduceIte]
  · intro id hlt
    have e1 : ((advance step b x (.parent q f)).st.parents id).qty =
      (if id = x.st.nParents then q else (x.st.parents id).qty) := by
      rw [hst]; exact mySt_parent_qty x q f id
    have e2 : ((advance step b x (.parent q f)).tr.qty id) = (upd x.tr.qty x.tr.nOrders q) id := by
      rw [htr]; exact my_obs_parent_qty_eq x.tr q f id
    rw [e1, e2]
    have hlt2 : id < x.tr.nOrders + 1 := by omega
    by_cases h : id = x.tr.nOrders
    · have h2 : id = x.st.nParents := by omega
      simp only [h2, ↓reduceIte]
      have e3 : upd x.tr.qty x.tr.nOrders q x.st.nParents = q := by
        rw [hNP]; exact upd_eq _ _ _
      rw [e3]
    · have hlt3 : id < x.tr.nOrders := by omega
      have hqold := hQty id hlt3
      have hne2 : id ≠ x.st.nParents := by omega
      simp only [hne2, ↓reduceIte]
      simp only [upd, h, ↓reduceIte]
      exact hqold
  · intro k hk
    have hk2 : k ∈ x.tr.kids := by
      have hmem : k ∈ (x.tr.observe (.parent q f)).kids := by rw [← htr]; exact hk
      rwa [hkids] at hmem
    have hlt0 := hKids k hk2
    omega
  · intro id
    have e1 : ((advance step b x (.parent q f)).st.parents id).sent =
      (if id = x.st.nParents then 0 else (x.st.parents id).sent) := by
      rw [hst]; exact mySt_parent_sent x q f id
    have e2 : ((advance step b x (.parent q f)).st.parents id).qty =
      (if id = x.st.nParents then q else (x.st.parents id).qty) := by
      rw [hst]; exact mySt_parent_qty x q f id
    rw [e1, e2]
    split
    · omega
    · exact hLe id

theorem my_route_parents_qty_eq (s : State) (id liq j : Nat) :
    ((routeBySent s id liq).1.parents j).qty = (s.parents j).qty := by
  unfold routeBySent
  simp only
  split
  · simp only
    by_cases hj : j = id
    · subst hj; simp [upd_eq]
    · simp [upd_neq _ _ _ _ hj]
  · rfl

theorem my_route_state_sent (s : State) (id liq j : Nat) :
    ((routeBySent s id liq).1.parents j).sent =
    ((routeBySent s id liq).1.parents j).sent := by rfl

theorem my_obs_route_is_id (t : Truth) (id liq : Nat) : t.observe (.route id liq) = t := by
  simp [Truth.observe]

theorem my_adv_route_st_eq (b : Build) (x : Sys) (id liq : Nat) :
    (advance step b x (.route id liq)).st = (routeBySent x.st id liq).1 := by
  simp [advance, my_step_route_eq]

theorem my_adv_route_tr_eq (b : Build) (x : Sys) (id liq : Nat) :
    (advance step b x (.route id liq)).tr =
    (x.tr.observe (.route id liq)).record (routeBySent x.st id liq).2 := by
  simp [advance, my_step_route_eq]

theorem my_route_parents_sent_eq2 (s : State) (id liq j : Nat) :
    ((routeBySent s id liq).1.parents j).sent =
    (if j = id ∧ id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
      (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent)
    else (s.parents j).sent) := by
  unfold routeBySent
  simp only
  split
  · rename_i h
    simp only
    by_cases hj : j = id
    · subst hj
      simp [upd_eq, h]
    · have hneg : ¬ (j = id ∧ id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) := by
        simp [hj]
      simp [hneg, upd_neq _ _ _ _ hj]
  · rename_i h
    have hneg : ¬ (j = id ∧ id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) := by
      intro hh
      exact h ⟨hh.2.1, hh.2.2⟩
    simp [hneg]

theorem my_route_out_active2 (s : State) (id liq : Nat)
    (hcond : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) :
    (routeBySent s id liq).2 = [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] := by
  simp [routeBySent, hcond]

theorem my_route_out_inactive2 (s : State) (id liq : Nat)
    (hcond : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    (routeBySent s id liq).2 = [] := by
  simp [routeBySent, hcond]

theorem plan1_route_inactive (s : State) (id liq : Nat)
    (h : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    routeBySent s id liq = (s, []) := by simp [routeBySent, h]

theorem plan1_advance_route (b : Build) (x : Sys) (id liq : Nat) :
    advance step b x (.route id liq) =
      ⟨(routeBySent x.st id liq).1, x.tr.record (routeBySent x.st id liq).2⟩ := by
  have h1 : step b x.st (.route id liq) = routeBySent x.st id liq := my_step_route_eq b x.st id liq
  have h2 : x.tr.observe (.route id liq) = x.tr := my_obs_route_is_id x.tr id liq
  simp only [advance, h1, h2]

theorem plan1_route_inactive_proof (s : State) (id liq : Nat)
    (h : ¬ (id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent))) :
    routeBySent s id liq = (s, []) := by
  simp [routeBySent, h]

theorem plan1_route_active_test2 (s : State) (id liq : Nat)
    (h : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) :
    (routeBySent s id liq).1.nParents = s.nParents := by
  simp [routeBySent, h]

theorem plan1_route_active (s : State) (id liq : Nat)
    (h : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)) :
    (routeBySent s id liq).2 = [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] ∧
    (routeBySent s id liq).1.nParents = s.nParents ∧
    ∀ j, ((routeBySent s id liq).1.parents j).qty = (s.parents j).qty ∧
      ((routeBySent s id liq).1.parents j).sent =
        if j = id then (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent)
        else (s.parents j).sent := by
  refine ⟨my_route_out_active2 s id liq h, ?_, ?_⟩
  · simp [routeBySent, h]
  · intro j
    constructor
    · exact my_route_parents_qty_eq s id liq j
    · have h2 := my_route_parents_sent_eq2 s id liq j
      rw [h2]
      by_cases hj : j = id
      · subst hj
        simp [h]
      · simp [hj]

theorem plan1_record_nil (t : Truth) : t.record [] = t := by simp [Truth.record]

theorem plan1_record_single_sent_aux_unique123 : True := trivial

theorem plan1_record_single_sent_proofcheck (t : Truth) (id c j : Nat) :
    (t.record [⟨id, c⟩]).sent j = t.sent j + (if id = j then c else 0) := by
  rw [my_record_sent2]
  simp

theorem plan1_record_single_sent (t : Truth) (id c j : Nat) :
    (t.record [⟨id, c⟩]).sent j = t.sent j + (if id = j then c else 0) := by
  rw [my_record_sent2]
  simp

theorem plan1_record_single_truth (t : Truth) (id c : Nat) (hid : id < t.nOrders)
    (hk : ∀ k ∈ t.kids, k.parent < t.nOrders) :
    (t.record [⟨id, c⟩]).nOrders = t.nOrders ∧
    (∀ j, (t.record [⟨id, c⟩]).qty j = t.qty j) ∧
    ∀ k ∈ (t.record [⟨id, c⟩]).kids, k.parent < (t.record [⟨id, c⟩]).nOrders := by
  refine ⟨my_record_nOrders2 _ _ , fun j => my_record_qty2 _ _ _, ?_⟩
  intro k hk2
  have hkids : (t.record [⟨id, c⟩]).kids = t.kids ++ [(⟨id, c, 0⟩ : Kid)] := by rfl
  have hn : (t.record [⟨id, c⟩]).nOrders = t.nOrders := my_record_nOrders2 _ _
  rw [hkids] at hk2
  rw [hn]
  simp at hk2
  rcases hk2 with hk2 | rfl
  · exact hk _ hk2
  · exact hid

theorem plan0_inv_weak2_route_aux1 (x : Sys) (id liq : Nat)
    (hSentAll : ∀ jj, (x.st.parents jj).sent = x.tr.sent jj)
    (hQtyAll : ∀ jj, jj < x.tr.nOrders → (x.st.parents jj).qty = x.tr.qty jj)
    (hid_tr : id < x.tr.nOrders) (jj : Nat) :
    (if jj = id then (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent)
      else (x.st.parents jj).sent) =
    (x.tr.sent jj + (if id = jj then min liq (x.tr.qty id - x.tr.sent id) else 0)) := by
  have hqty_id : (x.st.parents id).qty = x.tr.qty id := hQtyAll id hid_tr
  have hsent_id : (x.st.parents id).sent = x.tr.sent id := hSentAll id
  by_cases hjj : jj = id
  · subst hjj
    simp [hsent_id, hqty_id]
  · have h2 : ¬ (id = jj) := fun h => hjj h.symm
    simp [hjj, h2, hSentAll jj]

theorem plan0_ack_st_eq (b : Build) (x : Sys) (k : Nat) :
    (advance step b x (.ack k)).st = x.st := by
  simp [advance, step]

theorem plan0_ack_tr_eq (b : Build) (x : Sys) (k : Nat) :
    (advance step b x (.ack k)).tr = x.tr := by
  simp [advance, step, Truth.record, Truth.observe]

theorem plan0_fill_tr_eq2 (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr = x.tr.observe (.fill k q) := by
  have hout : (step b x.st (.fill k q)).2 = [] := my_step_fill_out b x.st k q
  simp only [advance, hout, plan1_record_nil]

theorem plan0_fill_st_fst (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := by rfl

theorem plan0_fill_nParents_eq4 (b : Build) (x : Sys) (k q : Nat) :
    (step b x.st (.fill k q)).1.nParents = x.st.nParents := by
  simp only [step]
  split
  · simp
  · rfl

theorem plan0_upd_parents_sent (x : Sys) (k q id : Nat) :
    ((upd x.st.parents (x.st.children k).parent
      { qty := (x.st.parents (x.st.children k).parent).qty, flag := (x.st.parents (x.st.children k).parent).flag,
        sent := (x.st.parents (x.st.children k).parent).sent,
        cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) })
      id).sent = (x.st.parents id).sent := by
  by_cases hj : (x.st.children k).parent = id
  · subst hj; rw [upd_eq]
  · have h2 : id ≠ (x.st.children k).parent := fun h => hj h.symm
    rw [upd_neq _ _ _ _ h2]

theorem plan0_upd_parents_qty (x : Sys) (k q id : Nat) :
    ((upd x.st.parents (x.st.children k).parent
      { qty := (x.st.parents (x.st.children k).parent).qty, flag := (x.st.parents (x.st.children k).parent).flag,
        sent := (x.st.parents (x.st.children k).parent).sent,
        cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) })
      id).qty = (x.st.parents id).qty := by
  by_cases hj : (x.st.children k).parent = id
  · subst hj; rw [upd_eq]
  · have h2 : id ≠ (x.st.children k).parent := fun h => hj h.symm
    rw [upd_neq _ _ _ _ h2]

theorem plan0_fill_parents_sent (b : Build) (x : Sys) (k q id : Nat) :
    ((step b x.st (.fill k q)).1.parents id).sent = (x.st.parents id).sent := by
  simp only [step]
  split
  · exact plan0_upd_parents_sent x k q id
  · rfl

theorem plan0_fill_parents_qty (b : Build) (x : Sys) (k q id : Nat) :
    ((step b x.st (.fill k q)).1.parents id).qty = (x.st.parents id).qty := by
  simp only [step]
  split
  · exact plan0_upd_parents_qty x k q id
  · rfl

theorem plan0_mem_set_helper (l : List Kid) (k : Nat) (v a : Kid) :
    a ∈ l.set k v → a ∈ l ∨ a = v := by
  induction l generalizing k with
  | nil => simp
  | cons b bs ih =>
    intro h
    cases k with
    | zero =>
      simp at h
      rcases h with rfl | h
      · exact Or.inr rfl
      · exact Or.inl (List.mem_cons_of_mem b h)
    | succ n =>
      simp at h
      rcases h with rfl | h
      · exact Or.inl (by simp)
      · rcases ih n h with h2 | rfl
        · exact Or.inl (List.mem_cons_of_mem b h2)
        · exact Or.inr rfl

theorem plan0_fill_kids_bound2 (t : Truth) (k q : Nat)
    (hKids : ∀ k ∈ t.kids, k.parent < t.nOrders) :
    ∀ k2 ∈ (t.observe (.fill k q)).kids, k2.parent < (t.observe (.fill k q)).nOrders := by
  have hn : (t.observe (.fill k q)).nOrders = t.nOrders := my_obs_fill_nOrders t k q
  rw [hn]
  simp only [Truth.observe]
  split
  · rename_i c hc
    intro k2 hk2
    have hmem : k2 ∈ t.kids ∨ k2 = { c with done := c.done + min q (c.qty - c.done) } :=
      plan0_mem_set_helper t.kids k _ k2 hk2
    rcases hmem with h | h
    · exact hKids k2 h
    · subst h
      have hcMem : c ∈ t.kids := List.mem_of_getElem? hc
      have hlt := hKids c hcMem
      simp
      exact hlt
  · exact hKids

theorem plan2_fill_parents_eq (b : Build) (x : Sys) (k q id : Nat) :
    ((advance step b x (.fill k q)).st.parents id).sent = (x.st.parents id).sent ∧
    ((advance step b x (.fill k q)).st.parents id).qty = (x.st.parents id).qty := by
  have hst : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := rfl
  rw [hst]
  exact ⟨plan0_fill_parents_sent b x k q id, plan0_fill_parents_qty b x k q id⟩

theorem plan2_ack_preserves (b : Build) (x : Sys) (k : Nat) :
    InvWeak2 x → InvWeak2 (advance step b x (.ack k)) := by
  intro hx
  have hst : (advance step b x (.ack k)).st = x.st := plan0_ack_st_eq b x k
  have htr : (advance step b x (.ack k)).tr = x.tr := plan0_ack_tr_eq b x k
  obtain ⟨hNP, hSent, hQty, hKids, hLe⟩ := hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hst, htr, hNP]
  · intro id
    rw [hst, htr]
    exact hSent id
  · intro id hlt
    have hlt' : id < x.tr.nOrders := by rw [← htr]; exact hlt
    have h1 := hQty id hlt'
    rw [hst, htr]
    exact h1
  · intro k0 hk0
    have hk0' : k0 ∈ x.tr.kids := by rw [← htr]; exact hk0
    have h1 := hKids k0 hk0'
    have heq : (advance step b x (.ack k)).tr.nOrders = x.tr.nOrders := by rw [htr]
    rw [heq]
    exact h1
  · intro id
    rw [hst]
    exact hLe id

theorem plan2_fill_parents_eq_proof : ∀ (b : Build) (x : Sys) (k q id : Nat),
    ((advance step b x (.fill k q)).st.parents id).sent = (x.st.parents id).sent ∧
    ((advance step b x (.fill k q)).st.parents id).qty = (x.st.parents id).qty := by
  intro b x k q id
  have hst : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := rfl
  rw [hst]
  exact ⟨plan0_fill_parents_sent b x k q id, plan0_fill_parents_qty b x k q id⟩

theorem plan2_fill_counts_truth_eq (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).st.nParents = x.st.nParents ∧
    (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders ∧
    (∀ id, (advance step b x (.fill k q)).tr.sent id = x.tr.sent id) ∧
    (∀ id, (advance step b x (.fill k q)).tr.qty id = x.tr.qty id) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [plan0_fill_st_fst]
    exact plan0_fill_nParents_eq4 b x k q
  · rw [plan0_fill_tr_eq2]
    exact my_obs_fill_nOrders x.tr k q
  · intro id
    rw [plan0_fill_tr_eq2]
    exact my_obs_fill_sent x.tr k q id
  · intro id
    rw [plan0_fill_tr_eq2]
    exact my_obs_fill_qty x.tr k q id

theorem plan2_fill_kids_bound_proof : ∀ (b : Build) (x : Sys) (k q : Nat),
    (∀ k0 ∈ x.tr.kids, k0.parent < x.tr.nOrders) →
    ∀ k0 ∈ (advance step b x (.fill k q)).tr.kids,
      k0.parent < (advance step b x (.fill k q)).tr.nOrders := by
  intro b x k q hKids k0 hk0
  have htr : (advance step b x (.fill k q)).tr = x.tr.observe (.fill k q) :=
    plan0_fill_tr_eq2 b x k q
  rw [htr] at hk0 ⊢
  exact plan0_fill_kids_bound2 x.tr k q hKids k0 hk0

theorem plan2_fill_kids_bound (b : Build) (x : Sys) (k q : Nat) :
    (∀ k0 ∈ x.tr.kids, k0.parent < x.tr.nOrders) →
    ∀ k0 ∈ (advance step b x (.fill k q)).tr.kids,
      k0.parent < (advance step b x (.fill k q)).tr.nOrders := by
  intro hKids k0 hk0
  have htr : (advance step b x (.fill k q)).tr = x.tr.observe (.fill k q) :=
    plan0_fill_tr_eq2 b x k q
  rw [htr] at hk0 ⊢
  exact plan0_fill_kids_bound2 x.tr k q hKids k0 hk0

theorem plan2_fill_preserves_proof (b : Build) (x : Sys) (k q : Nat) :
    InvWeak2 x → InvWeak2 (advance step b x (.fill k q)) := by
  intro hx
  obtain ⟨hNP, hSent, hQty, hKids, hLe⟩ := hx
  obtain ⟨hStNP, hTrNO, hTrSent, hTrQty⟩ := plan2_fill_counts_truth_eq b x k q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hStNP, hNP, ← hTrNO]
  · intro id
    have hPar := plan2_fill_parents_eq b x k q id
    rw [hPar.1, hSent id, ← hTrSent id]
  · intro id hlt
    have hlt' : id < x.tr.nOrders := by rw [← hTrNO]; exact hlt
    have h1 := hQty id hlt'
    have hPar := plan2_fill_parents_eq b x k q id
    have h2 := hTrQty id
    rw [hPar.2, h1, ← h2]
  · exact plan2_fill_kids_bound b x k q hKids
  · intro id
    have hPar := plan2_fill_parents_eq b x k q id
    rw [hPar.1, hPar.2]
    exact hLe id

theorem plan2_fill_preserves (b : Build) (x : Sys) (k q : Nat) :
    InvWeak2 x → InvWeak2 (advance step b x (.fill k q)) := by
  intro hx
  obtain ⟨hNP, hSent, hQty, hKids, hLe⟩ := hx
  obtain ⟨hStNP, hTrNO, hTrSent, hTrQty⟩ := plan2_fill_counts_truth_eq b x k q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hStNP, hNP, ← hTrNO]
  · intro id
    have hPar := plan2_fill_parents_eq b x k q id
    rw [hPar.1, hSent id, ← hTrSent id]
  · intro id hlt
    have hlt' : id < x.tr.nOrders := by rw [← hTrNO]; exact hlt
    have h1 := hQty id hlt'
    have hPar := plan2_fill_parents_eq b x k q id
    have h2 := hTrQty id
    rw [hPar.2, h1, ← h2]
  · exact plan2_fill_kids_bound b x k q hKids
  · intro id
    have hPar := plan2_fill_parents_eq b x k q id
    rw [hPar.1, hPar.2]
    exact hLe id

theorem plan0_inv_weak2_ack_fill_proof : ∀ (b : Build) (x : Sys) (k q : Nat),
    InvWeak2 x →
      InvWeak2 (advance step b x (.ack k)) ∧
        InvWeak2 (advance step b x (.fill k q)) := by
  intro b x k q hx
  exact ⟨plan2_ack_preserves b x k hx, plan2_fill_preserves b x k q hx⟩

theorem plan0_inv_weak2_ack_fill_aux : ∀ (b : Build) (x : Sys) (k q : Nat),
    InvWeak2 x →
      InvWeak2 (advance step b x (.ack k)) ∧
        InvWeak2 (advance step b x (.fill k q)) := by
  intro b x k q hx
  exact ⟨plan2_ack_preserves b x k hx, plan2_fill_preserves b x k q hx⟩

theorem selfContained_ack_fill_test5 : True := trivial

theorem check_record_nil (t : Truth) : t.record [] = t := by simp [Truth.record]

theorem mytest_plan0_aux2 (x : Sys) (id liq : Nat) :
    InvWeak2 x →
      (routeBySent x.st id liq).2 = expectedRoute x.tr id liq := by
  intro hx
  obtain ⟨hNP, hSent, hQty, hKids, hLe⟩ := hx
  have hsent : (x.st.parents id).sent = x.tr.sent id := hSent id
  by_cases hid : id < x.tr.nOrders
  · have hidS : id < x.st.nParents := by omega
    have hqty : (x.st.parents id).qty = x.tr.qty id := hQty id hid
    have hmin : min liq ((x.st.parents id).qty - (x.st.parents id).sent) =
        min liq (x.tr.qty id - x.tr.sent id) := by rw [hqty, hsent]
    by_cases hpos : 0 < min liq (x.tr.qty id - x.tr.sent id)
    · have hcondS : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent) := by
        rw [hmin]; exact ⟨hidS, hpos⟩
      have hcondT : id < x.tr.nOrders ∧ 0 < min liq (x.tr.qty id - x.tr.sent id) := ⟨hid, hpos⟩
      rw [my_route_out_active2 _ _ _ hcondS, hmin]
      unfold expectedRoute
      rw [if_pos hcondT]
    · have hcondS : ¬ (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) := by
        rw [hmin]; simp [hpos]
      have hcondT : ¬ (id < x.tr.nOrders ∧ 0 < min liq (x.tr.qty id - x.tr.sent id)) := by
        simp [hpos]
      rw [my_route_out_inactive2 _ _ _ hcondS]
      unfold expectedRoute
      rw [if_neg hcondT]
  · have hidS : ¬ id < x.st.nParents := by omega
    have hcondS : ¬ (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) := by
      simp [hidS]
    have hcondT : ¬ (id < x.tr.nOrders ∧ 0 < min liq (x.tr.qty id - x.tr.sent id)) := by
      simp [hid]
    rw [my_route_out_inactive2 _ _ _ hcondS]
    unfold expectedRoute
    rw [if_neg hcondT]

theorem plan0_route_output_of_inv_weak2 (x : Sys) (id liq : Nat) :
    InvWeak2 x →
      (routeBySent x.st id liq).2 = expectedRoute x.tr id liq :=
  fun hx => mytest_plan0_aux2 x id liq hx

theorem myRoutePreserves_aux8 (b : Build) (x : Sys) (rid liq : Nat)
    (hNP : x.st.nParents = x.tr.nOrders)
    (hSent : ∀ jj, (x.st.parents jj).sent = x.tr.sent jj)
    (hQty : ∀ jj, jj < x.tr.nOrders → (x.st.parents jj).qty = x.tr.qty jj)
    (hKids : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)
    (hLe : ∀ jj, (x.st.parents jj).sent ≤ (x.st.parents jj).qty) :
    InvWeak2 (advance step b x (.route rid liq)) := by
  have hadv : advance step b x (.route rid liq) =
      ⟨(routeBySent x.st rid liq).1, x.tr.record (routeBySent x.st rid liq).2⟩ :=
    plan1_advance_route b x rid liq
  rw [hadv]
  by_cases hcond : rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)
  · have hout : (routeBySent x.st rid liq).2 = [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩] :=
      my_route_out_active2 x.st rid liq hcond
    have hidN : rid < x.tr.nOrders := by omega
    have hNP2 : (routeBySent x.st rid liq).1.nParents = x.tr.nOrders := by
      have h1 := my_route_nParents2 x.st rid liq; omega
    rw [hout]
    have hnO : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).nOrders = x.tr.nOrders :=
      my_record_nOrders2 _ _
    refine ⟨by rw [hNP2, hnO], ?_, ?_, ?_, ?_⟩
    · intro jj
      have h1 := my_route_parents_sent_eq2 x.st rid liq jj
      have h2 := plan1_record_single_sent x.tr rid (min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) jj
      show ((routeBySent x.st rid liq).1.parents jj).sent =
        (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).sent jj
      rw [h1, h2]
      by_cases hjj : jj = rid
      · have hc : (jj = rid ∧ rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) := by
          exact ⟨hjj, hcond.1, hcond.2⟩
        rw [if_pos hc]
        have hidjj : rid = jj := hjj.symm
        rw [if_pos hidjj]
        rw [hjj, hSent]
      · have hne : ¬ (rid = jj) := fun h => hjj h.symm
        have hneg : ¬ (jj = rid ∧ rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) := by
          simp [hjj]
        rw [if_neg hneg, if_neg hne, Nat.add_zero]
        exact hSent jj
    · intro jj hlt
      rw [hnO] at hlt
      have h1 := hQty jj hlt
      have hq1 : ((routeBySent x.st rid liq).1.parents jj).qty = (x.st.parents jj).qty :=
        my_route_parents_qty_eq x.st rid liq jj
      have hq2 : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).qty jj = x.tr.qty jj :=
        my_record_qty2 _ _ _
      show ((routeBySent x.st rid liq).1.parents jj).qty =
        (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).qty jj
      rw [hq1, h1, hq2]
    · intro k hk
      have hkids : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids =
          x.tr.kids ++ [(⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)] := rfl
      have hn : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).nOrders = x.tr.nOrders :=
        my_record_nOrders2 _ _
      have hk' : k ∈ (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids := hk
      rw [hkids] at hk'
      rw [hn]
      simp at hk'
      rcases hk' with hk' | hkk
      · exact hKids _ hk'
      · subst hkk; exact hidN
    · intro jj
      have h1 := my_route_parents_sent_eq2 x.st rid liq jj
      have hq1 : ((routeBySent x.st rid liq).1.parents jj).qty = (x.st.parents jj).qty :=
        my_route_parents_qty_eq x.st rid liq jj
      show ((routeBySent x.st rid liq).1.parents jj).sent ≤ ((routeBySent x.st rid liq).1.parents jj).qty
      rw [h1, hq1]
      by_cases hjj : jj = rid
      · have hpos : (jj = rid ∧ rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) := by
          exact ⟨hjj, hcond.1, hcond.2⟩
        rw [if_pos hpos, hjj]
        have hle0 := hLe rid
        have hmin_le : min liq ((x.st.parents rid).qty - (x.st.parents rid).sent) ≤
          (x.st.parents rid).qty - (x.st.parents rid).sent := Nat.min_le_right _ _
        omega
      · have hneg : ¬ (jj = rid ∧ rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) := by
          simp [hjj]
        rw [if_neg hneg]
        exact hLe jj
  · have hpair : routeBySent x.st rid liq = (x.st, []) := plan1_route_inactive_proof x.st rid liq hcond
    have hout : (routeBySent x.st rid liq).2 = [] := by rw [hpair]
    have hfst : (routeBySent x.st rid liq).1 = x.st := by rw [hpair]
    simp only [hout, hfst]
    have hrec : x.tr.record ([] : List Child) = x.tr := plan1_record_nil x.tr
    simp only [hrec]
    exact ⟨hNP, hSent, hQty, hKids, hLe⟩

theorem myWeak2_route_clean2 (b : Build) (x : Sys) (rid liq : Nat) (h : InvWeak2 x) :
    InvWeak2 (advance step b x (.route rid liq)) := by
  obtain ⟨hNP, hSent, hQty, hKids, hLe⟩ := h
  exact myRoutePreserves_aux8 b x rid liq hNP hSent hQty hKids hLe

theorem myWeak2_run_clean2 (b : Build) (evs : List Event) : InvWeak2 (run step b evs) := by
  have hbase : InvWeak2 start := myInvWeak2_base
  have hstep : ∀ x e, InvWeak2 x → InvWeak2 (advance step b x e) := by
    intro x e hx
    cases e with
    | parent q f => exact plan0_inv_weak2_parent b x q f hx
    | route rid liq => exact myWeak2_route_clean2 b x rid liq hx
    | ack k => exact plan2_ack_preserves b x k hx
    | fill k q => exact plan2_fill_preserves b x k q hx
  exact run_induction step b InvWeak2 hbase hstep evs

theorem plan0_inv_weak2_route (b : Build) (x : Sys) (id liq : Nat) :
    InvWeak2 x → InvWeak2 (advance step b x (.route id liq)) :=
  fun hx => myWeak2_route_clean2 b x id liq hx

theorem plan0_inv_weak2_run (b : Build) (evs : List Event) :
    InvWeak2 (run step b evs) :=
  myWeak2_run_clean2 b evs

theorem plan0_routes_available_aux (b : Build) (evs : List Event) (id liq : Nat) :
    (step b (run step b evs).st (.route id liq)).2 =
      expectedRoute (run step b evs).tr id liq := by
  have hInv : InvWeak2 (run step b evs) := myWeak2_run_clean2 b evs
  have hOut : (routeBySent (run step b evs).st id liq).2 = expectedRoute (run step b evs).tr id liq :=
    plan0_route_output_of_inv_weak2 (run step b evs) id liq hInv
  have hStep : step b (run step b evs).st (.route id liq) = routeBySent (run step b evs).st id liq :=
    my_step_route_eq b (run step b evs).st id liq
  rw [hStep, hOut]

theorem my_stop_aux_final (b : Build) (evs : List Event) (rid liq pid : Nat)
    (_hNP : (run step b evs).st.nParents = (run step b evs).tr.nOrders)
    (hSent : ∀ jj, ((run step b evs).st.parents jj).sent = (run step b evs).tr.sent jj)
    (hQty : ∀ jj, jj < (run step b evs).tr.nOrders → ((run step b evs).st.parents jj).qty = (run step b evs).tr.qty jj)
    (hcond : rid < (run step b evs).st.nParents ∧
      0 < min liq (((run step b evs).st.parents rid).qty - (((run step b evs).st.parents rid).sent)))
    (hEqR : rid = pid)
    (hExec : (run step b evs).tr.exec pid = (run step b evs).tr.qty pid)
    (hid : pid < (run step b evs).tr.nOrders) : False := by
  have hqty : ((run step b evs).st.parents pid).qty = (run step b evs).tr.qty pid :=
    hQty pid hid
  have hsent : ((run step b evs).st.parents pid).sent = (run step b evs).tr.sent pid :=
    hSent pid
  have hexec_le : (run step b evs).tr.exec pid ≤ (run step b evs).tr.sent pid :=
    exec_le_sent step b evs pid
  have hcond2 : pid < (run step b evs).st.nParents ∧
      0 < min liq (((run step b evs).st.parents pid).qty - (((run step b evs).st.parents pid).sent)) := by
    rw [← hEqR]; exact hcond
  have h1 : min liq (((run step b evs).st.parents pid).qty - (((run step b evs).st.parents pid).sent)) =
      min liq ((run step b evs).tr.qty pid - (run step b evs).tr.sent pid) := by
    rw [hqty, hsent]
  have hpos : 0 < min liq (((run step b evs).st.parents pid).qty - (((run step b evs).st.parents pid).sent)) :=
    hcond2.2
  rw [h1] at hpos
  omega

theorem fa_parent_pres2 (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    InvFillAcc x → InvFillAcc (advance step b x (.parent q f)) := by
  intro hx
  obtain ⟨hNP, hNC, hCorr, hKB, hCum⟩ := hx
  have hst : (advance step b x (.parent q f)).st =
    ({ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ } : State) :=
    myAdv_parent_st b x q f
  have htr : (advance step b x (.parent q f)).tr = x.tr.observe (.parent q f) :=
    myAdv_parent_tr b x q f
  have hnO : (x.tr.observe (.parent q f)).nOrders = x.tr.nOrders + 1 :=
    my_obs_parent_nOrders x.tr q f
  have hkids : (x.tr.observe (.parent q f)).kids = x.tr.kids :=
    my_obs_parent_kids x.tr q f
  have hadv : advance step b x (.parent q f) =
      ⟨{ x.st with nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩ },
       (x.tr.observe (.parent q f)).record []⟩ := my_adv_parent_unfold b x q f
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hst, htr, hnO, hNP]
  · rw [hadv]
    simp [Truth.record, hkids, hNC]
  · intro k c hk
    rw [hadv] at hk ⊢
    simp only [Truth.record] at hk
    simp at hk
    rw [hkids] at hk
    have hcorr := hCorr k c hk
    simp [hcorr]
  · intro k hk
    rw [hadv] at hk ⊢
    simp only [Truth.record] at hk ⊢
    simp at hk ⊢
    rw [hkids] at hk
    rw [hnO] at ⊢
    have hlt := hKB k hk
    omega
  · intro id
    have hstC : ((advance step b x (.parent q f)).st.parents id).cum =
      (if id = x.st.nParents then 0 else (x.st.parents id).cum) := by
      rw [hst]
      simp only [upd]
      split
      · subst_vars; rfl
      · rfl
    have htrE : (advance step b x (.parent q f)).tr.exec id = x.tr.exec id := by
      rw [htr]
      simp [Truth.exec, hkids]
    rw [hstC, htrE]
    by_cases hid : id = x.st.nParents
    · rw [if_pos hid]
      have hge : x.tr.nOrders ≤ id := by omega
      have hex : x.tr.exec id = 0 := by
        simp [Truth.exec]
        exact my_execFor_ge x.tr.kids x.tr.nOrders id hKB hge
      omega
    · rw [if_neg hid, hCum id]

theorem fa_probe1 (l : List Kid) (v : Kid) (k : Nat) (h : k < l.length) :
    (l ++ [v])[k]? = l[k]? := by
  simp [List.getElem?_append, h]

theorem fa_probe2 (l : List Kid) (v : Kid) :
    (l ++ [v])[l.length]? = some v := by
  simp

theorem fa_get_append (l : List Kid) (v : Kid) (k : Nat) (c : Kid)
    (h : (l ++ [v])[k]? = some c) :
    (k < l.length ∧ l[k]? = some c) ∨ (k = l.length ∧ c = v) := by
  induction l generalizing k with
  | nil =>
    simp at h
    cases k with
    | zero =>
      simp at h
      exact Or.inr ⟨rfl, h.symm⟩
    | succ n =>
      simp at h
  | cons a as ih =>
    cases k with
    | zero =>
      simp at h
      subst h
      exact Or.inl ⟨by simp, rfl⟩
    | succ n =>
      simp at h
      rcases ih n h with ⟨hlt, heq⟩ | ⟨heq1, heq2⟩
      · exact Or.inl ⟨by simpa using Nat.succ_lt_succ hlt, heq⟩
      · exact Or.inr ⟨by simpa using congrArg Nat.succ heq1, heq2⟩

theorem fa_set_eq (l : List Kid) (k : Nat) (v : Kid) (hk : k < l.length) :
    (l.set k v)[k]? = some v := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ n =>
      simp at hk
      simp
      exact ih n (by omega)

theorem fa_set_neq (l : List Kid) (k j : Nat) (v : Kid) (h : j ≠ k) :
    (l.set k v)[j]? = l[j]? := by
  induction l generalizing k j with
  | nil => simp
  | cons a as ih =>
    cases k with
    | zero =>
      cases j with
      | zero => simp at h
      | succ m => simp
    | succ n =>
      cases j with
      | zero => simp
      | succ m =>
        simp
        have h2 : m ≠ n := fun hh => h (congrArg Nat.succ hh)
        exact ih n m h2

theorem fa_upd_eq2 {α : Type} (f : Nat → α) (k : Nat) (v : α) (j : Nat) (h : j = k) :
    upd f k v j = v := by simp [upd, h]

theorem fa_upd_neq2 {α : Type} (f : Nat → α) (k j : Nat) (v : α) (h : j ≠ k) :
    upd f k v j = f j := by simp [upd, h]

theorem fa_fill_obs_len2 (t : Truth) (k q : Nat) :
    (t.observe (.fill k q)).kids.length = t.kids.length := by
  simp only [Truth.observe]
  split
  · rename_i c hc
    simp
  · rfl

theorem fa_ack_pres3 (b : Build) (x : Sys) (k : Nat) (hx : InvFillAcc x) :
    InvFillAcc (advance step b x (.ack k)) := by
  obtain ⟨hNP, hNC, hCorr, hKB, hCum⟩ := hx
  have hst : (advance step b x (.ack k)).st = x.st := plan0_ack_st_eq b x k
  have htr : (advance step b x (.ack k)).tr = x.tr := plan0_ack_tr_eq b x k
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hst, htr, hNP]
  · rw [hst, htr, hNC]
  · intro j c hj
    rw [htr] at hj
    have h := hCorr j c hj
    rw [hst]
    exact h
  · intro j hj
    rw [htr] at hj ⊢
    exact hKB j hj
  · intro id
    rw [hst, htr]
    exact hCum id

theorem plan3_route_children_corr_proof4 (b : Build) (x : Sys) (rid liq : Nat)
    (hNC : x.st.nChildren = x.tr.kids.length)
    (hCorr : ∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c →
      x.st.children k = ⟨c.parent, c.qty, c.done⟩)
    (k : Nat) (c : Kid)
    (hk : ((advance step b x (.route rid liq)).tr.kids)[k]? = some c) :
    (advance step b x (.route rid liq)).st.children k = ⟨c.parent, c.qty, c.done⟩ := by
  have hst : (advance step b x (.route rid liq)).st = (routeBySent x.st rid liq).1 :=
    my_adv_route_st_eq b x rid liq
  have htr : (advance step b x (.route rid liq)).tr =
      (x.tr.observe (.route rid liq)).record (routeBySent x.st rid liq).2 :=
    my_adv_route_tr_eq b x rid liq
  have hobs : x.tr.observe (.route rid liq) = x.tr := my_obs_route_is_id x.tr rid liq
  rw [hobs] at htr
  by_cases hcond : rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)
  · have hout : (routeBySent x.st rid liq).2 = [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩] :=
      my_route_out_active2 x.st rid liq hcond
    have hchild : (routeBySent x.st rid liq).1.children =
        upd x.st.children x.st.nChildren ⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ := by
      simp [routeBySent, hcond]
    rw [hst, hchild]
    rw [htr, hout] at hk
    have htr_kids : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids =
        x.tr.kids ++ [(⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)] := rfl
    rw [htr_kids] at hk
    rcases fa_get_append x.tr.kids (⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid) k c hk with ⟨hlt, heq⟩ | ⟨heqk, heqc⟩
    · have hcorr := hCorr k c heq
      have hne : k ≠ x.st.nChildren := by omega
      rw [fa_upd_neq2 _ _ _ _ hne, hcorr]
    · rw [heqk, heqc, ← hNC]
      exact fa_upd_eq2 _ _ _ _ rfl
  · have hout : (routeBySent x.st rid liq).2 = [] :=
      my_route_out_inactive2 x.st rid liq hcond
    have hfst : (routeBySent x.st rid liq).1 = x.st := by simp [routeBySent, hcond]
    rw [hst, hfst]
    rw [htr, hout] at hk
    have hrec : (x.tr.record ([] : List Child)).kids = x.tr.kids := by simp [Truth.record]
    rw [hrec] at hk
    exact hCorr k c hk

theorem plan3_route_children_corr (b : Build) (x : Sys) (rid liq : Nat)
    (hNC : x.st.nChildren = x.tr.kids.length)
    (hCorr : ∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c →
      x.st.children k = ⟨c.parent, c.qty, c.done⟩)
    (k : Nat) (c : Kid)
    (hk : ((advance step b x (.route rid liq)).tr.kids)[k]? = some c) :
    (advance step b x (.route rid liq)).st.children k = ⟨c.parent, c.qty, c.done⟩ := by
  have hst : (advance step b x (.route rid liq)).st = (routeBySent x.st rid liq).1 :=
    my_adv_route_st_eq b x rid liq
  have htr : (advance step b x (.route rid liq)).tr =
      (x.tr.observe (.route rid liq)).record (routeBySent x.st rid liq).2 :=
    my_adv_route_tr_eq b x rid liq
  have hobs : x.tr.observe (.route rid liq) = x.tr := my_obs_route_is_id x.tr rid liq
  rw [hobs] at htr
  by_cases hcond : rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)
  · have hout : (routeBySent x.st rid liq).2 = [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩] :=
      my_route_out_active2 x.st rid liq hcond
    have hchild : (routeBySent x.st rid liq).1.children =
        upd x.st.children x.st.nChildren ⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ := by
      simp [routeBySent, hcond]
    rw [hst, hchild]
    rw [htr, hout] at hk
    have htr_kids : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids =
        x.tr.kids ++ [(⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)] := rfl
    rw [htr_kids] at hk
    rcases fa_get_append x.tr.kids (⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid) k c hk with ⟨hlt, heq⟩ | ⟨heqk, heqc⟩
    · have hcorr := hCorr k c heq
      have hne : k ≠ x.st.nChildren := by omega
      rw [fa_upd_neq2 _ _ _ _ hne, hcorr]
    · rw [heqk, heqc, ← hNC]
      exact fa_upd_eq2 _ _ _ _ rfl
  · have hout : (routeBySent x.st rid liq).2 = [] :=
      my_route_out_inactive2 x.st rid liq hcond
    have hfst : (routeBySent x.st rid liq).1 = x.st := by simp [routeBySent, hcond]
    rw [hst, hfst]
    rw [htr, hout] at hk
    have hrec : (x.tr.record ([] : List Child)).kids = x.tr.kids := by simp [Truth.record]
    rw [hrec] at hk
    exact hCorr k c hk

theorem plan4_get_set_cases_of_lt (l : List Kid) (k j : Nat) (v c : Kid)
    (hk : k < l.length) (h : (l.set k v)[j]? = some c) :
    (j = k ∧ c = v) ∨ (j ≠ k ∧ l[j]? = some c) := by
  by_cases hj : j = k
  · have heq := fa_set_eq l k v hk
    have h2 : (l.set k v)[k]? = some c := hj ▸ h
    rw [heq] at h2
    simp at h2
    exact Or.inl ⟨hj, h2.symm⟩
  · have heq := fa_set_neq l k j v hj
    rw [heq] at h
    exact Or.inr ⟨hj, h⟩

theorem plan4_fill_tr_kids_eq (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).tr.kids =
      match x.tr.kids[k]? with
      | some c => x.tr.kids.set k { c with done := c.done + min q (c.qty - c.done) }
      | none => x.tr.kids := by
  have htr : (advance step b x (.fill k q)).tr = x.tr.observe (.fill k q) :=
    plan0_fill_tr_eq2 b x k q
  rw [htr]
  cases h : x.tr.kids[k]? with
  | none => simp [Truth.observe, h]
  | some c => simp [Truth.observe, h]

theorem plan4_fill_st_children_ne (b : Build) (x : Sys) (k q j : Nat)
    (hj : j ≠ k) :
    (advance step b x (.fill k q)).st.children j = x.st.children j := by
  have hst : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := rfl
  rw [hst]
  simp only [step]
  split
  · rename_i hlt
    simp only
    have hne : j ≠ k := hj
    have heq : (upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) }) j = x.st.children j := by
      simp [upd, hj]
    exact heq
  · rfl

theorem probe_len (l : List Kid) (k : Nat) (hle : l.length ≤ k) : l[k]? = none := by
  simp [hle]

theorem plan4_fill_st_children_kid (b : Build) (x : Sys) (k q : Nat)
    (hNC : x.st.nChildren = x.tr.kids.length)
    (hCorr : ∀ (j : Nat) (c : Kid), x.tr.kids[j]? = some c →
      x.st.children j = ⟨c.parent, c.qty, c.done⟩)
    (c0 : Kid) (hc0 : x.tr.kids[k]? = some c0) :
    (advance step b x (.fill k q)).st.children k =
      ⟨c0.parent, c0.qty, c0.done + min q (c0.qty - c0.done)⟩ := by
  have hlen : k < x.tr.kids.length := by
    by_cases h : k < x.tr.kids.length
    · exact h
    · have hle : x.tr.kids.length ≤ k := Nat.le_of_not_gt h
      have hnone : x.tr.kids[k]? = none := probe_len x.tr.kids k hle
      rw [hnone] at hc0
      contradiction
  have hlt : k < x.st.nChildren := by omega
  have hcorr : x.st.children k = (⟨c0.parent, c0.qty, c0.done⟩ : ChildRec) := hCorr k c0 hc0
  have hst : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := rfl
  rw [hst]
  simp only [step, hlt, ↓reduceIte]
  simp only [hcorr]
  simp [upd]

theorem aux_no_kid_some (l : List Kid) (k : Nat) (hk : k < l.length) : l[k]? ≠ none := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ n => simp only [List.getElem?_cons_succ]; exact ih n (by simpa using hk)

theorem plan4_fill_st_children_of_no_kid (b : Build) (x : Sys) (k q : Nat)
    (hNC : x.st.nChildren = x.tr.kids.length)
    (h : x.tr.kids[k]? = none) :
    (advance step b x (.fill k q)).st.children = x.st.children := by
  have h_not : ¬ k < x.st.nChildren := by
    intro hlt
    have hlt2 : k < x.tr.kids.length := by omega
    exact aux_no_kid_some x.tr.kids k hlt2 h
  have hst : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := rfl
  rw [hst]
  simp [step, h_not]

theorem plan3_fill_children_corr (b : Build) (x : Sys) (k q : Nat)
    (hNC : x.st.nChildren = x.tr.kids.length)
    (hCorr : ∀ (j : Nat) (c : Kid), x.tr.kids[j]? = some c →
      x.st.children j = ⟨c.parent, c.qty, c.done⟩)
    (j : Nat) (c : Kid)
    (hj : ((advance step b x (.fill k q)).tr.kids)[j]? = some c) :
    (advance step b x (.fill k q)).st.children j = ⟨c.parent, c.qty, c.done⟩ := by
  have htr_eq := plan4_fill_tr_kids_eq b x k q
  cases hkk : x.tr.kids[k]? with
  | none =>
    have htr2 : (advance step b x (.fill k q)).tr.kids = x.tr.kids := by
      rw [htr_eq]
      simp [hkk]
    rw [htr2] at hj
    have hcorr := hCorr j c hj
    have hst_eq := plan4_fill_st_children_of_no_kid b x k q hNC hkk
    rw [hst_eq]
    exact hcorr
  | some c0 =>
    have htr2 : (advance step b x (.fill k q)).tr.kids =
        x.tr.kids.set k { c0 with done := c0.done + min q (c0.qty - c0.done) } := by
      rw [htr_eq]
      simp [hkk]
    rw [htr2] at hj
    by_cases heq : j = k
    · have hjk : (x.tr.kids.set k { c0 with done := c0.done + min q (c0.qty - c0.done) })[k]? = some c := heq ▸ hj
      have hk_len : k < x.tr.kids.length := by
        by_cases hlt : k < x.tr.kids.length
        · exact hlt
        · have hle : x.tr.kids.length ≤ k := by omega
          have hnn := probe_len x.tr.kids k hle
          rw [hkk] at hnn
          contradiction
      have hv := fa_set_eq x.tr.kids k { c0 with done := c0.done + min q (c0.qty - c0.done) } hk_len
      rw [hv] at hjk
      have hjc : c = { c0 with done := c0.done + min q (c0.qty - c0.done) } := by
        simp at hjk
        exact hjk.symm
      have hst_k := plan4_fill_st_children_kid b x k q hNC hCorr c0 hkk
      have hj_eq : j = k := heq
      rw [hj_eq]
      rw [hst_k]
      rw [hjc]
    · have hset_eq := fa_set_neq x.tr.kids k j { c0 with done := c0.done + min q (c0.qty - c0.done) } heq
      have h_old : x.tr.kids[j]? = some c := by
        have hrr : (x.tr.kids.set k { c0 with done := c0.done + min q (c0.qty - c0.done) })[j]? = x.tr.kids[j]? := hset_eq
        rw [hrr] at hj
        exact hj
      have hcorr := hCorr j c h_old
      have hst_ne := plan4_fill_st_children_ne b x k q j heq
      rw [hst_ne]
      exact hcorr

theorem probe_fill_match (x : Sys) (k q id : Nat) (c0 : Kid) (hkk : x.tr.kids[k]? = some c0) :
    (match x.tr.kids[k]? with | some c => (if c.parent = id then min q (c.qty - c.done) else 0) | none => 0)
    = (if c0.parent = id then min q (c0.qty - c0.done) else 0) := by
  simp [hkk]

theorem probe_fill_none (x : Sys) (k q id : Nat) (hkk : x.tr.kids[k]? = none) :
    (match x.tr.kids[k]? with | some c => (if c.parent = id then min q (c.qty - c.done) else 0) | none => 0) = 0 := by
  simp [hkk]

theorem probe_state_fill_none (b : Build) (x : Sys) (k q : Nat) (hnot : ¬ k < x.st.nChildren) (id : Nat) :
    ((advance step b x (.fill k q)).st.parents id).cum = (x.st.parents id).cum := by
  have hst : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := rfl
  rw [hst, my_step_fill_st3 b x.st k q hnot]

theorem probe_fill_st_cum3 (b : Build) (s : State) (k q id : Nat) (hlt : k < s.nChildren) :
    ((step b s (.fill k q)).1.parents id).cum =
      (s.parents id).cum + (if (s.children k).parent = id then min q ((s.children k).qty - (s.children k).done) else 0) := by
  rw [my_step_fill_st2 b s k q hlt]
  simp only
  by_cases heq : (s.children k).parent = id
  · subst heq
    simp [upd_eq]
  · have hne : id ≠ (s.children k).parent := fun h => heq h.symm
    have e : upd s.parents (s.children k).parent
      { qty := (s.parents (s.children k).parent).qty, flag := (s.parents (s.children k).parent).flag,
        sent := (s.parents (s.children k).parent).sent,
        cum := (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) } id
        = s.parents id := upd_neq _ _ _ _ hne
    rw [e]
    simp [heq]

theorem plan3_fill_cum_eq (b : Build) (x : Sys) (k q : Nat)
    (hNC : x.st.nChildren = x.tr.kids.length)
    (hCorr : ∀ (j : Nat) (c : Kid), x.tr.kids[j]? = some c →
      x.st.children j = ⟨c.parent, c.qty, c.done⟩)
    (hCum : ∀ id, (x.st.parents id).cum = x.tr.exec id)
    (id : Nat) :
    ((advance step b x (.fill k q)).st.parents id).cum =
      (advance step b x (.fill k q)).tr.exec id := by
  have htr : (advance step b x (.fill k q)).tr = x.tr.observe (.fill k q) :=
    plan0_fill_tr_eq2 b x k q
  cases hkk : x.tr.kids[k]? with
  | none =>
    have hex0 : (x.tr.observe (.fill k q)).exec id = x.tr.exec id := by
      have h := my_obs_fill_exec x.tr k q id
      rw [hkk] at h
      simpa using h
    rw [htr, hex0, ← hCum id]
    have hnot : ¬ k < x.st.nChildren := by
      intro hlt
      have hlt2 : k < x.tr.kids.length := by omega
      have hne := aux_no_kid_some x.tr.kids k hlt2
      rw [hkk] at hne
      exact hne rfl
    exact probe_state_fill_none b x k q hnot id
  | some c0 =>
    have hex1 : (x.tr.observe (.fill k q)).exec id =
        x.tr.exec id + (if c0.parent = id then min q (c0.qty - c0.done) else 0) := by
      have h := my_obs_fill_exec x.tr k q id
      rw [hkk] at h
      simpa using h
    rw [htr, hex1, ← hCum id]
    have hltT : k < x.tr.kids.length := by
      by_cases h : k < x.tr.kids.length
      · exact h
      · have hle : x.tr.kids.length ≤ k := Nat.le_of_not_gt h
        have hnn := probe_len x.tr.kids k hle
        rw [hkk] at hnn
        contradiction
    have hlt : k < x.st.nChildren := by omega
    have hcorr : x.st.children k = (⟨c0.parent, c0.qty, c0.done⟩ : ChildRec) := hCorr k c0 hkk
    have hst : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := rfl
    rw [hst, probe_fill_st_cum3 b x.st k q id hlt, hcorr]

theorem plan3_invFillAcc_route (b : Build) (x : Sys) (rid liq : Nat) :
    InvFillAcc x → InvFillAcc (advance step b x (.route rid liq)) := by
  intro hx
  obtain ⟨hNP, hNC, hCorr, hKB, hCum⟩ := hx
  have hadv : advance step b x (.route rid liq) =
      ⟨(routeBySent x.st rid liq).1, x.tr.record (routeBySent x.st rid liq).2⟩ :=
    plan1_advance_route b x rid liq
  rw [hadv]
  by_cases hcond : rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)
  · have hout : (routeBySent x.st rid liq).2 = [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩] :=
      my_route_out_active2 x.st rid liq hcond
    have hnP : (routeBySent x.st rid liq).1.nParents = x.st.nParents :=
      my_route_nParents2 x.st rid liq
    have hnC : (routeBySent x.st rid liq).1.nChildren = x.st.nChildren + 1 := by
      simp [routeBySent, hcond]
    have hrecN : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).nOrders = x.tr.nOrders :=
      my_record_nOrders2 _ _
    have hrecL : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids.length = x.tr.kids.length + 1 := by
      have h := my_record_len x.tr [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]
      simpa using h
    rw [hout]
    have hidN : rid < x.tr.nOrders := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [hnP, hrecN, hNP]
    · simp only [hnC, hrecL, hNC]
    · intro k c hk
      have hk2 : ((advance step b x (.route rid liq)).tr.kids)[k]? = some c := by
        rw [hadv, hout]; exact hk
      exact plan3_route_children_corr b x rid liq hNC hCorr k c hk2
    · intro k hk
      have hkids : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).kids =
          x.tr.kids ++ [(⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)] := rfl
      have hn : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).nOrders = x.tr.nOrders :=
        my_record_nOrders2 _ _
      rw [hkids] at hk
      rw [hn]
      simp at hk
      rcases hk with hk | rfl
      · exact hKB _ hk
      · exact hidN
    · intro id
      have hc1 : (((routeBySent x.st rid liq).1.parents id)).cum = (x.st.parents id).cum :=
        my_route_cum_old2 x.st rid liq id
      have he1 : (x.tr.record [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]).exec id = x.tr.exec id :=
        my_record_exec2 _ _ _
      rw [hc1, he1, hCum id]
  · have hout : (routeBySent x.st rid liq).2 = [] :=
      my_route_out_inactive2 x.st rid liq hcond
    have hfst : (routeBySent x.st rid liq).1 = x.st := by simp [routeBySent, hcond]
    rw [hout, hfst]
    have hrec : x.tr.record ([] : List Child) = x.tr := plan1_record_nil x.tr
    rw [hrec]
    exact ⟨hNP, hNC, hCorr, hKB, hCum⟩

theorem plan3_invFillAcc_fill (b : Build) (x : Sys) (k q : Nat) :
    InvFillAcc x → InvFillAcc (advance step b x (.fill k q)) := by
  intro hx
  obtain ⟨hNP, hNC, hCorr, hKB, hCum⟩ := hx
  have htr : (advance step b x (.fill k q)).tr = x.tr.observe (.fill k q) :=
    plan0_fill_tr_eq2 b x k q
  have hStNP : (advance step b x (.fill k q)).st.nParents = x.st.nParents := by
    rw [plan0_fill_st_fst]
    exact plan0_fill_nParents_eq4 b x k q
  have hTrNO : (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders := by
    rw [htr]; exact my_obs_fill_nOrders x.tr k q
  have hStNC : (advance step b x (.fill k q)).st.nChildren = x.st.nChildren := by
    have hst : (advance step b x (.fill k q)).st = (step b x.st (.fill k q)).1 := rfl
    rw [hst]
    simp only [step]
    split
    · simp
    · rfl
  have hTrLen : (advance step b x (.fill k q)).tr.kids.length = x.tr.kids.length := by
    rw [htr]; exact fa_fill_obs_len2 x.tr k q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hStNP, hTrNO, hNP]
  · rw [hStNC, hTrLen, hNC]
  · intro j c hj
    exact plan3_fill_children_corr b x k q hNC hCorr j c hj
  · exact plan2_fill_kids_bound b x k q hKB
  · intro id
    exact plan3_fill_cum_eq b x k q hNC hCorr hCum id

theorem plan3_invFillAcc_run_aux_test : InvFillAcc start := invFillAcc_base

theorem plan3_invFillAcc_run_stepcheck (b : Build) (x : Sys) (e : Event) (hx : InvFillAcc x) :
    InvFillAcc (advance step b x e) := by
  cases e with
  | parent q f => exact fa_parent_pres2 b x q f hx
  | route rid liq => exact plan3_invFillAcc_route b x rid liq hx
  | ack k => exact fa_ack_pres3 b x k hx
  | fill k q => exact plan3_invFillAcc_fill b x k q hx

theorem plan3_invFillAcc_run (b : Build) (evs : List Event) :
    InvFillAcc (run step b evs) :=
  run_induction step b InvFillAcc invFillAcc_base (fun x e hx => plan3_invFillAcc_run_stepcheck b x e hx) evs

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  constructor <;> (cases b <;> cases flag <;> rfl)

theorem req_routes_available : RoutesAvailable step :=
  fun b evs id liq => plan0_routes_available_aux b evs id liq

theorem req_never_overroute : NeverOverroute step := by
  intro b evs id
  have hW := myWeak2_run_clean2 b evs
  obtain ⟨hNP, hSent, hQty, hKids, hLe⟩ := hW
  by_cases hid : id < (run step b evs).tr.nOrders
  · have eS := hSent id
    have eQ := hQty id hid
    have eL := hLe id
    omega
  · have hsent0 : (run step b evs).tr.sent id = 0 := by
      exact my_sentFor_ge (run step b evs).tr.kids (run step b evs).tr.nOrders id hKids (by omega) |>.symm ▸ rfl
    omega

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e pid hExec c hc
  have hW := myWeak2_run_clean2 b evs
  obtain ⟨hNP, hSent, hQty, hKids, hLe⟩ := hW
  cases e with
  | parent q f =>
    have hout : (step b (run step b evs).st (.parent q f)).2 = [] :=
      my_step_parent_out b _ q f
    rw [hout] at hc
    simp at hc
  | ack k =>
    have hout : (step b (run step b evs).st (.ack k)).2 = [] :=
      my_step_ack_out b _ k
    rw [hout] at hc
    simp at hc
  | fill k q =>
    have hout : (step b (run step b evs).st (.fill k q)).2 = [] :=
      my_step_fill_out b _ k q
    rw [hout] at hc
    simp at hc
  | route rid liq =>
    have hStep : step b (run step b evs).st (.route rid liq) =
        routeBySent (run step b evs).st rid liq :=
      my_step_route_eq b _ rid liq
    rw [hStep] at hc
    by_cases hcond : rid < (run step b evs).st.nParents ∧
        0 < min liq (((run step b evs).st.parents rid).qty - (((run step b evs).st.parents rid).sent))
    · have hout := my_route_out_active2 (run step b evs).st rid liq hcond
      rw [hout] at hc
      simp only [List.mem_singleton] at hc
      have hcPar : c.parent = rid := by rw [hc]
      intro hEq
      have hEqR : rid = pid := by rw [← hcPar]; exact hEq
      by_cases hid : pid < (run step b evs).tr.nOrders
      · exact my_stop_aux_final b evs rid liq pid hNP hSent hQty hcond hEqR hExec hid
      · omega
    · have hout := my_route_out_inactive2 (run step b evs).st rid liq hcond
      rw [hout] at hc
      simp at hc

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  have h1 : (run step b evs).tr.exec id ≤ (run step b evs).tr.sent id :=
    exec_le_sent step b evs id
  have h2 : (run step b evs).tr.sent id ≤ (run step b evs).tr.qty id :=
    req_never_overroute b evs id
  omega

theorem req_fill_accounting : FillAccounting step := by
  intro b evs id _
  exact (plan3_invFillAcc_run b evs).2.2.2.2 id

end OrderRouter
