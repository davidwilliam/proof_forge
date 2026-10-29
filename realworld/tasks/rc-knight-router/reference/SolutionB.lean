import OrderRouter.Spec
import OrderRouter.Lemmas
/-!
Second reference: the port with the Power Peg path kept but repaired. The path a parent order
takes still depends on the server's code version and the flag, but both paths size a child
order from the shares not yet sent, and every execution report advances the cumulative
executed quantity, capped at the child order's unexecuted shares. The proofs show that this
router computes the same result as a canonical single-path router (`canon`) for every code
version, state and event, and prove the requirements for `canon`.
-/
namespace OrderRouter

/-- Shares of a parent order not yet sent in child orders. -/
def unsent (p : ParentRec) : Nat := p.qty - p.sent

/-- The smaller of two quantities. -/
def capAt (a b : Nat) : Nat := if a ≤ b then a else b

/-- Record a new child order of `c` shares for parent `id`. -/
def sendChild (s : State) (id c : Nat) : State :=
  { s with parents := upd s.parents id { s.parents id with sent := (s.parents id).sent + c },
           nChildren := s.nChildren + 1,
           children := upd s.children s.nChildren ⟨id, c, 0⟩ }

/-- Regular and RLP paths. -/
def routeNew (s : State) (id liq : Nat) : State × List Child :=
  if id < s.nParents then
    if capAt liq (unsent (s.parents id)) = 0 then (s, [])
    else (sendChild s id (capAt liq (unsent (s.parents id))), [⟨id, capAt liq (unsent (s.parents id))⟩])
  else (s, [])

/-- Power Peg path, repaired: it sizes child orders from the shares not yet sent. -/
def routePeg (s : State) (id liq : Nat) : State × List Child :=
  if id < s.nParents ∧ 0 < unsent (s.parents id) ∧ 0 < liq then
    (sendChild s id (capAt liq (unsent (s.parents id))), [⟨id, capAt liq (unsent (s.parents id))⟩])
  else (s, [])

/-- Execution report for child order `k`: record at most its unexecuted shares, on the child
order and on its parent's cumulative executed quantity. -/
def applyFill (s : State) (k q : Nat) : State :=
  let c := s.children k
  let x := capAt q (c.qty - c.done)
  { s with parents := upd s.parents c.parent { s.parents c.parent with cum := (s.parents c.parent).cum + x },
           children := upd s.children k { c with done := c.done + x } }

def step : Impl := fun b s e =>
  match e with
  | .parent q f =>
    ({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ }, [])
  | .route id liq =>
    match b, (s.parents id).flag with
    | .legacy, true => routePeg s id liq
    | _, _ => routeNew s id liq
  | .ack _ => (s, [])
  | .fill k q => if k < s.nChildren then (applyFill s k q, []) else (s, [])

/-! ## A canonical single-path router and its proofs -/

def canon : Impl := fun _ s e =>
  match e with
  | .parent q f =>
    ({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ }, [])
  | .route id liq =>
    if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
      ({ s with parents := upd s.parents id
                  { s.parents id with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) },
                nChildren := s.nChildren + 1,
                children := upd s.children s.nChildren
                  ⟨id, min liq ((s.parents id).qty - (s.parents id).sent), 0⟩ },
       [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩])
    else (s, [])
  | .ack _ => (s, [])
  | .fill k q =>
    if k < s.nChildren then
      ({ s with parents := upd s.parents (s.children k).parent
                  { s.parents (s.children k).parent with
                    cum := (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) },
                children := upd s.children k
                  { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) } },
       [])
    else (s, [])

/-- The canonical router's records agree with the facts of the run. -/
structure Inv (x : Sys) : Prop where
  np   : x.st.nParents = x.tr.nOrders
  nc   : x.st.nChildren = x.tr.kids.length
  par  : ∀ id, id < x.tr.nOrders → (x.st.parents id).qty = x.tr.qty id ∧
           (x.st.parents id).sent = x.tr.sent id ∧ (x.st.parents id).cum = x.tr.exec id
  out  : ∀ id, x.tr.nOrders ≤ id → x.tr.sent id = 0 ∧ x.tr.exec id = 0
  kid  : ∀ k, k < x.tr.kids.length →
           x.tr.kids[k]? = some ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done⟩
  kpar : ∀ c ∈ x.tr.kids, c.parent < x.tr.nOrders
  le   : ∀ id, x.tr.sent id ≤ x.tr.qty id

theorem inv_start : Inv start := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [start, init, Truth.empty, Truth.sent, Truth.exec]

theorem inv_advance (b : Build) (x : Sys) (e : Event) (h : Inv x) : Inv (advance canon b x e) := by
  obtain ⟨np, nc, par, out, kid, kpar, le⟩ := h
  cases e with
  | parent q f =>
    simp only [advance, canon, Truth.observe, Truth.record, List.map_nil, List.append_nil]
    refine ⟨by simp [np], nc, ?_, ?_, kid, ?_, ?_⟩ <;> dsimp only
    · intro id hid
      simp only [Truth.sent, Truth.exec] at *
      by_cases h : id = x.tr.nOrders
      · subst h; have := out _ (Nat.le_refl _); simp [upd, np, this]
      · have := par id (by omega); simp [upd, np, h, this]
    · intro id hid; exact out id (by omega)
    · intro c hc; have := kpar c hc; omega
    · intro id
      simp only [Truth.sent] at *
      by_cases h : id = x.tr.nOrders
      · subst h; have := (out _ (Nat.le_refl _)).1; simp [upd, this]
      · simp [upd, h]; exact le id
  | route id liq =>
    simp only [advance, canon, Truth.observe]
    by_cases hc : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      simp only [Truth.record, List.map_cons, List.map_nil]
      have hp := par id (by omega)
      refine ⟨np, by simp [nc], ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
      · intro j hj
        simp only [Truth.sent, Truth.exec, sentFor_append, execFor_append, sentFor_cons, execFor_cons,
          sentFor_nil, execFor_nil] at *
        by_cases h : j = id
        · subst h; simp [upd, hp]
        · have := par j hj; simp [upd, h, this, Ne.symm h]
      · intro j hj
        have := out j hj
        simp only [Truth.sent, Truth.exec, sentFor_append, execFor_append, sentFor_cons, execFor_cons,
          sentFor_nil, execFor_nil] at *
        have : id ≠ j := by omega
        simp [this, out j hj]
      · intro k hk
        simp only [List.length_append, List.length_cons, List.length_nil] at hk
        by_cases h : k = x.tr.kids.length
        · subst h; simp [upd, nc]
        · have hk' : k < x.tr.kids.length := by omega
          rw [List.getElem?_append_left hk', kid k hk']
          simp [upd, nc, show k ≠ x.tr.kids.length from h]
      · intro c hc'
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with hc' | rfl
        · exact kpar c hc'
        · simp; omega
      · intro j
        simp only [Truth.sent, sentFor_append, sentFor_cons, sentFor_nil] at *
        by_cases h : id = j
        · subst h; have := hp.1; have := hp.2.1; simp only [Truth.sent] at *; simp; omega
        · simp [h]; exact le j
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      simp only [Truth.record, List.map_nil, List.append_nil]
      exact ⟨np, nc, par, out, kid, kpar, le⟩
  | ack k =>
    simp only [advance, canon, Truth.observe, Truth.record, List.map_nil, List.append_nil]
    exact ⟨np, nc, par, out, kid, kpar, le⟩
  | fill k q =>
    simp only [advance, canon]
    by_cases hk : k < x.st.nChildren
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hk)]
      have hkk : k < x.tr.kids.length := by omega
      have hget := kid k hkk
      simp only [Truth.observe, hget, Truth.record, List.map_nil, List.append_nil]
      have hcp := kpar _ (List.mem_of_getElem? hget)
      simp only at hcp
      refine ⟨np, by simp [nc], ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
      · intro j hj
        simp only [Truth.sent, Truth.exec]
        rw [sentFor_set_done _ _ _ _ hget, execFor_set_done _ _ _ _ hget]
        have := par j hj
        simp only [Truth.sent, Truth.exec] at this
        by_cases h : j = (x.st.children k).parent
        · subst h; simp [upd, this]
        · simp [upd, h, this, Ne.symm h]
      · intro j hj
        simp only [Truth.sent, Truth.exec]
        rw [sentFor_set_done _ _ _ _ hget, execFor_set_done _ _ _ _ hget]
        have := out j hj
        simp only [Truth.sent, Truth.exec] at this
        have : (x.st.children k).parent ≠ j := by omega
        simp [*]
      · intro k' hk'
        simp only [List.length_set] at hk'
        rw [List.getElem?_set]
        by_cases h : k = k'
        · subst h; simp [upd, hk']
        · simp [h, upd, Ne.symm h, kid k' hk']
      · intro c hc'
        rcases List.mem_or_eq_of_mem_set hc' with hc' | rfl
        · exact kpar c hc'
        · exact hcp
      · intro j
        simp only [Truth.sent]
        rw [sentFor_set_done _ _ _ _ hget]
        exact le j
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]
      have hnone : x.tr.kids[k]? = none := by
        rw [List.getElem?_eq_none_iff]; omega
      simp only [Truth.observe, hnone, Truth.record, List.map_nil, List.append_nil]
      exact ⟨np, nc, par, out, kid, kpar, le⟩

theorem inv_run (b : Build) (evs : List Event) : Inv (run canon b evs) :=
  run_induction canon b Inv inv_start (inv_advance b) evs

theorem route_out (b : Build) (evs : List Event) (id liq : Nat) :
    (canon b (run canon b evs).st (.route id liq)).2 = expectedRoute (run canon b evs).tr id liq := by
  have h := inv_run b evs
  simp only [canon, expectedRoute]
  by_cases hid : id < (run canon b evs).tr.nOrders
  · have hp := h.par id hid
    rw [h.np, hp.1, hp.2.1]
    split <;> simp_all
  · have h1 : ¬ (id < (run canon b evs).st.nParents ∧
        0 < min liq (((run canon b evs).st.parents id).qty - ((run canon b evs).st.parents id).sent)) := by
      rw [h.np]; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem canon_req_normal_order_routed : NormalOrderRouted canon := by
  intro b flag
  cases b <;> cases flag <;> decide

theorem canon_req_routes_available : RoutesAvailable canon := route_out

theorem canon_req_never_overroute : NeverOverroute canon := fun b evs id => (inv_run b evs).le id

theorem canon_req_stop_when_filled : StopWhenFilled canon := by
  intro b evs e id hfull c hc
  have hle := (inv_run b evs).le id
  have hex := exec_le_sent canon b evs id
  cases e with
  | route j liq =>
    rw [route_out] at hc
    simp only [expectedRoute] at hc
    split at hc
    · rename_i hcond
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      intro hj
      simp only at hj
      subst hj
      omega
    · simp at hc
  | parent q f => simp [canon] at hc
  | ack k => simp [canon] at hc
  | fill k q =>
    simp only [canon] at hc
    split at hc <;> simp at hc

theorem canon_req_no_excess_execution : NoExcessExecution canon := fun b evs id =>
  Nat.le_trans (exec_le_sent canon b evs id) ((inv_run b evs).le id)

theorem canon_req_fill_accounting : FillAccounting canon := fun b evs id hid =>
  ((inv_run b evs).par id hid).2.2


theorem capAt_eq_min (a b : Nat) : capAt a b = min a b := by
  simp only [capAt]; split <;> omega

theorem routeNew_eq (s : State) (id liq : Nat) : routeNew s id liq = canon .rlp s (.route id liq) := by
  simp only [routeNew, canon, sendChild, unsent, capAt_eq_min]
  by_cases h1 : id < s.nParents <;> by_cases h2 : min liq ((s.parents id).qty - (s.parents id).sent) = 0 <;>
    simp [h1, h2] <;> omega

theorem routePeg_eq (s : State) (id liq : Nat) : routePeg s id liq = canon .rlp s (.route id liq) := by
  simp only [routePeg, canon, sendChild, unsent, capAt_eq_min]
  by_cases h1 : id < s.nParents <;> by_cases h2 : 0 < (s.parents id).qty - (s.parents id).sent <;>
    by_cases h3 : 0 < liq <;> simp [h1, h2, h3] <;> omega

theorem step_eq : step = canon := by
  funext b s e
  cases e with
  | parent q f => rfl
  | route id liq =>
    have hc : canon b s (.route id liq) = canon .rlp s (.route id liq) := rfl
    rw [hc]
    simp only [step]
    split
    · exact routePeg_eq s id liq
    · exact routeNew_eq s id liq
  | ack k => rfl
  | fill k q =>
    simp only [step, canon, applyFill, capAt_eq_min]

theorem req_normal_order_routed : NormalOrderRouted step := by rw [step_eq]; exact canon_req_normal_order_routed
theorem req_routes_available    : RoutesAvailable step := by rw [step_eq]; exact canon_req_routes_available
theorem req_never_overroute     : NeverOverroute step := by rw [step_eq]; exact canon_req_never_overroute
theorem req_stop_when_filled    : StopWhenFilled step := by rw [step_eq]; exact canon_req_stop_when_filled
theorem req_no_excess_execution : NoExcessExecution step := by rw [step_eq]; exact canon_req_no_excess_execution
theorem req_fill_accounting     : FillAccounting step := by rw [step_eq]; exact canon_req_fill_accounting

end OrderRouter
