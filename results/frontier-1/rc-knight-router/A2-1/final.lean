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
      let p' := ({ p with cum := p.cum + x } : ParentRec)
      ({ s with parents := upd s.parents c.parent p',
                children := upd s.children k { c with done := c.done + x } }, [])
    else (s, [])

theorem test_unfold (s : State) (id liq : Nat) : (step Build.rlp s (.route id liq)).2 = (routeBySent s id liq).2 := by rfl

theorem test_obs_parent (t : Truth) (q : Nat) (f : Bool) : (t.observe (.parent q f)).nOrders = t.nOrders + 1 := by simp [Truth.observe]

theorem tmp_route_out (s : State) (id liq : Nat) : (step Build.rlp s (.route id liq)).2 = (routeBySent s id liq).2 := rfl

theorem tmp_route_st (s : State) (id liq : Nat) : (step Build.rlp s (.route id liq)).1 = (routeBySent s id liq).1 := rfl

theorem sentFor_zero_of_ne (l : List Kid) (id : Nat) (h : ∀ k ∈ l, k.parent ≠ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent ≠ id := h a (by simp)
    simp [ha]
    exact ih (fun k hk => h k (by simp [hk]))

theorem inv_start : True := trivial
-- check unfold of advance for parent

theorem chk_adv_parent (st : State) (tr : Truth) (q : Nat) (f : Bool) (b : Build) :
    (advance step b ⟨st, tr⟩ (.parent q f)).1.nParents = st.nParents + 1 := by
  simp [advance, step]

theorem inv_npq_start : (start.st.nParents = start.tr.nOrders) := by rfl

theorem adv_parent_np (st : State) (tr : Truth) (q : Nat) (f : Bool) (b : Build) :
    (advance step b ⟨st, tr⟩ (.parent q f)).st.nParents = st.nParents + 1 := by
  simp [advance, step]

theorem adv_parent_nord (st : State) (tr : Truth) (q : Nat) (f : Bool) (b : Build) :
    (advance step b ⟨st, tr⟩ (.parent q f)).tr.nOrders = tr.nOrders + 1 := by
  simp [advance, Truth.observe, Truth.record]

theorem inv_nc_v1 (b : Build) (evs : List Event) :
    (run step b evs).st.nChildren = (run step b evs).tr.kids.length := by
  refine run_induction step b (fun x => x.st.nChildren = x.tr.kids.length) rfl ?_ evs
  intro x e hx
  cases e with
  | parent q f =>
    show ((advance step b x (.parent q f)).st.nChildren = (advance step b x (.parent q f)).tr.kids.length)
    simp [advance, step, Truth.observe, Truth.record, hx]
  | route id liq =>
    show ((advance step b x (.route id liq)).st.nChildren = (advance step b x (.route id liq)).tr.kids.length)
    simp only [advance]
    have hrec : ∀ (t : Truth) (out : List Child), (t.record out).kids.length = t.kids.length + out.length := by
      intro t out; simp [Truth.record]
    have hobs : (x.tr.observe (.route id liq)) = x.tr := rfl
    rw [hobs, hrec]
    simp only [step, routeBySent]
    split
    · simp [hx]
    · simp [hx]
  | ack k =>
    show ((advance step b x (.ack k)).st.nChildren = (advance step b x (.ack k)).tr.kids.length)
    simp [advance, step, Truth.observe, Truth.record, hx]
  | fill k q =>
    show ((advance step b x (.fill k q)).st.nChildren = (advance step b x (.fill k q)).tr.kids.length)
    simp only [advance]
    have hobs_len : ((x.tr.observe (.fill k q)).record (step b x.st (.fill k q)).2).kids.length = (x.tr.observe (.fill k q)).kids.length := by
      have : (step b x.st (.fill k q)).2 = ([] : List Child) := by
        simp [step]
        split <;> rfl
      rw [this]
      simp [Truth.record]
    rw [hobs_len]
    have hst : (step b x.st (.fill k q)).1.nChildren = x.st.nChildren := by
      simp [step]
      split <;> simp
    rw [hst, hx]
    simp [Truth.observe]
    split
    · rename_i c hc
      simp [List.length_set]
    · rfl

theorem tmp_le_trans_test (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Nat.le_trans h1 h2

theorem sentFor_eq_zero_of_bound (l : List Kid) (n id : Nat) (h : ∀ k ∈ l, k.parent < n) (hle : n ≤ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent ≠ id := by
      have hmem : a ∈ a :: as := by simp
      have hlt := h a hmem
      omega
    simp [ha]
    exact ih (fun k hk => h k (by simp [hk]))

theorem execFor_eq_zero_of_bound (l : List Kid) (n id : Nat) (h : ∀ k ∈ l, k.parent < n) (hle : n ≤ id) : execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent ≠ id := by
      have hmem : a ∈ a :: as := by simp
      have hlt := h a hmem
      omega
    simp [ha]
    exact ih (fun k hk => h k (by simp [hk]))

def arch0_Inv (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ id, id < x.tr.nOrders →
    (x.st.parents id).qty = x.tr.qty id ∧
    (x.st.parents id).sent = x.tr.sent id ∧
    (x.st.parents id).cum = x.tr.exec id) ∧
  (∀ k, k < x.tr.kids.length →
    ∃ kid, x.tr.kids[k]? = some kid ∧
      x.st.children k = ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < x.tr.nOrders) ∧
  (∀ id, x.tr.sent id ≤ x.tr.qty id)

theorem arch0_inv_start : arch0_Inv start := by
  unfold arch0_Inv start init Truth.empty
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro id h
    simp at h
  · intro k h
    simp at h
  · intro id
    simp [Truth.sent, sentFor]


theorem arch0_inv_parent_step (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    arch0_Inv x → arch0_Inv (advance step b x (.parent q f)) := by
  sorry

theorem arch0_inv_route_step (b : Build) (x : Sys) (id liq : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.route id liq)) := by
  sorry

theorem arch0_inv_ack_step (b : Build) (x : Sys) (k : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.ack k)) := by
  intro h
  have heq : advance step b x (.ack k) = x := by
    cases x with
    | mk st tr => simp [advance, step, Truth.observe, Truth.record]
  rw [heq]
  exact h


theorem arch0_inv_fill_step (b : Build) (x : Sys) (k q : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.fill k q)) := by
  sorry

theorem arch0_inv_advance (b : Build) (x : Sys) (e : Event) :
    arch0_Inv x → arch0_Inv (advance step b x e) := by
  intro h
  cases e with
  | parent q f => exact arch0_inv_parent_step b x q f h
  | route id liq => exact arch0_inv_route_step b x id liq h
  | ack k => exact arch0_inv_ack_step b x k h
  | fill k q => exact arch0_inv_fill_step b x k q h




theorem arch0_nParents_eq_of_inv {x : Sys} (h : arch0_Inv x) :
    x.st.nParents = x.tr.nOrders := h.1


theorem arch0_parent_qty_of_inv {x : Sys} (h : arch0_Inv x)
    {id : Nat} (hid : id < x.tr.nOrders) :
    (x.st.parents id).qty = x.tr.qty id :=
  (h.2.2.1 id hid).1


theorem arch0_parent_sent_of_inv {x : Sys} (h : arch0_Inv x)
    {id : Nat} (hid : id < x.tr.nOrders) :
    (x.st.parents id).sent = x.tr.sent id :=
  (h.2.2.1 id hid).2.1










theorem arch0_inv_run (b : Build) (evs : List Event) :
    arch0_Inv (run step b evs) :=
  run_induction step b arch0_Inv arch0_inv_start (fun x e h => arch0_inv_advance b x e h) evs

theorem aux_parent_kids (x : Sys) (q : Nat) (f : Bool) (b : Build) :
    (advance step b x (.parent q f)).tr.kids = x.tr.kids := by
  rcases x with ⟨st, tr⟩
  simp [advance, step, Truth.observe, Truth.record]

theorem aux_parent_nOrders (x : Sys) (q : Nat) (f : Bool) (b : Build) :
    (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 := by
  rcases x with ⟨st, tr⟩
  simp [advance, step, Truth.observe, Truth.record]

theorem aux_parent_nParents (x : Sys) (q : Nat) (f : Bool) (b : Build) :
    (advance step b x (.parent q f)).st.nParents = x.st.nParents + 1 := by
  rcases x with ⟨st, tr⟩
  simp [advance, step]

theorem aux_parent_nChildren (x : Sys) (q : Nat) (f : Bool) (b : Build) :
    (advance step b x (.parent q f)).st.nChildren = x.st.nChildren := by
  rcases x with ⟨st, tr⟩
  simp [advance, step]

theorem aux_upd_eq2 {α : Type} (f : Nat → α) (k : Nat) (v : α) : upd f k v k = v := by
  simp [upd]

theorem aux_upd_ne2 {α : Type} (f : Nat → α) (k j : Nat) (v : α) (h : j ≠ k) : upd f k v j = f j := by
  simp [upd, h]

theorem aux_probeA (l : List Kid) (a : Kid) (h : a ∈ l) : ∃ (n : Nat), l[n]? = some a :=
  List.mem_iff_getElem?.mp h

theorem aux_idx_lt_of_get_some (l : List Kid) (n : Nat) (k : Kid) (h : l[n]? = some k) : n < l.length := by
  cases Decidable.em (n < l.length) with
  | inl hl => exact hl
  | inr hl =>
    have hle : l.length ≤ n := Nat.le_of_not_gt hl
    have hnone : l[n]? = (none : Option Kid) := List.getElem?_eq_none hle
    rw [hnone] at h
    cases h



theorem plan0_parent_sent_exec_eq (b : Build) (x : Sys) (q : Nat) (f : Bool) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id = x.tr.sent id ∧
    (advance step b x (.parent q f)).tr.exec id = x.tr.exec id := by
  have hk : (advance step b x (.parent q f)).tr.kids = x.tr.kids :=
    aux_parent_kids x q f b
  constructor
  · simp [Truth.sent, hk]
  · simp [Truth.exec, hk]








theorem plan0_parent_sent_le_qty_step (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id ≤
      (advance step b x (.parent q f)).tr.qty id := by
  obtain ⟨hNP, hNC, hRec, hKid, hLe⟩ := h
  rcases x with ⟨st, tr⟩
  have hkids : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids :=
    aux_parent_kids ⟨st, tr⟩ q f b
  have hsent : (advance step b ⟨st, tr⟩ (.parent q f)).tr.sent id = tr.sent id := by
    unfold Truth.sent
    rw [hkids]
  have hqty_id : (advance step b ⟨st, tr⟩ (.parent q f)).tr.qty id = upd tr.qty tr.nOrders q id := by
    simp [advance, step, Truth.observe, Truth.record]
  rw [hsent, hqty_id]
  by_cases heq : id = tr.nOrders
  · subst heq
    rw [aux_upd_eq2]
    have hall : ∀ k ∈ tr.kids, k.parent < tr.nOrders := by
      intro k hk
      obtain ⟨n, hn⟩ := aux_probeA tr.kids k hk
      have hnlt : n < tr.kids.length := aux_idx_lt_of_get_some tr.kids n k hn
      obtain ⟨kid', hk', _, hlt⟩ := hKid n hnlt
      rw [hn] at hk'
      simp at hk'
      subst hk'
      exact hlt
    have h0 : tr.sent tr.nOrders = 0 := by
      unfold Truth.sent
      exact sentFor_eq_zero_of_bound tr.kids tr.nOrders tr.nOrders hall (Nat.le_refl _)
    rw [h0]
    exact Nat.zero_le q
  · rw [aux_upd_ne2 _ _ _ _ heq]
    exact hLe id


theorem plan0_parent_kids_eq (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    (advance step b x (.parent q f)).tr.kids = x.tr.kids :=
  aux_parent_kids x q f b

theorem plan0_parent_sent_exec_eq_proof (b : Build) (x : Sys) (q : Nat) (f : Bool) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id = x.tr.sent id ∧
    (advance step b x (.parent q f)).tr.exec id = x.tr.exec id := by
  have hk : (advance step b x (.parent q f)).tr.kids = x.tr.kids :=
    aux_parent_kids x q f b
  constructor
  · simp [Truth.sent, hk]
  · simp [Truth.exec, hk]

theorem plan0_kid_parent_lt_of_inv {x : Sys} (h : arch0_Inv x)
    {kid : Kid} (hkid : kid ∈ x.tr.kids) :
    kid.parent < x.tr.nOrders := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨n, hn⟩ := aux_probeA x.tr.kids kid hkid
  have hnlt : n < x.tr.kids.length := aux_idx_lt_of_get_some x.tr.kids n kid hn
  obtain ⟨kid', hk', _, hlt⟩ := h4 n hnlt
  rw [hn] at hk'
  simp at hk'
  subst hk'
  exact hlt

theorem plan0_sent_exec_new_parent_of_inv {x : Sys} (h : arch0_Inv x) :
    x.tr.sent x.tr.nOrders = 0 ∧ x.tr.exec x.tr.nOrders = 0 := by
  have hlt : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders := fun k hk => plan0_kid_parent_lt_of_inv (x := x) h hk
  constructor
  · unfold Truth.sent
    exact sentFor_eq_zero_of_bound x.tr.kids x.tr.nOrders x.tr.nOrders hlt (Nat.le_refl _)
  · unfold Truth.exec
    exact execFor_eq_zero_of_bound x.tr.kids x.tr.nOrders x.tr.nOrders hlt (Nat.le_refl _)

theorem plan0_parent_records_step_aux_test (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) :
    (advance step b x (.parent q f)).st.parents x.tr.nOrders =
      (⟨q, f, 0, 0⟩ : ParentRec) := by
  simp [advance, step, aux_upd_eq2, h.1]

theorem plan0_parent_records_step_probe1 (b : Build) (st : State) (tr : Truth) (q : Nat) (f : Bool) :
    (advance step b ⟨st, tr⟩ (.parent q f)).tr.nOrders = tr.nOrders + 1 := by
  simp [advance, step, Truth.observe, Truth.record]

theorem plan0_parent_records_step (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat)
    (hid : id < (advance step b x (.parent q f)).tr.nOrders) :
    ((advance step b x (.parent q f)).st.parents id).qty =
        (advance step b x (.parent q f)).tr.qty id ∧
    ((advance step b x (.parent q f)).st.parents id).sent =
        (advance step b x (.parent q f)).tr.sent id ∧
    ((advance step b x (.parent q f)).st.parents id).cum =
        (advance step b x (.parent q f)).tr.exec id := by
  obtain ⟨hNP, hNC, hRec, hKid, hLe⟩ := h
  rcases x with ⟨st, tr⟩
  simp only at hNP hNC hRec hKid hLe
  have hNOrders : (advance step b ⟨st, tr⟩ (.parent q f)).tr.nOrders = tr.nOrders + 1 := by
    simp [advance, Truth.observe, Truth.record]
  rw [hNOrders] at hid
  have hStPar : (advance step b ⟨st, tr⟩ (.parent q f)).st.parents id = upd st.parents st.nParents ⟨q, f, 0, 0⟩ id := by
    simp [advance, step]
  have hTrQty : (advance step b ⟨st, tr⟩ (.parent q f)).tr.qty id = upd tr.qty tr.nOrders q id := by
    simp [advance, Truth.observe, Truth.record, upd]
  have hTrSent : (advance step b ⟨st, tr⟩ (.parent q f)).tr.sent id = tr.sent id := by
    have hk : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids := aux_parent_kids _ q f b
    simp [Truth.sent, hk]
  have hTrExec : (advance step b ⟨st, tr⟩ (.parent q f)).tr.exec id = tr.exec id := by
    have hk : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids := aux_parent_kids _ q f b
    simp [Truth.exec, hk]
  have hNew := plan0_sent_exec_new_parent_of_inv (x := ⟨st, tr⟩) ⟨hNP, hNC, hRec, hKid, hLe⟩
  rw [hStPar, hTrQty, hTrSent, hTrExec]
  by_cases heq : id = tr.nOrders
  · subst heq
    rw [hNP]
    rw [aux_upd_eq2, aux_upd_eq2]
    simp [hNew.1, hNew.2]
  · have hne_st : id ≠ st.nParents := by omega
    have hid_old : id < tr.nOrders := by omega
    rw [aux_upd_ne2 _ _ _ _ hne_st]
    rw [aux_upd_ne2 _ _ _ _ heq]
    obtain ⟨hq, hs, hc⟩ := hRec id hid_old
    simp [hq, hs, hc]

theorem plan0_probe_qty (b : Build) (st : State) (tr : Truth) (q : Nat) (f : Bool) (id : Nat) :
    (advance step b ⟨st, tr⟩ (.parent q f)).tr.qty id = upd tr.qty tr.nOrders q id := by
  simp [advance, step, Truth.observe, Truth.record]

theorem probe_sent_rw (b : Build) (st : State) (tr : Truth) (q : Nat) (f : Bool) (id : Nat)
    (hkids : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids) :
    (advance step b ⟨st, tr⟩ (.parent q f)).tr.sent id = tr.sent id := by
  unfold Truth.sent
  rw [hkids]

theorem plan0_parent_sent_le_qty_step_proof2 (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id ≤
      (advance step b x (.parent q f)).tr.qty id := by
  obtain ⟨hNP, hNC, hRec, hKid, hLe⟩ := h
  rcases x with ⟨st, tr⟩
  have hkids : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids :=
    aux_parent_kids ⟨st, tr⟩ q f b
  have hsent : (advance step b ⟨st, tr⟩ (.parent q f)).tr.sent id = tr.sent id :=
    probe_sent_rw b st tr q f id hkids
  have hqty_id : (advance step b ⟨st, tr⟩ (.parent q f)).tr.qty id = upd tr.qty tr.nOrders q id :=
    plan0_probe_qty b st tr q f id
  rw [hsent, hqty_id]
  by_cases heq : id = tr.nOrders
  · subst heq
    rw [aux_upd_eq2]
    have h0 : tr.sent tr.nOrders = 0 :=
      (plan0_sent_exec_new_parent_of_inv (x := ⟨st, tr⟩) ⟨hNP, hNC, hRec, hKid, hLe⟩).1
    rw [h0]
    exact Nat.zero_le q
  · rw [aux_upd_ne2 _ _ _ _ heq]
    exact hLe id

theorem plan0_selfcontained_check (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id ≤
      (advance step b x (.parent q f)).tr.qty id := by
  obtain ⟨hNP, hNC, hRec, hKid, hLe⟩ := h
  rcases x with ⟨st, tr⟩
  have hkids : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids :=
    aux_parent_kids ⟨st, tr⟩ q f b
  have hsent : (advance step b ⟨st, tr⟩ (.parent q f)).tr.sent id = tr.sent id := by
    unfold Truth.sent
    rw [hkids]
  have hqty_id : (advance step b ⟨st, tr⟩ (.parent q f)).tr.qty id = upd tr.qty tr.nOrders q id := by
    simp [advance, step, Truth.observe, Truth.record]
  rw [hsent, hqty_id]
  by_cases heq : id = tr.nOrders
  · subst heq
    rw [aux_upd_eq2]
    have hall : ∀ k ∈ tr.kids, k.parent < tr.nOrders := by
      intro k hk
      obtain ⟨n, hn⟩ := aux_probeA tr.kids k hk
      have hnlt : n < tr.kids.length := aux_idx_lt_of_get_some tr.kids n k hn
      obtain ⟨kid', hk', _, hlt⟩ := hKid n hnlt
      rw [hn] at hk'
      simp at hk'
      subst hk'
      exact hlt
    have h0 : tr.sent tr.nOrders = 0 := by
      unfold Truth.sent
      exact sentFor_eq_zero_of_bound tr.kids tr.nOrders tr.nOrders hall (Nat.le_refl _)
    rw [h0]
    exact Nat.zero_le q
  · rw [aux_upd_ne2 _ _ _ _ heq]
    exact hLe id

theorem arch0_inv_parent_step_proof (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    arch0_Inv x → arch0_Inv (advance step b x (.parent q f)) := by
  intro h
  obtain ⟨hNP, hNC, hRec, hKid, hLe⟩ := h
  rcases x with ⟨st, tr⟩
  simp only at hNP hNC hRec hKid hLe
  have hkids : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids :=
    aux_parent_kids ⟨st, tr⟩ q f b
  have hnOrd : (advance step b ⟨st, tr⟩ (.parent q f)).tr.nOrders = tr.nOrders + 1 := by
    simp [advance, Truth.observe, Truth.record]
  have hnPar : (advance step b ⟨st, tr⟩ (.parent q f)).st.nParents = st.nParents + 1 := by
    simp [advance, step]
  have hnChi : (advance step b ⟨st, tr⟩ (.parent q f)).st.nChildren = st.nChildren := by
    simp [advance, step]
  have hklen : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids.length = tr.kids.length := by
    rw [hkids]
  have hchild_eq : ∀ k, (advance step b ⟨st, tr⟩ (.parent q f)).st.children k = st.children k := by
    intro k
    simp [advance, step]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hnPar, hnOrd, hNP]
  · rw [hnChi, hklen, hNC]
  · intro id hid
    exact plan0_parent_records_step b ⟨st, tr⟩ q f ⟨hNP, hNC, hRec, hKid, hLe⟩ id hid
  · intro k hk
    rw [hklen] at hk
    obtain ⟨kid, hkget2, hch, hlt⟩ := hKid k hk
    refine ⟨kid, ?_, ?_, ?_⟩
    · rw [hkids]; exact hkget2
    · rw [hchild_eq k]; exact hch
    · omega
  · intro id
    exact plan0_parent_sent_le_qty_step_proof2 b ⟨st, tr⟩ q f ⟨hNP, hNC, hRec, hKid, hLe⟩ id

theorem arch0_inv_parent_step2 (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    arch0_Inv x → arch0_Inv (advance step b x (.parent q f)) := by
  intro h
  obtain ⟨hNP, hNC, hRec, hKid, hLe⟩ := h
  rcases x with ⟨st, tr⟩
  simp only at hNP hNC hRec hKid hLe
  have hkids : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids :=
    aux_parent_kids ⟨st, tr⟩ q f b
  have hnOrd : (advance step b ⟨st, tr⟩ (.parent q f)).tr.nOrders = tr.nOrders + 1 := by
    simp [advance, Truth.observe, Truth.record]
  have hnPar : (advance step b ⟨st, tr⟩ (.parent q f)).st.nParents = st.nParents + 1 := by
    simp [advance, step]
  have hnChi : (advance step b ⟨st, tr⟩ (.parent q f)).st.nChildren = st.nChildren := by
    simp [advance, step]
  have hklen : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids.length = tr.kids.length := by
    rw [hkids]
  have hchild_eq : ∀ k, (advance step b ⟨st, tr⟩ (.parent q f)).st.children k = st.children k := by
    intro k
    simp [advance, step]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hnPar, hnOrd, hNP]
  · rw [hnChi, hklen, hNC]
  · intro id hid
    exact plan0_parent_records_step b ⟨st, tr⟩ q f ⟨hNP, hNC, hRec, hKid, hLe⟩ id hid
  · intro k hk
    rw [hklen] at hk
    obtain ⟨kid, hkget2, hch, hlt⟩ := hKid k hk
    refine ⟨kid, ?_, ?_, ?_⟩
    · rw [hkids]; exact hkget2
    · rw [hchild_eq k]; exact hch
    · omega
  · intro id
    exact plan0_parent_sent_le_qty_step_proof2 b ⟨st, tr⟩ q f ⟨hNP, hNC, hRec, hKid, hLe⟩ id

theorem probe_decide_em (l : List Kid) (n : Nat) (k : Kid) (h : l[n]? = some k) : n < l.length := by
  cases Decidable.em (n < l.length) with
  | inl hl => exact hl
  | inr hl =>
    have hle : l.length ≤ n := Nat.le_of_not_gt hl
    have hnone : l[n]? = (none : Option Kid) := List.getElem?_eq_none hle
    rw [hnone] at h
    cases h

theorem route_observe_eq (tr : Truth) (id liq : Nat) : tr.observe (.route id liq) = tr := rfl

theorem route_record_nOrders (tr : Truth) (out : List Child) : (tr.record out).nOrders = tr.nOrders := rfl

theorem route_record_qty (tr : Truth) (out : List Child) (j : Nat) : (tr.record out).qty j = tr.qty j := rfl

theorem route_record_sent (tr : Truth) (out : List Child) (j : Nat) : (tr.record out).sent j = tr.sent j + sentFor (out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) j := by simp [Truth.sent, Truth.record, sentFor_append]

theorem route_record_exec (tr : Truth) (out : List Child) (j : Nat) : (tr.record out).exec j = tr.exec j := by simp [Truth.exec, Truth.record, execFor_append, execFor_new]

theorem route_record_kids (tr : Truth) (out : List Child) : (tr.record out).kids = tr.kids ++ out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid)) := rfl

theorem route_record_len (tr : Truth) (out : List Child) : (tr.record out).kids.length = tr.kids.length + out.length := by simp [Truth.record]

theorem route_obs_eq2 (tr : Truth) (rid liq : Nat) : tr.observe (.route rid liq) = tr := by simp [Truth.observe]

theorem route_step_unfold2 (b : Build) (st : State) (tr : Truth) (rid liq : Nat) :
    advance step b ⟨st, tr⟩ (.route rid liq) =
    ⟨(routeBySent st rid liq).1, tr.record (routeBySent st rid liq).2⟩ := by
  simp [advance, step, Truth.observe]

theorem route_nocond_out (st : State) (rid liq : Nat)
    (h : ¬ (rid < st.nParents ∧ 0 < min liq ((st.parents rid).qty - (st.parents rid).sent))) :
    routeBySent st rid liq = (st, []) := by
  unfold routeBySent
  simp [h]

theorem route_sent_singleton (id c j : Nat) :
    sentFor ([(⟨id, c, 0⟩ : Kid)]) j = (if id = j then c else 0) := by
  simp [sentFor]

theorem probe_append_get (l : List Kid) (kidNew : Kid) (k : Nat) (hk : k < l.length) :
    (l ++ [kidNew])[k]? = l[k]? := by
  simp [List.getElem?_append, hk]

theorem route_adv_nop_st (st : State) (tr : Truth) (b : Build) (rid liq : Nat)
    (h : ¬ (rid < st.nParents ∧ 0 < min liq ((st.parents rid).qty - (st.parents rid).sent))) :
    (advance step b ⟨st, tr⟩ (.route rid liq)).st = st := by
  simp [advance, step, routeBySent, h]

theorem route_adv_nop_tr (st : State) (tr : Truth) (b : Build) (rid liq : Nat)
    (h : ¬ (rid < st.nParents ∧ 0 < min liq ((st.parents rid).qty - (st.parents rid).sent))) :
    (advance step b ⟨st, tr⟩ (.route rid liq)).tr = tr := by
  simp [advance, step, routeBySent, h, Truth.observe, Truth.record]

theorem route_nop_inv2 (b : Build) (st : State) (tr : Truth) (rid liq : Nat)
    (h : ¬ (rid < st.nParents ∧ 0 < min liq ((st.parents rid).qty - (st.parents rid).sent))) :
    arch0_Inv ⟨st, tr⟩ → arch0_Inv (advance step b ⟨st, tr⟩ (.route rid liq)) := by
  intro hinv
  have hst : (advance step b ⟨st, tr⟩ (.route rid liq)).st = st :=
    route_adv_nop_st st tr b rid liq h
  have htr : (advance step b ⟨st, tr⟩ (.route rid liq)).tr = tr :=
    route_adv_nop_tr st tr b rid liq h
  have hsys : advance step b ⟨st, tr⟩ (.route rid liq) = (⟨st, tr⟩ : Sys) := by
    cases hA : advance step b ⟨st, tr⟩ (.route rid liq) with
    | mk st' tr' =>
      simp [hA] at hst htr
      subst hst; subst htr; rfl
  rw [hsys]
  exact hinv



theorem plan1_route_yes_exec_qty_orders (b : Build) (x : Sys) (rid liq j : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).tr.exec j = x.tr.exec j ∧
    (advance step b x (.route rid liq)).tr.qty j = x.tr.qty j ∧
    (advance step b x (.route rid liq)).tr.nOrders = x.tr.nOrders := by
  cases x with
  | mk st tr =>
    simp only at h ⊢
    have hunfold := route_step_unfold2 b st tr rid liq
    have hn : (advance step b ⟨st, tr⟩ (.route rid liq)).tr.nOrders = tr.nOrders := by
      rw [hunfold]
      exact route_record_nOrders tr (routeBySent st rid liq).2
    have hq : (advance step b ⟨st, tr⟩ (.route rid liq)).tr.qty j = tr.qty j := by
      rw [hunfold]
      exact route_record_qty tr (routeBySent st rid liq).2 j
    have he : (advance step b ⟨st, tr⟩ (.route rid liq)).tr.exec j = tr.exec j := by
      rw [hunfold]
      exact route_record_exec tr (routeBySent st rid liq).2 j
    exact ⟨he, hq, hn⟩


theorem plan1_route_yes_parents (b : Build) (x : Sys) (rid liq : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nParents = x.st.nParents ∧
    ∀ j : Nat,
      (advance step b x (.route rid liq)).st.parents j =
        if j = rid then
          { x.st.parents rid with
            sent := (x.st.parents rid).sent +
              min liq ((x.st.parents rid).qty - (x.st.parents rid).sent) }
        else x.st.parents j := by
  rcases x with ⟨st, tr⟩
  simp only at h
  constructor
  · have hunfold : advance step b ⟨st, tr⟩ (.route rid liq) =
      ⟨(routeBySent st rid liq).1, tr.record (routeBySent st rid liq).2⟩ :=
      route_step_unfold2 b st tr rid liq
    rw [hunfold]
    simp only [routeBySent, h.1, h.2, and_self, ↓reduceIte]
  · intro j
    have hunfold : advance step b ⟨st, tr⟩ (.route rid liq) =
      ⟨(routeBySent st rid liq).1, tr.record (routeBySent st rid liq).2⟩ :=
      route_step_unfold2 b st tr rid liq
    rw [hunfold]
    simp only [routeBySent, h.1, h.2, and_self, ↓reduceIte, upd]








theorem plan1_route_yes_sent (b : Build) (x : Sys) (rid liq j : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).tr.sent j =
      x.tr.sent j +
        (if rid = j then
          min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)
        else 0) := by
  have hunfold : advance step b x (.route rid liq) =
    ⟨(routeBySent x.st rid liq).1, x.tr.record (routeBySent x.st rid liq).2⟩ := by
    cases x with
    | mk st tr => exact route_step_unfold2 b st tr rid liq
  have hRB2 : (routeBySent x.st rid liq).2 = [⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩] := by
    unfold routeBySent
    simp only [h.1, h.2, and_self, ↓reduceIte]
  have hsent : (x.tr.record (routeBySent x.st rid liq).2).sent j =
      x.tr.sent j + sentFor ((routeBySent x.st rid liq).2.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) j :=
    route_record_sent x.tr (routeBySent x.st rid liq).2 j
  rw [hunfold]
  simp only
  rw [hsent, hRB2]
  simp only [List.map_cons, List.map_nil, sentFor_cons, sentFor_nil, Nat.add_zero]

theorem snippet_probe_ok : True := trivial

theorem snippet_ascii_test2 : True := True.intro

theorem snippet_ascii_test3 : True := True.intro

theorem snippet_helper_exec2 (st : State) (tr : Truth) (rid liq j : Nat) : (tr.record (routeBySent st rid liq).2).exec j = tr.exec j := by exact route_record_exec tr (routeBySent st rid liq).2 j

theorem snippet_angle : (⟨0, 1, 0⟩ : Kid).parent = 0 := by rfl

theorem snippet_rcases_ok (x : Sys) : True := by cases x with | mk st tr => exact True.intro

theorem probe_route_parents_c (b : Build) (st : State) (tr : Truth) (rid liq j : Nat)
    (h : rid < st.nParents ∧
      0 < min liq ((st.parents rid).qty - (st.parents rid).sent)) :
    (advance step b ⟨st, tr⟩ (.route rid liq)).st.parents j =
        if j = rid then
          { st.parents rid with
            sent := (st.parents rid).sent +
              min liq ((st.parents rid).qty - (st.parents rid).sent) }
        else st.parents j := by
  have hunfold : advance step b ⟨st, tr⟩ (.route rid liq) =
    ⟨(routeBySent st rid liq).1, tr.record (routeBySent st rid liq).2⟩ :=
    route_step_unfold2 b st tr rid liq
  rw [hunfold]
  simp only [routeBySent, h.1, h.2, and_self, ↓reduceIte, upd]

theorem probe_route_parents_d (b : Build) (st : State) (tr : Truth) (rid liq : Nat)
    (h : rid < st.nParents ∧
      0 < min liq ((st.parents rid).qty - (st.parents rid).sent)) :
    (advance step b ⟨st, tr⟩ (.route rid liq)).st.nParents = st.nParents := by
  have hunfold : advance step b ⟨st, tr⟩ (.route rid liq) =
    ⟨(routeBySent st rid liq).1, tr.record (routeBySent st rid liq).2⟩ :=
    route_step_unfold2 b st tr rid liq
  rw [hunfold]
  simp only [routeBySent, h.1, h.2, and_self, ↓reduceIte]

theorem probe_parents_selfcontained (b : Build) (x : Sys) (rid liq : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nParents = x.st.nParents ∧
    ∀ j : Nat,
      (advance step b x (.route rid liq)).st.parents j =
        if j = rid then
          { x.st.parents rid with
            sent := (x.st.parents rid).sent +
              min liq ((x.st.parents rid).qty - (x.st.parents rid).sent) }
        else x.st.parents j := by
  rcases x with ⟨st, tr⟩
  simp only at h
  constructor
  · have hunfold : advance step b ⟨st, tr⟩ (.route rid liq) =
      ⟨(routeBySent st rid liq).1, tr.record (routeBySent st rid liq).2⟩ :=
      route_step_unfold2 b st tr rid liq
    rw [hunfold]
    simp only [routeBySent, h.1, h.2, and_self, ↓reduceIte]
  · intro j
    have hunfold : advance step b ⟨st, tr⟩ (.route rid liq) =
      ⟨(routeBySent st rid liq).1, tr.record (routeBySent st rid liq).2⟩ :=
      route_step_unfold2 b st tr rid liq
    rw [hunfold]
    simp only [routeBySent, h.1, h.2, and_self, ↓reduceIte, upd]

theorem plan1_route_yes_parents_auxchk (b : Build) (st : State) (tr : Truth) (rid liq : Nat)
    (h : rid < st.nParents ∧
      0 < min liq ((st.parents rid).qty - (st.parents rid).sent)) : True := trivial

theorem probe_children_a (st : State) (rid liq : Nat)
    (h : rid < st.nParents ∧
      0 < min liq ((st.parents rid).qty - (st.parents rid).sent)) :
    (routeBySent st rid liq).1.nChildren = st.nChildren + 1 := by
  unfold routeBySent
  simp only
  simp [h]

theorem probe_children_b (st : State) (rid liq : Nat)
    (h : rid < st.nParents ∧
      0 < min liq ((st.parents rid).qty - (st.parents rid).sent)) :
    (routeBySent st rid liq).1.children st.nChildren =
      (⟨rid, min liq ((st.parents rid).qty - (st.parents rid).sent), 0⟩ : ChildRec) := by
  unfold routeBySent
  simp only
  simp [h, upd]

theorem probe_children_c (st : State) (rid liq : Nat)
    (h : rid < st.nParents ∧
      0 < min liq ((st.parents rid).qty - (st.parents rid).sent))
    (k : Nat) (hk : k ≠ st.nChildren) :
    (routeBySent st rid liq).1.children k = st.children k := by
  unfold routeBySent
  simp only
  simp [h]
  simp [upd, hk]

theorem plan1_route_yes_children_proof2 (b : Build) (x : Sys) (rid liq : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nChildren = x.st.nChildren + 1 ∧
    (advance step b x (.route rid liq)).st.children x.st.nChildren =
      ⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ ∧
    ∀ k : Nat, k ≠ x.st.nChildren →
      (advance step b x (.route rid liq)).st.children k = x.st.children k := by
  rcases x with ⟨st, tr⟩
  simp only at h
  have hunfold : advance step b ⟨st, tr⟩ (.route rid liq) =
    ⟨(routeBySent st rid liq).1, tr.record (routeBySent st rid liq).2⟩ :=
    route_step_unfold2 b st tr rid liq
  have h1 : (advance step b ⟨st, tr⟩ (.route rid liq)).st = (routeBySent st rid liq).1 := by
    rw [hunfold]
  rw [h1]
  exact ⟨probe_children_a st rid liq h, probe_children_b st rid liq h,
    fun k hk => probe_children_c st rid liq h k hk⟩

theorem plan1_route_yes_children (b : Build) (x : Sys) (rid liq : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nChildren = x.st.nChildren + 1 ∧
    (advance step b x (.route rid liq)).st.children x.st.nChildren =
      ⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ ∧
    ∀ k : Nat, k ≠ x.st.nChildren →
      (advance step b x (.route rid liq)).st.children k = x.st.children k :=
  plan1_route_yes_children_proof2 b x rid liq h

theorem dbg2 (st : State) (rid liq : Nat)
    (h : rid < st.nParents ∧ 0 < min liq ((st.parents rid).qty - (st.parents rid).sent)) :
    (routeBySent st rid liq).2 = [⟨rid, min liq ((st.parents rid).qty - (st.parents rid).sent)⟩] := by
  unfold routeBySent
  simp only [h, and_self, ↓reduceIte]

theorem plan1_kids_tmp2 (b : Build) (st : State) (tr : Truth) (rid liq : Nat)
    (h : rid < st.nParents ∧ 0 < min liq ((st.parents rid).qty - (st.parents rid).sent)) :
    (advance step b ⟨st, tr⟩ (.route rid liq)).tr.kids =
      tr.kids ++ [⟨rid, min liq ((st.parents rid).qty - (st.parents rid).sent), 0⟩] := by
  have hunfold := route_step_unfold2 b st tr rid liq
  have hout := dbg2 st rid liq h
  rw [hunfold, hout]
  rfl

theorem helper_append_len (l : List Kid) (a : Kid) : (l ++ [a]).length = l.length + 1 := by
  simp

theorem helper_append_get_eq (l : List Kid) (a : Kid) (k : Nat) (hk : k < l.length) :
    (l ++ [a])[k]? = l[k]? := by
  exact probe_append_get l a k hk

theorem helper_append_get_new (l : List Kid) (a : Kid) :
    (l ++ [a])[l.length]? = some a := by
  simp

theorem plan1_route_yes_kids_get (b : Build) (x : Sys) (rid liq : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (∀ k : Nat, k < x.tr.kids.length →
      (advance step b x (.route rid liq)).tr.kids[k]? = x.tr.kids[k]?) ∧
    (advance step b x (.route rid liq)).tr.kids[x.tr.kids.length]? =
      some (⟨rid,
        min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid) ∧
    (advance step b x (.route rid liq)).tr.kids.length =
      x.tr.kids.length + 1 := by
  cases x with
  | mk st tr =>
    simp only at h ⊢
    have hkids := plan1_kids_tmp2 b st tr rid liq h
    refine ⟨?a, ?b, ?c⟩
    · intro k hk
      rw [hkids]
      exact probe_append_get tr.kids _ k hk
    · rw [hkids]
      simp
    · rw [hkids]
      simp

theorem plan1_route_yes_sent_le_of_inv_proof5 (b : Build) (x : Sys) (rid liq j : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).tr.sent j ≤
      (advance step b x (.route rid liq)).tr.qty j := by
  obtain ⟨hNP, hNC, hPar, hKid, hLe⟩ := hx
  have hSentEq := plan1_route_yes_sent b x rid liq j h
  have hQty := plan1_route_yes_exec_qty_orders b x rid liq j h
  have hQtyEq : (advance step b x (.route rid liq)).tr.qty j = x.tr.qty j := hQty.2.1
  rw [hSentEq, hQtyEq]
  by_cases heq : rid = j
  · subst heq
    rw [if_pos rfl]
    have hridLt : rid < x.tr.nOrders := by omega
    obtain ⟨hq, hs, _hc⟩ := hPar rid hridLt
    have hle0 : x.tr.sent rid ≤ x.tr.qty rid := hLe rid
    have hmem : min liq ((x.st.parents rid).qty - (x.st.parents rid).sent) ≤ (x.st.parents rid).qty - (x.st.parents rid).sent := Nat.min_le_right _ _
    omega
  · rw [if_neg heq, Nat.add_zero]
    exact hLe j

theorem plan1_route_yes_sent_le_of_inv (b : Build) (x : Sys) (rid liq j : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).tr.sent j ≤
      (advance step b x (.route rid liq)).tr.qty j := by
  obtain ⟨hNP, hNC, hPar, hKid, hLe⟩ := hx
  have hSentEq := plan1_route_yes_sent b x rid liq j h
  have hQty := plan1_route_yes_exec_qty_orders b x rid liq j h
  have hQtyEq : (advance step b x (.route rid liq)).tr.qty j = x.tr.qty j := hQty.2.1
  rw [hSentEq, hQtyEq]
  by_cases heq : rid = j
  · subst heq
    rw [if_pos rfl]
    have hridLt : rid < x.tr.nOrders := by omega
    obtain ⟨hq, hs, _hc⟩ := hPar rid hridLt
    have hle0 : x.tr.sent rid ≤ x.tr.qty rid := hLe rid
    have hmem : min liq ((x.st.parents rid).qty - (x.st.parents rid).sent) ≤ (x.st.parents rid).qty - (x.st.parents rid).sent := Nat.min_le_right _ _
    omega
  · rw [if_neg heq, Nat.add_zero]
    exact hLe j

theorem probe_dsimp_test (st : State) (tr : Truth) (h : arch0_Inv (⟨st, tr⟩ : Sys)) :
    st.nParents = tr.nOrders := by
  have h2 := h.1
  dsimp only at h2
  exact h2

theorem probe_struct_upd_qty (p : ParentRec) (v : Nat) :
    ({ p with sent := v } : ParentRec).qty = p.qty := rfl

theorem probe_struct_upd_sent (p : ParentRec) (v : Nat) :
    ({ p with sent := v } : ParentRec).sent = v := rfl

theorem probe_struct_upd_cum (p : ParentRec) (v : Nat) :
    ({ p with sent := v } : ParentRec).cum = p.cum := rfl

theorem ack_adv_eq_test (b : Build) (x : Sys) (k : Nat) :
    advance step b x (.ack k) = x := by
  simp [advance, step, Truth.observe, Truth.record]

theorem ack_inv_test2 (b : Build) (x : Sys) (k : Nat) (h : arch0_Inv x) :
    arch0_Inv (advance step b x (.ack k)) := by
  have heq : advance step b x (.ack k) = x := by
    cases x with
    | mk st tr => simp [advance, step, Truth.observe, Truth.record]
  rw [heq]
  exact h

theorem ack_inv_test3 (b : Build) (x : Sys) (k : Nat) (h : arch0_Inv x) :
    arch0_Inv (advance step b x (.ack k)) := by
  have heq : advance step b x (.ack k) = x := by
    cases x with
    | mk st tr => simp [advance, step, Truth.observe, Truth.record]
  rw [heq]
  exact h
-- check that arch0_inv_ack_step can be done inline

theorem ack_inline_check (b : Build) (x : Sys) (k : Nat) :
    advance step b x (.ack k) = x := by
  cases x with
  | mk st tr => simp [advance, step, Truth.observe, Truth.record]

theorem fill_step_unfold_test2 (b : Build) (st : State) (tr : Truth) (k q : Nat) :
    advance step b ⟨st, tr⟩ (.fill k q) =
    ⟨(step b st (.fill k q)).1, (tr.observe (.fill k q)).record (step b st (.fill k q)).2⟩ := by
  simp [advance]

theorem fill_out_nil (b : Build) (st : State) (k q : Nat) :
    (step b st (.fill k q)).2 = ([] : List Child) := by
  simp [step]
  split
  · rfl
  · rfl

theorem fill_st_nParents3 (b : Build) (st : State) (k q : Nat) :
    (step b st (.fill k q)).1.nParents = st.nParents := by
  simp only [step]
  split
  · rfl
  · rfl

theorem fill_st_nChildren4 (b : Build) (st : State) (k q : Nat) :
    (step b st (.fill k q)).1.nChildren = st.nChildren := by
  simp only [step]
  split
  · rfl
  · rfl

theorem fill_tr_nOrders4 (tr : Truth) (k q : Nat) :
    (tr.observe (.fill k q)).nOrders = tr.nOrders := by
  simp only [Truth.observe]
  split
  · rfl
  · rfl

theorem fill_record_nil_kids (t : Truth) : t.record ([] : List Child) = t := by
  simp [Truth.record]

theorem fill_adv_tr_eq (b : Build) (st : State) (tr : Truth) (k q : Nat) :
    (advance step b ⟨st, tr⟩ (.fill k q)).tr = (tr.observe (.fill k q)).record (step b st (.fill k q)).2 := by
  simp [advance]

theorem fill_adv_st_eq (b : Build) (st : State) (tr : Truth) (k q : Nat) :
    (advance step b ⟨st, tr⟩ (.fill k q)).st = (step b st (.fill k q)).1 := by
  simp [advance]







theorem plan2_fill_adv_qty_sent_of_inv (b : Build) {x : Sys} (h : arch0_Inv x)
    (k q id : Nat) (hid : id < (advance step b x (.fill k q)).tr.nOrders) :
    ((advance step b x (.fill k q)).st.parents id).qty =
        (advance step b x (.fill k q)).tr.qty id ∧
      ((advance step b x (.fill k q)).st.parents id).sent =
        (advance step b x (.fill k q)).tr.sent id := by
  rcases x with ⟨st, tr⟩
  obtain ⟨hNP, hNC, hRec, hKid, hLe⟩ := h
  simp only at hNP hNC hRec hKid hLe
  have hOut : (step b st (.fill k q)).2 = ([] : List Child) := fill_out_nil b st k q
  have hAdvTr : (advance step b ⟨st, tr⟩ (.fill k q)).tr = tr.observe (.fill k q) := by
    have h1 : (advance step b ⟨st, tr⟩ (.fill k q)).tr = (tr.observe (.fill k q)).record (step b st (.fill k q)).2 := by
      simp [advance]
    rw [h1, hOut]
    simp [Truth.record]
  have hAdvSt : (advance step b ⟨st, tr⟩ (.fill k q)).st = (step b st (.fill k q)).1 := by
    simp [advance]
  have hObsN : (tr.observe (.fill k q)).nOrders = tr.nOrders := fill_tr_nOrders4 tr k q
  have hTrQty : (advance step b ⟨st, tr⟩ (.fill k q)).tr.qty id = tr.qty id := by
    rw [hAdvTr]
    simp only [Truth.observe]
    cases hkk : tr.kids[k]? with
    | none => rfl
    | some c => rfl
  have hTrSent : (advance step b ⟨st, tr⟩ (.fill k q)).tr.sent id = tr.sent id := by
    rw [hAdvTr]
    simp only [Truth.observe]
    cases hkk : tr.kids[k]? with
    | none => rfl
    | some c =>
      simp only
      exact sentFor_set_done tr.kids k c _ hkk id
  have hStQty : ((advance step b ⟨st, tr⟩ (.fill k q)).st.parents id).qty = (st.parents id).qty := by
    rw [hAdvSt]
    simp only [step]
    split
    · rename_i hk
      by_cases heq : id = (st.children k).parent
      · subst heq
        simp [upd]
      · simp [upd, heq]
    · rfl
  have hStSent : ((advance step b ⟨st, tr⟩ (.fill k q)).st.parents id).sent = (st.parents id).sent := by
    rw [hAdvSt]
    simp only [step]
    split
    · rename_i hk
      by_cases heq : id = (st.children k).parent
      · subst heq
        simp [upd]
      · simp [upd, heq]
    · rfl
  have hidOld : id < tr.nOrders := by
    have h2 : id < (tr.observe (.fill k q)).nOrders := by rw [← hAdvTr]; exact hid
    rw [hObsN] at h2
    exact h2
  obtain ⟨hq, hs, _⟩ := hRec id hidOld
  rw [hStQty, hStSent, hTrQty, hTrSent]
  exact ⟨hq, hs⟩






theorem plan2_fill_truth_sent (t : Truth) (k q id : Nat) :
    (t.observe (.fill k q)).sent id = t.sent id := by
  simp only [Truth.observe]
  cases h : t.kids[k]? with
  | none => rfl
  | some c =>
    simp
    exact sentFor_set_done t.kids k c _ h id

theorem plan2_fill_truth_exec_some (t : Truth) (k q id : Nat) (kid : Kid)
    (h : t.kids[k]? = some kid) :
    (t.observe (.fill k q)).exec id =
      t.exec id + (if kid.parent = id then min q (kid.qty - kid.done) else 0) := by
  have hobs : t.observe (.fill k q) = { t with kids := t.kids.set k { kid with done := kid.done + min q (kid.qty - kid.done) } } := by
    simp only [Truth.observe, h]
  rw [hobs]
  simp only [Truth.exec]
  exact execFor_set_done t.kids k kid (min q (kid.qty - kid.done)) h id

theorem plan2_fill_child_match_of_inv_aux {x : Sys} (h : arch0_Inv x) {k : Nat}
    (hk : k < x.tr.kids.length) :
    ∃ kid, x.tr.kids[k]? = some kid ∧
      x.st.children k = ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < x.tr.nOrders ∧ k < x.st.nChildren := by
  obtain ⟨hNP, hNC, hPar, hChild, hBound⟩ := h
  obtain ⟨kid, hkSome, hStChild, hParentLt⟩ := hChild k hk
  exact ⟨kid, hkSome, hStChild, hParentLt, by omega⟩

theorem plan2_fill_child_match_of_inv {x : Sys} (h : arch0_Inv x) {k : Nat}
    (hk : k < x.tr.kids.length) :
    ∃ kid, x.tr.kids[k]? = some kid ∧
      x.st.children k = ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < x.tr.nOrders ∧ k < x.st.nChildren := by
  obtain ⟨hNP, hNC, hPar, hChild, hBound⟩ := h
  obtain ⟨kid, hkSome, hStChild, hParentLt⟩ := hChild k hk
  exact ⟨kid, hkSome, hStChild, hParentLt, by omega⟩

theorem plan2_fill_adv_qty_sent_of_inv_test2 (b : Build) {x : Sys} (h : arch0_Inv x)
    (k q id : Nat) (hid : id < (advance step b x (.fill k q)).tr.nOrders) :
    ((advance step b x (.fill k q)).st.parents id).qty =
        (advance step b x (.fill k q)).tr.qty id ∧
      ((advance step b x (.fill k q)).st.parents id).sent =
        (advance step b x (.fill k q)).tr.sent id := by
  rcases x with ⟨st, tr⟩
  obtain ⟨hNP, hNC, hRec, hKid, hLe⟩ := h
  simp only at hNP hNC hRec hKid hLe
  have hOut : (step b st (.fill k q)).2 = ([] : List Child) := fill_out_nil b st k q
  have hAdvTr : (advance step b ⟨st, tr⟩ (.fill k q)).tr = tr.observe (.fill k q) := by
    have h1 : (advance step b ⟨st, tr⟩ (.fill k q)).tr = (tr.observe (.fill k q)).record (step b st (.fill k q)).2 := by
      simp [advance]
    rw [h1, hOut]
    simp [Truth.record]
  have hAdvSt : (advance step b ⟨st, tr⟩ (.fill k q)).st = (step b st (.fill k q)).1 := by
    simp [advance]
  have hObsN : (tr.observe (.fill k q)).nOrders = tr.nOrders := fill_tr_nOrders4 tr k q
  have hTrQty : (advance step b ⟨st, tr⟩ (.fill k q)).tr.qty id = tr.qty id := by
    rw [hAdvTr]
    simp only [Truth.observe]
    cases hkk : tr.kids[k]? with
    | none => rfl
    | some c => rfl
  have hTrSent : (advance step b ⟨st, tr⟩ (.fill k q)).tr.sent id = tr.sent id := by
    rw [hAdvTr]
    exact plan2_fill_truth_sent tr k q id
  have hStQty : ((advance step b ⟨st, tr⟩ (.fill k q)).st.parents id).qty = (st.parents id).qty := by
    rw [hAdvSt]
    simp only [step]
    split
    · rename_i hk
      by_cases heq : id = (st.children k).parent
      · subst heq
        simp [upd]
      · simp [upd, heq]
    · rfl
  have hStSent : ((advance step b ⟨st, tr⟩ (.fill k q)).st.parents id).sent = (st.parents id).sent := by
    rw [hAdvSt]
    simp only [step]
    split
    · rename_i hk
      by_cases heq : id = (st.children k).parent
      · subst heq
        simp [upd]
      · simp [upd, heq]
    · rfl
  have hidOld : id < tr.nOrders := by
    have h2 : id < (tr.observe (.fill k q)).nOrders := by rw [← hAdvTr]; exact hid
    rw [hObsN] at h2
    exact h2
  obtain ⟨hq, hs, _⟩ := hRec id hidOld
  rw [hStQty, hStSent, hTrQty, hTrSent]
  exact ⟨hq, hs⟩

theorem plan2_fill_adv_qty_sent_of_inv_self (b : Build) {x : Sys} (h : arch0_Inv x)
    (k q id : Nat) (hid : id < (advance step b x (.fill k q)).tr.nOrders) :
    ((advance step b x (.fill k q)).st.parents id).qty =
        (advance step b x (.fill k q)).tr.qty id ∧
      ((advance step b x (.fill k q)).st.parents id).sent =
        (advance step b x (.fill k q)).tr.sent id := by
  rcases x with ⟨st, tr⟩
  obtain ⟨hNP, hNC, hRec, hKid, hLe⟩ := h
  simp only at hNP hNC hRec hKid hLe
  have hOut : (step b st (.fill k q)).2 = ([] : List Child) := fill_out_nil b st k q
  have hAdvTr : (advance step b ⟨st, tr⟩ (.fill k q)).tr = tr.observe (.fill k q) := by
    have h1 : (advance step b ⟨st, tr⟩ (.fill k q)).tr = (tr.observe (.fill k q)).record (step b st (.fill k q)).2 := by
      simp [advance]
    rw [h1, hOut]
    simp [Truth.record]
  have hAdvSt : (advance step b ⟨st, tr⟩ (.fill k q)).st = (step b st (.fill k q)).1 := by
    simp [advance]
  have hObsN : (tr.observe (.fill k q)).nOrders = tr.nOrders := fill_tr_nOrders4 tr k q
  have hTrQty : (advance step b ⟨st, tr⟩ (.fill k q)).tr.qty id = tr.qty id := by
    rw [hAdvTr]
    simp only [Truth.observe]
    cases hkk : tr.kids[k]? with
    | none => rfl
    | some c => rfl
  have hTrSent : (advance step b ⟨st, tr⟩ (.fill k q)).tr.sent id = tr.sent id := by
    rw [hAdvTr]
    simp only [Truth.observe]
    cases hkk : tr.kids[k]? with
    | none => rfl
    | some c =>
      simp only
      exact sentFor_set_done tr.kids k c _ hkk id
  have hStQty : ((advance step b ⟨st, tr⟩ (.fill k q)).st.parents id).qty = (st.parents id).qty := by
    rw [hAdvSt]
    simp only [step]
    split
    · rename_i hk
      by_cases heq : id = (st.children k).parent
      · subst heq
        simp [upd]
      · simp [upd, heq]
    · rfl
  have hStSent : ((advance step b ⟨st, tr⟩ (.fill k q)).st.parents id).sent = (st.parents id).sent := by
    rw [hAdvSt]
    simp only [step]
    split
    · rename_i hk
      by_cases heq : id = (st.children k).parent
      · subst heq
        simp [upd]
      · simp [upd, heq]
    · rfl
  have hidOld : id < tr.nOrders := by
    have h2 : id < (tr.observe (.fill k q)).nOrders := by rw [← hAdvTr]; exact hid
    rw [hObsN] at h2
    exact h2
  obtain ⟨hq, hs, _⟩ := hRec id hidOld
  rw [hStQty, hStSent, hTrQty, hTrSent]
  exact ⟨hq, hs⟩

theorem probe_fill_st_simp (st : State) (k q : Nat) (hk : k < st.nChildren) :
    (step Build.rlp st (.fill k q)).1.parents = upd st.parents (st.children k).parent
      ({ st.parents (st.children k).parent with cum :=
        (st.parents (st.children k).parent).cum + min q ((st.children k).qty - (st.children k).done) } : ParentRec) := by
  simp [step, if_pos hk]

theorem probe_fill_parents_cum (st : State) (k q id : Nat) (hk : k < st.nChildren) :
    ((step Build.rlp st (.fill k q)).1.parents id).cum =
      if id = (st.children k).parent then
        (st.parents (st.children k).parent).cum + min q ((st.children k).qty - (st.children k).done)
      else (st.parents id).cum := by
  simp only [step, if_pos hk]
  simp only [upd]
  split
  · rfl
  · rfl

theorem plan2_fill_adv_cum_of_inv_aux1 (b : Build) (st : State) (k q id : Nat) (hk : k < st.nChildren) :
    ((step b st (.fill k q)).1.parents id).cum =
      (if id = (st.children k).parent then
        (st.parents (st.children k).parent).cum + min q ((st.children k).qty - (st.children k).done)
      else (st.parents id).cum) := by
  simp only [step, if_pos hk]
  simp only [upd]
  split <;> rfl

theorem plan2_fill_adv_cum_of_inv_testB (b : Build) {x : Sys} (h : arch0_Inv x)
    (k q id : Nat) (hid : id < (advance step b x (.fill k q)).tr.nOrders) :
    ((advance step b x (.fill k q)).st.parents id).cum =
      (advance step b x (.fill k q)).tr.exec id := by
  rcases x with ⟨st, tr⟩
  obtain ⟨hNP, hNC, hRec, hKid, hLe⟩ := h
  simp only at hNP hNC hRec hKid hLe
  have hOut : (step b st (.fill k q)).2 = ([] : List Child) := fill_out_nil b st k q
  have hAdvTr : (advance step b ⟨st, tr⟩ (.fill k q)).tr = tr.observe (.fill k q) := by
    have h1 : (advance step b ⟨st, tr⟩ (.fill k q)).tr = (tr.observe (.fill k q)).record (step b st (.fill k q)).2 := by
      simp [advance]
    rw [h1, hOut]
    simp [Truth.record]
  have hAdvSt : (advance step b ⟨st, tr⟩ (.fill k q)).st = (step b st (.fill k q)).1 := by
    simp [advance]
  have hObsN : (tr.observe (.fill k q)).nOrders = tr.nOrders := fill_tr_nOrders4 tr k q
  have hidOld : id < tr.nOrders := by
    have h2 : id < (tr.observe (.fill k q)).nOrders := by rw [← hAdvTr]; exact hid
    rw [hObsN] at h2
    exact h2
  have hBase : (st.parents id).cum = tr.exec id := (hRec id hidOld).2.2
  by_cases hkSt : k < st.nChildren
  · have hkLen : k < tr.kids.length := by omega
    obtain ⟨kid, hSome, hStChild, hPlt, _hkSt2⟩ := plan2_fill_child_match_of_inv (x := ⟨st, tr⟩) ⟨hNP, hNC, hRec, hKid, hLe⟩ hkLen
    have hSome2 : tr.kids[k]? = some kid := hSome
    have hTrExec : (tr.observe (.fill k q)).exec id =
        tr.exec id + (if kid.parent = id then min q (kid.qty - kid.done) else 0) :=
      plan2_fill_truth_exec_some tr k q id kid hSome2
    have hSt : ((step b st (.fill k q)).1.parents id).cum =
        (if id = (st.children k).parent then
          (st.parents (st.children k).parent).cum + min q ((st.children k).qty - (st.children k).done)
        else (st.parents id).cum) :=
      plan2_fill_adv_cum_of_inv_aux1 b st k q id hkSt
    have hCh : st.children k = (⟨kid.parent, kid.qty, kid.done⟩ : ChildRec) := hStChild
    rw [hCh] at hSt
    simp only at hSt
    have hBk : (st.parents kid.parent).cum = tr.exec kid.parent := (hRec kid.parent hPlt).2.2
    by_cases heq : id = kid.parent
    · subst heq
      have hSt2 : ((step b st (.fill k q)).1.parents kid.parent).cum =
          tr.exec kid.parent + min q (kid.qty - kid.done) := by
        rw [hSt]
        simp [hBk]
      have hTr2 : (tr.observe (.fill k q)).exec kid.parent =
          tr.exec kid.parent + min q (kid.qty - kid.done) := by
        rw [hTrExec]
        simp
      rw [hAdvSt, hAdvTr, hSt2, hTr2]
    · have hne : kid.parent ≠ id := fun hcontra => heq (Eq.symm hcontra)
      have hSt2 : ((step b st (.fill k q)).1.parents id).cum = (st.parents id).cum := by
        rw [hSt]; simp [heq]
      have hTr2 : (tr.observe (.fill k q)).exec id = tr.exec id := by
        rw [hTrExec]; simp [hne]
      rw [hAdvSt, hAdvTr, hSt2, hTr2, hBase]
  · have hLenLe : tr.kids.length ≤ k := by omega
    have hNone : tr.kids[k]? = (none : Option Kid) := List.getElem?_eq_none hLenLe
    have hObs : tr.observe (.fill k q) = tr := by simp [Truth.observe, hNone]
    have hStepEq : (step b st (.fill k q)).1 = st := by simp [step, if_neg hkSt]
    rw [hAdvSt, hStepEq, hAdvTr, hObs]
    exact hBase

theorem plan2_fill_adv_cum_of_inv2 (b : Build) {x : Sys} (h : arch0_Inv x)
    (k q id : Nat) (hid : id < (advance step b x (.fill k q)).tr.nOrders) :
    ((advance step b x (.fill k q)).st.parents id).cum =
      (advance step b x (.fill k q)).tr.exec id :=
  plan2_fill_adv_cum_of_inv_testB b (x := x) h k q id hid

theorem plan2_fill_adv_cum_of_inv (b : Build) {x : Sys} (h : arch0_Inv x)
    (k q id : Nat) (hid : id < (advance step b x (.fill k q)).tr.nOrders) :
    ((advance step b x (.fill k q)).st.parents id).cum =
      (advance step b x (.fill k q)).tr.exec id := by
  rcases x with ⟨st, tr⟩
  obtain ⟨hNP, hNC, hRec, hKid, hLe⟩ := h
  simp only at hNP hNC hRec hKid hLe
  have hOut : (step b st (.fill k q)).2 = ([] : List Child) := fill_out_nil b st k q
  have hAdvTr : (advance step b ⟨st, tr⟩ (.fill k q)).tr = tr.observe (.fill k q) := by
    have h1 : (advance step b ⟨st, tr⟩ (.fill k q)).tr = (tr.observe (.fill k q)).record (step b st (.fill k q)).2 := by
      simp [advance]
    rw [h1, hOut]
    simp [Truth.record]
  have hAdvSt : (advance step b ⟨st, tr⟩ (.fill k q)).st = (step b st (.fill k q)).1 := by
    simp [advance]
  have hObsN : (tr.observe (.fill k q)).nOrders = tr.nOrders := fill_tr_nOrders4 tr k q
  have hidOld : id < tr.nOrders := by
    have h2 : id < (tr.observe (.fill k q)).nOrders := by rw [← hAdvTr]; exact hid
    rw [hObsN] at h2
    exact h2
  have hBase : (st.parents id).cum = tr.exec id := (hRec id hidOld).2.2
  by_cases hkSt : k < st.nChildren
  · have hkLen : k < tr.kids.length := by omega
    obtain ⟨kid, hSome, hStChild, hPlt, _hkSt2⟩ := plan2_fill_child_match_of_inv (x := ⟨st, tr⟩) ⟨hNP, hNC, hRec, hKid, hLe⟩ hkLen
    have hSome2 : tr.kids[k]? = some kid := hSome
    have hTrExec : (tr.observe (.fill k q)).exec id =
        tr.exec id + (if kid.parent = id then min q (kid.qty - kid.done) else 0) :=
      plan2_fill_truth_exec_some tr k q id kid hSome2
    have hSt : ((step b st (.fill k q)).1.parents id).cum =
        (if id = (st.children k).parent then
          (st.parents (st.children k).parent).cum + min q ((st.children k).qty - (st.children k).done)
        else (st.parents id).cum) :=
      plan2_fill_adv_cum_of_inv_aux1 b st k q id hkSt
    have hCh : st.children k = (⟨kid.parent, kid.qty, kid.done⟩ : ChildRec) := hStChild
    rw [hCh] at hSt
    simp only at hSt
    have hBk : (st.parents kid.parent).cum = tr.exec kid.parent := (hRec kid.parent hPlt).2.2
    by_cases heq : id = kid.parent
    · subst heq
      have hSt2 : ((step b st (.fill k q)).1.parents kid.parent).cum =
          tr.exec kid.parent + min q (kid.qty - kid.done) := by
        rw [hSt]
        simp [hBk]
      have hTr2 : (tr.observe (.fill k q)).exec kid.parent =
          tr.exec kid.parent + min q (kid.qty - kid.done) := by
        rw [hTrExec]
        simp
      rw [hAdvSt, hAdvTr, hSt2, hTr2]
    · have hne : kid.parent ≠ id := fun hcontra => heq (Eq.symm hcontra)
      have hSt2 : ((step b st (.fill k q)).1.parents id).cum = (st.parents id).cum := by
        rw [hSt]; simp [heq]
      have hTr2 : (tr.observe (.fill k q)).exec id = tr.exec id := by
        rw [hTrExec]; simp [hne]
      rw [hAdvSt, hAdvTr, hSt2, hTr2, hBase]
  · have hLenLe : tr.kids.length ≤ k := by omega
    have hNone : tr.kids[k]? = (none : Option Kid) := List.getElem?_eq_none hLenLe
    have hObs : tr.observe (.fill k q) = tr := by simp [Truth.observe, hNone]
    have hStepEq : (step b st (.fill k q)).1 = st := by simp [step, if_neg hkSt]
    rw [hAdvSt, hStepEq, hAdvTr, hObs]
    exact hBase

theorem probe_destruct_test {x : Sys} (h : arch0_Inv x) :
    x.st.nParents = x.tr.nOrders := by
  obtain ⟨hNP, hNC, hPar, hChild, hLe⟩ := h
  exact hNP

theorem probe_check_set_lemmas : True := by
  trivial
#check @List.getElem?_set
#check @List.getElem_set

theorem probe_set_get_self (l : List Kid) (k : Nat) (c : Kid) (hk : k < l.length) :
    (l.set k c)[k]? = some c := by
  simp [hk]

theorem probe_set_get2 (l : List Kid) (k : Nat) (c : Kid) (k' : Nat) (hk : k < l.length) (heq : k' = k) :
    (l.set k c)[k']? = some c := by
  subst heq
  simp [hk]

theorem probe_upd_child2 (st : State) (k q : Nat) (hk : k < st.nChildren) (k' : Nat) :
    (step Build.rlp st (.fill k q)).1.children k' =
      upd st.children k ({(st.children k) with done := (st.children k).done + min q ((st.children k).qty - (st.children k).done)}) k' := by
  simp only [step, if_pos hk]

theorem probe_fill_kids_eq (b : Build) (st : State) (tr : Truth) (k q : Nat) :
    (advance step b ⟨st, tr⟩ (.fill k q)).tr.kids = (tr.observe (.fill k q)).kids := by
  have hOut : (step b st (.fill k q)).2 = ([] : List Child) := fill_out_nil b st k q
  have h1 : (advance step b ⟨st, tr⟩ (.fill k q)).tr = (tr.observe (.fill k q)).record (step b st (.fill k q)).2 := by
    simp [advance]
  rw [h1, hOut]
  simp [Truth.record]

theorem probe_fill_nOrders_eq (b : Build) (st : State) (tr : Truth) (k q : Nat) :
    (advance step b ⟨st, tr⟩ (.fill k q)).tr.nOrders = tr.nOrders := by
  have h := probe_fill_kids_eq b st tr k q
  have hN : (tr.observe (.fill k q)).nOrders = tr.nOrders := fill_tr_nOrders4 tr k q
  have hOut : (step b st (.fill k q)).2 = ([] : List Child) := fill_out_nil b st k q
  have h1 : (advance step b ⟨st, tr⟩ (.fill k q)).tr = (tr.observe (.fill k q)).record (step b st (.fill k q)).2 := by
    simp [advance]
  rw [h1, hOut] at *
  simp [Truth.record, hN]

theorem probe_check_getset : True := by trivial
#check @List.getElem?_set
#check @List.getElem_set
#check @List.length_set

theorem probe_fill_inv_shape (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x) :
    (advance step b x (.fill k q)).st.nParents = x.st.nParents := by
  cases x with
  | mk st tr =>
    have h1 : (step b st (.fill k q)).1.nParents = st.nParents := fill_st_nParents3 b st k q
    have h2 : (advance step b ⟨st, tr⟩ (.fill k q)).st = (step b st (.fill k q)).1 := fill_adv_st_eq b st tr k q
    rw [h2, h1]

theorem probe_fill_adv_nOrders (b : Build) (st : State) (tr : Truth) (k q : Nat) :
    (advance step b ⟨st, tr⟩ (.fill k q)).tr.nOrders = tr.nOrders := by
  have htr : (advance step b ⟨st, tr⟩ (.fill k q)).tr = tr.observe (.fill k q) := by
    have h1 := fill_adv_tr_eq b st tr k q
    have h2 := fill_out_nil b st k q
    have h3 : (tr.observe (.fill k q)).record ([] : List Child) = tr.observe (.fill k q) := fill_record_nil_kids _
    rw [h2, h3] at h1
    exact h1
  rw [htr]
  exact fill_tr_nOrders4 tr k q

theorem probe_len_set_check (l : List Kid) (k : Nat) (c : Kid) :
    (l.set k c).length = l.length := by
  simp

theorem fill_qty_pres (tr : Truth) (k q : Nat) (j : Nat) :
    (tr.observe (.fill k q)).qty j = tr.qty j := by
  simp only [Truth.observe]
  split
  · rfl
  · rfl

theorem fill_qty_pres2 (b : Build) (st : State) (tr : Truth) (k q j : Nat) :
    (advance step b ⟨st, tr⟩ (.fill k q)).tr.qty j = tr.qty j := by
  have hOut : (step b st (.fill k q)).2 = ([] : List Child) := fill_out_nil b st k q
  have h1 : (advance step b ⟨st, tr⟩ (.fill k q)).tr = (tr.observe (.fill k q)).record (step b st (.fill k q)).2 := by
    simp [advance]
  rw [h1, hOut]
  simp [Truth.record, fill_qty_pres]

theorem probe_route_goal_shape (x : Sys) (id liq : Nat) :
    (routeBySent x.st id liq).2 = expectedRoute x.tr id liq →
    (step Build.rlp x.st (.route id liq)).2 = expectedRoute x.tr id liq := by
  intro h
  simp [step, h]

theorem arch0_route_output_of_inv (b : Build) (x : Sys) (id liq : Nat)
    (h : arch0_Inv x) :
    (step b x.st (.route id liq)).2 = expectedRoute x.tr id liq := by
  have hNP : x.st.nParents = x.tr.nOrders := arch0_nParents_eq_of_inv h
  have hstep : (step b x.st (.route id liq)).2 = (routeBySent x.st id liq).2 := by
    simp [step]
  rw [hstep]
  unfold routeBySent expectedRoute
  simp only
  by_cases hid : id < x.tr.nOrders
  · have hqty : (x.st.parents id).qty = x.tr.qty id :=
      arch0_parent_qty_of_inv h hid
    have hsent : (x.st.parents id).sent = x.tr.sent id :=
      arch0_parent_sent_of_inv h hid
    have hNPid : id < x.st.nParents := by omega
    rw [hqty, hsent]
    by_cases hpos : 0 < min liq (x.tr.qty id - x.tr.sent id)
    · simp [hNPid, hpos, hid]
    · simp [hNPid, hpos, hid]
  · have hNPid : ¬ id < x.st.nParents := by omega
    simp [hid, hNPid]

theorem arch0_nParents_eq_of_invX {x : Sys} (h : arch0_Inv x) :
    x.st.nParents = x.tr.nOrders := h.1

theorem arch0_parent_cum_of_inv {x : Sys} (h : arch0_Inv x)
    {id : Nat} (hid : id < x.tr.nOrders) :
    (x.st.parents id).cum = x.tr.exec id :=
  (h.2.2.1 id hid).2.2

theorem arch0_sent_le_qty_of_invX {x : Sys} (h : arch0_Inv x) (id : Nat) :
    x.tr.sent id ≤ x.tr.qty id :=
  h.2.2.2.2 id

theorem arch0_sent_le_qty_of_inv {x : Sys} (h : arch0_Inv x) (id : Nat) :
    x.tr.sent id ≤ x.tr.qty id := h.2.2.2.2 id

theorem probe_outA (s : State) (pid liq : Nat) (c : Child)
    (h : c ∈ (routeBySent s pid liq).2) :
    pid < s.nParents ∧ 0 < min liq ((s.parents pid).qty - (s.parents pid).sent) ∧
    c = ⟨pid, min liq ((s.parents pid).qty - (s.parents pid).sent)⟩ := by
  by_cases hcond : pid < s.nParents ∧ 0 < min liq ((s.parents pid).qty - (s.parents pid).sent)
  · have hout := dbg2 s pid liq hcond
    rw [hout] at h
    simp at h
    exact ⟨hcond.1, hcond.2, h⟩
  · have hRB := route_nocond_out s pid liq hcond
    have h2 : (routeBySent s pid liq).2 = ([] : List Child) := by rw [hRB]
    rw [h2] at h
    simp at h

theorem arch0_output_cases (b : Build) (s : State) (e : Event) (c : Child) :
    c ∈ (step b s e).2 →
    ∃ pid liq,
      e = .route pid liq ∧
      c = ⟨pid, min liq ((s.parents pid).qty - (s.parents pid).sent)⟩ ∧
      pid < s.nParents ∧
      0 < min liq ((s.parents pid).qty - (s.parents pid).sent) := by
  cases e with
  | parent q f =>
    simp [step]
  | route pid liq =>
    intro hc
    have hstep : (step b s (.route pid liq)).2 = (routeBySent s pid liq).2 := by simp [step]
    rw [hstep] at hc
    obtain ⟨hlt, hpos, heq⟩ := probe_outA s pid liq c hc
    exact ⟨pid, liq, rfl, heq, hlt, hpos⟩
  | ack k =>
    simp [step]
  | fill k q =>
    intro hc
    have hnil := fill_out_nil b s k q
    rw [hnil] at hc
    simp at hc













theorem plan3_parent_old_records_proof2 (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) (hid : id < x.tr.nOrders) :
    ((advance step b x (.parent q f)).st.parents id).qty =
        (advance step b x (.parent q f)).tr.qty id ∧
    ((advance step b x (.parent q f)).st.parents id).sent =
        (advance step b x (.parent q f)).tr.sent id ∧
    ((advance step b x (.parent q f)).st.parents id).cum =
        (advance step b x (.parent q f)).tr.exec id := by
  have heq : (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 :=
    aux_parent_nOrders x q f b
  have hlt : id < (advance step b x (.parent q f)).tr.nOrders := by omega
  exact plan0_parent_records_step b x q f h id hlt


theorem plan3_parent_new_record (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) :
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).qty =
        (advance step b x (.parent q f)).tr.qty x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).sent =
        (advance step b x (.parent q f)).tr.sent x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).cum =
        (advance step b x (.parent q f)).tr.exec x.tr.nOrders := by
  rcases x with ⟨st, tr⟩
  simp only at h ⊢
  have hSt : (advance step b ⟨st, tr⟩ (.parent q f)).st.parents tr.nOrders = (⟨q, f, 0, 0⟩ : ParentRec) := by
    have := plan0_parent_records_step_aux_test b ⟨st, tr⟩ q f ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    simpa using this
  have hQty : (advance step b ⟨st, tr⟩ (.parent q f)).tr.qty tr.nOrders = q := by
    have h1 := plan0_probe_qty b st tr q f tr.nOrders
    rw [h1, aux_upd_eq2]
  have hkids : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids :=
    aux_parent_kids ⟨st, tr⟩ q f b
  have hSentAdv : (advance step b ⟨st, tr⟩ (.parent q f)).tr.sent tr.nOrders = tr.sent tr.nOrders := by
    have := probe_sent_rw b st tr q f tr.nOrders hkids
    exact this
  have hExecAdv : (advance step b ⟨st, tr⟩ (.parent q f)).tr.exec tr.nOrders = tr.exec tr.nOrders := by
    unfold Truth.exec
    rw [hkids]
  have h0 := plan0_sent_exec_new_parent_of_inv (x := ⟨st, tr⟩) ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  rw [hSt, hQty, hSentAdv, hExecAdv, h0.1, h0.2]
  simp


theorem plan3_parent_children_self2 (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (k : Nat)
    (hk : k < x.tr.kids.length) :
    ∃ kid, x.tr.kids[k]? = some kid ∧
      x.st.children k =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < x.tr.nOrders := h.2.2.2.1 k hk


theorem plan3_parent_sent_le_qty (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id ≤
      (advance step b x (.parent q f)).tr.qty id := by
  have hsent := (plan0_parent_sent_exec_eq b x q f id).1
  have hle : x.tr.sent id ≤ x.tr.qty id := h.2.2.2.2 id
  cases x with
  | mk st tr =>
    simp only at hsent hle ⊢
    have hqty : (advance step b ⟨st, tr⟩ (.parent q f)).tr.qty id = upd tr.qty tr.nOrders q id :=
      plan0_probe_qty b st tr q f id
    rw [hsent]
    by_cases heq : id = tr.nOrders
    · subst heq
      have h0 : tr.sent tr.nOrders = 0 := (plan0_sent_exec_new_parent_of_inv h).1
      simp only [h0] at hle ⊢
      rw [hqty]
      simp [upd]
    · have hqy : upd tr.qty tr.nOrders q id = tr.qty id := aux_upd_ne2 tr.qty tr.nOrders id q heq
      rw [hqty, hqy]
      exact hle


theorem plan3_parent_frame (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    (advance step b x (.parent q f)).st.nParents = x.st.nParents + 1 ∧
    (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 ∧
    (advance step b x (.parent q f)).st.nChildren = x.st.nChildren ∧
    (advance step b x (.parent q f)).tr.kids = x.tr.kids := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [advance, step, Truth.observe, Truth.record]

theorem plan3_parent_old_records_proof (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) (hid : id < x.tr.nOrders) :
    ((advance step b x (.parent q f)).st.parents id).qty =
        (advance step b x (.parent q f)).tr.qty id ∧
    ((advance step b x (.parent q f)).st.parents id).sent =
        (advance step b x (.parent q f)).tr.sent id ∧
    ((advance step b x (.parent q f)).st.parents id).cum =
        (advance step b x (.parent q f)).tr.exec id := by
  have hframe := plan3_parent_frame b x q f
  have hlt : id < (advance step b x (.parent q f)).tr.nOrders := by
    rw [hframe.2.1]; omega
  exact plan0_parent_records_step b x q f h id hlt

theorem plan3_old_check2 (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) (hid : id < x.tr.nOrders) :
    ((advance step b x (.parent q f)).st.parents id).qty =
        (advance step b x (.parent q f)).tr.qty id ∧
    ((advance step b x (.parent q f)).st.parents id).sent =
        (advance step b x (.parent q f)).tr.sent id ∧
    ((advance step b x (.parent q f)).st.parents id).cum =
        (advance step b x (.parent q f)).tr.exec id := by
  have hlt : id < (advance step b x (.parent q f)).tr.nOrders := by
    have heq := aux_parent_nOrders x q f b
    omega
  exact plan0_parent_records_step b x q f h id hlt

theorem plan3_old_check3 : True := trivial

theorem plan3_parent_old_records (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) (hid : id < x.tr.nOrders) :
    ((advance step b x (.parent q f)).st.parents id).qty =
        (advance step b x (.parent q f)).tr.qty id ∧
    ((advance step b x (.parent q f)).st.parents id).sent =
        (advance step b x (.parent q f)).tr.sent id ∧
    ((advance step b x (.parent q f)).st.parents id).cum =
        (advance step b x (.parent q f)).tr.exec id := by
  have heq : (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 :=
    aux_parent_nOrders x q f b
  have hlt : id < (advance step b x (.parent q f)).tr.nOrders := by omega
  exact plan0_parent_records_step b x q f h id hlt

theorem plan3_parent_new_record_aux_tmp : True := trivial


theorem plan3_parent_new_record_proof_tmp (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) :
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).qty =
        (advance step b x (.parent q f)).tr.qty x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).sent =
        (advance step b x (.parent q f)).tr.sent x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).cum =
        (advance step b x (.parent q f)).tr.exec x.tr.nOrders := by
  rcases x with ⟨st, tr⟩
  simp only at h ⊢
  have hSt : (advance step b ⟨st, tr⟩ (.parent q f)).st.parents tr.nOrders = (⟨q, f, 0, 0⟩ : ParentRec) := by
    have := plan0_parent_records_step_aux_test b ⟨st, tr⟩ q f ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    simpa using this
  have hQty : (advance step b ⟨st, tr⟩ (.parent q f)).tr.qty tr.nOrders = q := by
    have h1 := plan0_probe_qty b st tr q f tr.nOrders
    rw [h1, aux_upd_eq2]
  have hkids : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids :=
    aux_parent_kids ⟨st, tr⟩ q f b
  have hSentAdv : (advance step b ⟨st, tr⟩ (.parent q f)).tr.sent tr.nOrders = tr.sent tr.nOrders := by
    have := probe_sent_rw b st tr q f tr.nOrders hkids
    exact this
  have hExecAdv : (advance step b ⟨st, tr⟩ (.parent q f)).tr.exec tr.nOrders = tr.exec tr.nOrders := by
    unfold Truth.exec
    rw [hkids]
  have h0 := plan0_sent_exec_new_parent_of_inv (x := ⟨st, tr⟩) ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  rw [hSt, hQty, hSentAdv, hExecAdv, h0.1, h0.2]
  simp

theorem plan3_parent_new_record2 (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) :
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).qty =
        (advance step b x (.parent q f)).tr.qty x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).sent =
        (advance step b x (.parent q f)).tr.sent x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).cum =
        (advance step b x (.parent q f)).tr.exec x.tr.nOrders := by
  rcases x with ⟨st, tr⟩
  simp only at h ⊢
  have hSt : (advance step b ⟨st, tr⟩ (.parent q f)).st.parents tr.nOrders = (⟨q, f, 0, 0⟩ : ParentRec) := by
    have := plan0_parent_records_step_aux_test b ⟨st, tr⟩ q f ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    simpa using this
  have hQty : (advance step b ⟨st, tr⟩ (.parent q f)).tr.qty tr.nOrders = q := by
    have h1 := plan0_probe_qty b st tr q f tr.nOrders
    rw [h1, aux_upd_eq2]
  have hkids : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids :=
    aux_parent_kids ⟨st, tr⟩ q f b
  have hSentAdv : (advance step b ⟨st, tr⟩ (.parent q f)).tr.sent tr.nOrders = tr.sent tr.nOrders := by
    have := probe_sent_rw b st tr q f tr.nOrders hkids
    exact this
  have hExecAdv : (advance step b ⟨st, tr⟩ (.parent q f)).tr.exec tr.nOrders = tr.exec tr.nOrders := by
    unfold Truth.exec
    rw [hkids]
  have h0 := plan0_sent_exec_new_parent_of_inv (x := ⟨st, tr⟩) ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  rw [hSt, hQty, hSentAdv, hExecAdv, h0.1, h0.2]
  simp

theorem plan3_parent_children_proof (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (k : Nat)
    (hk : k < (advance step b x (.parent q f)).tr.kids.length) :
    ∃ kid, (advance step b x (.parent q f)).tr.kids[k]? = some kid ∧
      (advance step b x (.parent q f)).st.children k =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.parent q f)).tr.nOrders := by
  have hframe := plan3_parent_frame b x q f
  obtain ⟨hnP, hnO, hnC, hkids⟩ := hframe
  have hk_lt : k < x.tr.kids.length := by rw [hkids] at hk; exact hk
  obtain ⟨kid, hget, hchild, hplt⟩ := h.2.2.2.1 k hk_lt
  refine ⟨kid, ?_, ?_, ?_⟩
  · rw [hkids]; exact hget
  · have hch : (advance step b x (.parent q f)).st.children k = x.st.children k := by
      cases x with
      | mk st tr => rfl
    rw [hch]; exact hchild
  · rw [hnO]; omega

theorem plan3_parent_children_check2 (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (k : Nat)
    (hk : k < (advance step b x (.parent q f)).tr.kids.length) :
    ∃ kid, (advance step b x (.parent q f)).tr.kids[k]? = some kid ∧
      (advance step b x (.parent q f)).st.children k =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.parent q f)).tr.nOrders := by
  have hkids : (advance step b x (.parent q f)).tr.kids = x.tr.kids :=
    aux_parent_kids x q f b
  have hnO : (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 :=
    aux_parent_nOrders x q f b
  have hk_lt : k < x.tr.kids.length := by rw [hkids] at hk; exact hk
  obtain ⟨kid, hget, hchild, hplt⟩ := h.2.2.2.1 k hk_lt
  refine ⟨kid, ?_, ?_, ?_⟩
  · rw [hkids]; exact hget
  · have hch : (advance step b x (.parent q f)).st.children k = x.st.children k := by
      cases x with
      | mk st tr => rfl
    rw [hch]; exact hchild
  · rw [hnO]; omega

theorem plan3_parent_children (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (k : Nat)
    (hk : k < (advance step b x (.parent q f)).tr.kids.length) :
    ∃ kid, (advance step b x (.parent q f)).tr.kids[k]? = some kid ∧
      (advance step b x (.parent q f)).st.children k =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.parent q f)).tr.nOrders := by
  have hkids : (advance step b x (.parent q f)).tr.kids = x.tr.kids :=
    aux_parent_kids x q f b
  have hnO : (advance step b x (.parent q f)).tr.nOrders = x.tr.nOrders + 1 :=
    aux_parent_nOrders x q f b
  have hk_lt : k < x.tr.kids.length := by rw [hkids] at hk; exact hk
  obtain ⟨kid, hget, hchild, hplt⟩ := h.2.2.2.1 k hk_lt
  refine ⟨kid, ?_, ?_, ?_⟩
  · rw [hkids]; exact hget
  · have hch : (advance step b x (.parent q f)).st.children k = x.st.children k := by
      cases x with
      | mk st tr => rfl
    rw [hch]; exact hchild
  · rw [hnO]; omega

theorem plan3_parent_sent_le_qty_try (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id ≤
      (advance step b x (.parent q f)).tr.qty id := by
  have hsent := (plan0_parent_sent_exec_eq b x q f id).1
  have hle : x.tr.sent id ≤ x.tr.qty id := h.2.2.2.2 id
  cases x with
  | mk st tr =>
    simp only at hsent hle ⊢
    have hqty : (advance step b ⟨st, tr⟩ (.parent q f)).tr.qty id = upd tr.qty tr.nOrders q id :=
      plan0_probe_qty b st tr q f id
    rw [hsent]
    by_cases heq : id = tr.nOrders
    · subst heq
      have h0 : tr.sent tr.nOrders = 0 := (plan0_sent_exec_new_parent_of_inv h).1
      simp only [h0] at hle ⊢
      rw [hqty]
      simp [upd]
    · have hqy : upd tr.qty tr.nOrders q id = tr.qty id := aux_upd_ne2 tr.qty tr.nOrders id q heq
      rw [hqty, hqy]
      exact hle

theorem arch0_inv_parent_step_dup (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) : arch0_Inv (advance step b x (.parent q f)) :=
  arch0_inv_parent_step_proof b x q f h

theorem tmp_parent_children_ok (b : Build) (st : State) (tr : Truth) (q : Nat) (f : Bool)
    (hKidInv : ∀ k, k < tr.kids.length → ∃ kid, tr.kids[k]? = some kid ∧
      st.children k = ({ parent := kid.parent, qty := kid.qty, done := kid.done } : ChildRec) ∧ kid.parent < tr.nOrders)
    (k : Nat)
    (hk : k < (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids.length) :
    ∃ kid, (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids[k]? = some kid ∧
      (advance step b ⟨st, tr⟩ (.parent q f)).st.children k =
        ({ parent := kid.parent, qty := kid.qty, done := kid.done } : ChildRec) ∧
      kid.parent < (advance step b ⟨st, tr⟩ (.parent q f)).tr.nOrders := by
  have hkids : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids := by
    simp [advance, step, Truth.observe, Truth.record]
  have hOrd : (advance step b ⟨st, tr⟩ (.parent q f)).tr.nOrders = tr.nOrders + 1 := by
    simp [advance, step, Truth.observe, Truth.record]
  have hLen : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids.length = tr.kids.length := by
    rw [hkids]
  have hk2 : k < tr.kids.length := by rw [← hLen]; exact hk
  obtain ⟨kid, hget, hch, hlt⟩ := hKidInv k hk2
  refine ⟨kid, ?_, ?_, ?_⟩
  · rw [hkids]; exact hget
  · have hce : (advance step b ⟨st, tr⟩ (.parent q f)).st.children k = st.children k := by
      simp [advance, step]
    rw [hce]; exact hch
  · rw [hOrd]; omega

theorem tmp_parent_assemble (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) : arch0_Inv (advance step b x (.parent q f)) := by
  have h1 : (advance step b x (.parent q f)).st.nParents =
      (advance step b x (.parent q f)).tr.nOrders := by
    rw [aux_parent_nParents x q f b, aux_parent_nOrders x q f b, h.1]
  have h2 : (advance step b x (.parent q f)).st.nChildren =
      (advance step b x (.parent q f)).tr.kids.length := by
    have hk : (advance step b x (.parent q f)).tr.kids = x.tr.kids :=
      aux_parent_kids x q f b
    have hc : (advance step b x (.parent q f)).st.nChildren = x.st.nChildren :=
      aux_parent_nChildren x q f b
    rw [hc, hk, h.2.1]
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro id hid
    exact plan0_parent_records_step b x q f h id hid
  · intro k hk
    exact plan3_parent_children b x q f h k hk
  · intro id
    exact plan0_parent_sent_le_qty_step_proof2 b x q f h id

theorem plan4_route_tr_frame (b : Build) (x : Sys) (rid liq : Nat) :
    (advance step b x (.route rid liq)).tr.nOrders = x.tr.nOrders ∧
    (∀ j : Nat, (advance step b x (.route rid liq)).tr.qty j = x.tr.qty j) ∧
    (∀ j : Nat, (advance step b x (.route rid liq)).tr.exec j = x.tr.exec j) := by
  obtain ⟨st, tr⟩ := x
  have hunfold := route_step_unfold2 b st tr rid liq
  have hn : (advance step b ⟨st, tr⟩ (.route rid liq)).tr.nOrders = tr.nOrders := by
    rw [hunfold]
    exact route_record_nOrders tr (routeBySent st rid liq).2
  refine ⟨hn, ?_, ?_⟩
  · intro j
    rw [hunfold]
    exact route_record_qty tr (routeBySent st rid liq).2 j
  · intro j
    rw [hunfold]
    exact route_record_exec tr (routeBySent st rid liq).2 j












theorem plan4_route_tr_frame_proof (b : Build) (x : Sys) (rid liq : Nat) :
    (advance step b x (.route rid liq)).tr.nOrders = x.tr.nOrders ∧
    (∀ j : Nat, (advance step b x (.route rid liq)).tr.qty j = x.tr.qty j) ∧
    (∀ j : Nat, (advance step b x (.route rid liq)).tr.exec j = x.tr.exec j) := by
  obtain ⟨st, tr⟩ := x
  have hunfold := route_step_unfold2 b st tr rid liq
  have hn : (advance step b ⟨st, tr⟩ (.route rid liq)).tr.nOrders = tr.nOrders := by
    rw [hunfold]
    exact route_record_nOrders tr (routeBySent st rid liq).2
  refine ⟨hn, ?_, ?_⟩
  · intro j
    rw [hunfold]
    exact route_record_qty tr (routeBySent st rid liq).2 j
  · intro j
    rw [hunfold]
    exact route_record_exec tr (routeBySent st rid liq).2 j

theorem plan4_route_yes_counts_aux_tmp (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nParents =
      (advance step b x (.route rid liq)).tr.nOrders ∧
    (advance step b x (.route rid liq)).st.nChildren =
      (advance step b x (.route rid liq)).tr.kids.length := by
  obtain ⟨hNP0, hNC0, _, _, _⟩ := hx
  obtain ⟨hTR_NP, _, _⟩ := plan4_route_tr_frame b x rid liq
  have hST_NP : (advance step b x (.route rid liq)).st.nParents = x.st.nParents :=
    (plan1_route_yes_parents b x rid liq h).1
  have hST_NC : (advance step b x (.route rid liq)).st.nChildren = x.st.nChildren + 1 :=
    (plan1_route_yes_children b x rid liq h).1
  have hTR_LEN : (advance step b x (.route rid liq)).tr.kids.length = x.tr.kids.length + 1 :=
    (plan1_route_yes_kids_get b x rid liq h).2.2
  constructor
  · rw [hST_NP, hTR_NP, hNP0]
  · rw [hST_NC, hTR_LEN, hNC0]

theorem plan4_route_yes_counts (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nParents =
      (advance step b x (.route rid liq)).tr.nOrders ∧
    (advance step b x (.route rid liq)).st.nChildren =
      (advance step b x (.route rid liq)).tr.kids.length := by
  obtain ⟨hNP0, hNC0, _, _, _⟩ := hx
  obtain ⟨hTR_NP, _, _⟩ := plan4_route_tr_frame b x rid liq
  have hST_NP : (advance step b x (.route rid liq)).st.nParents = x.st.nParents :=
    (plan1_route_yes_parents b x rid liq h).1
  have hST_NC : (advance step b x (.route rid liq)).st.nChildren = x.st.nChildren + 1 :=
    (plan1_route_yes_children b x rid liq h).1
  have hTR_LEN : (advance step b x (.route rid liq)).tr.kids.length = x.tr.kids.length + 1 :=
    (plan1_route_yes_kids_get b x rid liq h).2.2
  constructor
  · rw [hST_NP, hTR_NP, hNP0]
  · rw [hST_NC, hTR_LEN, hNC0]

theorem plan4_probe_sent_eq (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    ((advance step b x (.route rid liq)).st.parents rid).sent =
      (advance step b x (.route rid liq)).tr.sent rid := by
  have hst := plan1_route_yes_parents b x rid liq h
  obtain ⟨h_st_np, h_st_fun⟩ := hst
  have hsent := plan1_route_yes_sent b x rid liq rid h
  have h_np_eq : x.st.nParents = x.tr.nOrders := hx.1
  have h_rid_lt : rid < x.tr.nOrders := by omega
  have hrid_rec := hx.2.2.1 rid h_rid_lt
  obtain ⟨hrid_q, hrid_s, hrid_c⟩ := hrid_rec
  have hst_j := h_st_fun rid
  rw [hst_j]
  simp only [ite_true]
  rw [hsent]
  simp only [ite_true]
  rw [hrid_s]

theorem plan4_probe_sent_eq4 (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) (j : Nat) (heq : j = rid) :
    ((advance step b x (.route rid liq)).st.parents j).sent =
      (advance step b x (.route rid liq)).tr.sent j := by
  have hst := plan1_route_yes_parents b x rid liq h
  obtain ⟨h_st_np, h_st_fun⟩ := hst
  have hsent := plan1_route_yes_sent b x rid liq j h
  have h_np_eq : x.st.nParents = x.tr.nOrders := hx.1
  have h_rid_lt : rid < x.tr.nOrders := by omega
  have hrid_rec := hx.2.2.1 rid h_rid_lt
  obtain ⟨hrid_q, hrid_s, hrid_c⟩ := hrid_rec
  have hst_j := h_st_fun j
  have heq2 : rid = j := Eq.symm heq
  rw [hst_j, if_pos heq, hsent, if_pos heq2, hrid_s, heq]

theorem plan4_route_yes_parent_records (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent))
    (j : Nat) (hj : j < (advance step b x (.route rid liq)).tr.nOrders) :
    ((advance step b x (.route rid liq)).st.parents j).qty =
        (advance step b x (.route rid liq)).tr.qty j ∧
    ((advance step b x (.route rid liq)).st.parents j).sent =
        (advance step b x (.route rid liq)).tr.sent j ∧
    ((advance step b x (.route rid liq)).st.parents j).cum =
        (advance step b x (.route rid liq)).tr.exec j := by
  have hframe := plan4_route_tr_frame b x rid liq
  obtain ⟨h_nO, h_qty, h_exec⟩ := hframe
  have hst := plan1_route_yes_parents b x rid liq h
  obtain ⟨h_st_np, h_st_fun⟩ := hst
  have hsent := plan1_route_yes_sent b x rid liq j h
  have hqty_j := h_qty j
  have hexec_j := h_exec j
  have hst_j := h_st_fun j
  have h_np_eq : x.st.nParents = x.tr.nOrders := hx.1
  have h_rid_lt : rid < x.tr.nOrders := by omega
  have hj_lt : j < x.tr.nOrders := by omega
  have hrid_rec := hx.2.2.1 rid h_rid_lt
  have hj_rec := hx.2.2.1 j hj_lt
  obtain ⟨hrid_q, hrid_s, hrid_c⟩ := hrid_rec
  obtain ⟨hj_q, hj_s, hj_c⟩ := hj_rec
  by_cases heq : j = rid
  · have hsent_eq := plan4_probe_sent_eq4 b x rid liq hx h j heq
    refine ⟨?_, hsent_eq, ?_⟩
    · rw [hst_j, if_pos heq]
      simp only
      rw [hrid_q]
      have hrj : x.tr.qty rid = x.tr.qty j := by rw [← heq]
      rw [hrj, ← hqty_j]
    · rw [hst_j, if_pos heq]
      simp only
      rw [hrid_c]
      have hrj2 : x.tr.exec rid = x.tr.exec j := by rw [← heq]
      rw [hrj2, ← hexec_j]
  · refine ⟨?_, ?_, ?_⟩
    · rw [hst_j, if_neg heq, hj_q, hqty_j]
    · rw [hst_j, if_neg heq, hj_s, hsent]
      have hne : ¬ (rid = j) := by omega
      rw [if_neg hne, Nat.add_zero]
    · rw [hst_j, if_neg heq, hj_c, hexec_j]

theorem mytest_by_cases (a b : Nat) (h : a < b + 1) : a ≤ b := by
  rcases Decidable.em (a < b) with hlt | hlt
  · omega
  · omega

theorem plan4_route_yes_child_records_aux2 (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent))
    (k : Nat) (hk : k < (advance step b x (.route rid liq)).tr.kids.length) :
    ∃ kid, (advance step b x (.route rid liq)).tr.kids[k]? = some kid ∧
      (advance step b x (.route rid liq)).st.children k =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.route rid liq)).tr.nOrders := by
  have hkids := plan1_route_yes_kids_get b x rid liq h
  have hch := plan1_route_yes_children b x rid liq h
  have hframe := plan4_route_tr_frame b x rid liq
  have hnPar : x.st.nParents = x.tr.nOrders := hx.1
  have hnCh : x.st.nChildren = x.tr.kids.length := hx.2.1
  have hchildInv := hx.2.2.2.1
  have hnOrd : (advance step b x (.route rid liq)).tr.nOrders = x.tr.nOrders := hframe.1
  have hlen : (advance step b x (.route rid liq)).tr.kids.length = x.tr.kids.length + 1 := hkids.2.2
  rcases Decidable.em (k < x.tr.kids.length) with hlt | hlt
  · obtain ⟨hk_old, hnew, hlen2⟩ := hkids
    obtain ⟨kid, hk_some, hch_eq, hlt_ord⟩ := hchildInv k hlt
    have hkeq : (advance step b x (.route rid liq)).tr.kids[k]? = x.tr.kids[k]? := hk_old k hlt
    have hne : k ≠ x.st.nChildren := by omega
    have hchk : (advance step b x (.route rid liq)).st.children k = x.st.children k := hch.2.2 k hne
    exact ⟨kid, by rw [hkeq, hk_some], by rw [hchk, hch_eq], by rw [hnOrd]; exact hlt_ord⟩
  · obtain ⟨hk_old, hnew, hlen2⟩ := hkids
    have hk_eq : k = x.tr.kids.length := by omega
    subst hk_eq
    have hch_new : (advance step b x (.route rid liq)).st.children x.st.nChildren =
        (⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec) := hch.2.1
    rw [hnCh] at hch_new
    exact ⟨⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩, hnew, hch_new, by rw [hnOrd, hnPar.symm]; exact h.1⟩

theorem plan4_route_yes_child_records (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent))
    (k : Nat) (hk : k < (advance step b x (.route rid liq)).tr.kids.length) :
    ∃ kid, (advance step b x (.route rid liq)).tr.kids[k]? = some kid ∧
      (advance step b x (.route rid liq)).st.children k =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.route rid liq)).tr.nOrders := by
  have hkids := plan1_route_yes_kids_get b x rid liq h
  have hch := plan1_route_yes_children b x rid liq h
  have hframe := plan4_route_tr_frame b x rid liq
  have hnPar : x.st.nParents = x.tr.nOrders := hx.1
  have hnCh : x.st.nChildren = x.tr.kids.length := hx.2.1
  have hchildInv := hx.2.2.2.1
  have hnOrd : (advance step b x (.route rid liq)).tr.nOrders = x.tr.nOrders := hframe.1
  have hlen : (advance step b x (.route rid liq)).tr.kids.length = x.tr.kids.length + 1 := hkids.2.2
  rcases Decidable.em (k < x.tr.kids.length) with hlt | hlt
  · obtain ⟨hk_old, hnew, hlen2⟩ := hkids
    obtain ⟨kid, hk_some, hch_eq, hlt_ord⟩ := hchildInv k hlt
    have hkeq : (advance step b x (.route rid liq)).tr.kids[k]? = x.tr.kids[k]? := hk_old k hlt
    have hne : k ≠ x.st.nChildren := by omega
    have hchk : (advance step b x (.route rid liq)).st.children k = x.st.children k := hch.2.2 k hne
    exact ⟨kid, by rw [hkeq, hk_some], by rw [hchk, hch_eq], by rw [hnOrd]; exact hlt_ord⟩
  · obtain ⟨hk_old, hnew, hlen2⟩ := hkids
    have hk_eq : k = x.tr.kids.length := by omega
    subst hk_eq
    have hch_new : (advance step b x (.route rid liq)).st.children x.st.nChildren =
        (⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec) := hch.2.1
    rw [hnCh] at hch_new
    exact ⟨⟨rid, min liq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩, hnew, hch_new, by rw [hnOrd, hnPar.symm]; exact h.1⟩

theorem plan4_route_yes_inv (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    arch0_Inv (advance step b x (.route rid liq)) := by
  have hcounts := plan4_route_yes_counts b x rid liq hx h
  have hpar := plan4_route_yes_parent_records b x rid liq hx h
  have hch := plan4_route_yes_child_records b x rid liq hx h
  have hle : ∀ id, (advance step b x (.route rid liq)).tr.sent id ≤ (advance step b x (.route rid liq)).tr.qty id :=
    fun id => plan1_route_yes_sent_le_of_inv b x rid liq id hx h
  exact ⟨hcounts.1, hcounts.2, hpar, hch, hle⟩

theorem plan1_route_yes_exec_qty_orders_aux_tmp : True := trivial

theorem tmp_plan1_exec_qty_check2 (b : Build) (x : Sys) (rid liq j : Nat)
    (hh : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).tr.exec j = x.tr.exec j ∧
    (advance step b x (.route rid liq)).tr.qty j = x.tr.qty j ∧
    (advance step b x (.route rid liq)).tr.nOrders = x.tr.nOrders := by
  cases x with
  | mk st tr =>
    simp only at hh ⊢
    have hunfold := route_step_unfold2 b st tr rid liq
    have hn : (advance step b ⟨st, tr⟩ (.route rid liq)).tr.nOrders = tr.nOrders := by
      rw [hunfold]
      exact route_record_nOrders tr (routeBySent st rid liq).2
    have hq : (advance step b ⟨st, tr⟩ (.route rid liq)).tr.qty j = tr.qty j := by
      rw [hunfold]
      exact route_record_qty tr (routeBySent st rid liq).2 j
    have he : (advance step b ⟨st, tr⟩ (.route rid liq)).tr.exec j = tr.exec j := by
      rw [hunfold]
      exact route_record_exec tr (routeBySent st rid liq).2 j
    exact ⟨he, hq, hn⟩

theorem tmp_plan1_exec_qty_final_probe (b : Build) (x : Sys) (rid liq j : Nat)
    (h : rid < x.st.nParents ∧
      0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).tr.exec j = x.tr.exec j ∧
    (advance step b x (.route rid liq)).tr.qty j = x.tr.qty j ∧
    (advance step b x (.route rid liq)).tr.nOrders = x.tr.nOrders := by
  cases x with
  | mk st tr =>
    simp only at h ⊢
    have hunfold := route_step_unfold2 b st tr rid liq
    have hn : (advance step b ⟨st, tr⟩ (.route rid liq)).tr.nOrders = tr.nOrders := by
      rw [hunfold]
      exact route_record_nOrders tr (routeBySent st rid liq).2
    have hq : (advance step b ⟨st, tr⟩ (.route rid liq)).tr.qty j = tr.qty j := by
      rw [hunfold]
      exact route_record_qty tr (routeBySent st rid liq).2 j
    have he : (advance step b ⟨st, tr⟩ (.route rid liq)).tr.exec j = tr.exec j := by
      rw [hunfold]
      exact route_record_exec tr (routeBySent st rid liq).2 j
    exact ⟨he, hq, hn⟩

theorem plan4_inv_route_step_proof_tmp (b : Build) (x : Sys) (id liq : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.route id liq)) := by
  intro hx
  by_cases h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · exact plan4_route_yes_inv b x id liq hx h
  · cases x with
    | mk st tr =>
      simp only at h hx ⊢
      exact route_nop_inv2 b st tr id liq h hx

theorem plan4_check_order : True := trivial

theorem plan4_inline_counts (b : Build) (x : Sys) (rid liq : Nat)
    (hx : arch0_Inv x)
    (h : rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)) :
    (advance step b x (.route rid liq)).st.nParents =
      (advance step b x (.route rid liq)).tr.nOrders ∧
    (advance step b x (.route rid liq)).st.nChildren =
      (advance step b x (.route rid liq)).tr.kids.length := by
  obtain ⟨hNP0, hNC0, _, _, _⟩ := hx
  obtain ⟨hTR_NP, _, _⟩ := plan4_route_tr_frame b x rid liq
  have hST_NP : (advance step b x (.route rid liq)).st.nParents = x.st.nParents :=
    (plan1_route_yes_parents b x rid liq h).1
  have hST_NC : (advance step b x (.route rid liq)).st.nChildren = x.st.nChildren + 1 :=
    (plan1_route_yes_children b x rid liq h).1
  have hTR_LEN : (advance step b x (.route rid liq)).tr.kids.length = x.tr.kids.length + 1 :=
    (plan1_route_yes_kids_get b x rid liq h).2.2
  constructor
  · rw [hST_NP, hTR_NP, hNP0]
  · rw [hST_NC, hTR_LEN, hNC0]

theorem plan4_inv_route_step_dup2 (b : Build) (x : Sys) (id liq : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.route id liq)) := by
  intro hx
  by_cases h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · exact plan4_route_yes_inv b x id liq hx h
  · cases x with
    | mk st tr =>
      exact route_nop_inv2 b st tr id liq h hx

theorem plan4_inv_route_step (b : Build) (x : Sys) (id liq : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.route id liq)) := by
  intro hx
  by_cases h : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · exact plan4_route_yes_inv b x id liq hx h
  · cases x with
    | mk st tr =>
      exact route_nop_inv2 b st tr id liq h hx

theorem my_route_step_helper (b : Build) (x : Sys) (id liq : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.route id liq)) :=
  plan4_inv_route_step b x id liq

theorem arch0_inv_route_step_dup_test (b : Build) (x : Sys) (id liq : Nat) (h : arch0_Inv x) :
    arch0_Inv (advance step b x (.route id liq)) :=
  plan4_inv_route_step b x id liq h

theorem route_nop_selfcontained (b : Build) (st : State) (tr : Truth) (rid liq : Nat)
    (hneg : ¬ (rid < st.nParents ∧ 0 < min liq ((st.parents rid).qty - (st.parents rid).sent))) :
    advance step b ⟨st, tr⟩ (.route rid liq) = (⟨st, tr⟩ : Sys) := by
  simp [advance, step, routeBySent, hneg, Truth.observe, Truth.record]

theorem route_nop_selfcontained2 (b : Build) (x : Sys) (rid liq : Nat)
    (hneg : ¬ (rid < x.st.nParents ∧ 0 < min liq ((x.st.parents rid).qty - (x.st.parents rid).sent)))
    (hinv : arch0_Inv x) : arch0_Inv (advance step b x (.route rid liq)) := by
  have heq : advance step b x (.route rid liq) = x := by
    cases x with
    | mk st tr =>
      simp only at hneg ⊢
      simp [advance, step, routeBySent, hneg, Truth.observe, Truth.record]
  rw [heq]
  exact hinv

theorem self_route_nop_eq (b : Build) (st : State) (tr : Truth) (rid liq : Nat)
    (hneg : ¬ (rid < st.nParents ∧ 0 < min liq ((st.parents rid).qty - (st.parents rid).sent))) :
    advance step b ⟨st, tr⟩ (.route rid liq) = (⟨st, tr⟩ : Sys) := by
  simp [advance, step, routeBySent, hneg, Truth.observe, Truth.record]



theorem plan5_fill_sent_le_qty (b : Build) (x : Sys) (k q id : Nat) (h : arch0_Inv x) :
    (advance step b x (.fill k q)).tr.sent id ≤
      (advance step b x (.fill k q)).tr.qty id := by
  obtain ⟨st, tr⟩ := x
  have hout : (step b st (.fill k q)).2 = ([] : List Child) := fill_out_nil b st k q
  have hadv_tr : (advance step b ⟨st, tr⟩ (.fill k q)).tr = tr.observe (.fill k q) := by
    simp only [advance, hout, fill_record_nil_kids]
  rw [hadv_tr]
  rw [plan2_fill_truth_sent]
  have hqty : (tr.observe (.fill k q)).qty id = tr.qty id := fill_qty_pres tr k q id
  rw [hqty]
  exact h.2.2.2.2 id


theorem plan5_fill_child_at (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x)
    (kid : Kid) (hkid : x.tr.kids[k]? = some kid) :
    (advance step b x (.fill k q)).tr.kids[k]? =
        some { kid with done := kid.done + min q (kid.qty - kid.done) } ∧
    (advance step b x (.fill k q)).st.children k =
        ⟨kid.parent, kid.qty, kid.done + min q (kid.qty - kid.done)⟩ ∧
    kid.parent < (advance step b x (.fill k q)).tr.nOrders := by sorry

theorem plan5_fill_child_ne (b : Build) (x : Sys) (k q k' : Nat) (h : arch0_Inv x)
    (hne : k' ≠ k) :
    (advance step b x (.fill k q)).tr.kids[k']? = x.tr.kids[k']? ∧
    (advance step b x (.fill k q)).st.children k' = x.st.children k' ∧
    (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders := by sorry



theorem fill_observe_len_aux (tr : Truth) (k q : Nat) :
    (tr.observe (.fill k q)).kids.length = tr.kids.length := by
  unfold Truth.observe
  cases h : tr.kids[k]? with
  | none => simp [h]
  | some c => simp [h]

theorem plan5_fill_counts (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x) :
    (advance step b x (.fill k q)).st.nParents =
        (advance step b x (.fill k q)).tr.nOrders ∧
    (advance step b x (.fill k q)).st.nChildren =
        (advance step b x (.fill k q)).tr.kids.length := by
  obtain ⟨st, tr⟩ := x
  have hNP : st.nParents = tr.nOrders := h.1
  have hNC : st.nChildren = tr.kids.length := h.2.1
  have hout : (step b st (.fill k q)).2 = ([] : List Child) := fill_out_nil b st k q
  have hNPs : (step b st (.fill k q)).1.nParents = st.nParents := fill_st_nParents3 b st k q
  have hNCs : (step b st (.fill k q)).1.nChildren = st.nChildren := fill_st_nChildren4 b st k q
  have hNO : (tr.observe (.fill k q)).nOrders = tr.nOrders := fill_tr_nOrders4 tr k q
  have hlen : (tr.observe (.fill k q)).kids.length = tr.kids.length := fill_observe_len_aux tr k q
  have hadv_st : (advance step b ⟨st, tr⟩ (.fill k q)).st = (step b st (.fill k q)).1 := rfl
  have hadv_tr : (advance step b ⟨st, tr⟩ (.fill k q)).tr = (tr.observe (.fill k q)).record (step b st (.fill k q)).2 := rfl
  have hrec : (tr.observe (.fill k q)).record (step b st (.fill k q)).2 = (tr.observe (.fill k q)) := by
    rw [hout]; exact fill_record_nil_kids _
  rw [hadv_st, hadv_tr, hrec, hNPs, hNCs, hNO, hNP, hNC, hlen]
  exact ⟨rfl, rfl⟩

theorem plan5_fill_sent_le_qty_proof : ∀ (b : Build) (x : Sys) (k q id : Nat), arch0_Inv x →
    (advance step b x (.fill k q)).tr.sent id ≤
      (advance step b x (.fill k q)).tr.qty id := by
  intro b x k q id h
  obtain ⟨st, tr⟩ := x
  have hout : (step b st (.fill k q)).2 = ([] : List Child) := fill_out_nil b st k q
  have hadv_tr : (advance step b ⟨st, tr⟩ (.fill k q)).tr = tr.observe (.fill k q) := by
    simp only [advance, hout, fill_record_nil_kids]
  rw [hadv_tr]
  rw [plan2_fill_truth_sent]
  have hqty : (tr.observe (.fill k q)).qty id = tr.qty id := fill_qty_pres tr k q id
  rw [hqty]
  exact h.2.2.2.2 id

theorem plan5_fill_child_at_aux_tmp (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x)
    (kid : Kid) (hkid : x.tr.kids[k]? = some kid) :
    (advance step b x (.fill k q)).tr.kids[k]? =
        some { kid with done := kid.done + min q (kid.qty - kid.done) } := by
  rcases x with ⟨st, tr⟩
  simp only at hkid ⊢
  have hNC : st.nChildren = tr.kids.length := h.2.1
  have hk_lt : k < tr.kids.length := aux_idx_lt_of_get_some tr.kids k kid hkid
  have hkSt : k < st.nChildren := by omega
  have hkids_eq : (advance step b ⟨st, tr⟩ (.fill k q)).tr.kids = (tr.observe (.fill k q)).kids :=
    probe_fill_kids_eq b st tr k q
  rw [hkids_eq]
  simp only [Truth.observe, hkid]
  simp [hk_lt]

theorem plan5_fill_child_at_step2b (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x)
    (kid : Kid) (hkid : x.tr.kids[k]? = some kid) :
    (advance step b x (.fill k q)).st.children k =
        ⟨kid.parent, kid.qty, kid.done + min q (kid.qty - kid.done)⟩ := by
  rcases x with ⟨st, tr⟩
  simp only at hkid ⊢
  have hNC : st.nChildren = tr.kids.length := h.2.1
  have hk_len : k < tr.kids.length := aux_idx_lt_of_get_some tr.kids k kid hkid
  have hkSt : k < st.nChildren := by omega
  obtain ⟨kid2, hget2, hch2, hlt2⟩ := h.2.2.2.1 k hk_len
  rw [hkid] at hget2
  simp at hget2
  subst hget2
  have hch : st.children k = (⟨kid.parent, kid.qty, kid.done⟩ : ChildRec) := hch2
  have hadv : (advance step b ⟨st, tr⟩ (.fill k q)).st = (step b st (.fill k q)).1 :=
    fill_adv_st_eq b st tr k q
  rw [hadv]
  simp only [step, if_pos hkSt]
  simp only [aux_upd_eq2]
  rw [hch]

theorem plan5_fill_child_at_full (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x)
    (kid : Kid) (hkid : x.tr.kids[k]? = some kid) :
    (advance step b x (.fill k q)).tr.kids[k]? =
        some { kid with done := kid.done + min q (kid.qty - kid.done) } ∧
    (advance step b x (.fill k q)).st.children k =
        ⟨kid.parent, kid.qty, kid.done + min q (kid.qty - kid.done)⟩ ∧
    kid.parent < (advance step b x (.fill k q)).tr.nOrders := by
  rcases x with ⟨st, tr⟩
  simp only at hkid ⊢
  have hNC : st.nChildren = tr.kids.length := h.2.1
  have hk_len : k < tr.kids.length := aux_idx_lt_of_get_some tr.kids k kid hkid
  have hkSt : k < st.nChildren := by omega
  obtain ⟨kid2, hget2, hch2, hlt2⟩ := h.2.2.2.1 k hk_len
  rw [hkid] at hget2
  simp at hget2
  subst hget2
  have hch : st.children k = (⟨kid.parent, kid.qty, kid.done⟩ : ChildRec) := hch2
  have hkids_eq : (advance step b ⟨st, tr⟩ (.fill k q)).tr.kids = (tr.observe (.fill k q)).kids :=
    probe_fill_kids_eq b st tr k q
  have hobs_eq : (tr.observe (.fill k q)).kids = tr.kids.set k { kid with done := kid.done + min q (kid.qty - kid.done) } := by
    simp [Truth.observe, hkid]
  have hget_set : (tr.kids.set k { kid with done := kid.done + min q (kid.qty - kid.done) })[k]? = some { kid with done := kid.done + min q (kid.qty - kid.done) } :=
    probe_set_get_self tr.kids k _ hk_len
  have htr_get : (advance step b ⟨st, tr⟩ (.fill k q)).tr.kids[k]? = some { kid with done := kid.done + min q (kid.qty - kid.done) } := by
    rw [hkids_eq, hobs_eq, hget_set]
  have hadv : (advance step b ⟨st, tr⟩ (.fill k q)).st = (step b st (.fill k q)).1 :=
    fill_adv_st_eq b st tr k q
  have hst_get : (advance step b ⟨st, tr⟩ (.fill k q)).st.children k = (⟨kid.parent, kid.qty, kid.done + min q (kid.qty - kid.done)⟩ : ChildRec) := by
    rw [hadv]
    simp only [step, if_pos hkSt]
    simp only [aux_upd_eq2]
    rw [hch]
  have hnord : (advance step b ⟨st, tr⟩ (.fill k q)).tr.nOrders = tr.nOrders :=
    probe_fill_adv_nOrders b st tr k q
  refine ⟨htr_get, hst_get, ?_⟩
  rw [hnord]
  exact hlt2

theorem plan5_fill_child_at_checktmp : True := trivial

theorem plan5_fill_child_at_copy (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x)
    (kid : Kid) (hkid : x.tr.kids[k]? = some kid) :
    (advance step b x (.fill k q)).tr.kids[k]? =
        some { kid with done := kid.done + min q (kid.qty - kid.done) } ∧
    (advance step b x (.fill k q)).st.children k =
        ⟨kid.parent, kid.qty, kid.done + min q (kid.qty - kid.done)⟩ ∧
    kid.parent < (advance step b x (.fill k q)).tr.nOrders := by
  rcases x with ⟨st, tr⟩
  simp only at hkid ⊢
  have hNC : st.nChildren = tr.kids.length := h.2.1
  have hk_len : k < tr.kids.length := aux_idx_lt_of_get_some tr.kids k kid hkid
  have hkSt : k < st.nChildren := by omega
  obtain ⟨kid2, hget2, hch2, hlt2⟩ := h.2.2.2.1 k hk_len
  rw [hkid] at hget2
  simp at hget2
  subst hget2
  have hch : st.children k = (⟨kid.parent, kid.qty, kid.done⟩ : ChildRec) := hch2
  have hkids_eq : (advance step b ⟨st, tr⟩ (.fill k q)).tr.kids = (tr.observe (.fill k q)).kids :=
    probe_fill_kids_eq b st tr k q
  have hobs_eq : (tr.observe (.fill k q)).kids = tr.kids.set k { kid with done := kid.done + min q (kid.qty - kid.done) } := by
    simp [Truth.observe, hkid]
  have hget_set : (tr.kids.set k { kid with done := kid.done + min q (kid.qty - kid.done) })[k]? = some { kid with done := kid.done + min q (kid.qty - kid.done) } :=
    probe_set_get_self tr.kids k _ hk_len
  have htr_get : (advance step b ⟨st, tr⟩ (.fill k q)).tr.kids[k]? = some { kid with done := kid.done + min q (kid.qty - kid.done) } := by
    rw [hkids_eq, hobs_eq, hget_set]
  have hadv : (advance step b ⟨st, tr⟩ (.fill k q)).st = (step b st (.fill k q)).1 :=
    fill_adv_st_eq b st tr k q
  have hst_get : (advance step b ⟨st, tr⟩ (.fill k q)).st.children k = (⟨kid.parent, kid.qty, kid.done + min q (kid.qty - kid.done)⟩ : ChildRec) := by
    rw [hadv]
    simp only [step, if_pos hkSt]
    simp only [aux_upd_eq2]
    rw [hch]
  have hnord : (advance step b ⟨st, tr⟩ (.fill k q)).tr.nOrders = tr.nOrders :=
    probe_fill_adv_nOrders b st tr k q
  refine ⟨htr_get, hst_get, ?_⟩
  rw [hnord]
  exact hlt2

theorem probe_tmp_ne1b (b : Build) (st : State) (k q k' : Nat) (hne : k' ≠ k) :
    (step b st (.fill k q)).1.children k' = st.children k' := by
  unfold step
  simp only
  split
  · simp only [upd]
    split
    · rename_i heq; exact absurd heq hne
    · rfl
  · rfl

theorem set_get_ne_helper (l : List Kid) (k k' : Nat) (a : Kid) (hne : k' ≠ k) :
    (l.set k a)[k']? = l[k']? := by
  induction l generalizing k k' with
  | nil => simp
  | cons b bs ih =>
    cases k with
    | zero =>
      cases k' with
      | zero => simp at hne
      | succ k' => simp
    | succ k =>
      cases k' with
      | zero => simp
      | succ k' =>
        simp at hne ⊢
        exact ih k k' hne

theorem probe_tmp_ne2c (tr : Truth) (k q k' : Nat) (hne : k' ≠ k) :
    (tr.observe (.fill k q)).kids[k']? = tr.kids[k']? := by
  simp only [Truth.observe]
  split
  · rename_i heq
    exact set_get_ne_helper tr.kids k k' _ hne
  · rfl

theorem probe_obs_fill_nord (tr : Truth) (k q : Nat) : (tr.observe (.fill k q)).nOrders = tr.nOrders := by
  simp only [Truth.observe]
  split
  · rfl
  · rfl

theorem plan5_fill_child_records_auxchk (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x)
    (k' : Nat) (hk' : k' < (advance step b x (.fill k q)).tr.kids.length) :
    ∃ kid, (advance step b x (.fill k q)).tr.kids[k']? = some kid ∧
      (advance step b x (.fill k q)).st.children k' =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.fill k q)).tr.nOrders := by
  have hcounts := plan5_fill_counts b x k q h
  have h1 : (advance step b x (.fill k q)).st.nChildren = x.st.nChildren :=
    fill_st_nChildren4 b x.st k q
  have h2 : x.st.nChildren = x.tr.kids.length := h.2.1
  have hlen_eq : (advance step b x (.fill k q)).tr.kids.length = x.tr.kids.length := by omega
  by_cases heq : k' = k
  · obtain ⟨kid, hkid_some, hchild_eq, hpar_lt⟩ := h.2.2.2.1 k' (by omega)
    have hkid_some_k : x.tr.kids[k]? = some kid := by rw [← heq]; exact hkid_some
    obtain ⟨h_tr_eq, h_st_eq, h_par⟩ := plan5_fill_child_at b x k q h kid hkid_some_k
    have h_tr_eq' : (advance step b x (.fill k q)).tr.kids[k']? =
        some { kid with done := kid.done + min q (kid.qty - kid.done) } := by rw [heq]; exact h_tr_eq
    have h_st_eq' : (advance step b x (.fill k q)).st.children k' =
        ⟨kid.parent, kid.qty, kid.done + min q (kid.qty - kid.done)⟩ := by rw [heq]; exact h_st_eq
    exact ⟨{ kid with done := kid.done + min q (kid.qty - kid.done) }, h_tr_eq', by simpa using h_st_eq',
      by simpa using h_par⟩
  · obtain ⟨kid, hkid_some, hchild_eq, hpar_lt⟩ := h.2.2.2.1 k' (by omega)
    obtain ⟨h_tr_eq, h_st_eq, h_nord_eq⟩ := plan5_fill_child_ne b x k q k' h heq
    exact ⟨kid, by rw [h_tr_eq]; exact hkid_some, by rw [h_st_eq]; exact hchild_eq, by rw [h_nord_eq]; exact hpar_lt⟩

theorem plan5_fill_child_records_auxchk2 (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x)
    (k' : Nat) (hk' : k' < (advance step b x (.fill k q)).tr.kids.length) :
    ∃ kid, (advance step b x (.fill k q)).tr.kids[k']? = some kid ∧
      (advance step b x (.fill k q)).st.children k' =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.fill k q)).tr.nOrders :=
  plan5_fill_child_records_auxchk b x k q h k' hk'

theorem plan5_fill_child_records (b : Build) (x : Sys) (k q : Nat) (h : arch0_Inv x)
    (k' : Nat) (hk' : k' < (advance step b x (.fill k q)).tr.kids.length) :
    ∃ kid, (advance step b x (.fill k q)).tr.kids[k']? = some kid ∧
      (advance step b x (.fill k q)).st.children k' =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.fill k q)).tr.nOrders :=
  plan5_fill_child_records_auxchk b x k q h k' hk'

theorem arch1_sent_le_of_inv (x : Sys) (h : arch0_Inv x) (id : Nat) :
    x.tr.sent id ≤ x.tr.qty id := h.2.2.2.2 id

theorem arch1_routes_of_inv (b : Build) (x : Sys) (id liq : Nat)
    (h : arch0_Inv x) :
    (step b x.st (.route id liq)).2 = expectedRoute x.tr id liq :=
  arch0_route_output_of_inv b x id liq h

theorem arch1_cum_of_inv (x : Sys) (h : arch0_Inv x) (id : Nat)
    (hid : id < x.tr.nOrders) :
    (x.st.parents id).cum = x.tr.exec id := (h.2.2.1 id hid).2.2

theorem arch1_exec_le_qty_run (b : Build) (evs : List Event) (id : Nat) :
    (run step b evs).tr.exec id ≤ (run step b evs).tr.qty id := by
  have h1 := exec_le_sent step b evs id
  have h2 := arch1_sent_le_of_inv (run step b evs) (arch0_inv_run b evs) id
  omega

theorem arch1_no_child_of_filled (b : Build) (x : Sys) (h : arch0_Inv x)
    (e : Event) (id : Nat)
    (hfilled : x.tr.exec id = x.tr.qty id)
    (hle : x.tr.exec id ≤ x.tr.sent id)
    (c : Child) (hc : c ∈ (step b x.st e).2) :
    c.parent ≠ id := by
  obtain ⟨pid, liq, heq, hceq, hlt, hpos⟩ := arch0_output_cases b x.st e c hc
  subst heq
  have hNP : x.st.nParents = x.tr.nOrders := h.1
  have hpid : pid < x.tr.nOrders := by omega
  have hsent := (h.2.2.1 pid hpid).2.1
  have hqty := (h.2.2.1 pid hpid).1
  intro hcon
  have hcp : c.parent = pid := by rw [hceq]
  have hpid_eq : pid = id := by omega
  rw [hpid_eq] at hsent hqty hpos
  omega

def arch2_Inv (x : Sys) : Prop :=
  arch0_Inv x

theorem arch2_inv_start : arch2_Inv start := by sorry

theorem arch2_inv_parent_step (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    arch2_Inv x → arch2_Inv (advance step b x (.parent q f)) := by sorry

theorem arch2_inv_route_step (b : Build) (x : Sys) (id liq : Nat) :
    arch2_Inv x → arch2_Inv (advance step b x (.route id liq)) := by sorry

theorem arch2_inv_ack_step (b : Build) (x : Sys) (k : Nat) :
    arch2_Inv x → arch2_Inv (advance step b x (.ack k)) := by sorry

theorem arch2_inv_fill_step (b : Build) (x : Sys) (k q : Nat) :
    arch2_Inv x → arch2_Inv (advance step b x (.fill k q)) := by sorry

theorem arch2_inv_advance (b : Build) (x : Sys) (e : Event) :
    arch2_Inv x → arch2_Inv (advance step b x e) := by sorry

theorem arch2_inv_run (b : Build) (evs : List Event) :
    arch2_Inv (run step b evs) := arch0_inv_run b evs


theorem arch2_inv_run_aux (b : Build) (evs : List Event) :
    arch2_Inv (run step b evs) := arch0_inv_run b evs

theorem arch2_inv_run2 (b : Build) (evs : List Event) :
    arch2_Inv (run step b evs) := arch0_inv_run b evs



theorem plan6_parent_new_record (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) :
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).qty =
        (advance step b x (.parent q f)).tr.qty x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).sent =
        (advance step b x (.parent q f)).tr.sent x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).cum =
        (advance step b x (.parent q f)).tr.exec x.tr.nOrders :=
  plan3_parent_new_record b x q f h








theorem plan6_parent_old_records_aux_wrap (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) (hid : id < x.tr.nOrders) :
    ((advance step b x (.parent q f)).st.parents id).qty =
        (advance step b x (.parent q f)).tr.qty id ∧
    ((advance step b x (.parent q f)).st.parents id).sent =
        (advance step b x (.parent q f)).tr.sent id ∧
    ((advance step b x (.parent q f)).st.parents id).cum =
        (advance step b x (.parent q f)).tr.exec id :=
  plan3_parent_old_records b x q f h id hid

theorem plan6_parent_old_records (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) (hid : id < x.tr.nOrders) :
    ((advance step b x (.parent q f)).st.parents id).qty =
        (advance step b x (.parent q f)).tr.qty id ∧
    ((advance step b x (.parent q f)).st.parents id).sent =
        (advance step b x (.parent q f)).tr.sent id ∧
    ((advance step b x (.parent q f)).st.parents id).cum =
        (advance step b x (.parent q f)).tr.exec id :=
  plan3_parent_old_records b x q f h id hid

theorem plan6_parent_new_record_proof (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) :
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).qty =
        (advance step b x (.parent q f)).tr.qty x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).sent =
        (advance step b x (.parent q f)).tr.sent x.tr.nOrders ∧
    ((advance step b x (.parent q f)).st.parents x.tr.nOrders).cum =
        (advance step b x (.parent q f)).tr.exec x.tr.nOrders :=
  plan3_parent_new_record b x q f h

theorem plan6_parent_children (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (k : Nat)
    (hk : k < (advance step b x (.parent q f)).tr.kids.length) :
    ∃ kid, (advance step b x (.parent q f)).tr.kids[k]? = some kid ∧
      (advance step b x (.parent q f)).st.children k =
        ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < (advance step b x (.parent q f)).tr.nOrders :=
  plan3_parent_children b x q f h k hk

theorem plan6_parent_sent_le_qty_aux_wrap (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id ≤
      (advance step b x (.parent q f)).tr.qty id :=
  plan3_parent_sent_le_qty b x q f h id

theorem plan6_parent_sent_le_qty (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) (id : Nat) :
    (advance step b x (.parent q f)).tr.sent id ≤
      (advance step b x (.parent q f)).tr.qty id :=
  plan3_parent_sent_le_qty b x q f h id

theorem plan6_inv_parent_step_proof_via_existing (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) :
    arch0_Inv (advance step b x (.parent q f)) :=
  arch0_inv_parent_step_proof b x q f h

theorem plan6_inv_parent_step (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (h : arch0_Inv x) :
    arch0_Inv (advance step b x (.parent q f)) :=
  arch0_inv_parent_step_proof b x q f h

theorem arch0_parent_selfcontained (b : Build) (st : State) (tr : Truth) (q : Nat) (f : Bool)
    (hNP : st.nParents = tr.nOrders)
    (hNC : st.nChildren = tr.kids.length)
    (hRec : ∀ id, id < tr.nOrders → (st.parents id).qty = tr.qty id ∧ (st.parents id).sent = tr.sent id ∧ (st.parents id).cum = tr.exec id)
    (hKid : ∀ k, k < tr.kids.length → ∃ kid, tr.kids[k]? = some kid ∧ st.children k = ⟨kid.parent, kid.qty, kid.done⟩ ∧ kid.parent < tr.nOrders)
    (hLe : ∀ id, tr.sent id ≤ tr.qty id) :
    arch0_Inv (advance step b ⟨st, tr⟩ (.parent q f)) := by
  have hkids : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids = tr.kids := by
    simp [advance, step, Truth.observe, Truth.record]
  have hnOrd : (advance step b ⟨st, tr⟩ (.parent q f)).tr.nOrders = tr.nOrders + 1 := by
    simp [advance, step, Truth.observe, Truth.record]
  have hnPar : (advance step b ⟨st, tr⟩ (.parent q f)).st.nParents = st.nParents + 1 := by
    simp [advance, step]
  have hnChi : (advance step b ⟨st, tr⟩ (.parent q f)).st.nChildren = st.nChildren := by
    simp [advance, step]
  have hklen : (advance step b ⟨st, tr⟩ (.parent q f)).tr.kids.length = tr.kids.length := by rw [hkids]
  have hchild_eq : ∀ k, (advance step b ⟨st, tr⟩ (.parent q f)).st.children k = st.children k := by
    intro k; simp [advance, step]
  have hStPar : ∀ id, (advance step b ⟨st, tr⟩ (.parent q f)).st.parents id = upd st.parents st.nParents ⟨q, f, 0, 0⟩ id := by
    intro id; simp [advance, step]
  have hTrQty : ∀ id, (advance step b ⟨st, tr⟩ (.parent q f)).tr.qty id = upd tr.qty tr.nOrders q id := by
    intro id; simp [advance, step, Truth.observe, Truth.record, upd]
  have hTrSent : ∀ id, (advance step b ⟨st, tr⟩ (.parent q f)).tr.sent id = tr.sent id := by
    intro id; simp [Truth.sent, hkids]
  have hTrExec : ∀ id, (advance step b ⟨st, tr⟩ (.parent q f)).tr.exec id = tr.exec id := by
    intro id; simp [Truth.exec, hkids]
  have h0sent : tr.sent tr.nOrders = 0 := by
    unfold Truth.sent
    apply sentFor_eq_zero_of_bound tr.kids tr.nOrders tr.nOrders _ (Nat.le_refl _)
    intro k hk
    obtain ⟨n, hn⟩ := aux_probeA tr.kids k hk
    have hnlt : n < tr.kids.length := aux_idx_lt_of_get_some tr.kids n k hn
    obtain ⟨kid', hk', _, hlt⟩ := hKid n hnlt
    rw [hn] at hk'; simp at hk'; subst hk'; exact hlt
  have h0exec : tr.exec tr.nOrders = 0 := by
    unfold Truth.exec
    apply execFor_eq_zero_of_bound tr.kids tr.nOrders tr.nOrders _ (Nat.le_refl _)
    intro k hk
    obtain ⟨n, hn⟩ := aux_probeA tr.kids k hk
    have hnlt : n < tr.kids.length := aux_idx_lt_of_get_some tr.kids n k hn
    obtain ⟨kid', hk', _, hlt⟩ := hKid n hnlt
    rw [hn] at hk'; simp at hk'; subst hk'; exact hlt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hnPar, hnOrd, hNP]
  · rw [hnChi, hklen, hNC]
  · intro id hid
    rw [hnOrd] at hid
    rw [hStPar id, hTrQty id, hTrSent id, hTrExec id]
    by_cases heq : id = tr.nOrders
    · subst heq; rw [hNP, aux_upd_eq2, aux_upd_eq2]; simp [h0sent, h0exec]
    · have hne_st : id ≠ st.nParents := by omega
      have hid_old : id < tr.nOrders := by omega
      rw [aux_upd_ne2 _ _ _ _ hne_st, aux_upd_ne2 _ _ _ _ heq]
      exact hRec id hid_old
  · intro k hk
    rw [hklen] at hk
    obtain ⟨kid, hkget2, hch, hlt⟩ := hKid k hk
    refine ⟨kid, ?_, ?_, ?_⟩
    · rw [hkids]; exact hkget2
    · rw [hchild_eq k]; exact hch
    · omega
  · intro id
    rw [hTrSent id, hTrQty id]
    by_cases heq : id = tr.nOrders
    · subst heq; rw [aux_upd_eq2, h0sent]; exact Nat.zero_le q
    · rw [aux_upd_ne2 _ _ _ _ heq]; exact hLe id

theorem arch0_inv_parent_step_aux (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    arch0_Inv x → arch0_Inv (advance step b x (.parent q f)) := by
  intro h; rcases x with ⟨st, tr⟩; exact arch0_parent_selfcontained b st tr q f h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> refine ⟨rfl, rfl⟩

theorem req_routes_available    : RoutesAvailable step := by
  intro b evs id liq
  exact arch1_routes_of_inv b (run step b evs) id liq (arch2_inv_run b evs)

theorem req_never_overroute     : NeverOverroute step := by
  intro b evs id
  exact arch1_sent_le_of_inv (run step b evs) (arch2_inv_run b evs) id

theorem req_stop_when_filled    : StopWhenFilled step := by
  intro b evs e id hfilled c hc
  exact arch1_no_child_of_filled b (run step b evs) (arch2_inv_run b evs)
    e id hfilled (exec_le_sent step b evs id) c hc

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  exact Nat.le_trans (exec_le_sent step b evs id)
    (arch1_sent_le_of_inv (run step b evs) (arch2_inv_run b evs) id)

theorem req_fill_accounting     : FillAccounting step := by
  intro b evs id hid
  exact arch1_cum_of_inv (run step b evs) (arch2_inv_run b evs) id hid

end OrderRouter
