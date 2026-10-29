import OrderRouter.Spec
/-!
# Generic helper lemmas (agent-visible)

Proved facts about `run`, `sentFor`, `execFor` and the venue model in `Truth.observe`. They
add no trust and say nothing about any router: every lemma holds for every `step`.
-/

namespace OrderRouter

@[simp] theorem run_nil (step : Impl) (b : Build) : run step b [] = start := rfl

theorem run_snoc (step : Impl) (b : Build) (evs : List Event) (e : Event) :
    run step b (evs ++ [e]) = advance step b (run step b evs) e := by
  simp [run, List.foldl_append]

/-- Induction over event sequences: a property of the start that every event preserves
holds after every sequence of events. -/
theorem run_induction (step : Impl) (b : Build) (P : Sys → Prop) (h0 : P start)
    (hs : ∀ x e, P x → P (advance step b x e)) : ∀ evs, P (run step b evs) := by
  intro evs
  suffices h : ∀ (l : List Event) x, P x → P (l.foldl (advance step b) x) from h evs start h0
  intro l
  induction l with
  | nil => intro x hx; exact hx
  | cons e es ih => intro x hx; exact ih _ (hs x e hx)

@[simp] theorem sentFor_nil (id : Nat) : sentFor [] id = 0 := rfl
@[simp] theorem execFor_nil (id : Nat) : execFor [] id = 0 := rfl

@[simp] theorem sentFor_cons (k : Kid) (ks : List Kid) (id : Nat) :
    sentFor (k :: ks) id = (if k.parent = id then k.qty else 0) + sentFor ks id := rfl

@[simp] theorem execFor_cons (k : Kid) (ks : List Kid) (id : Nat) :
    execFor (k :: ks) id = (if k.parent = id then k.done else 0) + execFor ks id := rfl

@[simp] theorem sentFor_append (l₁ l₂ : List Kid) (id : Nat) :
    sentFor (l₁ ++ l₂) id = sentFor l₁ id + sentFor l₂ id := by
  induction l₁ with
  | nil => simp
  | cons k ks ih => simp [ih]; omega

@[simp] theorem execFor_append (l₁ l₂ : List Kid) (id : Nat) :
    execFor (l₁ ++ l₂) id = execFor l₁ id + execFor l₂ id := by
  induction l₁ with
  | nil => simp
  | cons k ks ih => simp [ih]; omega

/-- Newly sent child orders have nothing executed. -/
@[simp] theorem execFor_new (out : List Child) (id : Nat) :
    execFor (out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id = 0 := by
  induction out with
  | nil => rfl
  | cons c cs ih => simp [ih]

/-- Shares sent in newly sent child orders, as a sum over the router's output. -/
theorem sentFor_new_cons (c : Child) (cs : List Child) (id : Nat) :
    sentFor ((c :: cs).map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id
      = (if c.parent = id then c.qty else 0) + sentFor (cs.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id := rfl

/-- Recording executions on one child order leaves the shares sent unchanged. -/
theorem sentFor_set_done (l : List Kid) (k : Nat) (c : Kid) (d : Nat) (h : l[k]? = some c) (id : Nat) :
    sentFor (l.set k { c with done := d }) id = sentFor l id := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => simp at h; subst h; simp
    | succ k => simp at h; simp [ih k h]

/-- Recording `x` more executed shares on child order `k` adds `x` to its parent's total. -/
theorem execFor_set_done (l : List Kid) (k : Nat) (c : Kid) (x : Nat) (h : l[k]? = some c) (id : Nat) :
    execFor (l.set k { c with done := c.done + x }) id = execFor l id + (if c.parent = id then x else 0) := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero =>
      simp at h; subst h
      simp only [List.set_cons_zero, execFor_cons]
      split <;> omega
    | succ k =>
      simp at h
      simp only [List.set_cons_succ, execFor_cons, ih k h]
      omega

/-- Shares executed never exceed shares sent, when no child order has more executed than its
quantity. -/
theorem execFor_le_sentFor (l : List Kid) (h : ∀ k ∈ l, k.done ≤ k.qty) (id : Nat) :
    execFor l id ≤ sentFor l id := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have := ih (fun k hk => h k (by simp [hk]))
    simp only [execFor_cons, sentFor_cons]
    split <;> omega

/-- The venue model never executes more shares of a child order than its quantity, whatever
the router does. -/
theorem done_le_qty (step : Impl) (b : Build) (evs : List Event) :
    ∀ k ∈ (run step b evs).tr.kids, k.done ≤ k.qty := by
  refine run_induction step b (fun x => ∀ k ∈ x.tr.kids, k.done ≤ k.qty) (by simp [start, Truth.empty]) ?_ evs
  intro x e hx
  have hobs : ∀ k ∈ (x.tr.observe e).kids, k.done ≤ k.qty := by
    cases e with
    | fill j q =>
      simp only [Truth.observe]
      split
      · rename_i c hc
        intro k hk
        rcases List.mem_or_eq_of_mem_set hk with hk | hk
        · exact hx k hk
        · subst hk; have := hx c (List.mem_of_getElem? (by assumption)); simp; omega
      · exact hx
    | _ => exact hx
  intro k hk
  simp only [advance, Truth.record, List.mem_append, List.mem_map] at hk
  rcases hk with hk | ⟨c, _, rfl⟩
  · exact hobs k hk
  · simp

/-- For every router, the shares executed for a parent never exceed the shares sent for it. -/
theorem exec_le_sent (step : Impl) (b : Build) (evs : List Event) (id : Nat) :
    (run step b evs).tr.exec id ≤ (run step b evs).tr.sent id :=
  execFor_le_sentFor _ (done_le_qty step b evs) id

end OrderRouter
