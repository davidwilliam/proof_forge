Proof plan: Split on admissibility: the inadmissible case is unchanged, while the admissible case preserves the limit and maps each client entry either to itself or to `advance`. For a mapped requesting entry, admissibility must refer to that exact entry: distinct ids imply that any member with the requested id is the `lookup` result, so its `windowCount` is below the limit and advancing it adds one without exceeding the limit. Other entries keep their assumed bound.

```lean
theorem plan0_id_mem_map (l : List Client) (x : Client) (h : x ∈ l) :
    x.id ∈ l.map Client.id := by sorry

theorem plan0_lookup_self_of_nodup (l : List Client) (x : Client)
    (hnd : List.Nodup (l.map Client.id)) (hmem : x ∈ l) :
    lookup l x.id = some x := by sorry

theorem plan0_advance_count_le (s : State) (c : Client) (t : Nat)
    (h : windowCount s c t < s.limit) :
    (advance s c t).count ≤ s.limit := by sorry

theorem plan0_windowCount_lt_of_admissible (s : State) (r : Request) (x : Client)
    (hadm : Admissible s r) (hmem : x ∈ s.clients) (hid : x.id = r.client) :
    windowCount s x r.time < s.limit := by sorry

theorem plan0_mapped_count_le (s : State) (r : Request)
    (hadm : Admissible s r)
    (hbound : ∀ c ∈ s.clients, c.count ≤ s.limit)
    (c : Client)
    (hc : c ∈ s.clients.map (fun x => if x.id = r.client then advance s x r.time else x)) :
    c.count ≤ s.limit := by sorry
```