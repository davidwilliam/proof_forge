-- Protected definitions (trusted).
structure Wallet where
  cents : Nat
deriving Repr

def total (ws : List Wallet) : Nat := (ws.map (·.cents)).foldl (· + ·) 0

def Spec.SplitsEvenly (split : Nat → Nat → List Nat) : Prop :=
  ∀ a n, 0 < n → (split a n).length = n ∧ (split a n).foldl (· + ·) 0 = a
